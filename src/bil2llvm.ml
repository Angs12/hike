(* LLVM emitter core: declarations, blocks, subs, sigs, entry.
   The lanes live in bil2llvm_{env,section,exp,mem,fp,calls}.
   The emission state is two values: the run ctx and one sub_scope
   per sub, opened and dropped by [emit_program]'s body loop. *)

open Bap.Std
module Abi = Hike_abi
open Bil2llvm_env
open Bil2llvm_exp
open Bil2llvm_mem
open Bil2llvm_calls
open Bil2llvm_fp
open Bil2llvm_section

(* The phi incomings ARE the emitted CFG's edges: the per-sub row table
   records every rendered terminator, so a block the emitter never
   branches to takes no incoming. *)
let update_phis ctx scope transfer_vars blks =
  (* The rendered edges group by target once; per block the join is a
     lookup, not a filter over every edge. *)
  let by_target =
    Base.List.fold !(scope.edges) ~init:Tid.Map.empty
      ~f:(fun m r ->
        Core.Map.add_multi m ~key:r.e_target ~data:r)
  in
  Seq.iter blks ~f:(fun blk ->
      let blk_tid = Term.tid blk in
      let rows =
        Core.Map.find by_target blk_tid |> Option.value ~default:[]
      in
      Base.List.iter transfer_vars ~f:(fun var ->
          let phi = get_phi scope blk_tid var in
          Bil2llvm_phi.add_incomings ctx scope ~phi ~rows ~target:blk_tid var))


(* Each jmp of a series renders in its own basic block; every direct
   edge lands in the edge table so target phis name the terminator's
   block.  The terminal guard is complete: literal-true branches
   unconditionally, else the false edge is [unreachable]. *)
let create_branches ctx scope blk_tid llvm_builder branches =
  let open Bap.Std in
  let llvm_ctx = ctx.llvm_ctx in
  let fn = Llvm.block_parent (Llvm.insertion_block llvm_builder) in
  let jmps = Seq.to_list branches in
  let note_edge ~(cur : Llvm.llbasicblock) (tid : Tid.t) =
    Bil2llvm_phi.record_edge scope ~pred:blk_tid ~target:tid ~term_bb:cur ()
  in
  (* The series' terminal guard: an unconditional branch when no
     other path can fall through (a true condition, or the first edge
     of a two-way branch); otherwise the condition selects between the
     target and a dead end. *)
  let emit_terminal_guard ~(first : bool) ~bb ~(cond : exp) =
    if Hike_stack_model.is_true_cond cond || first then
      Llvm.build_br bb llvm_builder |> ignore
    else
      let dead = Llvm.append_block llvm_ctx (Tid.name blk_tid ^ "-dead") fn in
      let cond_val = create_exp ctx scope llvm_builder blk_tid cond in
      Llvm.build_cond_br cond_val bb dead llvm_builder |> ignore;
      Llvm.position_at_end dead llvm_builder;
      Llvm.build_unreachable llvm_builder |> ignore
  in
  let rec step ~(first : bool) cur = function
    | [] -> ()
    | j :: rest -> (
        let cont_bb =
          match rest with
          | [] -> None
          | _ -> Some (Llvm.append_block llvm_ctx (Tid.name blk_tid ^ "-sw") fn)
        in
        match Jmp.kind j |> goto_label_exn with
        | Direct tid ->
            if Bil2llvm_env.is_interrupt_name (Tid.name tid) then
              (* A divide-by-zero trap lifts as a direct goto to the
                 interrupt sub; it is terminal. *)
              create_interrupt ctx llvm_builder
            else (
              let bb = get_bb scope tid in
              note_edge ~cur tid;
              match cont_bb with
              | Some next ->
                let cond = create_exp ctx scope llvm_builder blk_tid (Jmp.cond j) in
                Llvm.build_cond_br cond bb next llvm_builder |> ignore;
                Llvm.position_at_end next llvm_builder;
                step ~first:false next rest
              | None -> emit_terminal_guard ~first ~bb ~cond:(Jmp.cond j))
        | Indirect exp -> (
            (* An indirect jmp ends its own path; later jmps still
               render. *)
            let target_val = create_exp ctx scope llvm_builder blk_tid exp in
            build_indirect_br llvm_builder target_val
               ~reserved_destinations:indirect_br_one_reserved |> ignore;
            (match cont_bb with
             | Some next ->
                 Llvm.position_at_end next llvm_builder;
                 step ~first:false next rest
             | None -> ())))
  in
  step ~first:true (Llvm.insertion_block llvm_builder) jmps

let create_control_flow ctx scope llvm_builder blk sub fr =
  let control_flow = Term.enum jmp_t blk in
  let tid = Term.tid blk in
  if Seq.is_empty control_flow then
    (* Def-only blocks still need a terminator. *)
    create_return ctx scope tid llvm_builder sub
  else
  match cf_type control_flow with
  | Br -> create_branches ctx scope tid llvm_builder control_flow
  | Int -> create_interrupt ctx llvm_builder
  | Ret -> create_return ctx scope tid llvm_builder sub
  | CallIndirect ->
      let j = Bap.Std.Seq.hd_exn control_flow in
      create_indirect_call ctx scope llvm_builder tid j
  | CallIndirectTail ->
      let j = Bap.Std.Seq.hd_exn control_flow in
      create_indirect_tail ctx scope llvm_builder tid blk sub j
  | CallFun ->
      let call = Bap.Std.Seq.hd_exn control_flow |> call_exn in
      create_call ctx scope llvm_builder tid blk sub call fr

let transfer_with_phis ctx scope transfer_vars llvm_builder blk_tid =
  Base.List.iter transfer_vars ~f:(fun var ->
      let typ = var_lltype ctx var in
      let res = Llvm.build_empty_phi typ "" llvm_builder in
      insert_phi scope blk_tid var res;
      insert_local scope blk_tid var res)

let create_elts ctx scope llvm_builder blk sub_tid fr =
  let tid = Term.tid blk in
  Blk.elts blk
  |> Seq.iter ~f:(fun elt ->
      match elt with
      | `Def def -> create_def ctx scope tid llvm_builder sub_tid fr def
      | `Phi _ -> ()
      | `Jmp _ -> ())

let populate_blks ctx scope transfer_vars blks sub fr =
  let sub_tid = Term.tid sub in
  Seq.iter blks ~f:(fun blk ->
      let llvm_builder =
        Llvm.builder_at_end ctx.llvm_ctx (get_bb scope (Term.tid blk))
      in
      transfer_with_phis ctx scope transfer_vars llvm_builder (Term.tid blk);
      create_elts ctx scope llvm_builder blk sub_tid fr;
      create_control_flow ctx scope llvm_builder blk sub fr)


let exit_entry scope llvm_builder sub =
  let target = entry_blk_tid sub in
  ignore (Llvm.build_br (get_bb scope target) llvm_builder);
  Bil2llvm_phi.record_edge scope ~pred:Graphs.Tid.start ~target
    ~term_bb:(get_bb scope Graphs.Tid.start) ()

let build_entry_block ctx scope llvm_builder transfer_vars fr sub fn =
  let tid = Graphs.Tid.start in
  let args = get_args ctx (Term.tid sub) in
  Base.List.iter transfer_vars ~f:(fun var ->
      let arg =
        Base.List.find args ~f:(fun arg -> Var.same (Arg.lhs arg) var)
      in
      let llval =
        match arg with
        | Some arg -> create_exp ctx scope llvm_builder tid (Arg.rhs arg)
        | None ->
            (* Unbound transfer vars freeze to one fixed value:
               repeated reads of an undefined register observe
               identical bits. *)
            frozen_undef ctx scope ~builder:llvm_builder var
      in
      insert_local scope tid var llval);
  (* The SP local binds to a per-invocation entry-block alloca: the
     anchor is invocation-private — reentrancy-safe, no SP parameter. *)
  let sp0 =
    (* storage-free subs: the constant anchor *)
    frame_stack0 fr
  in
  insert_local scope tid ctx.sp sp0;
  exit_entry scope llvm_builder sub

(* Builds blocks and transfer set in one walk. *)
let transfer_vars_of_sub ctx scope llvm_ctx blks fn sub =
  insert_bb scope Graphs.Tid.start (Llvm.entry_block fn);
  init_blk_llvals scope Graphs.Tid.start;
  (* (transfer set, defined set); the defined set includes phi lhs —
     phi lanes need definedness. *)
  let indirect_rets = ret_set ctx in
  let defined_and_transferred =
    Seq.fold blks
      ~f:(fun (reg_set, def_set) blk ->
        let tid = Term.tid blk in
        init_blk_llvals scope tid;
        insert_bb scope tid (Llvm.append_block llvm_ctx (Term.name blk) fn);
        let blk_free = Blk.free_vars blk in
        let call_args, call_rets =
          Term.enum jmp_t blk
          |> Seq.fold ~init:(Var.Set.empty, Var.Set.empty) ~f:(fun (acc, rets) jmp ->
              match Jmp.kind jmp with
              | Call c when not (Hike_return.is_jmp jmp) -> (
                  let rets, args =
                    match Call.target c with
                    | Direct ctid ->
                        ( Base.List.fold (get_rets ctx ctid) ~init:rets
                            ~f:(fun acc arg -> Core.Set.add acc (Var.base (Arg.lhs arg))),
                          get_args ctx ctid )
                    | Indirect _ -> (Core.Set.union rets indirect_rets, [])
                  in
                  ( Base.List.fold args ~init:acc ~f:(fun acc arg ->
                        Core.Set.add acc (Var.base (Arg.lhs arg))),
                    rets ))
              | _ -> (acc, rets))
        in
        let blk_defs =
          Blk.elts blk
          |> Seq.fold ~init:Var.Set.empty ~f:(fun acc elt ->
                 match elt with
                 | `Def def -> Core.Set.add acc (Var.base (Def.lhs def))
                 | `Phi phi -> Core.Set.add acc (Var.base (Phi.lhs phi))
                 | _ -> acc)
        in
        ( Core.Set.union (Core.Set.union reg_set (Core.Set.union blk_free call_args))
            call_rets,
          Core.Set.union (Core.Set.union def_set blk_defs) call_rets ))
      ~init:(Var.Set.empty, Var.Set.empty)
  in
  let reg_set, def_set = defined_and_transferred in
  let arg_set =
    Base.List.fold (get_args ctx (Term.tid sub)) ~init:Var.Set.empty
      ~f:(fun acc arg -> Core.Set.add acc (Var.base (Arg.lhs arg)))
  in
  (* [def_set] never joins the transfer set. *)
  reg_set
  |> Core.Set.union indirect_rets
  |> Core.Set.union arg_set
  |> Core.Set.filter ~f:(fun var ->
      ((not @@ Hike_stack_model.is_mem var) || Var.same var (Abi.pc ctx.target))
      (* SP and callee-saved lanes stay live. *)
      || Var.same var ctx.sp
      || Abi.is_callee_saved ctx.abi var)
  |> Core.Set.filter ~f:(fun var ->
      Core.Set.mem def_set var
      || Core.Set.mem arg_set var
      || Var.same var ctx.sp)
  |> Core.Set.to_list


(* The anchor pointer: the alloca position the SP Slot's stored integer
   relativizes against.  [idx] keeps the SysV entry-SP residue mod 16, so
   lifted alignment tests evaluate as the native. *)
let anchor_gep llvm_ctx llvm_builder base idx =
  Llvm.build_gep (Llvm.i8_type llvm_ctx) base
    [| Llvm.const_of_int64 (Llvm.i64_type llvm_ctx) idx false |]
    "anchor" llvm_builder

(* Consumes the sub's LAYOUT tag (region geometry). *)
let create_sub ctx scope sub =
  if is_empty sub then ()
  else if
    (* Skips soft-float bodies for mapped intrinsics. *)
    Base.Option.is_some (native_fp_op (Tid.name (Term.tid sub)))
  then ()
  else
    let llvm_ctx = ctx.llvm_ctx in
    let blks = Term.enum blk_t sub in
    let fn, _ =
      Core.Map.find !(ctx.ll_funcs) (Term.tid sub)
      |> Base.Option.value_exn ~message:"create sub : function not found"
    in
    let llvm_builder = Llvm.builder_at_end llvm_ctx (Llvm.entry_block fn) in

    let transfer_vars = transfer_vars_of_sub ctx scope llvm_ctx blks fn sub in
    let layout =
      Base.Option.value (Term.get_attr sub Hike_stack_model.layout_tag)
        ~default:{ Hike_stack_model.Sub_layout.regions = [];
                   anchor = None; window_param = false }
    in
    let regions =
      Hike_stack_ptr.build ~llvm_ctx ~llvm_builder layout
      |> Base.List.map ~f:(fun (s : Hike_stack_ptr.storage) ->
             (s.mem, (s.base, s.rel)))
    in
    let layout_anchor = layout.Hike_stack_model.Sub_layout.anchor in
    (* The anchor: (region id, byte index) into the regions above. *)
    let anchor_ptr =
      Base.Option.bind layout_anchor ~f:(fun (rid, idx) ->
          Base.Option.bind
            (Base.List.find regions
               ~f:(fun (v, _) -> Var.equal v (Hike_stack_model.region_mem rid)))
            ~f:(fun (_, (base, _)) ->
              Some (anchor_gep llvm_ctx llvm_builder base idx)))
    in
    Base.List.iter regions ~f:(fun (v, (base, _)) ->
        insert_local scope Graphs.Tid.start v base);
    let anchor_i64 =
      Base.Option.value_map anchor_ptr
        ~default:(Llvm.const_int (Llvm.i64_type llvm_ctx) 0)
        ~f:(fun p ->
          Llvm.build_ptrtoint p (Llvm.i64_type llvm_ctx) "anchor_i64"
            llvm_builder)
    in
    let sp_slot = Base.Option.is_some anchor_ptr in
    let stack0 =
      if sp_slot then begin
        let slot =
          Llvm.build_alloca (Llvm.i64_type llvm_ctx) "sp_slot" llvm_builder
        in
        ignore (Llvm.build_store anchor_i64 slot llvm_builder);
        Some (Llvm.build_load (Llvm.i64_type llvm_ctx) slot "stack_0" llvm_builder)
      end
      else None
    in
    let fr : sub_frame = { anchor_i64; stack0; anchor_ptr; regions } in
    scope.cur_frame := Some fr;
    add_args_to_vars ctx scope llvm_builder Graphs.Tid.start (Term.tid sub) fn;
    build_entry_block ctx scope llvm_builder transfer_vars fr sub fn;
    populate_blks ctx scope transfer_vars blks sub fr;
    update_phis ctx scope transfer_vars blks;
    scope.cur_frame := None;
    let sub_tid = Term.tid sub in
    let lane_reads =
      Core.Map.fold !(scope.undef_warned) ~init:Var.Set.empty
        ~f:(fun ~key:_ ~data:warned_vars acc ->
          Core.Set.union acc !warned_vars)
      |> Core.Set.filter ~f:(fun v ->
             let abi = ctx.abi in
             Abi.is_vector_param_reg abi v || Abi.is_return_reg abi v)
    in
    if not (Core.Set.is_empty lane_reads) then
      Hike_diag.warn
        "undef-read: sub %s: %d never-defined model-ABI lane read(s) [undef]"
        (Tid.name sub_tid) (Core.Set.length lane_reads)

(* The emission entry: signature collection, declarations, bodies.
   Phase order — sigs, thunks, bodies, initializers — is load-bearing;
   the body loop opens one [sub_scope] per sub and drops it at the
   boundary. *)
let emit_program (llvm_ctx : Llvm.llcontext) (llvm_module : Llvm.llmodule)
    ~(target : Bap_core_theory.Theory.Target.t) ~(addr_bits : int)
    ~(symtab : Symtab.t option)
    ~(copy_relocs : int64 list)
    (spec : section_spec)
    (prog : program term) : unit =
  (* The sections construct from the spec before any function declares. *)
  let sections = Bil2llvm_section.build_sections llvm_ctx llvm_module spec in
  let abi = Abi.of_target target in
  (* The signature rides each sub's own [arg] terms (written by the types
     pass); the emitter reads it off the sub. *)
  let subs_list = Term.enum sub_t prog |> Base.Sequence.to_list in
  let sub_of =
    Base.List.fold subs_list ~init:Tid.Map.empty ~f:(fun acc s ->
        Core.Map.set acc ~key:(Term.tid s) ~data:s)
  in
  (* Every pointer call passes the caller's SP, so a promoted
     target's thunk can unpack the caller window. *)
  (* A sub earns a thunk twin iff its own signature carries promoted
     slots; the twin's signature is the synthetic indirect
     convention. *)
  let has_slot_args args = count_slot_args args > 0 in
  (* The synthetic conventions: the indirect call and every sub that
     earned a twin.  Their signatures are DERIVED from the ABI — only
     their names are held. *)
  let synthetic =
    Base.List.fold subs_list
      ~init:(Core.Set.of_list (module Tid) [ indirect_call_tid ])
      ~f:(fun acc sub ->
        let args = Hike_stack_model.sig_args sub in
        if has_slot_args args && not (Hike_stack_model.fixed_signature sub)
        then Core.Set.add acc (Bil2llvm_calls.thunk_tid_of (Term.tid sub))
        else acc)
  in
  let ctx =
    { symtab;
      copy_relocs;
      target;
      abi;
      sp = Abi.sp target;
      addr_bits;
      sub_of;
      synthetic;
      llvm_ctx;
      llvm_module;
      sections;
      ll_funcs = ref Tid.Map.empty;
      thunks = ref [];
      sec_comps = ref Var.Map.empty;
      tls_anchor = ref None;
      trap_fn = ref None;
      plt_trampolines = ref Tid.Map.empty;
      i64_ty = Llvm.i64_type llvm_ctx;
      ptr_ty = Llvm.pointer_type llvm_ctx;
      word_ty = Llvm.integer_type llvm_ctx (abi.Abi.word * 8);
      native_starts =
        (match symtab with
         | Some st ->
           Symtab.to_sequence st
           |> Base.Sequence.fold ~init:Core.Int64.Set.empty
                ~f:(fun acc (_, entry, _) ->
                  Core.Set.add acc (Word.to_int64_exn (Block.addr entry)))
         | None -> Core.Int64.Set.empty) }
  in
  (* The named-component map: filled before any body emits; the
     rip-relative path renders through the same owners. *)
  Base.List.iter sections ~f:(fun section ->
      Base.List.iter section.owners ~f:(fun o ->
          match o.own_id with
          | Some id ->
            let v = Hike_stack_model.sec_comp_mem id in
            ctx.sec_comps := Core.Map.set !(ctx.sec_comps) ~key:v ~data:(o.base, o.own_lo)
          | None -> ()));
  (* An external function's PLT stub defines no function and emits no
     body — its declaration carries the name for every call site. *)
  let self_call_stubs =
    Term.enum sub_t prog
    |> Base.Sequence.filter ~f:(Bil2llvm_calls.is_self_call_stub ctx)
    |> Base.Sequence.map ~f:Term.tid
    |> Base.Sequence.to_list
    |> Core.Set.of_list (module Tid)
  in
  let is_self_call_stub_tid t = Core.Set.mem self_call_stubs t in
  let declare_phase () =
    Base.List.iter subs_list ~f:(fun sub ->
        let tid = Term.tid sub in
        if Base.Option.is_some (native_fp_op (Tid.name tid)) then ()
        else if is_self_call_stub_tid tid then
          create_fun_declaration ctx tid
        else create_fun ctx tid ~rets:(get_rets ctx tid) ~args:(get_args ctx tid))
  in
  let thunk_phase () =
    Base.List.iter subs_list ~f:(fun sub -> create_thunk ctx (Term.tid sub))
  in
  let bodies_phase () =
    Base.List.iter subs_list ~f:(fun s ->
        if is_self_call_stub_tid (Term.tid s) then ()
        else
          let scope = fresh_scope () in
          create_sub ctx scope s)
  in
  let initializer_phase () =
    (* Word data goes through [remap_native_addr], so function-pointer
       data lands on a promoted sub's thunk. *)
  Base.List.iter sections ~f:(fun section ->
      match section.bytes with
      | Some arr ->
          let lo = Word.to_int64_exn section.min_addr in
          let word = ctx.abi.Abi.word in
          (* An ownerless section serves whole: one row spanning it. *)
          let owners =
            if Base.List.is_empty section.owners then
              [ { own_id = None; own_lo = lo;
                  own_hi = Word.to_int64_exn section.max_addr;
                  base = section.base; typed_w = word } ]
            else section.owners
          in
          Base.List.iter owners ~f:(fun o ->
              let w (a : int64) =
                Int64.to_int (Int64.sub a lo) / word
              in
              Bil2llvm_section.set_owner_initializer ctx llvm_ctx
                llvm_module o.base arr
                ~word_lo:(w o.own_lo)
                ~word_hi:(w o.own_hi)
                ~typed_w:o.typed_w
                ~bss:false ~word)
      | None -> ())
  in
  (* Phase order — sigs, thunks, bodies, initializers — is load-bearing. *)
  declare_phase ();
  thunk_phase ();
  bodies_phase ();
  initializer_phase ()

(* Re-exports from the lane modules (the mli surface). *)
type native_fp = Bil2llvm_fp.native_fp =
  | FMUL | FADD | FSUB | FDIV | FREM | SFLOAT | SINT
  | FCONVERT of int | FORDER | FHLT | ISNAN

type sec_owner = Bil2llvm_env.sec_owner = {
  own_id : int option;
  own_lo : int64;
  own_hi : int64;
  base : Llvm.llvalue;
  typed_w : int;
}


type section = Bil2llvm_env.section = {
  base : Llvm.llvalue;
  min_addr : word;
  max_addr : word;
  bytes : Bytes.t option;
  owners : sec_owner list;
}

type section_type = Bil2llvm_env.section_type

type sec_input = Bil2llvm_env.sec_input =
  | Sec_bytes of {
      si_type : section_type;
      si_lo : int64;
      si_hi : int64;
      si_words : int;
      si_const : bool;
      si_image : Bytes.t;
    }
  | Sec_bss of {
      si_lo : int64;
      si_hi : int64;
      si_words : int;
      si_copy_relocs : (int * string) list;
    }

type section_spec = Bil2llvm_env.section_spec = {
  spec_comps : Hike_stack_model.sec_comp list;
  spec_whole : (int * int64 * int64) list;
  spec_word : int;
  spec_sections : sec_input option list;
}

let native_fp_op = Bil2llvm_fp.native_fp_op

let sanitize_name = Bil2llvm_env.sanitize_name

(* The signature pass, re-exported for the direct emitter callers (the
   fixtures), which run it exactly as the pipeline does. *)
let sign_program = Hike_types.sign_program

let build_sections = Bil2llvm_section.build_sections
