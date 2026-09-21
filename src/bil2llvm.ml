(* LLVM emitter core: declarations, blocks, subs, sigs, entry.
   The lanes live in bil2llvm_{env,section,exp,mem,fp,calls}.
   The emission state is two values: the run ctx and one sub_scope
   per sub, opened and dropped by [emit_program]'s body loop. *)

open Bap.Std
open Bap.Std.Bil.Types
module Abi = Hike_abi
open Bil2llvm_env
open Bil2llvm_exp
open Bil2llvm_mem
open Bil2llvm_calls
open Bil2llvm_fp
open Bil2llvm_section

let section_type_to_string = Bil2llvm_env.section_type_to_string

let update_phis ctx scope transfer_vars blks sub =
  let cfg = Sub.to_graph sub in
  Seq.iter blks ~f:(fun blk ->
      let blk_tid = Term.tid blk in
      let preds =
        Graphs.Tid.Node.preds blk_tid cfg
        |> Base.Sequence.to_list
      in
      Base.List.iter transfer_vars ~f:(fun var ->
          let phi = get_phi scope blk_tid var in
          Bil2llvm_phi.add_incomings ctx scope ~phi ~preds ~target:blk_tid var))

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
      create_indirect_call ctx scope llvm_builder tid blk sub j
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
  ignore (Llvm.build_br (get_bb scope (entry_blk_tid sub)) llvm_builder)

let build_entry_block ctx scope llvm_builder transfer_vars fr sub fn =
  let tid = Graphs.Tid.start in
  Base.List.iter transfer_vars ~f:(fun var ->
      let arg =
        Base.List.find (get_args ctx (Term.tid sub)) ~f:(fun arg ->
            Var.same (Arg.lhs arg) var)
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
    Base.Option.value fr.stack0 ~default:fr.anchor_i64
  in
  insert_local scope tid ctx.sp sp0;
  exit_entry scope llvm_builder sub;
  fr

(* Builds blocks and transfer set in one walk. *)
let collect_sub_data ctx scope llvm_ctx blks fn sub =
  insert_bb scope Graphs.Tid.start (Llvm.entry_block fn);
  init_blk_llvals scope Graphs.Tid.start;
  (* (transfer set, defined set); the defined set includes phi lhs —
     phi lanes need definedness. *)
  let defined_and_transfered =
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
              | Call c -> (
                  let rets, args =
                    match Call.target c with
                    | Direct ctid ->
                        ( Base.List.fold (get_rets ctx ctid) ~init:rets
                            ~f:(fun acc arg -> Core.Set.add acc (Var.base (Arg.lhs arg))),
                          get_args ctx ctid )
                    | Indirect _ ->
                        ( Core.Set.union rets (ret_set ctx),
                          [] )
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
  let reg_set, def_set = defined_and_transfered in
  let arg_set =
    Base.List.fold (get_args ctx (Term.tid sub)) ~init:Var.Set.empty
      ~f:(fun acc arg -> Core.Set.add acc (Var.base (Arg.lhs arg)))
  in
  (* [def_set] never joins the transfer set. *)
  reg_set
  |> Core.Set.union (ret_set ctx)
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


(* The anchor word: the integer the SP Slot stores and every
   materialization relativizes against.  [idx] keeps the SysV entry-SP
   residue mod 16, so lifted alignment tests evaluate as the native. *)
let anchor_word llvm_ctx llvm_builder base idx =
  let anchor =
    Llvm.build_gep (Llvm.i8_type llvm_ctx) base
      [| Llvm.const_of_int64 (Llvm.i64_type llvm_ctx) idx false |]
      "anchor" llvm_builder
  in
  Llvm.build_ptrtoint anchor (Llvm.i64_type llvm_ctx) "anchor_i64"
    llvm_builder

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

    let transfer_vars = collect_sub_data ctx scope llvm_ctx blks fn sub in
    let layout_regions, layout_anchor =
      Base.Option.value_map (Term.get_attr sub Hike_stack_model.layout_tag)
        ~default:([], None)
        ~f:(fun { regions; anchor } -> (regions, anchor))
    in
    let regions =
      Base.List.map layout_regions
        ~f:(fun (id, (lo, _), bytes) ->
          (* LLVM array counts cross the binding as 32-bit unsigned:
             clamp loudly rather than truncate silently. *)
          let bytes =
            if Int64.compare bytes 0x7fff_fff0L >= 0 then begin
              Hike_diag.warn
                "frame: region request %Ld bytes is absurd (array-count bound 2^31) — clamped; the producer's extents are wrong"
                bytes;
              0x7fff_fff0L
            end
            else bytes
          in
          let base =
            Llvm.build_alloca
              (Llvm.array_type (Llvm.i8_type llvm_ctx) (Int64.to_int bytes))
              (Hike_stack_model.region_name id)
              llvm_builder
          in
          Llvm.set_alignment 16 base;
          ( Hike_stack_model.region_mem id,
            (base, Stdlib.Int64.sub lo Hike_stack_model.segment_base) ))
    in
    (* The anchor: (region id, byte index) into the regions above. *)
    let anchor =
      Base.Option.bind layout_anchor ~f:(fun (rid, idx) ->
          Base.Option.bind
            (Base.List.find regions
               ~f:(fun (v, _) -> Var.equal v (Hike_stack_model.region_mem rid)))
            ~f:(fun (_, (base, _)) ->
              Some (anchor_word llvm_ctx llvm_builder base idx)))
    in
    Base.List.iter regions ~f:(fun (v, (base, _)) ->
        insert_local scope Graphs.Tid.start v base);
    let anchor_val, sp_slot =
      Base.Option.value_map anchor
        ~default:(Llvm.const_int (Llvm.i64_type llvm_ctx) 0, false)
        ~f:(fun v -> (v, true))
    in
    let stack0 =
      if sp_slot then begin
        let slot =
          Llvm.build_alloca (Llvm.i64_type llvm_ctx) "sp_slot" llvm_builder
        in
        ignore (Llvm.build_store anchor_val slot llvm_builder);
        Some (Llvm.build_load (Llvm.i64_type llvm_ctx) slot "stack_0" llvm_builder)
      end
      else None
    in
    let anchor_i64 =
      Base.Option.value anchor ~default:(Llvm.const_int (Llvm.i64_type llvm_ctx) 0)
    in
    let fr : sub_frame = { anchor_i64; stack0; regions } in
    scope.cur_frame := Some fr;
    add_args_to_vars ctx scope llvm_builder Graphs.Tid.start (Term.tid sub) fn;
    let fr = build_entry_block ctx scope llvm_builder transfer_vars fr sub fn in
    scope.cur_frame := Some fr;
    populate_blks ctx scope transfer_vars blks sub fr;
    update_phis ctx scope transfer_vars blks sub;
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

let free_vars sub =
  Sub.free_vars sub
  |> Core.Set.filter ~f:(fun var -> not @@ Hike_stack_model.is_mem var)
  |> Core.Set.to_list

let fp_returning ~(abi : Abi.t) (sub : sub term) : bool =
  let is_value_reg v =
    Base.List.mem Abi.value_return_names (Var.name (Var.base v))
      ~equal:String.equal
    || Abi.is_vector_param_reg abi v
  in
  let is_epilogue blk =
    Term.enum jmp_t blk
    |> Seq.exists ~f:(fun j ->
        match Jmp.kind j with
        | Call c -> (
            match Call.target c with
            | Indirect _ -> Option.is_none (Call.return c)
            | _ -> false)
        | _ -> false)
  in
  let value_defs blk =
    Term.enum def_t blk
    |> Seq.fold ~init:[] ~f:(fun acc d ->
        if is_value_reg (Def.lhs d) then d :: acc else acc)
  in
  let cfg = Sub.to_graph sub in
  let return_path_defs =
    Term.enum blk_t sub
    |> Seq.fold ~init:[] ~f:(fun acc blk ->
        if not (is_epilogue blk) then acc
        else
          let preds = Graphs.Tid.Node.preds (Term.tid blk) cfg in
          let pred_defs =
            Seq.fold preds ~init:[] ~f:(fun acc p ->
                match Term.find blk_t sub p with
                | Some pb -> value_defs pb @ acc
                | None -> acc)
          in
          value_defs blk @ pred_defs @ acc)
  in
  match return_path_defs with
  | [] -> false
  | d :: _ -> Abi.is_vector_param_reg abi (Def.lhs d)

let compute_sub_sig (target : Bap_core_theory.Theory.Target.t) ~(abi : Abi.t)
    (sub : sub term) : Arg.t list * Arg.t list =
  let free_vars = free_vars sub in
  let rets =
    (if Bap_core_theory.Theory.Target.matches target "x86_64-gnu-elf" then
       abi.return_regs
     else [])
    |> Base.List.map ~f:(fun reg -> Arg.create ~intent:Out reg (Var reg))
  in
  let rets =
    (* Double returns arrive via [%YMM0]. *)
    if fp_returning ~abi sub then
      let ymm0 = Base.List.nth_exn abi.vector_param_regs 0 in
      rets
      @ [ Arg.create ~intent:Out ymm0 (Var ymm0) ]
    else rets
  in
  let rets, args =
    (* A sub reading its incoming window carries the caller-window
       base: its above-entry accesses materialize against the
       caller's frame. *)
    let window_arg =
      match Term.get_attr sub Hike_stack_model.layout_tag with
      | Some { Hike_stack_model.window_param = true; _ } ->
        let w = abi.Abi.word in
        [ Arg.create ~intent:In (Hike_stack_model.hike_window_var ~word:w)
            (Bil.Var (Hike_stack_model.hike_window_var ~word:w)) ]
      | _ -> []
    in
    if Hike_stack_model.is_emittable_intrinsic sub then begin
    let args =
      Base.List.map free_vars ~f:(fun reg ->
          Arg.create ~intent:In reg (Var reg))
    in
    let rets =
      Term.enum blk_t sub
      |> Seq.fold ~init:[] ~f:(fun acc blk ->
          Term.enum def_t blk
          |> Seq.fold ~init:acc ~f:(fun acc d ->
              let v = Def.lhs d in
              let is_input =
                Base.List.exists free_vars ~f:(fun fv -> Var.same fv v)
              in
              let already =
                Base.List.exists acc ~f:(fun a -> Var.same (Arg.lhs a) v)
              in
              if is_input || already then acc
              else Arg.create ~intent:Out v (Var v) :: acc))
    in
      (rets, args)
    end
  else if Hike_stack_model.fixed_signature sub then
     let rdi = Base.List.nth_exn abi.int_param_regs 0 in
     let rsi = Base.List.nth_exn abi.int_param_regs 1 in
     let args =
       [
         Arg.create ~intent:In rdi (Var rdi);
         Arg.create ~intent:In rsi (Var rsi);
       ]
     in
      (rets, args)
   else
       (* The signature transcribes the sub term's own BIR args
         (promoted slots included). *)
       let arg_terms = Term.enum arg_t sub |> Base.Sequence.to_list in
       let args =
         let rank_of_var (v : var) : int * string =
           let n = Var.name (Var.base v) in
           match Base.List.findi (Abi.param_regs abi) ~f:(fun _ r -> Var.same r v) with
           | Some (i, _) -> (i, n)
           | None -> (100, n)
         in
         Base.List.filter free_vars ~f:(fun reg ->
             let n = Var.name (Var.base reg) in
             let is_callee_saved =
               Abi.is_callee_saved abi reg
             in
             (* Filters non-parameter lanes: callee-saved regs, the
                 self-basing TLS base, the emitter's own promoted
                 names. *)
             not
               (Var.same reg (Abi.sp target)
               || Var.same reg abi.thread_pointer
               || is_callee_saved
               || Hike_stack_model.is_intrinsic_name n
               || Base.String.is_prefix n ~prefix:"hike_slot"
               || Base.String.is_prefix n ~prefix:"hike_arg"))
         |> Base.List.sort ~compare:(fun a b ->
             let ra, na = rank_of_var a in
             let rb, nb = rank_of_var b in
             match Int.compare ra rb with
             | 0 -> String.compare na nb
             | c -> c)
         |> Base.List.map ~f:(fun reg -> Arg.create ~intent:In reg (Var reg))
         |> fun regs -> regs @ arg_terms
       in
      (* Signature-shape PLT rule (args = [] + any call); distinct
         from [is_plt_trampoline]'s BIL-shape rule — different
         inputs, do not merge. *)
      let is_plt_sig =
        args = []
        && Term.enum blk_t sub
           |> Seq.exists ~f:(fun blk ->
                  Term.enum jmp_t blk
                  |> Seq.exists ~f:(fun j ->
                         match Jmp.kind j with
                         | Call _ -> true
                         | _ -> false))
      in
      let args =
        if is_plt_sig then
          Base.List.map (Abi.param_regs abi)
            ~f:(fun reg -> Arg.create ~intent:In reg (Var reg))
        else args
      in
       (rets, args @ window_arg)
   in
   (rets, args)

(* The emission entry: signature collection, declarations, bodies.
   Phase order — sigs, thunks, bodies, initializers — is load-bearing;
   the body loop opens one [sub_scope] per sub and drops it at the
   boundary. *)
let emit_program (llvm_ctx : Llvm.llcontext) (llvm_module : Llvm.llmodule)
    ~(target : Bap_core_theory.Theory.Target.t) ~(ptrsize : int)
    ~(symtab : Symtab.t option)
    ~(copy_relocs : int64 list)
    (spec : section_spec)
    (prog : program term) : unit =
  (* The sections construct from the spec before any function declares. *)
  let sections = Bil2llvm_section.build_sections llvm_ctx llvm_module spec in
  (* The section base map: every native address renders through its
     owning global. *)
  let section_remap =
    Base.List.map sections ~f:(fun s ->
        ( Word.to_int64_exn s.min_addr,
          Word.to_int64_exn s.max_addr,
          s.base,
          s.owners ))
  in
  let abi = Abi.of_target target in
  (* Signature collection fills the table once. *)
  let sigs =
    Term.enum sub_t prog
    |> Base.Sequence.to_list
    |> Base.List.map ~f:(fun sub -> (sub, compute_sub_sig target ~abi sub))
  in
  (* Every pointer call passes the caller's SP, so a promoted
     target's thunk can unpack the caller window. *)
  let icall_tid = Tid.for_name "indirect_call" in
  let conv = Abi.of_target target in
  let icall_sig =
    ( Base.List.map conv.return_regs ~f:(fun reg ->
          Arg.create ~intent:Out reg (Var reg)),
      window_conv_args ~word:conv.Abi.word conv )
  in
  (* A sub earns a thunk twin iff its own signature carries promoted
     slots; the twin's signature is the synthetic indirect
     convention. *)
  let has_slot_args args =
    Base.List.exists args ~f:(fun a -> Hike_stack_model.is_arg_slot (Arg.lhs a))
  in
  let twin_sig_of (sub, (rets, args)) =
    let sub_tid = Term.tid sub in
    if has_slot_args args && not (Hike_stack_model.fixed_signature sub)
    then
      Some
        ( Bil2llvm_calls.thunk_tid_of sub_tid,
          (rets, window_conv_args ~word:conv.Abi.word conv) )
    else None
  in
  let twin_sigs = Base.List.filter_map sigs ~f:twin_sig_of in
  let subs =
    Base.List.fold twin_sigs
      ~init:
        (Core.Map.add_exn Tid.Map.empty ~key:icall_tid ~data:icall_sig)
      ~f:(fun acc (tid, (rets, args)) -> add_sub_sig acc tid ~rets ~args)
  in
  let subs =
    Base.List.fold sigs ~init:subs
      ~f:(fun acc (sub, (rets, args)) ->
          add_sub_sig acc (Term.tid sub) ~rets ~args)
  in
  let ctx =
    { symtab;
      section_remap;
      copy_relocs;
      target;
      abi;
      sp = Abi.sp target;
      ptrsize;
      subs;
      llvm_ctx;
      llvm_module;
      sections;
      ll_funcs = ref Tid.Map.empty;
      thunks = ref [];
      sec_comps = ref [] }
  in
  (* The named-component map: filled before any body emits; the
     rip-relative path renders through the same owners. *)
  Base.List.iter sections ~f:(fun section ->
      Base.List.iter section.owners ~f:(fun o ->
          match o.own_id with
          | Some id ->
            let v = Hike_stack_model.sec_comp_mem id in
            ctx.sec_comps :=
              (v, (o.base, o.own_lo))
              :: Base.List.filter !(ctx.sec_comps)
                   ~f:(fun (k, _) -> not (Var.equal k v))
          | None -> ()));
  (* An external function's PLT stub defines no function and emits no
     body — its declaration carries the name for every call site. *)
  let self_call_stubs =
    Term.enum sub_t prog
    |> Base.Sequence.filter ~f:(Bil2llvm_calls.is_self_call_stub ctx)
    |> Base.Sequence.map ~f:(Term.tid)
    |> Base.Sequence.to_list
  in
  let is_self_call_stub_tid t =
    Base.List.mem self_call_stubs t ~equal:Tid.equal
  in
  (* Phase 1: declarations. *)
  Base.List.iter sigs ~f:(fun (sub, (rets, args)) ->
      let tid = Term.tid sub in
      if Base.Option.is_some (native_fp_op (Tid.name tid)) then ()
      else if is_self_call_stub_tid tid then
        create_fun_declaration ctx tid
      else create_fun ctx tid ~rets ~args);
  (* Phase 2: thunks. *)
  Base.List.iter sigs ~f:(fun (sub, _) -> create_thunk ctx (Term.tid sub));
  (* Phase 3: bodies — one sub_scope per sub, opened here, dead at
     the boundary. *)
  Term.enum sub_t prog
  |> Seq.iter ~f:(fun s ->
      if is_self_call_stub_tid (Term.tid s) then ()
      else
        let scope = fresh_scope () in
        create_sub ctx scope s);
  (* Phase 4: initializers render inside the emission value: word data
     goes through [remap_native_addr], so function-pointer data lands
     on a promoted sub's thunk. *)
  Base.List.iter sections ~f:(fun section ->
      match section.bytes with
      | Some arr when Base.List.is_empty section.owners ->
          let word = ctx.abi.Abi.word in
          Bil2llvm_section.set_owner_initializer ctx llvm_ctx
            llvm_module section.base arr
            ~word_lo:0
            ~word_hi:((Bytes.length arr + word - 1) / word - 1)
            ~typed_w:word ~bss:false ~word
      | Some arr ->
          let lo = Word.to_int64_exn section.min_addr in
          let word = ctx.abi.Abi.word in
          Base.List.iter section.owners ~f:(fun o ->
              let w (a : int64) =
                Int64.to_int (Int64.sub a lo) / word
              in
              Bil2llvm_section.set_owner_initializer ctx llvm_ctx
                llvm_module o.base arr
                ~word_lo:(w o.own_lo)
                ~word_hi:(w o.own_hi)
                ~typed_w:
                  (if Option.is_none o.own_id then word
                   else o.typed_w)
                ~bss:false ~word)
      | None -> ())

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

type section_type = Bil2llvm_env.section_type =
  | DATA
  | RODATA
  | BSS
  | GOT
  | GOTPLT
  | RODATA_REL
  | TEXT

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

let build_sections = Bil2llvm_section.build_sections
let create_section_global = Bil2llvm_section.create_section_global
let create_uninitialized_global = Bil2llvm_section.create_uninitialized_global
let create_copy_reloc_bss = Bil2llvm_section.create_copy_reloc_bss
