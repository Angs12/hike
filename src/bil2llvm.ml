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

(* Mechanical: a split piece is one jmp (an unconditional transfer) or
   two (a guard plus its explicit fallthrough Goto).  The completion
   writes the false edge and the splitter canonicalizes the shape, so
   the emitter maps it directly — no chain walking, no term-order
   fallthrough. *)
let create_branches ctx scope blk_tid llvm_builder branches =
  let open Bap.Std in
  let llvm_ctx = ctx.llvm_ctx in
  let fn = Llvm.block_parent (Llvm.insertion_block llvm_builder) in
  let is_interrupt tid = Bil2llvm_env.is_interrupt_name (Tid.name tid) in
  (* A conditional target that is an interrupt sub needs its own block;
     the trap is terminal there. *)
  let target_bb tid =
    if is_interrupt tid then begin
      let bb = Llvm.append_block llvm_ctx (Tid.name tid ^ "-trap") fn in
      let cur = Llvm.insertion_block llvm_builder in
      Llvm.position_at_end bb llvm_builder;
      create_interrupt ctx llvm_builder;
      Llvm.position_at_end cur llvm_builder;
      bb
    end
    else get_bb scope tid
  in
  let emit_indirect _exp =
    (* A dispatch with no enumerated destinations is UB the moment it is
       taken; the module never carries it behind a warning. *)
    failwith
      (Printf.sprintf
         "hike: indirect jump at block %s has no enumerated destinations"
         (Tid.name blk_tid))
  in
  match Seq.to_list branches with
  | [ j ] -> (
      match Jmp.kind j with
      | Goto (Direct tid) ->
          if Hike_stack_model.is_true_cond (Jmp.cond j) then (
            if is_interrupt tid then create_interrupt ctx llvm_builder
            else Llvm.build_br (get_bb scope tid) llvm_builder |> ignore)
          else
            failwith
              (Printf.sprintf
                 "hike: create_branches: block %s: a lone guarded goto has \
                  no explicit false edge (jmp %s)"
                 (Tid.name blk_tid) (Tid.name (Term.tid j)))
      | Goto (Indirect exp) -> emit_indirect exp
      | _ ->
          failwith "hike: create_branches: a piece's lone jmp is not a goto")
  | [ j1; j2 ] -> (
      match (Jmp.kind j1, Jmp.kind j2) with
      | Goto (Direct t1), Goto (Direct t2) ->
          if Hike_stack_model.is_true_cond (Jmp.cond j1) then
            (* The first edge transfers unconditionally; the second is
               the dead fallthrough. *)
            if is_interrupt t1 then create_interrupt ctx llvm_builder
            else Llvm.build_br (get_bb scope t1) llvm_builder |> ignore
          else
            let cond =
              create_exp ctx scope llvm_builder blk_tid (Jmp.cond j1)
            in
            Llvm.build_cond_br cond (target_bb t1) (target_bb t2)
              llvm_builder |> ignore
      | _ ->
          failwith
            "hike: create_branches: a two-jmp piece is not a guard plus a \
             fallthrough goto")
  | _ ->
      failwith
        "hike: create_branches: an unsplit multi-jmp series reached the emitter"

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

let create_elts ctx scope llvm_builder blk sub_tid fr =
  let tid = Term.tid blk in
  Blk.elts blk
  |> Seq.iter ~f:(fun elt ->
      match elt with
      | `Def def -> create_def ctx scope tid llvm_builder sub_tid fr def
      | `Phi phi ->
          (* A BIR phi renders as the LLVM phi of its own lhs; the
             incomings fill after every body (a compound incoming
             builds before its source block's terminator).  The type is
             the lhs's, OR a pointer when any incoming is a pointer
             value (D13). *)
          let var = Phi.lhs phi in
          let incoming_ptr =
            Phi.values phi
            |> Seq.exists ~f:(fun (_, e) ->
                   match e with
                   | Bil.Var v -> is_ptr_var v
                   | _ -> false)
          in
          let typ =
            if incoming_ptr then ctx.ptr_ty else var_lltype ctx var
          in
          let res = Llvm.build_empty_phi typ "" llvm_builder in
          insert_bir_phi scope tid var res;
          insert_local scope tid var res;
          bind_ssaval scope var res
      | `Jmp _ -> ())

(* One incoming per (source block, exp): the exp evaluates in the
   source block's context, before its terminator. *)
let fill_bir_phis ctx scope blks =
  Seq.iter blks ~f:(fun blk ->
      let tid = Term.tid blk in
      Term.enum phi_t blk
      |> Seq.iter ~f:(fun phi ->
          let phi_ll =
            Base.Option.value_exn
              (get_bir_phi scope tid (Phi.lhs phi))
          in
          Phi.values phi
          |> Seq.iter ~f:(fun (src, exp) ->
              let src_bb = get_bb scope src in
              let src_b =
                match Llvm.block_terminator src_bb with
                | Some t -> Llvm.builder_before ctx.llvm_ctx t
                | None -> Llvm.builder_at_end ctx.llvm_ctx src_bb
              in
              let value =
                match exp with
                | Bil.Var v when Base.Option.is_some (get_ssaval scope v) ->
                    Base.Option.value_exn (get_ssaval scope v)
                | _ -> create_exp ctx scope src_b src exp
              in
              (* The phi's type is its lhs's; an integer incoming at a
                 pointer phi inttoptrs (D13's one sanctioned value
                 conversion). *)
              let phi_is_ptr =
                Llvm.classify_type (Llvm.type_of phi_ll) = Llvm.TypeKind.Pointer
              in
              let value =
                if phi_is_ptr && not (Bil2llvm_ptr.is_ptr_value value) then
                  Bil2llvm_ptr.as_pointer ctx src_b value
                else value
              in
              Llvm.add_incoming (value, src_bb) phi_ll)))

let populate_blks ctx scope blks sub fr =
  let sub_tid = Term.tid sub in
  Seq.iter blks ~f:(fun blk ->
      let llvm_builder =
        Llvm.builder_at_end ctx.llvm_ctx (get_bb scope (Term.tid blk))
      in
      create_elts ctx scope llvm_builder blk sub_tid fr;
      create_control_flow ctx scope llvm_builder blk sub fr)


let exit_entry scope llvm_builder sub =
  let target = entry_blk_tid sub in
  ignore (Llvm.build_br (get_bb scope target) llvm_builder)

let build_entry_block ctx scope llvm_builder fr sub =
  (* The SP is the entry line: its offset is the model base, its pointer
     is the residue's entry position.  Every pre-def SP read sees it. *)
  let sp0 =
    Base.Option.value fr.entry_ptr ~default:(frame_stack0 fr)
  in
  insert_local scope Graphs.Tid.start ctx.sp sp0;
  bind_ssaval scope ctx.sp sp0;
  insert_ptr_offset scope ctx.sp (frame_stack0 fr);
  exit_entry scope llvm_builder sub

(* Creates the LLVM blocks: one per BIR block plus the entry. *)
let create_blocks ctx scope llvm_ctx blks fn sub =
  insert_bb scope Graphs.Tid.start (Llvm.entry_block fn);
  init_blk_llvals scope Graphs.Tid.start;
  Seq.iter blks ~f:(fun blk ->
      let tid = Term.tid blk in
      init_blk_llvals scope tid;
      insert_bb scope tid (Llvm.append_block llvm_ctx (Term.name blk) fn))

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

    create_blocks ctx scope llvm_ctx blks fn sub;
    load_ssa_versions scope blks;
    let layout =
      Base.Option.value (Term.get_attr sub Hike_stack_model.layout_tag)
        ~default:{ Hike_stack_model.Sub_layout.regions = [];
                   window_param = false }
    in
    let storages =
      Hike_stack_ptr.build ~llvm_ctx ~llvm_builder ~addr_bits:ctx.addr_bits layout
    in
    let regions =
      Base.List.map storages
        ~f:(fun (s : Hike_stack_ptr.storage) -> (s.mem, (s.base, s.rel)))
    in
    Base.List.iter storages ~f:(fun (s : Hike_stack_ptr.storage) ->
        insert_local scope Graphs.Tid.start s.mem s.base;
        (* The storage's base var binds to its alloca pointer: a
           rewritten address def's value GEPs it directly. *)
        let pv =
          Hike_stack_model.region_ptr ~addr_bits:ctx.addr_bits s.id
        in
        insert_local scope Graphs.Tid.start pv s.base;
        bind_ssaval scope pv s.base);
    (* The entry line is the model's fixed stack base; its residue pointer
       is the storage's base GEP'd at the entry position. *)
    let entry_line =
      Llvm.const_of_int64 (Llvm.i64_type llvm_ctx)
        Hike_stack_model.segment_base false
    in
    let entry_ptr =
      Base.Option.map
        (Base.List.find regions ~f:(fun (v, _) ->
             Var.equal v
               (Hike_stack_model.region_mem ~addr_bits:ctx.addr_bits
                  Hike_stack_model.residue_id)))
        ~f:(fun (_, (base, rel)) ->
          Llvm.build_gep (Llvm.i8_type llvm_ctx) base
            [| Llvm.const_of_int64 (Llvm.i64_type llvm_ctx)
                 (Stdlib.Int64.neg rel) false |]
            "entry" llvm_builder)
    in
    let fr : sub_frame = { entry_line; entry_ptr; regions } in
    scope.cur_frame := Some fr;
    (* The window-value vars: a store of one materializes the real
       address at the use. *)
    scope.window_vars :=
      Term.enum blk_t sub
      |> Seq.concat_map ~f:(Term.enum def_t)
      |> Seq.fold ~init:Var.Set.empty ~f:(fun acc d ->
          if Hike_def_slots.def_is_window_value d then
            Core.Set.add acc (Def.lhs d)
          else acc);
    (* The section-component storage base vars bind to their globals
       (the run's sec_comps map carries (global, native base)). *)
    Core.Map.to_sequence !(ctx.sec_comps)
    |> Seq.iter ~f:(fun (v, (base, _)) ->
        Base.Option.iter (Hike_stack_model.sec_comp_id_of_mem v) ~f:(fun id ->
            let pv = Hike_stack_model.sec_comp_ptr ~addr_bits:ctx.addr_bits id in
            scope.sec_comp_ptrs :=
              WVarMap.add (wvar_of pv) base !(scope.sec_comp_ptrs)));
    add_args_to_vars ctx scope llvm_builder Graphs.Tid.start (Term.tid sub) fn;
    build_entry_block ctx scope llvm_builder fr sub;
    populate_blks ctx scope blks sub fr;
    fill_bir_phis ctx scope blks;
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
        "undef-read: sub %s: %d never-defined model-ABI lane read(s) [undef] {%s}"
        (Tid.name sub_tid) (Core.Set.length lane_reads)
        (String.concat ","
           (Core.Set.to_list lane_reads |> Base.List.map ~f:Var.name))

(* The emission entry: signature collection, declarations, bodies.
   Phase order — sigs, thunks, bodies, initializers — is load-bearing;
   the body loop opens one [sub_scope] per sub and drops it at the
   boundary. *)
let emit_program (llvm_ctx : Llvm.llcontext) (llvm_module : Llvm.llmodule)
    ~(target : Bap_core_theory.Theory.Target.t) ~(addr_bits : int)
    ~(symtab : Symtab.t option)
    (spec : section_spec)
    (prog : program term) : unit =
  (* The sections construct from the spec before any function declares. *)
  let sections = Bil2llvm_section.build_sections llvm_ctx llvm_module spec in
  let copy_relocs = spec.spec_copy_relocs in
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
      relative = spec.spec_relative;
      externals = spec.spec_externals;
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
      i64_ty = Llvm.i64_type llvm_ctx;
      ptr_ty = Llvm.pointer_type llvm_ctx;
      word_ty = Llvm.integer_type llvm_ctx (Hike_stack_model.word_bits abi.Abi.word);
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
            let v = Hike_stack_model.sec_comp_mem ~addr_bits:ctx.addr_bits id in
            ctx.sec_comps := Core.Map.set !(ctx.sec_comps) ~key:v ~data:(o.base, o.own_lo)
          | None -> ()));
  (* An external function's PLT stub defines no function and emits no
     body — its declaration carries the name for every call site. *)
  let self_call_stubs =
    Term.enum sub_t prog
    |> Base.Sequence.filter ~f:Bil2llvm_calls.is_self_call_stub
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
        else
          create_fun ctx tid ~rets:(get_rets ctx tid) ~args:(get_args ctx tid)
            ~variadic:(Hike_stack_model.is_variadic sub))
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
    (* The initializer rule consults the loader's relocation facts
       (ctx.relative/externals); function-pointer data lands on a
       promoted sub's thunk through the same address map. *)
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
                ~base_addr:lo
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
module Fp = Bil2llvm_fp

type native_fp = Bil2llvm_fp.native_fp

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

type sec_meta = Hike_stack_model.sec_meta = {
  sm_type : section_type;
  sm_const : bool;
  sm_lo : int64;
  sm_hi : int64;
  sm_words : int;
  sm_image : Bytes.t option;
  sm_copy_relocs : (int * string) list;
}

type section_spec = Bil2llvm_env.section_spec = {
  spec_comps : Hike_stack_model.sec_comp list;
  spec_whole : (int * int64 * int64) list;
  spec_word : int;
  spec_sections : sec_meta option list;
  spec_relative : (int64 * int64) list;
  spec_externals : (int64 * string) list;
  spec_copy_relocs : int64 list;
}

let native_fp_op = Bil2llvm_fp.native_fp_op

let sanitize_name = Bil2llvm_env.sanitize_name

(* The signature pass, re-exported for the direct emitter callers (the
   fixtures), which run it exactly as the pipeline does. *)
let sign_program = Hike_types.sign_program

let build_sections = Bil2llvm_section.build_sections
