(* LLVM emitter core: declarations, blocks, subs, sigs, entry.
   The lanes live in bil2llvm_{env,section,exp,mem,fp,calls}.
   The emission state is two values: the run ctx and one sub_scope
   per sub, opened and dropped by [emit_program]'s body loop. *)

open Bap.Std
module Abi = Hike_abi
open Bil2llvm_env
open Bil2llvm_exp
open Bil2llvm_access
open Bil2llvm_calls
open Bil2llvm_fp
open Bil2llvm_section

(* Mechanical: a split piece is one jmp (an unconditional transfer) or
   two (a guard plus its explicit fallthrough Goto).  The completion
   writes the false edge and the splitter canonicalizes the shape, so
   the emitter maps it directly — no chain walking, no term-order
   fallthrough. *)
let create_branches ctx scope blk llvm_builder ?(sub : sub term option)
    branches =
  let open Bap.Std in
  let llvm_ctx = ctx.llvm_ctx in
  let fn = Llvm.block_parent (Llvm.insertion_block llvm_builder) in
  let is_interrupt tid = Hike_abi.is_interrupt_name (Tid.name tid) in
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
  let blk_tid = Term.tid blk in
  let emit_indirect blk exp =
    (* The boundary class: the target is read through an
       external-symbol slot, so the transfer leaves the program — the
       module calls the symbol the slot binds and returns. *)
    match external_slot_target ctx ?sub exp with
    | Some name -> (
        match sub with
        | Some s -> create_external_boundary ctx scope llvm_builder blk_tid s name
        | None ->
          failwith
            (Printf.sprintf
               "hike: boundary indirect jump at block %s has no sub scope"
               (Tid.name blk_tid)))
    | None ->
      (* A dispatch with no enumerated destinations is UB the moment it
         is taken; the module never carries it behind a warning. *)
      failwith
        (Printf.sprintf
           "hike: indirect jump at block %s%s has no enumerated destinations"
           (Tid.name blk_tid)
           (match sub with
            | Some s -> Printf.sprintf " (sub %s)" (Tid.name (Term.tid s))
            | None -> ""))
  in
  match Seq.to_list branches with
  | [ j ] -> (
      match Jmp.kind j with
      | Goto (Direct tid) ->
          if Hike_stack_model.is_true_cond (Jmp.cond j) then (
            if is_interrupt tid then create_interrupt ctx llvm_builder
            else
              let bb =
                match sub with
                | None -> get_bb scope tid
                | Some s -> (
                  match get_bb_opt scope tid with
                  | Some bb -> bb
                  | None ->
                    failwith
                      (Printf.sprintf
                         "hike: block %s: goto names block %s, which is not \
                          a block of sub %s"
                         (Tid.name blk_tid) (Tid.name tid)
                         (Tid.name (Term.tid s))))
              in
              Llvm.build_br bb llvm_builder |> ignore)
          else
            failwith
              (Printf.sprintf
                 "hike: create_branches: block %s: a lone guarded goto has \
                  no explicit false edge (jmp %s)"
                 (Tid.name blk_tid) (Tid.name (Term.tid j)))
      | Goto (Indirect exp) -> emit_indirect blk exp
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
              as_int ctx llvm_builder
                (create_exp ctx scope llvm_builder blk_tid (Jmp.cond j1))
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

let create_control_flow ctx scope llvm_builder blk sub =
  let control_flow = Term.enum jmp_t blk in
  let tid = Term.tid blk in
  if Seq.is_empty control_flow then
    (* Def-only blocks still need a terminator. *)
    create_return ctx scope tid llvm_builder sub
  else
  match cf_type control_flow with
  | Br ->
      create_branches ctx scope blk llvm_builder ~sub control_flow
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
      create_call ctx scope llvm_builder tid blk sub call

let create_elts ctx scope llvm_builder blk sub_tid =
  let tid = Term.tid blk in
  Blk.elts blk
  |> Seq.iter ~f:(fun elt ->
      match elt with
      | `Def def -> create_def ctx scope tid llvm_builder sub_tid def
      | `Phi phi ->
          (* A BIR phi renders as the LLVM phi of its own lhs; the
             incomings fill after every body (a compound incoming
             builds before its source block's terminator).  The type is
             the lhs's: the type pass makes a phi with a pointer incoming a
             pointer. *)
          let var = Phi.lhs phi in
          let res =
            if var_is_ptr var then
              Bil2llvm_value.Ptr (Llvm.build_empty_phi ctx.ptr_ty "" llvm_builder)
            else
              Bil2llvm_value.Int
                (Llvm.build_empty_phi (typ_lltype ctx (Var.typ var)) ""
                   llvm_builder)
          in
          insert_bir_phi scope tid var (Bil2llvm_value.ll res);
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
              let src_bb =
                match get_bb_opt scope src with
                | Some bb -> bb
                | None ->
                  failwith
                    (Printf.sprintf
                       "hike: phi incoming from block %s, which is not a \
                        block of sub %s"
                       (Tid.name src)
                       (Tid.name (Term.tid (Seq.hd_exn blks))))
              in
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
              (* The incoming takes the phi's type. *)
              let phi_is_ptr =
                match get_ssaval scope (Phi.lhs phi) with
                | Some (Bil2llvm_value.Ptr _) -> true
                | _ -> false
              in
              let value =
                Bil2llvm_value.ll
                  (Bil2llvm_value.coerce ~addr_bits:ctx.addr_bits src_b
                     ~ptr:phi_is_ptr value)
              in
              (* An environment register's phi also stores each
                 incoming to the process-global cell at its own source
                 block — whichever edge runs leaves its value there. *)
              if Abi.is_env_reg ctx.abi (Phi.lhs phi) then
                ignore (Llvm.build_store value (env_global ctx (Phi.lhs phi)) src_b);
              Llvm.add_incoming (value, src_bb) phi_ll)))

let populate_blks ctx scope blks sub =
  let sub_tid = Term.tid sub in
  Seq.iter blks ~f:(fun blk ->
      let llvm_builder =
        Llvm.builder_at_end ctx.llvm_ctx (get_bb scope (Term.tid blk))
      in
      create_elts ctx scope llvm_builder blk sub_tid;
      create_control_flow ctx scope llvm_builder blk sub)


let exit_entry scope llvm_builder sub =
  let target = entry_blk_tid sub in
  ignore (Llvm.build_br (get_bb scope target) llvm_builder)

let build_entry_block ctx scope llvm_builder fr sub =
  (* The SP is the entry line: its offset is the model base, its pointer
     is the residue's entry position.  Every pre-def SP read sees it. *)
  let sp0 =
    match fr.entry_ptr with
    | Some p -> Bil2llvm_value.Ptr p
    | None -> Bil2llvm_value.Int fr.entry_line
  in
  insert_local scope Graphs.Tid.start ctx.sp sp0;
  bind_ssaval scope ctx.sp sp0;
  insert_ptr_offset scope ctx.sp fr.entry_line;
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
    (* The lock-marker brackets' plan, before any body emits. *)
    scope.atomic_plan := Bil2llvm_access.plan_atomics sub;
    let layout =
      Base.Option.value (Term.get_attr sub Hike_stack_model.layout_tag)
        ~default:{ Hike_stack_model.Sub_layout.regions = [];
                   window_param = false }
    in
    let storages =
      Hike_stack_ptr.build ~llvm_ctx ~llvm_builder ~addr_bits:ctx.addr_bits layout
    in
    Base.List.iter storages ~f:(fun (s : Hike_stack_ptr.storage) ->
        Bil2llvm_synth.bind_storage scope s.mem s.base s.rel;
        (* The storage's base var binds to its alloca pointer: a
           rewritten address def's value GEPs it directly. *)
        let pv =
          Hike_stack_model.region_ptr ~addr_bits:ctx.addr_bits s.id
        in
        Bil2llvm_synth.bind_storage scope pv s.base s.rel;
        insert_local scope Graphs.Tid.start pv (Bil2llvm_value.Ptr s.base);
        bind_ssaval scope pv (Bil2llvm_value.Ptr s.base));
    (* The entry line is the model's fixed stack base; its residue pointer
       is the storage's base GEP'd at the entry position. *)
    let entry_line =
      Llvm.const_of_int64 (Llvm.i64_type llvm_ctx)
        Hike_stack_model.segment_base false
    in
    let entry_ptr =
      Base.Option.map
        (Bil2llvm_synth.storage_base_of_id scope
           ~addr_bits:ctx.addr_bits Hike_stack_model.residue_id)
        ~f:(fun (base, rel) ->
          Llvm.build_gep (Llvm.i8_type llvm_ctx) base
            [| Llvm.const_of_int64 (Llvm.i64_type llvm_ctx)
                 (Stdlib.Int64.neg rel) false |]
            "entry" llvm_builder)
    in
    let fr : sub_frame = { entry_line; entry_ptr } in
    scope.cur_frame := Some fr;
    add_args_to_vars ctx scope llvm_builder Graphs.Tid.start (Term.tid sub) fn;
    build_entry_block ctx scope llvm_builder fr sub;
    populate_blks ctx scope blks sub;
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
    ~(symtab : Symtab.t option) ~(synth : Hike_synth.table)
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
  (* The sub-start map: an address naming a lifted sub's entry. *)
  let sub_starts =
    Base.List.fold subs_list ~init:Core.Int64.Map.empty
      ~f:(fun m sub ->
        if is_empty sub then m
        else
          match
            Base.Option.bind
              (Term.find blk_t sub (Bil2llvm_env.entry_blk_tid sub))
              ~f:(fun b ->
                Base.Option.map (Term.get_attr b address)
                  ~f:(fun a -> (a, Term.tid sub)))
          with
          | Some (a, t) ->
            Core.Map.set m ~key:(Word.to_int64_exn a) ~data:t
          | None -> m)
  in
  (* Every sub whose start address escapes as a VALUE — a loader
     relocation word, a section image word, or a BIR constant (an
     address-taken def) — earns a public face: the machine-convention
     wrapper a foreign caller reaches through the word.  An unescaped
     sub needs none: every call the program itself makes is a direct
     arm that forwards the caller's window slots. *)
  let escaped =
    let is_start v = Core.Map.mem sub_starts v in
    let from_relative =
      Base.List.fold spec.spec_relative ~init:Core.Int64.Set.empty
        ~f:(fun acc (_, rv) ->
          if is_start rv then Core.Set.add acc rv else acc)
    in
    let from_images =
      Base.List.fold spec.spec_sections ~init:Core.Int64.Set.empty
        ~f:(fun acc -> function
          | Some { Hike_stack_model.sm_image = Some bytes; _ } ->
            let n = Bytes.length bytes in
            let wb = spec.spec_word in
            let rec go off acc =
              if off + wb > n then acc
              else
                let w =
                  Base.List.fold (Base.List.init wb ~f:(fun i -> i)) ~init:0L
                    ~f:(fun v i ->
                      Stdlib.Int64.logor v
                        (Stdlib.Int64.shift_left
                           (Stdlib.Int64.of_int
                              (Char.code (Bytes.get bytes (off + i))))
                           (8 * i)))
                in
                go (off + wb)
                  (if is_start w then Core.Set.add acc w else acc)
            in
            go 0 acc
          | _ -> acc)
    in
    let from_bir =
      Base.List.fold subs_list ~init:Core.Int64.Set.empty
        ~f:(fun acc sub ->
          Term.enum blk_t sub
          |> Seq.fold ~init:acc ~f:(fun acc blk ->
              let consts acc e =
                (object
                   inherit [ Core.Int64.Set.t ] Exp.visitor
                   method! visit_int w acc =
                     match Word.to_int64 w with
                     | Ok x when is_start x -> Core.Set.add acc x
                     | _ -> acc
                   method! visit_var v acc =
                     match Hike_synth.module_addr_of synth v with
                     | Some x when is_start x -> Core.Set.add acc x
                     | _ -> acc
                 end)#visit_exp
                  e acc
              in
              let acc =
                Term.enum def_t blk
                |> Seq.fold ~init:acc ~f:(fun acc d -> consts acc (Def.rhs d))
              in
              let acc =
                Term.enum phi_t blk
                |> Seq.fold ~init:acc ~f:(fun acc p ->
                    Base.Sequence.fold (Phi.values p) ~init:acc
                      ~f:(fun acc (_, e) -> consts acc e))
              in
              Term.enum jmp_t blk
              |> Seq.fold ~init:acc ~f:(fun acc j -> consts acc (Jmp.cond j))))
    in
    Core.Set.fold
      (Core.Set.union from_relative (Core.Set.union from_images from_bir))
      ~init:Tid.Set.empty ~f:(fun acc v ->
        match Core.Map.find sub_starts v with
        | Some t -> Core.Set.add acc t
        | None -> acc)
  in
  (* A sub earns a public face iff its address escapes; its signature
     must still fit the machine convention.  The synthetic conventions:
     the indirect call and every escaped sub.  Their signatures are
     DERIVED from the ABI — only their names are held. *)
  let has_slot_args args = count_slot_args args > 0 in
  let synthetic =
    Base.List.fold subs_list
      ~init:(Core.Set.of_list (module Tid) [ indirect_call_tid ])
      ~f:(fun acc sub ->
        let args = Hike_stack_model.sig_args sub in
        if has_slot_args args
           && not (Hike_stack_model.fixed_signature sub)
           && Core.Set.mem escaped (Term.tid sub)
        then Core.Set.add acc (Bil2llvm_calls.thunk_tid_of (Term.tid sub))
        else acc)
  in
  let ctx =
    { symtab;
      address =
        Bil2llvm_section.build_address_index sections
          ~relative:spec.spec_relative ~externals:spec.spec_externals;
      target;
      abi;
      sp = Abi.sp target;
      addr_bits;
      sub_of;
      synthetic;
      synth;
      llvm_ctx;
      llvm_module;
      sections;
      ll_funcs = ref Tid.Map.empty;
      thunks = ref [];
      synth_origins = ref Var.Map.empty;
      synth_vals = ref Var.Map.empty;
      tls = ref None;
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
         | None -> Core.Int64.Set.empty);
      sub_starts }
  in
  (* An external function's PLT stub defines no function and emits no
     body — its declaration carries the name for every call site.  A
     PLT entry the re-decode discovered is named by BAP's symtab after
     the external it lands in, so the external names themselves are the
     discriminator. *)
  let external_names =
    Core.Map.data ctx.address.externals |> Core.String.Set.of_list
  in
  let self_call_stubs =
    Term.enum sub_t prog
    |> Base.Sequence.filter ~f:(fun sub ->
           Hike_stack_model.is_declared ~reloc_names:external_names sub)
    |> Base.Sequence.map ~f:Term.tid
    |> Base.Sequence.to_list
    |> Core.Set.of_list (module Tid)
  in
  let is_self_call_stub_tid t = Core.Set.mem self_call_stubs t in
  (* The entry is analysed, not executed: the module never defines,
     thunks, or bodies its own _start — the native crt1 runs and calls
     the lifted main.  A dead call site naming it (a fallthrough fold
     after a no-return call) declares against crt1's own _start. *)
  let is_entry sub = Term.has_attr sub Sub.entry_point in
  (* The executable owns one TLS block. Its size and alignment reproduce
     PT_TLS's Variant-II layout, including any first-byte padding. *)
  (match spec.spec_tls with
   | Some tls when tls.Hike_spec.tls_memsz > 0L ->
     let init = Bil2llvm_section.image_initializer ~resolve:false ctx llvm_ctx llvm_module
         ~word:abi.Abi.word ~arr:tls.tls_image ~base_addr:tls.tls_lo
         ~prefix:tls.tls_prefix
         ~zero_tail:(Int64.to_int tls.tls_memsz - Bytes.length tls.tls_image) in
     let g = Llvm.declare_global (Llvm.type_of init) "hike_tls_block" llvm_module in
     Llvm.set_thread_local_mode Llvm.ThreadLocalMode.GeneralDynamic g;
     Llvm.set_initializer (Llvm.const_null (Llvm.type_of init)) g;
     Llvm.set_alignment tls.tls_align g;
     ctx.tls := Some (g, tls)
   | _ -> ());
  let declare_phase () =
    Base.List.iter subs_list ~f:(fun sub ->
        let tid = Term.tid sub in
        if is_entry sub then
          create_fun_declaration ~name:ctx.abi.Abi.entry_symbol ctx tid
        else if Base.Option.is_some (native_fp_op (Tid.name tid)) then ()
        else if is_self_call_stub_tid tid then
          create_fun_declaration ctx tid
        else
          create_fun ctx tid ~rets:(get_rets ctx tid) ~args:(get_args ctx tid)
            ~variadic:(Hike_variadic.is_variadic sub))
  in
  let thunk_phase () =
    Base.List.iter subs_list ~f:(fun sub ->
        if is_entry sub || not (Core.Set.mem escaped (Term.tid sub)) then ()
        else create_thunk ctx (Term.tid sub))
  in
  (* The per-run synth-var bindings: the synth-value lane enumerates the
     vocabulary once and binds each module-lifetime var before any body
     emits. *)
  let synth_phase () =
    let b = Bil2llvm_synth.build ctx in
    ctx.synth_vals := b.values;
    ctx.synth_origins := b.origins
  in
  let bodies_phase () =
    Base.List.iter subs_list ~f:(fun s ->
        if is_entry s then ()
        else if is_self_call_stub_tid (Term.tid s) then ()
        else
          let scope = fresh_scope () in
          create_sub ctx scope s)
  in
  let initializer_phase () =
    (match !(ctx.tls) with
     | None -> ()
     | Some (g, tls) ->
       Llvm.set_initializer
         (Bil2llvm_section.image_initializer ctx llvm_ctx llvm_module
            ~word:abi.Abi.word ~arr:tls.tls_image ~base_addr:tls.tls_lo
            ~prefix:tls.tls_prefix
            ~zero_tail:(Int64.to_int tls.tls_memsz - Bytes.length tls.tls_image)) g);
    (* The initializer rule consults the loader's relocation facts
       (in the emission address index); function-pointer data lands on a
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
  synth_phase ();
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
  sm_access : Hike_section.access;
  sm_lo : int64;
  sm_hi : int64;
  sm_words : int;
  sm_image : Bytes.t option;
  sm_copy_relocs : (int * string) list;
}

type section_spec = Hike_spec.section_spec

let native_fp_op = Bil2llvm_fp.native_fp_op

let sanitize_name = Bil2llvm_env.sanitize_name

let build_sections = Bil2llvm_section.build_sections
