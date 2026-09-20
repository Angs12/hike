(* LLVM emitter core: declarations, blocks, subs, sigs, entry.
   The lanes live in bil2llvm_{env,section,exp,mem,fp,calls}. *)

open Bap.Std
open Bap.Std.Bil.Types
module Abi = Hike_abi
module KB = Bap_knowledge.Knowledge
open Bil2llvm_env
open Bil2llvm_exp
open Bil2llvm_mem
open Bil2llvm_calls
open Bil2llvm_fp
open Bil2llvm_section

let section_type_to_string = Bil2llvm_env.section_type_to_string

let update_phi transfer_vars blk_incoming blk_tid =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  (* The edge bridge's SP restore wins over the pred's local binding. *)
  let edge_val (pred_tid : tid) (var : var) : Llvm.llvalue option =
    if Var.same var ctx.sp then
      match Edge_tbl.find !(ctx.edge_tbl) ~pred:pred_tid ~target:blk_tid with
      | Some r -> r.sp_restore
      | None -> None
    else None
  in
  KB.List.iter transfer_vars ~f:(fun var ->
      let phi_llvar = get_phi ctx blk_tid var in
      List.iter blk_incoming ~f:(fun (tid, pred_bb) ->
          let phi_reg =
            match edge_val tid var with
            | Some v -> Some v
            | None -> get_local ctx tid var
          in
          match phi_reg with
          | Some phi_reg ->
              Llvm.add_incoming (phi_reg, pred_bb) phi_llvar;
              return ()
          | None ->
              (* An incoming with no value on its edge reads the
                 register's frozen undef. *)
              warn_undef_read ctx var blk_tid;
              let* v = frozen_undef ctx var in
              Llvm.add_incoming (v, pred_bb) phi_llvar;
              return ()))

(* LLVM phis take one incoming per terminator edge; two conditional
   gotos to the same target are two edges where the graph shows one. *)
let multiplicity (pred_blk : blk term) (target : Tid.t) : int =
  let n =
    Term.enum jmp_t pred_blk
    |> Seq.count ~f:(fun j ->
        match Jmp.kind j with
        | Goto (Direct t) | Ret (Direct t) -> Tid.equal t target
        | _ -> false)
  in
  if n = 0 then 1 else n

let update_phis transfer_vars blks sub () =
  let blk_of =
    Core.Map.of_alist_exn (module Tid)
      (Base.List.map (Seq.to_list blks) ~f:(fun b -> (Term.tid b, b)))
  in
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  let cfg = Sub.to_graph sub in
  Seq.iter blks ~f:(fun blk ->
      let blk_tid = Term.tid blk in
      let term_preds =
        Graphs.Tid.Node.preds blk_tid cfg
        |> Base.Sequence.to_list
      in
      let blk_incoming =
        Base.List.concat_map term_preds ~f:(fun ptid ->
            let n =
              match Core.Map.find blk_of ptid with
              | Some pb -> multiplicity pb blk_tid
              | None -> 1
            in
            Base.List.init n ~f:(fun _ ->
                (* Phi incomings name the pred's terminator block, not
                   its entry. *)
                let edge_bb =
                  match Edge_tbl.find !(ctx.edge_tbl) ~pred:ptid ~target:blk_tid with
                  | Some r -> r.term_bb
                  | None -> get_bb ctx ptid
                in
                (ptid, edge_bb)))
      in
      update_phi transfer_vars blk_incoming blk_tid)

let create_control_flow llvm_builder blk sub fr () =
  let control_flow = Term.enum jmp_t blk in
  let tid = Term.tid blk in
  if Seq.is_empty control_flow then
    (* Def-only blocks still need a terminator. *)
    create_return tid llvm_builder sub
  else
  match cf_type control_flow with
  | Br -> create_branches tid llvm_builder control_flow
  | Int -> create_interrupt llvm_builder
  | Ret -> create_return tid llvm_builder sub
  | CallIndirect ->
      let j = Bap.Std.Seq.hd_exn control_flow in
      create_indirect_call llvm_builder (Term.tid blk) blk sub j
  | CallFun ->
      let call = Bap.Std.Seq.hd_exn control_flow |> call_exn in
      create_call llvm_builder (Term.tid blk) blk sub call fr

let transfer_with_phis transfer_vars llvm_builder blk_tid () =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  KB.List.iter transfer_vars ~f:(fun var ->
      let* typ = var_lltype var in
      let res = Llvm.build_empty_phi typ "" llvm_builder in
      insert_phi ctx blk_tid var res;
      insert_local ctx blk_tid var res;
      return ())

let create_elts llvm_builder blk sub_tid fr () =
  let open KB in
  let tid = Term.tid blk in
  Blk.elts blk
  |> Seq.iter ~f:(fun elt ->
      match elt with
      | `Def def -> create_def tid llvm_builder sub_tid fr def
      | `Phi _ -> return ()
      | `Jmp _ -> return ())

let populate_blks transfer_vars blks sub fr () =
  let open KB in
  let* ctx, llvm_ctx = emit_env () in
  let sub_tid = Term.tid sub in
  Seq.iter blks ~f:(fun blk ->
      let llvm_builder =
        Llvm.builder_at_end llvm_ctx (get_bb ctx (Term.tid blk))
      in
      transfer_with_phis transfer_vars llvm_builder (Term.tid blk) ()
      >>= create_elts llvm_builder blk sub_tid fr
      >>= create_control_flow llvm_builder blk sub fr)


let exit_entry llvm_builder sub () =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  KB.return
  @@ Llvm.build_br (get_bb ctx (entry_blk_tid sub)) llvm_builder

let build_entry_block llvm_builder transfer_vars fr sub fn () =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  let tid = Graphs.Tid.start in
  KB.List.iter transfer_vars ~f:(fun var ->
      let arg =
        Base.List.find (get_args ctx (Term.tid sub)) ~f:(fun arg ->
            Var.same (Arg.lhs arg) var)
      in
      let llval =
        match arg with
        | Some arg -> create_exp llvm_builder tid (Arg.rhs arg)
        | None ->
            (* Unbound transfer vars freeze to one fixed value:
               repeated reads of an undefined register observe
               identical bits. *)
            frozen_undef ~builder:llvm_builder ctx var
      in
      !$(insert_local ctx tid var) llval)
  >>= fun () ->
  (* The SP local binds to a per-invocation entry-block alloca: the
     anchor is invocation-private — reentrancy-safe, no SP parameter. *)
  let sp0 =
    (* storage-free subs: the constant anchor *)
    Base.Option.value fr.stack0 ~default:fr.anchor_i64
  in
  insert_local ctx tid ctx.sp sp0;
  exit_entry llvm_builder sub () >>= fun _ -> return fr

(* Builds blocks and transfer set in one walk. *)
let collect_sub_data ctx llvm_ctx blks fn sub =
  insert_bb ctx Graphs.Tid.start (Llvm.entry_block fn);
  init_blk_llvals ctx Graphs.Tid.start;
  (* (transfer set, defined set); the defined set includes phi lhs —
     phi lanes need definedness. *)
  let defined_and_transfered =
    Seq.fold blks
      ~f:(fun (reg_set, def_set) blk ->
        let tid = Term.tid blk in
        init_blk_llvals ctx tid;
        insert_bb ctx tid (Llvm.append_block llvm_ctx (Term.name blk) fn);
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
let create_sub sub =
  let open KB in
  if is_empty sub then return ()
  else if
    (* Skips soft-float bodies for mapped intrinsics. *)
    Base.Option.is_some (native_fp_op (Tid.name (Term.tid sub)))
  then return ()
  else
    let* { llvm_ctx; _ } = Context.get emit_ctx_var in
    let* ctx = Context.get emit_ctx_var in
    let blks = Term.enum blk_t sub in
    let fn, _ =
      Core.Map.find !(ctx.ll_funcs) (Term.tid sub)
      |> Base.Option.value_exn ~message:"create sub : function not found"
    in
    let llvm_builder = Llvm.builder_at_end llvm_ctx (Llvm.entry_block fn) in

    clear_bbs ctx;
    clear_blk_llvals ctx;
    clear_undef_vals ctx;
    ctx.undef_warned := Tid.Map.empty;
    let transfer_vars = collect_sub_data ctx llvm_ctx blks fn sub in
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
    let* () =
      let rec bind_regions = function
        | [] -> return ()
        | (v, (base, _)) :: rest ->
            insert_local ctx Graphs.Tid.start v base;
            bind_regions rest
      in
      bind_regions regions
    in
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
    ctx.cur_frame := Some fr;
    add_args_to_vars llvm_builder Graphs.Tid.start (Term.tid sub) fn ()
    >>= fun () ->
    build_entry_block llvm_builder transfer_vars fr sub fn ()
    >>= fun fr ->
    ctx.cur_frame := Some fr;
    populate_blks transfer_vars blks sub fr ()
    >>= update_phis transfer_vars blks sub
    >>= fun () ->
    ctx.cur_frame := None;
    let sub_tid = Term.tid sub in
    let lane_reads =
      Core.Map.fold !(ctx.undef_warned) ~init:Var.Set.empty
        ~f:(fun ~key:_ ~data:warned_vars acc ->
          Core.Set.union acc !warned_vars)
      |> Core.Set.filter ~f:(fun v ->
             let abi = ctx.abi in
             Abi.is_vector_param_reg abi v || Abi.is_return_reg abi v)
    in
    if not (Core.Set.is_empty lane_reads) then
      Hike_diag.warn
        "undef-read: sub %s: %d never-defined model-ABI lane read(s) [undef]"
        (Tid.name sub_tid) (Core.Set.length lane_reads);
    return ()

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

(* One emission phase: the KB context var with the LLVM handles and
   sections bound.  Phase order — sigs, thunks, bodies, initializers —
   is load-bearing. *)
let run_emission ctx llvm_ctx llvm_module sections body =
  let ctx = { ctx with llvm_ctx; llvm_module; sections } in
  Toplevel.exec begin
    KB.Context.with_var emit_ctx_var ctx (fun () -> body ())
  end

(* The emission entry: signature collection, declarations, bodies. *)
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
  let ctx =
    {
      (empty_emit_ctx ()) with
      symtab = symtab;
      section_remap;
      copy_relocs;
      target;
      abi = abi;
      sp = Abi.sp target;
      ptrsize;
    }
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
        (Core.Map.add_exn ctx.subs ~key:icall_tid ~data:icall_sig)
      ~f:(fun acc (tid, (rets, args)) -> add_sub_sig acc tid ~rets ~args)
  in
  let subs =
    Base.List.fold sigs ~init:subs
      ~f:(fun acc (sub, (rets, args)) ->
          add_sub_sig acc (Term.tid sub) ~rets ~args)
  in
  let ctx = { ctx with subs = subs } in
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
  run_emission ctx llvm_ctx llvm_module sections (fun () ->
      KB.List.iter sigs ~f:(fun (sub, (rets, args)) ->
          let tid = Term.tid sub in
          if Base.Option.is_some (native_fp_op (Tid.name tid)) then
            KB.return ()
          else if is_self_call_stub_tid tid then
            Bil2llvm_calls.create_fun_declaration tid
          else create_fun tid ~rets ~args));
  run_emission ctx llvm_ctx llvm_module sections (fun () ->
      KB.List.iter sigs ~f:(fun (sub, _) ->
          Bil2llvm_calls.create_thunk (Term.tid sub)));
  run_emission ctx llvm_ctx llvm_module sections (fun () ->
      KB.Seq.iter (Term.enum sub_t prog) ~f:(fun s ->
          if is_self_call_stub_tid (Term.tid s) then KB.return ()
          else create_sub s));
  (* Initializers render inside the emission context: word data goes
     through [remap_native_addr], so function-pointer data lands on a
     promoted sub's thunk. *)
  run_emission ctx llvm_ctx llvm_module sections (fun () ->
      KB.List.iter sections ~f:(fun section ->
          match section.bytes with
          | Some arr when Base.List.is_empty section.owners ->
              let word = ctx.abi.Abi.word in
              KB.return
              @@ Bil2llvm_section.set_owner_initializer ctx llvm_ctx
                   llvm_module section.base arr
                   ~word_lo:0
                   ~word_hi:((Bytes.length arr + word - 1) / word - 1)
                   ~typed_w:word ~bss:false ~word
          | Some arr ->
              let lo = Word.to_int64_exn section.min_addr in
              let word = ctx.abi.Abi.word in
              KB.List.iter section.owners ~f:(fun o ->
                  let w (a : int64) =
                    Int64.to_int (Int64.sub a lo) / word
                  in
                  KB.return
                  @@ Bil2llvm_section.set_owner_initializer ctx llvm_ctx
                       llvm_module o.base arr
                       ~word_lo:(w o.own_lo)
                       ~word_hi:(w o.own_hi)
                       ~typed_w:
                         (if Option.is_none o.own_id then word
                          else o.typed_w)
                       ~bss:false ~word)
          | None -> KB.return ()))

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
