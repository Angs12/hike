(* LLVM emitter core: declarations, blocks, subs, sigs, entry.
   Lanes live in bil2llvm_{env,section,exp,mem,calls}; this module
   orchestrates and carries the frozen seam (bil2llvm.mli). *)

open Bap.Std
open Bap.Std.Bil.Types
open Convutils
module Abi = Hike_abi
module KB = Bap_knowledge.Knowledge
open Bil2llvm_env
open Bil2llvm_exp
open Bil2llvm_mem
open Bil2llvm_calls
open Bil2llvm_section

let update_phi transfer_vars blk_incoming blk_tid =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  (* Consults edge-keyed restores first. *)
  let edge_val (pred_tid : tid) (var : var) : Llvm.llvalue option =
    if Var.same var ctx.Convutils.sp then
      match EHashtbl.find !(ctx.edge_sp_restores) pred_tid with
      | Some inner -> EHashtbl.find inner blk_tid
      | None -> None
    else None
  in
  KB.List.iter transfer_vars ~f:(fun var ->
      let phi_llvar = get_phi ctx blk_tid var in
      Seq.iter blk_incoming ~f:(fun tid ->
          let phi_reg =
            match edge_val tid var with
            | Some v -> Some v
            | None -> get_local ctx tid var
          in
          match phi_reg with
          | Some phi_reg ->
              Llvm.add_incoming (phi_reg, get_bb ctx tid) phi_llvar;
              return ()
          | None -> failwith "update_phi: phi_reg not found"))

(* Counts edge multiplicities. *)
let edge_counts_of_sub (sub : sub term) :
    (Tid.t, (Tid.t, int) EHashtbl.t) EHashtbl.t =
  let edge_count = EHashtbl.create (module Tid) in
  let bump (ptid : Tid.t) (t : Tid.t) : unit =
    let inner =
      match EHashtbl.find edge_count ptid with
      | Some h -> h
      | None ->
          let h = EHashtbl.create (module Tid) in
          EHashtbl.set edge_count ~key:ptid ~data:h;
          h
    in
    let cur = match EHashtbl.find inner t with Some n -> n | None -> 0 in
    EHashtbl.set inner ~key:t ~data:(cur + 1)
  in
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun pb ->
      let ptid = Term.tid pb in
      Term.enum jmp_t pb
      |> Seq.iter ~f:(fun j ->
          match Jmp.kind j with
          | Goto (Direct t) | Ret (Direct t) -> bump ptid t
          | _ -> ()));
  edge_count

let update_phis transfer_vars blks sub () =
  let open KB in
  let edge_count = edge_counts_of_sub sub in
  let cfg = Sub.to_graph sub in
  Seq.iter blks ~f:(fun blk ->
      let blk_tid = Term.tid blk in
      (* Phis need one entry per edge. *)
      let blk_incoming =
        Graphs.Tid.Node.preds blk_tid cfg
        |> Base.Sequence.to_list
        |> Base.List.concat_map ~f:(fun ptid ->
            let n =
              match
                EHashtbl.find edge_count ptid
                |> Base.Option.bind ~f:(fun h -> EHashtbl.find h blk_tid)
              with
              | Some n -> n
              | None -> 1
            in
            Base.List.init n ~f:(fun _ -> ptid))
        |> Base.Sequence.of_list
      in
      update_phi transfer_vars blk_incoming blk_tid)

(* Int edges trap. *)
let create_control_flow llvm_builder blk sub fr () =
  let control_flow = Term.enum jmp_t blk in
  let tid = Term.tid blk in
  if Seq.is_empty control_flow then
    (* Def-only blocks return implicitly. *)
    create_return tid llvm_builder sub
  else
  match cf_type control_flow with
  | Br -> create_branches tid llvm_builder control_flow
  | Int -> create_interrupt llvm_builder
  | Ret -> create_return tid llvm_builder sub
  | CallIndirect ->
      let j = Bap.Std.Seq.hd_exn control_flow in
      create_indirect_call llvm_builder (Term.tid blk) sub j fr
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

let create_elts llvm_builder blk sub_tid sub_info fr alloc_tids () =
  let open KB in
  let tid = Term.tid blk in
  Blk.elts blk
  |> Seq.iter ~f:(fun elt ->
      match elt with
      | `Def def -> create_def tid llvm_builder sub_tid sub_info fr alloc_tids def
      | `Phi _ -> return ()
      | `Jmp _ -> return ())

let populate_blks transfer_vars blks sub sub_info fr () =
  let open KB in
  let* ctx, llvm_ctx = emit_env () in
  let sub_tid = Term.tid sub in
  (* VLA tids travel in vsa_info (spec §2.3): the producer detected them
     once on the pre-rewrite sub. *)
  let alloc_tids = sub_info.Hike_stack_model.vla_alloc_tids in
  Seq.iter blks ~f:(fun blk ->
      let llvm_builder =
        Llvm.builder_at_end llvm_ctx (get_bb ctx (Term.tid blk))
      in
      transfer_with_phis transfer_vars llvm_builder (Term.tid blk) ()
      >>= create_elts llvm_builder blk sub_tid sub_info fr alloc_tids
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
            (* Unbound transfer vars yield undef. *)
            !$Llvm.undef (var_lltype var)
      in
      !$(insert_local ctx tid var) llval)
  >>= fun () ->
  (* The SP Slot (T4): every storage-carrying sub owns an entry-block
     alloca holding its per-invocation anchor — the ptrtoint of its own
     frame (or of its first region alloca for precise subs).  The SP
     local binds to the slot's value: stack_0 is PRIVATE to this
     invocation, reentrancy-safe, and NO sub takes an SP parameter.
     SROA erases the constant cases. *)
  let sp0 =
    match fr.stack0 with
    | Some v -> v
    | None -> fr.anchor_i64 (* storage-free subs: the constant anchor *)
  in
  insert_local ctx tid ctx.Convutils.sp sp0;
  (* The Caller-Window Parameter local (variadic/mixed subs only). *)
  let fr = { fr with stack = get_local ctx tid Hike_stack_model.hike_window_var } in
  exit_entry llvm_builder sub () >>= fun _ -> return fr

(* Builds blocks and transfer set in one walk. *)
let collect_sub_data ctx llvm_ctx blks fn sub =
  insert_bb ctx Graphs.Tid.start (Llvm.entry_block fn);
  init_blk_llvals ctx Graphs.Tid.start;
  (* Transfer set includes call-arg regs. *)
  (* Phi lanes need definedness. *)
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
                        (* Indirect callees bind all ret regs. *)
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
                 (* Phi lhs counts as defined. *)
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
      ((not @@ is_mem var) || Var.same var (Abi.pc ctx.Convutils.target))
      (* Keeps SP and every callee-saved lane (fp is an ordinary one). *)
      || Var.same var ctx.Convutils.sp
      || Abi.is_callee_saved ctx.Convutils.abi var)
  |> Core.Set.filter ~f:(fun var ->
      (* Drops never-defined vars from transfer. *)
      Core.Set.mem def_set var
      || Hike_stack_model.is_region_base var
      || Core.Set.mem arg_set var
      || Var.same var ctx.Convutils.sp)
  |> Core.Set.to_list


(* Allocates the per-sub frame. *)
let build_frame_anchor llvm_ctx llvm_builder n anchor_idx =
  let frame =
    Llvm.build_alloca
      (Llvm.array_type (Llvm.i8_type llvm_ctx) (Int64.to_int n))
      "frame" llvm_builder
  in
  Llvm.set_alignment 16 frame;
  let anchor =
    Llvm.build_gep (Llvm.i8_type llvm_ctx) frame
      [| Llvm.const_of_int64 (Llvm.i64_type llvm_ctx) anchor_idx false |]
      "anchor" llvm_builder
  in
  let anchor_i64 =
    Llvm.build_ptrtoint anchor (Llvm.i64_type llvm_ctx) "anchor_i64"
      llvm_builder
  in
  (frame, anchor_idx, anchor_i64)

(* Stack model decision is consumed here. *)











let create_sub sub =
  let open KB in
  if is_empty sub then return ()
  else if
    (* Skips soft-float bodies for mapped intrinsics. *)
    Base.Option.is_some (native_fp_op (Tid.name (Term.tid sub)))
  then return ()
  else
    let* llvm_ctx = Context.get llvm_ctx_var in
    let* ctx = Context.get emit_ctx_var in
    let blks = Term.enum blk_t sub in
    let fn, _ =
      Core.Map.find !(ctx.Convutils.ll_funcs) (Term.tid sub)
      |> Base.Option.value_exn ~message:"create sub : function not found"
    in
    let llvm_builder = Llvm.builder_at_end llvm_ctx (Llvm.entry_block fn) in

    clear_bbs ctx;
    clear_blk_llvals ctx;
    let transfer_vars = collect_sub_data ctx llvm_ctx blks fn sub in
    (* The record IS the producer's verdict (one accessor, one default). *)
    let sub_info = Hike_kb.info_of_sub (Term.tid sub) in
    let tags = sub_info.Hike_stack_model.offsets in
    (* Consumes the stack plan. *)
    let plan = sub_info.Hike_stack_model.stack_plan in
    let is_precise = Hike_stack_model.is_precise sub_info in
    let frame, anchor_idx, anchor_i64 =
      if is_precise || (Core.Map.is_empty tags && not sub_info.Hike_stack_model.degraded)
      then (None, 0L, Llvm.const_int (Llvm.i64_type llvm_ctx) 0)
      else
        let n, anchor_idx =
          Hike_stack_model.frame_dims sub ~abi:ctx.Convutils.abi sub_info
        in
        let frame, anchor_idx, anchor_i64 =
          build_frame_anchor llvm_ctx llvm_builder n anchor_idx
        in
        (Some frame, anchor_idx, anchor_i64)
    in
    let regions =
      if is_precise then
        Base.List.mapi plan ~f:(fun _ r ->
            let n = Hike_stack_model.region_bytes r in
            let base =
              Llvm.build_alloca
                (Llvm.array_type (Llvm.i8_type llvm_ctx) (Int64.to_int n))
                (Hike_stack_model.region_name r.Hike_stack_model.id)
                llvm_builder
            in
            Llvm.set_alignment 16 base;
            (r, base))
      else []
    in
    (* Binds region bases to alloca cell-0. *)
    let* () =
      let rec bind_regions = function
        | [] -> return ()
        | (r, base) :: rest ->
            let base_var = Hike_stack_model.region_base r.Hike_stack_model.id in
            insert_local ctx Graphs.Tid.start base_var base;
            bind_regions rest
      in
      bind_regions regions
    in
    (* THE stack anchor — one fact, two consumers: create_addr_ptr's
       licensed GEP and the SP Slot's stack_0 below.  Frame storage
       anchors to the sub's %frame alloca; the region split anchors to
       its first region alloca (index 0 — the exact value the SP Slot
       binds for precise subs).  [None] = the sub owns no stack storage
       (tag-free, non-degraded): no def can then carry a Range/Infinite
       tag, no address is ever licensed, and the absent anchor is never
       queried. *)
    let anchor =
      match frame, regions with
      | Some frame, _ -> Some (frame, anchor_i64, anchor_idx)
      | None, (_, base) :: _ ->
          let v =
            Llvm.build_ptrtoint base (Llvm.i64_type llvm_ctx) "anchor_i64"
              llvm_builder
          in
          Some (base, v, 0L)
      | None, [] -> None
    in
    ctx.Convutils.stack_anchor := anchor;
    (* The SP Slot (T4): the entry-block alloca holding this
       invocation's anchor — the sub's own anchor integer. *)
    let anchor_val, sp_slot =
      match anchor with
      | Some (_, v, _) -> (v, true)
      | None -> (anchor_i64, false)
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
    (* The outgoing slot sites (T4): the site's proven outgoing stores
       become the promoted call's slot arguments, keyed by the storing
       def — the store's own emission records its value in
       [store_vals] (create_def), and [create_call_args] passes it. *)
    let store_vals = EHashtbl.create (module Tid) in
    let outgoing = sub_info.Hike_stack_model.prom_sites in
    let fr : sub_frame =
      { anchor_i64; stack = None; stack0; regions;
        is_precise; outgoing; store_vals; resolved = sub_info.Hike_stack_model.prom_resolved }
    in
    add_args_to_vars llvm_builder Graphs.Tid.start (Term.tid sub) fn ()
    >>= build_entry_block llvm_builder transfer_vars fr sub fn
    >>= fun fr -> populate_blks transfer_vars blks sub sub_info fr ()
    >>= update_phis transfer_vars blks sub
    >>= fun () ->
    (* Summarizes model-ABI undef reads. *)
    let sub_tid = Term.tid sub in
    let lane_reads =
      Core.Map.fold !(ctx.Convutils.undef_warned) ~init:Var.Set.empty
        ~f:(fun ~key:_ ~data:warned_vars acc ->
          Core.Set.union acc !warned_vars)
      |> Core.Set.filter ~f:(fun v ->
             let abi = ctx.Convutils.abi in
             Abi.is_vector_param_reg abi v || Abi.is_return_reg abi v)
    in
    if not (Core.Set.is_empty lane_reads) then
      Hike_diag.warn
        "undef-read: sub %s: %d never-defined model-ABI lane read(s) [undef]"
        (Tid.name sub_tid) (Core.Set.length lane_reads);
    return ()

(* Sub-signature facts shared with the filter pass. *)

let free_vars sub =
  Sub.free_vars sub
  |> Core.Set.filter ~f:(fun var -> not @@ is_mem var)
  |> Core.Set.to_list

(* Tests the [Sub.intrinsic] attribute. *)
let is_intrinsic (term : sub term) : bool =
  Term.has_attr term Sub.intrinsic

(* Intrinsics with bodies we can emit. *)
let is_emittable_intrinsic (term : sub term) : bool =
  is_intrinsic term && not (Seq.is_empty (Term.enum blk_t term))

(* Bodyless LLVM intrinsics. *)
let is_llvm_x86_intrinsic (term : sub term) : bool =
  Term.has_attr term Sub.intrinsic && Seq.is_empty (Term.enum blk_t term)

let fp_returning (sub : sub term) : bool =
  let is_ymm n = Base.String.is_prefix n ~prefix:Abi.vector_param_prefix in
  let is_value_reg v =
    let n = Var.name (Var.base v) in
    Base.List.mem Abi.value_return_names n ~equal:String.equal
    || is_ymm n
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
  | d :: _ -> is_ymm (Var.name (Var.base (Def.lhs d)))

let compute_sub_sig (target : Bap_core_theory.Theory.Target.t) ~(abi : Abi.t)
    (sub : sub term) : Arg.t list * Arg.t list =
  let free_vars = free_vars sub in
  (* Per-var ABI projection, hoisted out of the signature sort. *)
  let int_order = Base.List.map abi.int_param_regs ~f:Var.name in
  let rets =
    (if Bap_core_theory.Theory.Target.matches target "x86_64-gnu-elf" then
       abi.return_regs
     else [])
    |> Base.List.map ~f:(fun reg -> Arg.create ~intent:Out reg (Var reg))
  in
  let rets =
    (* Double returns arrive via [%YMM0]. *)
    if fp_returning sub then
      let ymm0 = Base.List.nth_exn abi.vector_param_regs 0 in
      rets
      @ [ Arg.create ~intent:Out ymm0 (Var ymm0) ]
    else rets
  in
  let rets, args =
    if is_emittable_intrinsic sub then begin
    (* Intrinsic signature is the model's own interface. *)
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
  else if Term.name sub = "@main" then
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
       (* T4: the signature is the callee's own promoted interface. The
         producer's record is the SOLE origin: proven incoming slots
         become positional parameters ([hike_slotN], width 64 — the
         SysV slot width; narrower reads truncate); the Caller-Window
         Parameter survives only for variadic/mixed subs (the unproven
         remainder — the caller-window base, not SP). *)
       let info = Hike_kb.info_of_sub (Term.tid sub) in
       let is_main = String.equal (Tid.name (Term.tid sub)) "@main" in
       let window_arg =
         if info.Hike_stack_model.prom_window && not is_main then
           [ Arg.create ~intent:In Hike_stack_model.hike_window_var
               (Var Hike_stack_model.hike_window_var) ]
         else []
       in
       let slot_args =
         Base.List.init info.Hike_stack_model.prom_arity ~f:(fun i ->
             let v = Hike_stack_model.arg_slot i in
             Arg.create ~intent:In v (Var v))
       in
       let args =
         let rank_of_var (v : var) : int * string =
           let n = Var.name (Var.base v) in
           match Base.List.findi int_order ~f:(fun _ s -> String.equal s n) with
           | Some (i, _) -> (i, n)
           | None ->
             if Base.String.is_prefix n ~prefix:Abi.vector_param_prefix then
               (try
                  let num = int_of_string (String.sub n 3 (String.length n - 3)) in
                  if 0 <= num && num < 8 then (6 + num, n) else (100, n)
                with _ -> (100, n))
             else (100, n)
         in
         Base.List.filter free_vars ~f:(fun reg ->
             let n = Var.name (Var.base reg) in
             let is_callee_saved =
               Abi.is_callee_saved abi reg
             in
             (* RBP parses via [callee_saved] (the deleted explicit fp
                 test's same filter result); SP-only by construction.
                 The promoted interface names (hike_slotN / the window
                 base) are the emitter's own vocabulary — never
                 register lanes. *)
             not
               (Var.same reg (Abi.sp target)
               || is_callee_saved
               || Convutils.is_intrinsic_name n
               || Base.String.is_prefix n ~prefix:"hike_slot"
               || Var.same reg Hike_stack_model.hike_window_var))
         |> Base.List.sort ~compare:(fun a b ->
             let ra, na = rank_of_var a in
             let rb, nb = rank_of_var b in
             match Int.compare ra rb with
             | 0 -> String.compare na nb
             | c -> c)
         |> Base.List.map ~f:(fun reg -> Arg.create ~intent:In reg (Var reg))
         |> fun regs -> regs @ slot_args @ window_arg
       in
      (* PLT stubs take the full param list. Signature-shape rule (args = []
         + any call): distinct from the emitter's BIL-shape rule
         [is_plt_trampoline] (no reg free-vars + call) — the two run on
         different inputs (pre-DCE raw sub vs post-DCE sub) and must not
         be merged blindly. *)
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
          Base.List.map (abi.int_param_regs @ abi.vector_param_regs)
            ~f:(fun reg -> Arg.create ~intent:In reg (Var reg))
        else args
      in
       (rets, args)
   in
   (rets, args)

(* The emission entry: signature collection, declarations, bodies. *)
let emit_program (llvm_ctx : Llvm.llcontext) (llvm_module : Llvm.llmodule)
    ~(target : Bap_core_theory.Theory.Target.t) ~(ptrsize : int)
    ~(symtab : Symtab.t option)
    ~(text_section : (int array * int64 * int64) option)
    ~(section_remap : (int64 * int64 * Llvm.llvalue) list)
    ~(copy_relocs : int64 list)
    (sections : Convutils.section list)
    (prog : program term) : unit =
  let abi = Abi.of_target target in
  let ctx =
    {
      (Convutils.empty_emit_ctx ()) with
      Convutils.symtab = symtab;
      text_section;
      section_remap;
      copy_relocs;
      target;
      Convutils.abi = abi;
      Convutils.sp = Abi.sp target;
      ptrsize;
    }
  in
  (* Signature collection fills the table once. *)
  let sigs =
    Term.enum sub_t prog
    |> Base.Sequence.to_list
    |> Base.List.map ~f:(fun sub -> (sub, compute_sub_sig target ~abi sub))
  in
  (* The synthetic indirect-call signature gains the Caller-Window
     Parameter (T4): every pointer call passes the caller's SP at the
     call, so the Thunk of a promoted target can unpack the window. *)
  let icall_tid = Tid.for_name "indirect_call" in
  let conv = Abi.of_target target in
  let icall_sig =
    ( Base.List.map conv.return_regs ~f:(fun reg ->
          Arg.create ~intent:Out reg (Var reg)),
      Base.List.map (conv.int_param_regs @ conv.vector_param_regs)
        ~f:(fun reg -> Arg.create ~intent:In reg (Var reg))
      @ [
          Arg.create ~intent:In Hike_stack_model.hike_window_var
            (Var Hike_stack_model.hike_window_var);
        ] )
  in
  (* The Thunks' signatures: the legacy memory-path convention (the
     register lanes plus the window base) — registered so the
     unprovable-direct-site path can call the twin wholesale. *)
  let twin_sig_of (sub, (rets, _)) =
    let sub_tid = Term.tid sub in
    let info = Hike_kb.info_of_sub sub_tid in
    if info.Hike_stack_model.prom_arity > 0
       && not (String.equal (Tid.name sub_tid) "@main")
    then
      (* The twin's signature = the synthetic indirect convention (the
         register lanes plus the window base), exactly what a pointer
         call passes. *)
      Some
        ( Bil2llvm_calls.thunk_tid_of sub_tid,
          ( rets,
            Base.List.map
              (conv.Abi.int_param_regs @ conv.Abi.vector_param_regs)
              ~f:(fun reg -> Arg.create ~intent:In reg (Var reg))
            @ [
                Arg.create ~intent:In Hike_stack_model.hike_window_var
                  (Var Hike_stack_model.hike_window_var);
              ] ) )
    else None
  in
  let twin_sigs = Base.List.filter_map sigs ~f:twin_sig_of in
  let subs =
    Base.List.fold twin_sigs
      ~init:
        (Core.Map.add_exn ctx.Convutils.subs ~key:icall_tid ~data:icall_sig)
      ~f:(fun acc (tid, (rets, args)) -> add_sub_sig acc tid ~rets ~args)
  in
  let subs =
    Base.List.fold sigs ~init:subs
      ~f:(fun acc (sub, (rets, args)) ->
          add_sub_sig acc (Term.tid sub) ~rets ~args)
  in
  let ctx = { ctx with Convutils.subs = subs } in
  Toplevel.exec begin
    KB.Context.with_var emit_ctx_var ctx (fun () ->
      KB.Context.with_var llvm_ctx_var llvm_ctx (fun () ->
        KB.Context.with_var llvm_module_var llvm_module (fun () ->
          KB.Context.with_var section_list_var sections (fun () ->
            KB.List.iter sigs ~f:(fun (sub, (rets, args)) ->
                (* Mapped intrinsics store the sig but define no function. *)
                if
                  Base.Option.is_none
                    (native_fp_op (Tid.name (Term.tid sub)))
                then create_fun (Term.tid sub) ~rets ~args
                else KB.return ())))))
  end;
  Toplevel.exec begin
    KB.Context.with_var emit_ctx_var ctx (fun () ->
      KB.Context.with_var llvm_ctx_var llvm_ctx (fun () ->
        KB.Context.with_var llvm_module_var llvm_module (fun () ->
          KB.Context.with_var section_list_var sections (fun () ->
            KB.List.iter sigs ~f:(fun (sub, _) ->
                Bil2llvm_calls.create_thunk (Term.tid sub))))))
  end;
  Toplevel.exec begin
    KB.Context.with_var emit_ctx_var ctx (fun () ->
      KB.Context.with_var llvm_ctx_var llvm_ctx (fun () ->
        KB.Context.with_var llvm_module_var llvm_module (fun () ->
          KB.Context.with_var section_list_var sections (fun () ->
            KB.Seq.iter
              (Term.enum sub_t prog)
              ~f:(fun s -> create_sub s)))))
  end;
  (* The data-section initializers render INSIDE the one emission
     context (T4): every 8-byte word goes through [remap_native_addr],
     whose symtab arm now resolves to the Thunk of a promoted sub —
     function-pointer data must land on the memory-convention twin so
     unresolvable pointer sites stay sound. *)
  Toplevel.exec begin
    KB.Context.with_var emit_ctx_var ctx (fun () ->
      KB.Context.with_var llvm_ctx_var llvm_ctx (fun () ->
        KB.Context.with_var llvm_module_var llvm_module (fun () ->
          KB.List.iter sections ~f:(fun section ->
              match section.Convutils.bytes with
              | Some arr ->
                  KB.return
                  @@ Bil2llvm_section.set_section_initializer ctx llvm_ctx
                       llvm_module section.Convutils.base arr
                       (Word.to_int64_exn section.Convutils.min_addr)
              | None -> KB.return ()))))
  end

(* The frozen seam (bil2llvm.mli): re-exports from the lane modules. *)
type native_fp = Bil2llvm_calls.native_fp =
  | FMUL | FADD | FSUB | FDIV | FREM | SFLOAT | SINT | FORDER | FHLT | ISNAN

let native_fp_op = Bil2llvm_calls.native_fp_op
let create_section_global = Bil2llvm_section.create_section_global
let set_section_initializer = Bil2llvm_section.set_section_initializer
let create_uninitialized_global = Bil2llvm_section.create_uninitialized_global
let create_copy_reloc_bss = Bil2llvm_section.create_copy_reloc_bss
