(* LLVM emitter core: declarations, blocks, subs, sigs, entry.
   Lanes live in bil2llvm_{env,section,exp,mem,fp,calls}; this module
   orchestrates and carries the frozen seam (bil2llvm.mli). *)

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

let update_phi transfer_vars blk_incoming blk_tid =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  (* Consults edge-keyed restores first. *)
  let edge_val (pred_tid : tid) (var : var) : Llvm.llvalue option =
    if Var.same var ctx.sp then
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
          | None ->
              (* An incoming with no value on its edge reads the
                 register's fixed garbage — the never-defined-var
                 rule, with the sanctioned diagnostic. *)
              warn_undef_read ctx var blk_tid;
              let* v = frozen_undef ctx var in
              Llvm.add_incoming (v, get_bb ctx tid) phi_llvar;
              return ()))

(* Counts edge multiplicities over the term edges: every conditional
   goto of a completed dispatch is a real BIR edge, so one bump per
   (predecessor, target) jmp — the rewrite's one-goto-per-target rule
   keeps a multi-word case at one incoming. *)
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
      let term_preds =
        Graphs.Tid.Node.preds blk_tid cfg
        |> Base.Sequence.to_list
      in
      let blk_incoming =
        Base.List.concat_map term_preds ~f:(fun ptid ->
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
            (* Unbound transfer vars read the register's fixed garbage:
               a freeze, so every later read of the same undefined
               register observes identical bits. *)
            frozen_undef ~builder:llvm_builder ctx var
      in
      !$(insert_local ctx tid var) llval)
  >>= fun () ->
  (* The SP Slot: every storage-carrying sub owns an entry-block
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
  insert_local ctx tid ctx.sp sp0;
  exit_entry llvm_builder sub () >>= fun _ -> return fr

(* Builds blocks and transfer set in one walk. *)
let collect_sub_data ctx llvm_ctx blks fn sub =
  insert_bb ctx Graphs.Tid.start (Llvm.entry_block fn);
  init_blk_llvals ctx Graphs.Tid.start;
  (* The transfer set (live across blocks: call-arg regs, callee rets,
     free vars) and the defined set (defs plus phi lhs — phi lanes need
     definedness). *)
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
      ((not @@ Hike_stack_model.is_mem var) || Var.same var (Abi.pc ctx.target))
      (* Keeps SP and every callee-saved lane (fp is an ordinary one). *)
      || Var.same var ctx.sp
      || Abi.is_callee_saved ctx.abi var)
  |> Core.Set.filter ~f:(fun var ->
      (* Drops never-defined vars from transfer. *)
      Core.Set.mem def_set var
      || Hike_stack_model.is_region_base var
      || Core.Set.mem arg_set var
      || Var.same var ctx.sp)
  |> Core.Set.to_list


(* The anchor word: ptrtoint of the base GEP at [idx] — the integer the
   SP Slot stores and every materialization relativizes against.  [idx]
   is ≡ 16 − word (mod 16): the SysV entry SP carries that residue, and
   the lifted word arithmetic (an SSE #GP fault guard tests
   (stack_0 + k) & 15) must evaluate the residue the native does. *)
let anchor_word llvm_ctx llvm_builder base idx =
  let anchor =
    Llvm.build_gep (Llvm.i8_type llvm_ctx) base
      [| Llvm.const_of_int64 (Llvm.i64_type llvm_ctx) idx false |]
      "anchor" llvm_builder
  in
  Llvm.build_ptrtoint anchor (Llvm.i64_type llvm_ctx) "anchor_i64"
    llvm_builder

(* The sub body: the stack model's LAYOUT decision is consumed here
   (the layout tag read below). *)
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
      Core.Map.find !(ctx.ll_funcs) (Term.tid sub)
      |> Base.Option.value_exn ~message:"create sub : function not found"
    in
    let llvm_builder = Llvm.builder_at_end llvm_ctx (Llvm.entry_block fn) in

    clear_bbs ctx;
    clear_blk_llvals ctx;
    clear_undef_vals ctx;
    let transfer_vars = collect_sub_data ctx llvm_ctx blks fn sub in
    (* The LAYOUT fact: the alloca-construction inputs ride the
       sub term — no analysis record reaches the emitter. *)
    let layout_regions, layout_anchor =
      match Term.get_attr sub Hike_stack_model.layout_tag with
      | Some { regions; anchor } -> (regions, anchor)
      | None -> ([], None)
    in
    let regions =
      Base.List.map layout_regions
        ~f:(fun (id, (lo, _), bytes) ->
          (* The array count crosses the LLVM binding as a 32-BIT
             UNSIGNED (the stub's Int_val -> unsigned param), so a
             count at/above 2^31 would truncate silently there.  The
             request is loud and bounded, never silently truncated;
             the fold keeps every sound producer below the boundary. *)
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
    (* THE stack anchor — the entry RSP's runtime position, from the
       fold: (region id, byte index).  The SP Slot stores its
       ptrtoint; every materialization relativizes against it. *)
    let anchor =
      match layout_anchor with
      | Some (rid, idx) -> (
          match
            Base.List.find regions
              ~f:(fun (v, _) -> Var.equal v (Hike_stack_model.region_mem rid))
          with
          | Some (_, (base, _)) -> Some (anchor_word llvm_ctx llvm_builder base idx)
          | None -> None)
      | None -> None
    in
    (* Binds region bases to alloca cell-0. *)
    let* () =
      let rec bind_regions = function
        | [] -> return ()
        | (v, (base, _)) :: rest ->
            insert_local ctx Graphs.Tid.start v base;
            bind_regions rest
      in
      bind_regions regions
    in
    (* The SP Slot: the entry-block alloca holding this
       invocation's anchor — the sub's own anchor integer. *)
    let anchor_val, sp_slot =
      match anchor with
      | Some v -> (v, true)
      | None ->
        (Llvm.const_int (Llvm.i64_type llvm_ctx) 0, false)
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
      match anchor with
      | Some v -> v
      | None -> Llvm.const_int (Llvm.i64_type llvm_ctx) 0
    in
    let fr : sub_frame =
      { anchor_i64; stack0; regions;
        is_precise = not (Base.List.is_empty regions) }
    in
    cur_frame := Some fr;
    add_args_to_vars llvm_builder Graphs.Tid.start (Term.tid sub) fn ()
    >>= fun () ->
    build_entry_block llvm_builder transfer_vars fr sub fn ()
    >>= fun fr ->
    cur_frame := Some fr;
    populate_blks transfer_vars blks sub fr ()
    >>= update_phis transfer_vars blks sub
    >>= fun () ->
    cur_frame := None;
    (* Summarizes model-ABI undef reads. *)
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

(* Sub-signature facts shared with the filter pass. *)

let free_vars sub =
  Sub.free_vars sub
  |> Core.Set.filter ~f:(fun var -> not @@ Hike_stack_model.is_mem var)
  |> Core.Set.to_list

(* Tests the [Sub.intrinsic] attribute. *)
let is_intrinsic (term : sub term) : bool =
  Term.has_attr term Sub.intrinsic

(* Intrinsics with bodies we can emit. *)
let is_emittable_intrinsic (term : sub term) : bool =
  is_intrinsic term && not (Seq.is_empty (Term.enum blk_t term))

(* The signature is FIXED — the promotion does not define it: the
   emittable intrinsics (free-var projection) and @main (rdi/rsi). *)
let fixed_signature (term : sub term) : bool =
  is_emittable_intrinsic term
  || String.equal (Tid.name (Term.tid term)) "@main"

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
    (* A sub whose incoming window it reads (the layout's window_param)
       carries the caller-window base: its above-entry accesses
       materialize against the CALLER's world. *)
    let window_arg =
      match Term.get_attr sub Hike_stack_model.layout_tag with
      | Some { Hike_stack_model.window_param = true; _ } ->
        let w = abi.Abi.word in
        [ Arg.create ~intent:In (Hike_stack_model.hike_window_var ~word:w)
            (Bil.Var (Hike_stack_model.hike_window_var ~word:w)) ]
      | _ -> []
    in
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
  else if fixed_signature sub then
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
       (* The signature is the callee's own promoted interface,
         transcribed from the SUB TERM'S OWN BIR ARGS (the promotion
         rewrite added them: the proven slots and the window class's
         hull slots 0..arity-1).  No record read: the args ARE the
         structure. *)
       let arg_terms = Term.enum arg_t sub |> Base.Sequence.to_list in
       let args =
         (* The convention's parameter order: the integer lanes, then
            the vector lanes. *)
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
             (* RBP filters out via [callee_saved] (an ordinary
                 callee-saved GPR — SP-only); the TLS base filters out
                 via [thread_pointer] (reads are self-basing — the
                 read site renders the target's own base); the promoted
                 interface names (hike_slotN / the call-arg temps) are
                 the emitter's own vocabulary — never register lanes. *)
             not
               (Var.same reg (Abi.sp target)
               || Var.same reg abi.thread_pointer
               || is_callee_saved
               || is_intrinsic_name n
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
          Base.List.map (Abi.param_regs abi)
            ~f:(fun reg -> Arg.create ~intent:In reg (Var reg))
        else args
      in
       (rets, args @ window_arg)
   in
   (rets, args)

(* One emission phase: the four KB context vars every lane reads,
   bound around [body].  The phases and their order — signatures,
   thunks, bodies, initializers — are the emission's load-bearing
   structure. *)
let run_emission ctx llvm_ctx llvm_module sections body =
  Toplevel.exec begin
    KB.Context.with_var emit_ctx_var ctx (fun () ->
      KB.Context.with_var llvm_ctx_var llvm_ctx (fun () ->
        KB.Context.with_var llvm_module_var llvm_module (fun () ->
          KB.Context.with_var section_list_var sections (fun () ->
            body ()))))
  end

(* The emission entry: signature collection, declarations, bodies. *)
let emit_program (llvm_ctx : Llvm.llcontext) (llvm_module : Llvm.llmodule)
    ~(target : Bap_core_theory.Theory.Target.t) ~(ptrsize : int)
    ~(symtab : Symtab.t option)
    ~(copy_relocs : int64 list)
    (spec : section_spec)
    (prog : program term) : unit =
  (* The sections construct from the spec — the globals, the tiles, and
     the owner lists — before any function declares. *)
  let sections = Bil2llvm_section.build_sections llvm_ctx llvm_module spec in
  (* The section base map: every native address in a section renders
     through its owning global. *)
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
  (* The named-component map: the BIL's sec_comp_N_mem routes
     through it; filled before any body emits (the rip-relative lane
     renders through the same owners). *)
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
  (* The synthetic indirect-call signature gains the Caller-Window
     Parameter: every pointer call passes the caller's SP at the
     call, so the Thunk of a promoted target can unpack the window. *)
  let icall_tid = Tid.for_name "indirect_call" in
  let conv = Abi.of_target target in
  let icall_sig =
    ( Base.List.map conv.return_regs ~f:(fun reg ->
          Arg.create ~intent:Out reg (Var reg)),
      window_conv_args ~word:conv.Abi.word conv )
  in
  (* The Thunks' signatures: the memory-path convention (the
     register lanes plus the window base) — registered so the
     unprovable-direct-site path can call the twin wholesale.  A sub
     earns a twin iff its own signature carries promoted slots (read
     from the signature, not a record). *)
  let has_slot_args args =
    Base.List.exists args ~f:(fun a -> Hike_stack_model.is_arg_slot (Arg.lhs a))
  in
  let twin_sig_of (sub, (rets, args)) =
    let sub_tid = Term.tid sub in
    if has_slot_args args && not (fixed_signature sub)
    then
      (* The twin's signature = the synthetic indirect convention (the
         register lanes plus the window base), exactly what a pointer
         call passes. *)
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
          (* Mapped intrinsics store the sig but define no function; a
             self-call stub declares instead of defining. *)
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
  (* The data-section initializers render INSIDE the one emission
     context: every 8-byte word goes through [remap_native_addr],
     whose symtab arm resolves to the Thunk of a promoted sub —
     function-pointer data must land on the memory-convention twin so
     unresolvable pointer sites stay sound.  Split sections
     render per owner: components with their typed/ptr decisions, gap
     runs as word slices. *)
  run_emission ctx llvm_ctx llvm_module sections (fun () ->
      KB.List.iter sections ~f:(fun section ->
          match section.bytes with
          | Some arr when Base.List.is_empty section.owners ->
              (* The unsplit section is one owner: the whole image,
                 word cells 0 through the last. *)
              let word = ctx.abi.Abi.word in
              KB.return
              @@ Bil2llvm_section.set_owner_initializer ctx llvm_ctx
                   llvm_module section.base arr
                   ~word_lo:0
                   ~word_hi:((Array.length arr + word - 1) / word - 1)
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

(* The frozen seam (bil2llvm.mli): re-exports from the lane modules. *)
type native_fp = Bil2llvm_fp.native_fp =
  | FMUL | FADD | FSUB | FDIV | FREM | SFLOAT | SINT
  | FCONVERT of int | FORDER | FHLT | ISNAN

(* The section construction's surface, from the env lane. *)
type sec_owner = Bil2llvm_env.sec_owner = {
  own_id : int option;
  own_lo : int64;
  own_hi : int64;
  base : Llvm.llvalue;
  typed_w : int;
  is_const : bool;
  bss : bool;
}

type section = Bil2llvm_env.section = {
  base : Llvm.llvalue;
  min_addr : word;
  max_addr : word;
  bytes : int array option;
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
      si_image : int array;
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

(* The name-minting fact, shared (see the mli). *)
let sanitize_name = Bil2llvm_env.sanitize_name

(* The section construction, from the section lane. *)
let build_sections = Bil2llvm_section.build_sections
let create_section_global = Bil2llvm_section.create_section_global
let create_uninitialized_global = Bil2llvm_section.create_uninitialized_global
let create_copy_reloc_bss = Bil2llvm_section.create_copy_reloc_bss
