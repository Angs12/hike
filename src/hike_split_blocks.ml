(* The block/jmp split: a 3+-jmp direct-goto series becomes one block per
   jmp — piece 1 keeps the tid, defs, phis, and attrs; every piece carries
   an explicit Goto to the next.  The guards' false edges are already
   explicit by then (the completion writes them), so the BIR's edges are
   the jmps themselves: every later pass (the emitter included) reads the
   BIR, never a term order.  A series that is not all direct gotos stays
   whole, named on the channel. *)

open Bap.Std
module Model = Hike_stack_model

(* Materialize before attribution rewrites addresses. Keep the call arms
   beside their stores until promotion binds the outgoing slot pointers;
   [normalize] then gives every call its own block before signature/SSA. *)
let materialize ~(facts : Hike_kb.facts) (prog : program term) : program term =
  let sub_at a =
    match Core.Map.find facts.sub_addrs a with
    | Some t -> Some t
    | None -> facts.lookup (Word.to_int64_exn a)
  in
  let name ~(sub : sub term) (j : jmp term) w =
    let a = Cbat_word.to_word w in
    let local =
      Base.Option.bind (Core.Map.find facts.block_addrs a) ~f:(fun t ->
          Base.Option.some_if (Option.is_some (Term.find blk_t sub t)) t)
    in
    match Jmp.kind j, local, sub_at a with
    | Goto _, Some t, _ -> Goto (Direct t)
    | Goto _, _, Some t -> Call (Call.create ~target:(Direct t) ())
    | Call c, _, Some t -> Call (Call.with_target c (Direct t))
    | Call c, Some t, _ when Option.is_none (Call.return c) ->
      (* The noreturn rendering of an indirect TAIL jump: the drive's
         second channel — the words name jump destinations, and the arms
         are gotos. *)
      Goto (Direct t)
    | Call _, Some _, _ ->
      failwith
        (Printf.sprintf
           "hike: dispatch: call target %s names a block, not a sub start"
           (Word.to_string a))
    | _ ->
      failwith
        (Printf.sprintf
           "hike: dispatch: sub %s block target %s at jmp %s names no transfer destination"
           (Sub.name sub) (Word.to_string a) (Tid.name (Term.tid j)))
  in
  let series sub blk j e =
    if Base.Option.value_map (Hike_transfer.slot_of_target ~sub e)
         ~default:false ~f:(Core.Set.mem facts.foreign_slots)
    then [ j ]
    else
      match Hike_cfg_complete.dispatch_words ~denote:facts.denote
              ~block_addrs:facts.block_addrs ~last_defs:(Cbat_vsa.last_defs blk)
              ~sub ~blk ~images:facts.images e with
      | None -> [ j ]
      | Some (base, bases, words) ->
        let base = Option.value base ~default:0L in
        let subject =
          Base.List.fold (Option.value bases ~default:[]) ~init:e
            ~f:(fun acc b -> Bil.BinOp (Bil.MINUS, acc, b))
        in
        let groups =
          Base.List.fold words ~init:[] ~f:(fun acc w ->
              let kind = name ~sub j w in
              let w = Word.of_int64 ~width:(Word.bitwidth (Cbat_word.to_word w))
                        (Int64.sub (Word.to_int64_exn (Cbat_word.to_word w)) base) in
              match Base.List.Assoc.find acc kind ~equal:Base.Poly.equal with
              | Some ws -> Base.List.Assoc.add acc kind (w :: ws) ~equal:Base.Poly.equal
              | None -> (kind, [ w ]) :: acc)
          |> List.rev
        in
        Base.List.mapi groups ~f:(fun i (kind, ws) ->
            let cond =
              if i + 1 = Base.List.length groups then Jmp.cond j
              else Hike_cfg_complete.guarded_cond subject ws in
            let cond = Hike_cfg_complete.and_guard
                         (Hike_cfg_complete.guard_of j) cond in
            let arm = if i = 0 then j else Jmp.create kind in
            Jmp.with_kind arm kind |> fun arm -> Jmp.with_cond arm cond)
  in
  Cbat_vsa.with_images facts.images (fun () ->
      Term.map sub_t prog ~f:(fun sub ->
          Term.map blk_t sub ~f:(fun blk ->
              Term.concat_map jmp_t blk ~f:(fun j ->
                  if Hike_return.is_jmp j then [ j ]
                  else match Jmp.kind j with
                    | Goto (Indirect e) -> series sub blk j e
                    | Call c -> (match Call.target c with
                        | Indirect e -> series sub blk j e
                        | Direct _ -> [ j ])
                    | _ -> [ j ]))))

(* Calls execute in their own arm blocks; the selector blocks contain
   only guarded gotos and explicit false edges. A call's return remains
   its original continuation, so SSA sees one ret-lane definition per arm. *)
let compilable_series (jmps : jmp term list) : bool =
  Base.List.for_all jmps ~f:(fun j ->
      match Jmp.kind j with
      | Goto (Direct tid) ->
          not (Bil2llvm_env.is_interrupt_name (Tid.name tid))
      | Call c -> (match Call.target c with Direct _ -> true | _ -> false)
      | _ -> false)

let pieces (blk : blk term) : blk term list =
  match Term.enum jmp_t blk |> Seq.to_list with
  | [] | [ _ ] -> [ blk ]
  | jmps ->
      let actions = ref [] in
      let selectors =
        Base.List.map jmps ~f:(fun j ->
            match Jmp.kind j with
            | Call _ ->
              let action =
                let bindings =
                  Term.enum def_t blk
                  |> Seq.filter ~f:(fun d -> Model.is_call_arg (Def.lhs d))
                  |> Seq.map ~f:(fun d -> Def.create (Def.lhs d) (Def.rhs d))
                  |> Seq.to_list
                in
                Blk.create ~defs:bindings
                  ~jmps:[ Jmp.with_cond j (Bil.Int (Word.one 1)) ] ()
              in
              actions := action :: !actions;
              Jmp.create ~cond:(Jmp.cond j) (Goto (Direct (Term.tid action)))
            | _ -> j)
      in
      let tids = Term.tid blk ::
                 Base.List.map (Base.List.tl_exn selectors) ~f:(fun _ -> Tid.create ()) in
      let n = Base.List.length selectors in
      let pieces =
        Base.List.mapi selectors ~f:(fun i j ->
            let blk_i =
              if Int.equal i 0 then
                Term.filter jmp_t blk ~f:(fun _ -> false)
                |> Term.filter def_t ~f:(fun d ->
                     Base.List.is_empty !actions || not (Model.is_call_arg (Def.lhs d)))
                |> fun b -> Term.append jmp_t b j
              else Blk.create ~tid:(Base.List.nth_exn tids i) ~jmps:[ j ] ()
            in
            if i + 1 < n then
              Term.append jmp_t blk_i
                (Jmp.create (Goto (Direct (Base.List.nth_exn tids (i + 1)))))
            else blk_i)
      in
      pieces @ List.rev !actions

let split_sub (sub : sub term) : sub term =
  Term.concat_map blk_t sub ~f:(fun blk ->
      let jmps = Term.enum jmp_t blk |> Seq.to_list in
      let needs_split =
        Base.List.length jmps > 2
        || (Base.List.length jmps > 1
            && Base.List.exists jmps ~f:(fun j ->
                   match Jmp.kind j with Call _ -> true | _ -> false))
      in
      if not needs_split then [ blk ]
      else if compilable_series jmps then pieces blk
      else begin
        Hike_diag.warn "split-blocks: sub %s: block %s: unsupported multi-jmp series; left unsplit"
          (Sub.name sub) (Tid.name (Term.tid blk));
        [ blk ]
      end)

let normalize (prog : program term) : program term =
  Term.map sub_t prog ~f:split_sub

(* The sub's free registers, read at its own entries over the BIR's
   explicit edges.  A split piece carries no defs; its entering edge is
   the previous piece's explicit Goto, so liveness does not transport a
   target's live set to the sub entry. *)
let free_regs ~(abi : Hike_abi.t) (sub : sub term) : var list =
  let blks = Term.enum blk_t sub |> Seq.to_list in
  (* The exit seed mirrors BAP's liveness: outgoing lanes read their
     value at the return. *)
  let exit_seed =
    Term.enum arg_t sub
    |> Seq.fold ~init:Var.Set.empty ~f:(fun acc arg ->
           match Arg.intent arg with
           | Some (Out | Both) ->
               Core.Set.union acc (Exp.free_vars (Arg.rhs arg))
           | _ -> acc)
  in
  let def live d =
    Core.Set.union
      (Core.Set.diff live (Model.def_writes d))
      (Model.def_reads d)
  in
  let phi live p =
    Core.Set.union (Core.Set.diff live (Model.phi_writes p))
      (Model.phi_reads p)
  in
  let jmp live j = Core.Set.union live (Model.jmp_reads ~abi j) in
  let graph = Sub.to_graph sub in
  let block_ids =
    Base.List.map blks ~f:Term.tid |> Core.Set.of_list (module Tid)
  in
  let live =
    Hike_bir_flow.run ~graph ~sub ~rev:true
      ~initial:(Tid.Map.singleton Graphs.Tid.exit exit_seed)
      ~default:Var.Set.empty ~equal:Core.Set.equal ~merge:Core.Set.union
      ~def ~phi ~jmp
  in
  Base.List.fold blks ~init:Var.Set.empty ~f:(fun acc blk ->
      let tid = Term.tid blk in
      let has_block_pred =
        Graphs.Tid.Node.preds tid graph
        |> Seq.exists ~f:(Core.Set.mem block_ids)
      in
      if has_block_pred then acc
      else
        Core.Set.union acc
          (Option.value (Core.Map.find live.before tid)
             ~default:Var.Set.empty))
  |> Core.Set.filter ~f:(fun v ->
         not (Hike_abi.is_sp abi (Var.base v))
         && match Var.typ v with Type.Mem _ -> false | _ -> true)
  |> Core.Set.to_list
