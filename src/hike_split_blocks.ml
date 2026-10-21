(* The block/jmp split: a multi-jmp series of direct gotos and calls
   becomes one block per jmp — piece 1 keeps the tid, defs, phis, and attrs; every piece carries
   an explicit Goto to the next.  The guards' false edges are already
   explicit by then (the completion writes them), so the BIR's edges are
   the jmps themselves: every later pass (the emitter included) reads the
   BIR, never a term order.  A series with any other jmp stays
   whole, named on the channel. *)

open Bap.Std
module Model = Hike_stack_model

(* Calls execute in their own arm blocks; the selector blocks contain
   only guarded gotos and explicit false edges. A call's return remains
   its original continuation, so SSA sees one ret-lane definition per arm. *)
let compilable_series (jmps : jmp term list) : bool =
  Base.List.for_all jmps ~f:(fun j ->
      match Jmp.kind j with
      | Goto (Direct tid) ->
          not (Hike_abi.is_interrupt_name (Tid.name tid))
      | Call c -> (match Call.target c with Direct _ -> true | _ -> false)
      | _ -> false)

(* Materialize before attribution rewrites addresses. Keep the call arms
   beside their stores until promotion binds the outgoing slot pointers;
   [normalize] then gives every call its own block before signature/SSA. *)
let materialize ~(facts : Hike_kb.facts) (prog : program term) :
    Hike_synth.table * program term =
  let synth = ref facts.synth in
  let module_addr ~bits a =
    Hike_synth.record synth (Hike_synth.mint_module_addr ~addr_bits:bits a) in
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
  (* The target of an indirect transfer that reads no foreign slot. *)
  let target_of ~index j =
    let target =
      match Jmp.kind j with
      | _ when Hike_return.is_jmp j -> None
      | Goto (Indirect e) -> Some e
      | Call c -> (match Call.target c with Indirect e -> Some e | Direct _ -> None)
      | _ -> None
    in
    Base.Option.filter target ~f:(fun e ->
        not (Base.Option.value_map (Hike_transfer.slot_of_target ~index ~synth:!synth e)
               ~default:false ~f:(Core.Set.mem facts.foreign_slots)))
  in
  (* The case test for one word: the target equals the word's module
     address, or — over a module-relative base — the loaded data equals
     [word - base] while the base is [base]. *)
  let case e (base : (int64 list * exp) option) (w : word) : exp =
    let bits = Word.bitwidth w in
    let a = Word.to_int64_exn w in
    match base with
    | Some (bs, b_exp) ->
      let delta b =
        Bil.BinOp (Bil.EQ, Bil.BinOp (Bil.MINUS, e, b_exp),
                   Bil.Int (Word.of_int64 ~width:bits (Int64.sub a b)))
      in
      (match bs with
       | [ b ] -> delta b
       | _ ->
         Base.List.map bs ~f:(fun b ->
             Bil.BinOp (Bil.AND,
                        Bil.BinOp (Bil.EQ, b_exp,
                                   Bil.Var (module_addr ~bits b)),
                        delta b))
         |> Base.List.reduce_exn ~f:(fun x y -> Bil.BinOp (Bil.OR, x, y)))
    | None ->
      Bil.BinOp (Bil.EQ, e, Bil.Var (module_addr ~bits a))
  in
  (* The words no arm tests, grouped by transfer kind; the last group is
     the default.  A word naming an in-sub block is a real destination:
     when the arming phase did not already arm it ([arm_dispatches] keys
     on the solve's destination sets, which can lag the final word set)
     the series arms it here under its own case test. *)
  let series sub j e words (base : (int64 list * exp) option) =
    let groups =
      Base.List.fold words ~init:[] ~f:(fun acc w ->
          let kind = name ~sub j w in
          let w = Cbat_word.to_word w in
          let equal a b = Int.equal (compare_jmp_kind a b) 0 in
          match Base.List.Assoc.find acc kind ~equal with
          | Some ws -> Base.List.Assoc.add acc kind (w :: ws) ~equal
          | None -> (kind, [ w ]) :: acc)
      |> List.rev
    in
    Base.List.mapi groups ~f:(fun i (kind, ws) ->
        let cond =
          if i + 1 = Base.List.length groups then Jmp.cond j
          else
            (match ws with
             | w :: rest -> Base.List.fold rest ~init:(case e base w)
                 ~f:(fun acc w -> Bil.BinOp (Bil.OR, acc, case e base w))
             | [] -> failwith "hike: dispatch: empty case group")
            |> Hike_coerce.coerce_exp in
        let cond = Hike_cfg_complete.and_guard
                     (Hike_cfg_complete.guard_of j) cond in
        let arm = if i = 0 then j else Jmp.create kind in
        Jmp.with_kind arm kind |> fun arm -> Jmp.with_cond arm cond)
  in
  (* A block's dispatch: its arms' guards become the relocation-safe case
     tests; when the arms cover every word, the last arm's edge is the
     fallback's default, else the remaining words follow the fallback as
     a series.  An armed block without a sound series fails: its guards
     compare model addresses. *)
  let dispatch_jmps ~sub ~plans blk =
    let jmps = Term.enum jmp_t blk |> Seq.to_list in
    let arms = Base.List.filter jmps ~f:(fun j -> Option.is_some (Hike_cfg_complete.arm_word j)) in
    match Base.List.find jmps ~f:(fun j -> Core.Map.mem plans (Term.tid j)) with
    | None when Base.List.is_empty arms -> None
    | None ->
      failwith
        (Printf.sprintf "hike: dispatch: sub %s block %s: an armed transfer has no sound case series"
           (Sub.name sub) (Tid.name (Term.tid blk)))
    | Some fb ->
      let e, d, base = Core.Map.find_exn plans (Term.tid fb) in
      let bits =
        match Type.infer e with
        | Ok (Type.Imm n) -> n
        | _ -> failwith "hike: dispatch: the target is not a word"
      in
      let armed = Base.List.filter_map arms ~f:Hike_cfg_complete.arm_word in
      let rest =
        Base.List.filter d.Hike_cfg_complete.words ~f:(fun w ->
            not (Base.Option.value_map (Cbat_word.to_int64_opt w) ~default:false
                   ~f:(fun w -> Base.List.mem armed w ~equal:Int64.equal)))
      in
      let tested a =
        let w = Word.of_int64 ~width:bits (Base.Option.value_exn (Hike_cfg_complete.arm_word a)) in
        Jmp.with_cond a
          (Hike_cfg_complete.and_guard (Hike_cfg_complete.guard_of fb)
             (Hike_coerce.coerce_exp (case e base w)))
      in
      let default, tail =
        match rest, Base.List.last arms with
        | [], Some last -> (Some (Term.tid last), [ Jmp.with_kind fb (Jmp.kind last) ])
        | _ -> (None, series sub fb e rest base)
      in
      Some
        (Base.List.concat_map jmps ~f:(fun j ->
             if Tid.equal (Term.tid j) (Term.tid fb) then tail
             else if Option.is_some (Hike_cfg_complete.arm_word j) then
               if Base.Option.exists default ~f:(Tid.equal (Term.tid j)) then []
               else [ tested j ]
             else [ j ]))
  in
  (* Every dispatch is read on the unbound sub; a base whose var is
     rewritten before the transfer is bound at its site, and the guards
     read the binding. *)
  let prog = Cbat_vsa.with_images facts.images (fun () ->
      Term.map sub_t prog ~f:(fun sub ->
          let index = Hike_transfer.index_of_sub sub in
          (* The arms are the BIR's case edges: the base walk reads
             every predecessor. *)
          let graph = Hike_backsubst.graph_of_sub sub in
          let plans =
            Term.enum blk_t sub
            |> Seq.concat_map ~f:(fun blk ->
                Term.enum jmp_t blk
                |> Seq.filter_map ~f:(fun j ->
                    Base.Option.bind (target_of ~index j) ~f:(fun e ->
                        Hike_cfg_complete.dispatch_words ~denote:facts.denote ~graph
                          ~block_addrs:facts.block_addrs
                          ~last_defs:(Cbat_vsa.last_defs blk) ~blk e
                        |> Base.Option.map ~f:(fun d ->
                          let bound =
                            match d.Hike_cfg_complete.base with
                            | Some { summand; site = Some f; _ } ->
                              let bits =
                                match Type.infer summand with
                                | Ok (Type.Imm n) -> n
                                | _ -> failwith "hike: dispatch: base summand is not a word"
                              in
                              Some ({ f with Hike_backsubst.exp = summand },
                                    Hike_synth.record synth (Hike_synth.mint_fresh ~bits Hike_synth.Binding))
                            | _ -> None
                          in
                          (Term.tid j, (e, d, bound))))))
            |> Seq.to_list
          in
          let binds = Base.List.filter_map plans ~f:(fun (_, (_, _, b)) -> b) in
          let plans = Tid.Map.of_alist_exn plans in
          let plans =
            Core.Map.map plans ~f:(fun (e, d, bound) ->
                let base =
                  Base.Option.map d.Hike_cfg_complete.base ~f:(fun b ->
                      match bound with
                      | Some (_, v) -> (b.values, Bil.Var v)
                      | None -> (b.values, b.summand))
                in
                (e, d, base))
          in
          let edit =
            Hike_ssa.Edit.start ~synth:!synth ~target:facts.target
              ~callee:(fun _ -> None) sub
          in
          let edit =
            Base.List.fold binds ~init:edit ~f:(fun edit (f, v) ->
                Hike_ssa.Edit.add_def edit ~blk:(Term.tid f.blk)
                  ?before:(Base.Option.map f.at ~f:Term.tid)
                  (Def.create v f.exp))
          in
          let edit =
            Term.enum blk_t sub
            |> Seq.fold ~init:edit ~f:(fun edit blk ->
                   match dispatch_jmps ~sub ~plans blk with
                   | None -> edit
                   | Some js ->
                       Hike_ssa.Edit.set_jmps edit (Term.tid blk) js)
          in
          (* Promotion must see the call arms beside their stores; the
             SSA commit is [normalize]'s, after promotion. *)
          Hike_ssa.Edit.view edit))
  in
  (!synth, prog)

(* The block/jmp split rides the SSA edit session: each jmp becomes its
   own piece, a call moves into an action block, and successor phi edges
   are duplicated per holder.  A series with another jmp stays whole. *)
let split_sub ?(update = true) ~synth ~target (sub : sub term) : sub term =
  let t0 =
    Hike_ssa.Edit.start ~synth ~target ~callee:(fun _ -> None) sub
  in
  let t =
    Term.enum blk_t sub
    |> Seq.fold ~init:t0 ~f:(fun t blk ->
           let jmps = Term.enum jmp_t blk |> Seq.to_list in
           let needs_split =
             Base.List.length jmps > 2
             || (Base.List.length jmps > 1
                 && Base.List.exists jmps ~f:(fun j ->
                        match Jmp.kind j with Call _ -> true | _ -> false))
           in
           if not needs_split then t
           else if compilable_series jmps then
             Hike_ssa.Edit.split_block t (Term.tid blk)
               (Base.List.map jmps ~f:(fun j -> [ j ]))
           else begin
             Hike_diag.warn
               "split-blocks: sub %s: block %s: unsupported multi-jmp series; left unsplit"
               (Sub.name sub) (Tid.name (Term.tid blk));
             t
           end)
  in
  if update then Hike_ssa.Edit.finish t
  else Hike_ssa.Edit.view t

let normalize ~synth ~target (prog : program term) : program term =
  Term.map sub_t prog ~f:(split_sub ~synth ~target)

(* Test-only liveness seam: production reads [Hike_ssa.free_regs_ssa].
   The sub's free registers, read at its own entries over the BIR's
   explicit edges.  A split piece carries no defs; its entering edge is
   the previous piece's explicit Goto, so liveness does not transport a
   target's live set to the sub entry. *)
let free_regs ~synth ~(abi : Hike_abi.t) (sub : sub term) : var list =
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
  let sub = Model.prepare_effects ~synth ~abi ~callee:(fun _ -> None) sub in
  let effects term = (Model.writes term, Model.reads term) in
  let def d = effects (`Def d) in
  let phi p = effects (`Phi p) in
  let jmp j = effects (`Jmp j) in
  let graph = Sub.to_graph sub in
  let block_ids =
    Base.List.map blks ~f:Term.tid |> Core.Set.of_list (module Tid)
  in
  let live =
    Hike_bir_flow.liveness ~graph ~sub
      ~initial:(Tid.Map.singleton Graphs.Tid.exit exit_seed)
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
         && not (Hike_synth.is_address_var synth v)
         && match Var.typ v with Type.Mem _ -> false | _ -> true)
  |> Core.Set.to_list
