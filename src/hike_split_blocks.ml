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
   only guarded gotos and explicit false edges. A call needs a direct
   return, not a direct target: an indirect call still splits. *)
let compilable_jmp ~last (j : jmp term) : bool =
  match Jmp.kind j with
  | Goto (Direct tid) ->
      not (Hike_abi.is_interrupt_name (Tid.name tid))
  | Goto (Indirect _) -> last
  | Call c -> (
      match Call.return c with
      | Some (Direct _) -> true
      | None -> last
      | Some _ -> false)
  | _ -> false

let compilable_series (jmps : jmp term list) : bool =
  let rec loop = function
    | [] -> true
    | [ j ] -> compilable_jmp ~last:true j
    | j :: js -> compilable_jmp ~last:false j && loop js
  in
  loop jmps

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
