(* The phi planner: one owner of the rendered edges and the incoming
   values.  Every rendered jmp records its edge; a target's phi takes
   one incoming per rendered predecessor — the block holding the
   winning terminator — with the edge's SP restore winning over the
   pred's local binding, and a never-bound read warning and freezing.
   BIR-graph edge counts play no part: after the series render the
   block that branches is the planner's recorded terminator block. *)

open Bap.Std
open Bil2llvm_env

let record_edge scope ~pred ~target ~term_bb ?sp_restore () =
  scope.edges :=
    { e_pred = pred;
      e_term_bb = term_bb;
      e_sp_restore = sp_restore;
      e_target = target }
    :: !(scope.edges)

(* The incoming's value for one rendered edge: the edge's SP restore
   wins over the pred's local binding; a never-bound read warns and
   freezes. *)
let incoming_value ctx scope ~sp_restore ~pred_tid ~target var =
  match sp_restore with
  | Some v when Var.same var ctx.sp -> v
  | _ -> (
    match get_local scope pred_tid var with
    | Some v -> v
    | None ->
        warn_undef_read ctx scope var target;
        frozen_undef ctx scope var)

(* One incoming per rendered edge into [target]: the recorded rows ARE
   the emitted CFG's predecessor set, so a block the render lanes never
   branch to takes no incoming. *)
let add_incomings ctx scope ~phi ~(rows : phi_edge list) ~target var =
  Base.List.iter rows ~f:(fun r ->
      Llvm.add_incoming
        (incoming_value ctx scope ~sp_restore:r.e_sp_restore
           ~pred_tid:r.e_pred ~target var,
         r.e_term_bb)
        phi)

(* The phi pruner: a phi that merges nothing goes away.  A
   single-incoming phi folds to its incoming (the one pred dominates
   every path to the target, so the value dominates every use); a phi
   whose incomings are one identical value folds to it (the value is
   the preds' shared local binding, so a common definition already
   dominates them); a dead phi — no users, or only dead-phi users — is
   deleted.  Identity is the printed value: LLVM names are uniqued, so
   equal prints are the same value. *)
let prune_phis scope =
  let key (v : Llvm.llvalue) : string = Llvm.string_of_llvalue v in
  let users_of v =
    let rec go acc = function
      | None -> acc
      | Some u -> go (Llvm.user u :: acc) (Llvm.use_succ u)
    in
    go [] (Llvm.use_begin v)
  in
  let phis =
    Core.Map.data !(scope.blk_llvals)
    |> Base.List.concat_map ~f:(fun bv ->
           Base.List.map (WVarMap.bindings !(bv.phis)) ~f:snd)
    |> Base.List.map ~f:(fun p -> (key p, p))
  in
  let fold (_, p) =
    match Llvm.incoming p with
    | [ (v, _) ] when key v <> key p ->
      Llvm.replace_all_uses_with p v;
      Llvm.delete_instruction p;
      true
    | (v0, _) :: _ :: _ when key v0 <> key p ->
      let inc = Llvm.incoming p in
      if false && Base.List.for_all inc ~f:(fun (v, _) -> key v = key v0) then begin
        Llvm.replace_all_uses_with p v0;
        Llvm.delete_instruction p;
        true
      end
      else false
    | _ -> false
  in
  let survivors = Base.List.filter phis ~f:(fun kp -> not (fold kp)) in
  let graph =
    Base.List.map survivors ~f:(fun (k, p) ->
        (k, p, Base.List.map (users_of p) ~f:key))
  in
  let rec sweep dead =
    let newly =
      Base.List.filter graph ~f:(fun (k, _, users) ->
          not (Base.List.mem dead k ~equal:String.equal)
          && Base.List.for_all users ~f:(fun u ->
                 Base.List.mem dead u ~equal:String.equal))
    in
    if Base.List.is_empty newly then dead
    else sweep (Base.List.map newly ~f:(fun (k, _, _) -> k) @ dead)
  in
  let dead = sweep [] in
  let dead_phis =
    Base.List.filter_map graph ~f:(fun (k, p, _) ->
        if Base.List.mem dead k ~equal:String.equal then Some p else None)
  in
  Base.List.iter dead_phis ~f:(fun p ->
      Llvm.replace_all_uses_with p (Llvm.undef (Llvm.type_of p)));
  Base.List.iter dead_phis ~f:Llvm.delete_instruction;
#ifdef VSA_DEBUG
  Base.List.iter phis ~f:(fun _ -> Cbat_vsa.Cbat_attr_census.bump "phi.total");
  Base.List.iter survivors ~f:(fun _ ->
      Cbat_vsa.Cbat_attr_census.bump "phi.merged");
  Base.List.iter dead_phis ~f:(fun _ ->
      Cbat_vsa.Cbat_attr_census.bump "phi.dead");
#endif
  ()
