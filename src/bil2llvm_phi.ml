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

(* The rendered rows of one BIR edge (pred -> target): usually one,
   one per jmp when a series targets the same block twice. *)
let rows_for scope ~pred ~target : phi_edge list =
  Base.List.filter !(scope.edges)
    ~f:(fun r -> Tid.equal r.e_pred pred && Tid.equal r.e_target target)

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

(* One incoming per rendered predecessor of [target]: each BIR pred
   contributes one incoming per rendered row, and a pred with no
   recorded row — an edge the render lanes never see, such as a
   call's fallthrough when SP needs no restore — falls back to the
   pred's own block. *)
let add_incomings ctx scope ~phi ~(preds : Tid.t list) ~target var =
  Base.List.iter preds ~f:(fun ptid ->
      match rows_for scope ~pred:ptid ~target with
      | [] ->
        Llvm.add_incoming
          (incoming_value ctx scope ~sp_restore:None ~pred_tid:ptid ~target var,
           get_bb scope ptid)
          phi
      | rows ->
        Base.List.iter rows ~f:(fun r ->
            Llvm.add_incoming
              (incoming_value ctx scope
                 ~sp_restore:r.e_sp_restore ~pred_tid:r.e_pred ~target var,
               r.e_term_bb)
              phi))
