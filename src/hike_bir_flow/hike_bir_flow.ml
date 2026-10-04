open Core
open Bap.Std
open Graphlib.Std

type 'a solution = {
  before : 'a Tid.Map.t;
  after : 'a Tid.Map.t;
}

let apply_term ~def ~phi ~jmp state = function
  | `Def d -> def state d
  | `Phi p -> phi state p
  | `Jmp j -> jmp state j

let apply_block ~equal ~rev ~def ~phi ~jmp (blk : blk term) state =
  let elts = Blk.elts blk |> Seq.to_list in
  let elts = if rev then List.rev elts else elts in
  let rec close state =
    let next =
      List.fold elts ~init:state ~f:(apply_term ~def ~phi ~jmp)
    in
    if equal state next then next else close next
  in
  close state

let run ~(graph : Graphs.Tid.t) ~(sub : sub term) ~rev ~initial ~default
    ~equal ~merge ~def ~phi ~jmp =
  let blocks =
    Term.enum blk_t sub
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun blocks blk ->
           Core.Map.set blocks ~key:(Term.tid blk) ~data:blk)
  in
  let transfer tid state =
    match Core.Map.find blocks tid with
    | None -> state
    | Some blk -> apply_block ~equal ~rev ~def ~phi ~jmp blk state
  in
  let start = if rev then Graphs.Tid.exit else Graphs.Tid.start in
  let fixed =
    Graphlib.fixpoint (module Graphs.Tid) ~start ~rev
      ~init:(Solution.create initial default) ~equal ~merge ~f:transfer graph
  in
  let before, after =
    Core.Map.fold blocks ~init:(Tid.Map.empty, Tid.Map.empty)
      ~f:(fun ~key:tid ~data:_ (before, after) ->
        let state = Solution.get fixed tid in
        let transferred = transfer tid state in
        let before_state, after_state =
          if rev then transferred, state else state, transferred
        in
        ( Core.Map.set before ~key:tid ~data:before_state,
          Core.Map.set after ~key:tid ~data:after_state ))
  in
  { before; after }
