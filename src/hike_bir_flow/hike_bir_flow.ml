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

let apply_block ~equal ~def ~phi ~jmp elts state =
  let rec close state =
    let next =
      List.fold elts ~init:state ~f:(apply_term ~def ~phi ~jmp)
    in
    if equal state next then next else close next
  in
  close state

(* The fixpoint over per-block transfers; [before]/[after] re-apply the
   fixed state's transfer once per block. *)
let solve ~(graph : Graphs.Tid.t) ~(sub : sub term) ~rev ~initial ~default
    ~equal ~merge ~(transfer_of : blk term -> 'a -> 'a) =
  let blocks =
    Term.enum blk_t sub
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun blocks blk ->
           Core.Map.set blocks ~key:(Term.tid blk) ~data:(transfer_of blk))
  in
  let transfer tid state =
    match Core.Map.find blocks tid with
    | None -> state
    | Some f -> f state
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

let run ~graph ~sub ~rev ~initial ~default ~equal ~merge ~def ~phi ~jmp =
  solve ~graph ~sub ~rev ~initial ~default ~equal ~merge
    ~transfer_of:(fun blk ->
        let elts = Blk.elts blk |> Seq.to_list in
        let elts = if rev then List.rev elts else elts in
        apply_block ~equal ~def ~phi ~jmp elts)

(* A block's backward transfer as one idempotent [(live \ kill) U gen]:
   each element, last to first, replaces the gen set by
   [(gen \ writes) U reads] and adds its writes to the kill set. *)
let liveness ~graph ~sub ~initial ~def ~phi ~jmp =
  let empty = Var.Set.empty in
  solve ~graph ~sub ~rev:true ~initial ~default:empty ~equal:Core.Set.equal
    ~merge:Core.Set.union
    ~transfer_of:(fun blk ->
        let step (gen, kill) (writes, reads) =
          (Core.Set.union (Core.Set.diff gen writes) reads,
           Core.Set.union kill writes) in
        let gen, kill =
          Blk.elts blk |> Seq.to_list |> List.rev
          |> List.fold ~init:(empty, empty) ~f:(fun acc -> function
              | `Def d -> step acc (def d)
              | `Phi p -> step acc (phi p)
              | `Jmp j -> step acc (jmp j))
        in
        fun live -> Core.Set.union (Core.Set.diff live kill) gen)

type rule = {
  reads : var list;
  fire : holds:(var -> bool) -> add:(var -> unit) -> unit;
}

let closure (rules : rule list) =
  let waiting = Var.Table.create () in
  List.iter rules ~f:(fun r ->
      List.iter r.reads ~f:(fun v -> Hashtbl.add_multi waiting ~key:v ~data:r));
  fun seeds ->
    let members = Var.Table.create () in
    let queue = Queue.create () in
    let holds v = Hashtbl.mem members v in
    let add v =
      if not (holds v) then begin
        Hashtbl.set members ~key:v ~data:();
        List.iter (Hashtbl.find_multi waiting v) ~f:(Queue.enqueue queue)
      end
    in
    List.iter seeds ~f:add;
    List.iter rules ~f:(Queue.enqueue queue);
    let rec drain () =
      match Queue.dequeue queue with
      | None -> ()
      | Some r -> r.fire ~holds ~add; drain ()
    in
    drain ();
    Hashtbl.keys members
