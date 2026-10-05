(* The CFG materializer's canonical return edge.  Its direct target is
   reserved for the return transfer; consumers compare the target identity,
   not a generated block name.  BAP can expose the edge as a no-return
   call, so this predicate is the single return classifier. *)
open Bap.Std

let tid : tid = Tid.for_name "hike_return"

let is_target (t : tid) : bool = Tid.equal t tid

let is_jmp (j : jmp term) : bool =
  match Jmp.kind j with
  | Ret (Direct t) -> is_target t
  | Ret (Indirect _) -> false
  | Call c ->
      Option.is_none (Call.return c)
      && (match Call.target c with Direct t -> is_target t | Indirect _ -> false)
  | Goto _ | Int _ -> false

let create () : jmp term = Jmp.create_ret (Direct tid)
