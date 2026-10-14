(* The callee-first discovery worklist (ADR 0027). *)
open Bap.Std

(** The discovered program and the analysis facts of its solves. *)
type result = { program : program term; facts : Hike_kb.facts }

(** Main's closure (or, when main is not agreed or a reached indirect
    call stays unresolved, every subroutine's of [subroutines] in the
    text): each function solved once its callees' summaries are final,
    with one jump per block, plus a block-less declaration per external
    target.  [state] is the initial decode of the program in package
    [file], and [subroutines] its subroutine entries.  The entry carries
    [Sub.entry_point] and main [main_role] when main exists. *)
val run :
  Project.t -> file:string -> state:Disasm.Driver.state ->
  subroutines:int64 list -> result
