(* The callee-first discovery worklist (ADR 0027). *)
open Bap.Std

(** Main's closure (or, when main is not agreed or a reached indirect
    call stays unresolved, every BAP subroutine's) as linked, armed raw
    bodies, each published once its summary is final, plus a block-less
    sub per external and intrinsic target.  The entry carries
    [Sub.entry_point] and main [main_role] when main exists. *)
val run : Project.t -> program term
