(* The noreturn fact. *)
open Bap.Std

(* [classify ~target prog] answers the set of subs whose control never
   returns to their caller: the runtime contract's names (body-less
   externs and the loader-named stubs) plus the call-graph fixpoint.
   Run it on the SOLVED program, where the denotations and the canonical
   return edges are final; thread the set into the next round's solve,
   where the completion's edge set consumes it. *)
val classify : target:Bap_core_theory.Theory.Target.t -> program term -> Tid.Set.t
