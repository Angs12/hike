open Bap.Std

(** Discover the complete program before the transformation passes.
    Decode, analysis, destination facts and convergence are internal.
    The result is BIR; no analysis products are installed for later passes. *)
val run : Project.t -> program term
