open Bap.Std

(** Backward substitution: an exp read at a block's end, re-read at each
    earlier position by substituting the defs the walk passes (backward
    through the block only), simplified by exact rewrites after each
    step. *)

(** The node count of an exp. *)
val size : exp -> int

val has_unknown : exp -> bool

(** The exp's value read at one position: before [at] in [blk], or at
    the block's end with no [at] (the start).  [pos] orders positions
    within a block (later is larger).  [written] are the vars defined
    between the position and the start; [substituted] are the vars whose
    defs the walk substituted. *)
type form = {
  exp : exp;
  blk : blk term;
  at : def term option;
  pos : int;
  written : Var.Set.t;
  substituted : Var.Set.t;
}

(** An exp read at the form's position reads the same value at the
    start: none of its vars is written in between. *)
val holds : form -> exp -> bool

(** Every form of an exp read at the end of a block: the start first,
    then one per substituting def, nearest first. *)
val forms : blk term -> exp -> form list

(** Binds each form's exp to its var by a def at the form's position. *)
val bind : sub term -> (form * var) list -> sub term
