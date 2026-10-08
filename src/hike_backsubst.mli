open Bap.Std

(** Backward substitution: an exp read at a block's end, re-read at each
    earlier position by substituting the defs the walk passes (backward
    through the block and on into a unique goto predecessor), simplified
    by exact rewrites after each step. *)

(** The node count of an exp. *)
val size : exp -> int

val has_unknown : exp -> bool

(** Exact rewrites to a fixpoint: constant folding, integer identities,
    the flag idioms, and relation combination over one operand pair. *)
val simplify : exp -> exp

(** A sub's blocks and incoming edges; a call, return, or interrupt edge
    ends a walk, as does the entry block. *)
type graph

(** [targets] names an indirect jump's known destination blocks (none by
    default): the BIR carries no edge for them. *)
val graph_of_sub : ?targets:(jmp term -> tid list) -> sub term -> graph

(** The exp's value read at one position: before [at] in [blk], or at
    the block's end with no [at] (the start).  [hops] counts the blocks
    back from the start and [pos] orders positions within a block (later
    is larger).  [written] are the vars defined between the position and
    the start; [substituted] are the vars whose defs the walk
    substituted. *)
type form = {
  exp : exp;
  blk : blk term;
  at : def term option;
  hops : int;
  pos : int;
  written : Var.Set.t;
  substituted : Var.Set.t;
}

(** An exp read at the form's position reads the same value at the
    start: none of its vars is written in between. *)
val holds : form -> exp -> bool

(** Every form of an exp read at the end of a block: the start first,
    then one per substituting def, nearest first. *)
val forms : graph -> blk term -> exp -> form list

(** Binds each form's exp to its var by a def at the form's position. *)
val bind : sub term -> (form * var) list -> sub term
