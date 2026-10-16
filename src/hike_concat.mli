(** Extract of a concat. *)
open Bap.Std

(** A field read from a double-width temporary's operands (or from a
    literal concat) that lies inside one operand reads that operand. *)
val normalize : program term -> program term

val normalize_block : blk term -> blk term
