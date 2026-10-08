open Bap.Std

(** Stable BAP intrinsic lanes; [bits] is the lane's own width. *)
val lane : string -> int -> var

(** Tags describe emission roles. All values remain ordinary BIR operands. *)
val operation : string Value.Tag.t
val input : int Value.Tag.t
val write : unit Value.Tag.t

(** Expand BAP atomic calls before analysis into tagged memory accesses.
    The producer captures address and input lanes in the call block. *)
val normalize : addr_bits:int -> program term -> program term
