open Bap.Std

type unop = Lnot | Neg | Extract of int option * int | Cast of Bil.cast * int
type binop = Op of Bil.binop | Concat

(* Malformed widths supply no inverse constraint. *)
val valid1 : unop -> arg:int -> result:int -> bool
val valid2 : binop -> left:int -> right:int -> result:int -> bool

(* Concrete semantics shared by the finite representation kernels.
   Undefined division supplies no exclusion evidence. *)
val word1 : unop -> Cbat_word.t -> Cbat_word.t
val word2 : binop -> Cbat_word.t -> Cbat_word.t -> Cbat_word.t option

module type Representation = sig
  type t

  val bitwidth : t -> int
  val parts : t -> t list
  val assemble : width:int -> t list -> t
  val intersection : t -> t -> t
  val is_bottom : t -> bool
  val unary : unop -> arg:t -> result:t -> t
  val binary : binop -> left:t -> right:t -> result:t -> t * t
end

(* Lift the representation's inverse kernels over all alternatives,
   returning sound projections of the satisfying inputs. *)
module Make (R : Representation) : sig
  val backward1 : unop -> arg:R.t -> result:R.t -> R.t
  val backward2 : binop -> left:R.t -> right:R.t -> result:R.t -> R.t * R.t
end
