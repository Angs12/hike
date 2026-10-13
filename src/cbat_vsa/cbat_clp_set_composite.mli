(* The analysis's word sets: the scalar domain ([Cbat_clp_set_scalar]),
   plus values wider than a word whose words keep their own origins. *)

type t

include
  module type of Cbat_clp_set_scalar
  with type t := t
   and type kind = Cbat_clp_set_scalar.kind
   and type binop := Cbat_clp_set_scalar.binop
   and type unop := Cbat_clp_set_scalar.unop
