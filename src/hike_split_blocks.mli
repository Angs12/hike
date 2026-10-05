(* The block/jmp split and the free-register seam. *)
open Bap.Std

  val materialize : facts:Hike_kb.facts -> program term -> program term

  val split_sub : sub term -> sub term
  val normalize : program term -> program term

  (** The BIR's free registers over its explicit edges, memory vars
      dropped. *)
  val free_regs : abi:Hike_abi.t -> sub term -> var list
