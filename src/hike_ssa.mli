(* SSA materialization. *)
open Bap.Std
open Bap_core_theory

  val ssa_program :
    target:Theory.Target.t -> program term -> program term

  (** The input lanes of an SSA sub: its index-0 reads. *)
  val free_regs_ssa : sub term -> var list

  (** The sub's SSA mark. *)
  val is_ssa : sub term -> bool
