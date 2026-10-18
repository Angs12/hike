(* SSA materialization. *)
open Bap.Std
open Bap_core_theory

  val ssa_program :
    synth:Hike_synth.table -> target:Theory.Target.t -> program term ->
    program term

  (** The input lanes of an SSA sub: its index-0 reads. *)
  val free_regs_ssa :
    synth:Hike_synth.table -> abi:Hike_abi.t -> sub term -> var list

  (** The sub's SSA mark. *)
  val is_ssa : sub term -> bool
