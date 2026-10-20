(* The block/jmp split and the free-register seam. *)
open Bap.Std

  val materialize :
    facts:Hike_kb.facts -> program term -> Hike_synth.table * program term

  val split_sub :
    synth:Hike_synth.table -> target:Bap_core_theory.Theory.Target.t ->
    sub term -> sub term

  val normalize :
    synth:Hike_synth.table -> target:Bap_core_theory.Theory.Target.t ->
    program term -> program term

  (** The BIR's free registers over its explicit edges, memory vars
      dropped. *)
  val free_regs :
    synth:Hike_synth.table -> abi:Hike_abi.t -> sub term -> var list
