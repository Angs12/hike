(* SSA materialization. *)
open Bap.Std
open Bap_core_theory

  (** The SSA of a lifted sub: calls read and write the machine
      convention, returns the ABI's return lanes. *)
  val prepare_sub :
    synth:Hike_synth.table -> target:Theory.Target.t -> sub term -> sub term

  (** The initial edge inserted before an entry block with backedges. *)
  val entry_tag : unit Value.Tag.t

  (** Every incoming register has a phi, including with one predecessor.
      Memory retains its model identity. *)
  val ssa_sub :
    synth:Hike_synth.table -> target:Theory.Target.t -> sub term -> sub term

  val ssa_program :
    synth:Hike_synth.table -> target:Theory.Target.t -> program term ->
    program term

  (** Re-derives the lanes of the call jmps [select] accepts under
      [callee]; every lane keeps the version the call had, a gained lane
      reads the block's live version and mints a fresh one for a write. *)
  val refresh_calls :
    synth:Hike_synth.table -> abi:Hike_abi.t ->
    callee:(Tid.t -> sub term option) -> select:(jmp term -> bool) ->
    sub term -> sub term

  (** A call jmp that is not the canonical return. *)
  val is_call_jmp : jmp term -> bool

  (** Reserves all versions minted by a derived view without changing claims. *)
  val retain_history : from:sub term -> sub term -> sub term

  (** Refreshes signed call lanes, preserving existing register identities
      when only reads narrow; updates SSA for newly live merges or results. *)
  val relane_sub :
    synth:Hike_synth.table -> target:Theory.Target.t ->
    callee:(Tid.t -> sub term option) -> sub term -> sub term

  (** The input lanes of an SSA sub: its index-0 reads. *)
  val free_regs_ssa :
    synth:Hike_synth.table -> abi:Hike_abi.t -> sub term -> var list

  (** [update_sub ~old sub] brings an SSA sub up to date after blocks
      and edges were added.  [old] is the previous SSA sub; [sub] is
      [old] with the new blocks (pre-SSA), new edges, and any replaced
      terms (fresh tids) applied.  Only the blocks that are new,
      changed, need different phis or are reachable from those are
      renamed, with versions above every earlier index; every other
      block is returned untouched.  The result is [equivalent] to
      constructing SSA from scratch on [sub]. *)
  val update_sub :
    synth:Hike_synth.table -> target:Theory.Target.t -> old:sub term ->
    sub term -> sub term

  (** [update_sub] with the blocks it renamed (new, changed, or reached
      from those): the blocks a warm solve must recompute. *)
  val update_sub_woken :
    synth:Hike_synth.table -> target:Theory.Target.t -> old:sub term ->
    sub term -> sub term * Tid.Set.t

  (** Equal up to a consistent renaming of versions per base var. *)
  val equivalent : sub term -> sub term -> bool

  (** The sub in pre-SSA form: base names, no phis, no version stamps. *)
  val unssa_sub : sub term -> sub term
