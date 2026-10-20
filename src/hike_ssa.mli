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

  (** [update_sub ~old sub] updates SSA after CFG discovery. New blocks
      and genuinely new local definitions receive fresh names above the
      retained high-water history. Existing phi lhs values and local
      definition identities stay stable; incoming phi operands are
      rewired for the current predecessors. *)
  val update_sub :
    synth:Hike_synth.table -> target:Theory.Target.t -> old:sub term ->
    sub term -> sub term

  (** [update_sub] with the conservative VSA invalidation region. *)
  val update_sub_woken :
    synth:Hike_synth.table -> target:Theory.Target.t -> old:sub term ->
    sub term -> sub term * Tid.Set.t

  (** Equal up to a consistent renaming of versions per base var. *)
  val equivalent : sub term -> sub term -> bool

  (** The sub in pre-SSA form: base names, no phis, no version stamps. *)
  val unssa_sub : sub term -> sub term

  (** A mutable edit session over an SSA sub.  Restructuring passes use
      the primitives instead of rebuilding terms; [finish] derives the
      new calls' lanes from [callee] and commits the whole edit through
      one update.  Existing identities are preserved. *)
  module Edit : sig
    type t

    val start :
      synth:Hike_synth.table -> target:Theory.Target.t ->
      callee:(Tid.t -> sub term option) -> sub term -> t

    val view : t -> sub term

    val append_jmp : t -> Tid.t -> jmp term -> t

    val replace_jmp : t -> jmp term -> jmp term -> t

    val remove_jmp : t -> Tid.t -> t

    (** Replace a block's jmp series; its calls get derived lanes. *)
    val set_jmps : t -> Tid.t -> jmp term list -> t

    (** Add a local definition, optionally before [before]. *)
    val add_def : t -> blk:Tid.t -> ?before:Tid.t -> def term -> t

    val add_block : t -> blk term -> t

    val remove_block : t -> Tid.t -> t

    (** Split a block into the given groups, one piece per group; a call
        moves into its own action block and successor phi edges are
        duplicated per holder. *)
    val split_block : t -> Tid.t -> jmp term list list -> t

    (** Commit the edit: derive the edited calls' lanes, mint versions,
        rewire phis, and return the sub with the VSA invalidation set. *)
    val finish : t -> sub term * Tid.Set.t
  end
