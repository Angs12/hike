(* The VSA: the fused solve, its kill summaries, and the def-origin
   stamp — the producer's public surface. *)
open Bap.Std
open Bap_core_theory

  (** Arms the classifier's address width.  Analysis entries self-arm;
    probes may set it directly before a standalone solve. *)
  val set_addr_bits : int -> unit

  (** The per-def runtime origin: the origin the solve computed for
    the def's value, stamped at the solve boundary.  [None] = outside
    the analysis boundary (reads [Abs]). *)
  module Def_origin : sig
    val def_origin : def term -> Hike_origin.t option
    val with_origin : Hike_origin.t -> def term -> def term
  end

  (** An image-backed section: inclusive bounds plus static content;
      [img_slots] are the linker-owned slot addresses in the span. *)
  type section_image = Cbat_vsa.section_image = {
    img_lo : int64;
    img_hi : int64;
    img_bytes : Bytes.t;
    img_slots : Core.Int64.Set.t;
  }

  (** The fused solve: phases of solve + resolution growth until
      stable, materialization once at drain.  Returns the per-block
      (pre, post) environments, the rewritten sub, the grown
      block-address map, and the phases' dispatch facts (the site's
      address, its call class, the case words — the drive loop's fact
      source).  Non-convergence is the top identity: empty
      environments, the shape-canonicalized sub, the input
      block-address map, no facts.  [images] arm every denotation the
      solve, the completion, and the replay compute (one bracket,
      inside); [written] is the program's kill-summary pass, computed
      once at the boundary. *)
  val fixpoint :
    Theory.Target.t ->
    lookup:(int64 -> Tid.t option) ->
    sub_addrs:Tid.t Addr.Map.t ->
    images:section_image list ->
    written:Core.Int.Set.t option Tid.Map.t ->
    block_addrs:Tid.t Addr.Map.t ->
    foreign_slots:Core.Int64.Set.t ->
    ?noreturn:Tid.Set.t ->
    sub term ->
    (Cbat_vsa.AI.t * Cbat_vsa.AI.t) Tid.Map.t * sub term * Tid.t Addr.Map.t

  (** The persistent registers a sub's defs write (partial defs at
      their base register). *)
  val written_regs_of_sub : sub term -> Var.Set.t

  (** The program's kill summaries (every subs' transitive written
      register set); computed once per program at the boundary and
      consumed by the fixpoint. *)
  val kill_summaries :
    abi:Hike_abi.t -> program term -> Core.Int.Set.t option Tid.Map.t
