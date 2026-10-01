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

  (** An image-backed section: inclusive bounds plus static content. *)
  type section_image = Cbat_vsa.section_image = {
    img_lo : int64;
    img_hi : int64;
    img_bytes : Bytes.t;
  }

  (** The fused solve: phases of solve + resolution growth until
      stable, materialization once at drain.  Returns the per-block
      (pre, post) environments, the rewritten sub, and the grown
      block-address map.  Non-convergence is the top identity: empty
      environments, the shape-canonicalized sub, the input
      block-address map.  [images] arm every denotation the solve, the
      completion, and the replay compute (one bracket, inside);
      [written] is the program's kill-summary pass, computed
      once at the boundary. *)
  val fixpoint :
    Theory.Target.t ->
    lookup:(int64 -> Tid.t option) ->
    sub_addrs:Tid.t Addr.Map.t ->
    images:section_image list ->
    written:Core.Int.Set.t option Tid.Map.t ->
    lift_at:(Addr.t -> block_addrs:Tid.t Addr.Map.t -> blk term list option) ->
    block_addrs:Tid.t Addr.Map.t ->
    sub term ->
    (Cbat_vsa.AI.t * Cbat_vsa.AI.t) Tid.Map.t * sub term * Tid.t Addr.Map.t

  (** The program's kill summaries (every subs' transitive written
      register set); computed once per program at the boundary and
      consumed by the fixpoint. *)
  val kill_summaries :
    abi:Hike_abi.t -> program term -> Core.Int.Set.t option Tid.Map.t
