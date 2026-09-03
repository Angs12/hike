(* Public interface. Consumers use [Hike.Abi], [Hike.Relevance], etc. *)

open Bap.Std
open Bap_core_theory

(** Register and convention facts. [Abi.sp] is the stack pointer. *)
module Abi = Hike_abi

(** Stack access tagging and relevance closure. *)
module Relevance : sig
  (** Tags a stack access def. *)
  val stack_access : unit tag

  (** Tags defs feeding a stack access. *)
  val relevant : unit tag

  (** Tags runtime-sized SP decrements. *)
  val dynamic_alloc : unit tag

  (** Tags [sub] with all three tags. *)
  val analyze : var -> sub term -> sub term

  (** Checks the [stack_access] tag. *)
  val has_stack_access : def term -> bool

  (** Tests for the stack pointer. *)
  val is_sp : Theory.Target.t -> var -> bool
end

(** Per-sub stack offset ranges. *)
module Vsa : sig
  (** Forwards the address width into the VSA. *)
  val set_addr_bits : int -> unit

  (** Computes [sub]'s offset tags and stack plan. *)
  val offsets_of_sub :
    Theory.Target.t -> var -> sub term -> Convutils.vsa_info
end

(** Dead-code elimination. *)
module Dce : sig
  (** Rewrites the return epilogue, then sweeps unused defs. *)
  val dce :
    target:Theory.Target.t -> sub term -> sub term
end

(** Stack split decision and helpers. *)
module Stack_model : sig
  (** Merges overlapping ranges into regions. *)
  val regions_of_sub :
    var -> Theory.Target.t -> sub term -> Convutils.vsa_info ->
    frame_escaped:bool -> Convutils.region list

  (** Returns split regions, or [[]] for the single-frame fallback. *)
  val split_plan :
    var -> Theory.Target.t -> sub term -> Convutils.vsa_info ->
    Convutils.split_plan

  (** Tests whether a derived value escapes. *)
  val sp_escaped : var -> Theory.Target.t -> sub term -> bool

  (** Tests for reads through a materialized frame pointer. *)
  val frame_addr_alias : var -> Theory.Target.t -> sub term -> bool

  (** Tests whether the frame is reachable from outside. *)
  val frame_escapes : var -> Theory.Target.t -> sub term -> bool

  (** Returns the region alloca size. *)
  val region_bytes : Convutils.region -> int64

  (** Tests the region size guard. *)
  val region_size_ok : Convutils.region -> bool

  (** Tests for the split model. *)
  val is_precise : Convutils.vsa_info -> bool

  (** Mints and recognizes fission vars. *)
  val region_mem : int -> var
  val region_base : int -> var
  val is_region_mem : var -> bool
  val is_region_base : var -> bool
end

(** Stack-to-locals rewrite. *)
module Stack_to_locals : sig
  (** Rewrites stack accesses to locals. *)
  val stack_to_locals : Theory.Target.t -> var -> sub term -> sub term
end

(** Per-sub VSA result store. *)
module Kb = Hike_kb

(** Shared pass/emitter vocabulary. *)
module Convutils = Convutils

(** LLVM emitter. *)
module Bil2llvm = Bil2llvm
