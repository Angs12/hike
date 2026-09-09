(* Public interface. Consumers use [Hike.Abi], [Hike.Vsa], etc. *)

open Bap.Std
open Bap_core_theory

(** Register and convention facts. [Abi.sp] is the stack pointer. *)
module Abi = Hike_abi

(** Per-sub stack offset ranges. *)
module Vsa : sig
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
  (** Merges overlapping ranges into regions; a region's facts (span,
      membership, storage class) derive from the tags alone. *)
  val regions_of_sub :
    sub term -> Convutils.vsa_info -> Convutils.region list

  (** The plan IS the convertible regions — no refusals.  An oversized
      region joins to Frame storage with a diagnostic naming it. *)
  val split_plan :
    sub term -> Convutils.vsa_info -> Convutils.split_plan

  (** Returns the region alloca size. *)
  val region_bytes : Convutils.region -> int64

  (** Mints and recognizes fission vars. *)
  val region_mem : int -> var
  val region_base : int -> var
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

(** Copy-relocated BSS slots needing fresh values, pure in (relocs,
    program). Exported for direct fixture tests. *)
val copy_reloc_slots :
  bss_addr:int64 -> (int * string) list -> program term -> int64 list
