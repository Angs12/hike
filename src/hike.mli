(* Public interface. Consumers use [Hike.Abi], [Hike.Vsa], etc. *)

open Bap.Std
open Bap_core_theory

(** Register and convention facts. [Abi.sp] is the stack pointer. *)
module Abi = Hike_abi

(** Per-sub stack offset ranges. *)
module Vsa : sig
  (** Computes [sub]'s offset tags, stack plan, and promotion facts
      (T4).  The name map of [prog] and [symtab] resolve indirect-call
      targets to lifted subs. *)
  val offsets_of_sub :
    Theory.Target.t ->
    var ->
    symtab:Symtab.t option ->
    prog:program term ->
    sub term ->
    Hike_stack_model.vsa_info

  (** The target-resolution predicate (T4): a singleton whose word
      names a lifted sub resolves ([Some tid] — the Resolved Call
      Site); a bounded multi-target set, a foreign singleton, and TOP
      take the pointer call ([None]). *)
  val resolve_target :
    lookup:(int64 -> Tid.t option) -> Cbat_vsa.WordSet.t -> Tid.t option
end

(** Dead-code elimination. *)
module Dce : sig
  (** Rewrites the return epilogue, then sweeps unused defs. *)
  val dce :
    target:Theory.Target.t -> sub term -> sub term
end

(** Stack split decision and helpers.  Also the home of the Vsa record
    (S10b): the producer/emitter contract point — the producer builds
    it, the KB stores it, the model and the emitter consume it. *)
module Stack_model : sig
  (** Alias of the kind enum in [Cbat_extraction]. *)
  type vsa_kind = Hike_stack_model.vsa_kind =
    | Range of int64 * int64
    | Infinite of int64 * int64
    | Caller of int64 * int64
    | Mixed of int64 * int64
    | Unbounded
    | Dead
    | VLA of Tid.t

  type region = Hike_stack_model.region = {
    id : int;
    span : int64 * int64;
    members : (Tid.t * (int64 * int64)) list;
    convertible : bool;
    max_width : int;
  }

  (** [plan <> []] splits into [stack_rN] allocas; [[]] uses one [%frame]. *)
  type split_plan = Hike_stack_model.split_plan

  type call_site = Hike_stack_model.call_site = {
    site_slots : (int * Tid.t) list;
  }

  (** Per-def index map: [offsets] — the possible range of each access;
      plus the T4 promotion facts. *)
  type vsa_info = Hike_stack_model.vsa_info = {
    offsets : vsa_kind Tid.Map.t;
    regions : region list;
    stack_plan : split_plan;
    degraded : bool;
    vla_alloc_tids : Tid.Set.t;
    prom_slots : int Tid.Map.t;
    prom_arity : int;
    prom_window : bool;
    prom_retaddr : Tid.Set.t;
    prom_sites : call_site Tid.Map.t;
    prom_resolved : Tid.t option Tid.Map.t;
    sp_extents : (int64 * int64) list;
  }

  (** Builds info from maps. *)
  val mk_vsa_info_maps :
    ?prom_slots:int Tid.Map.t ->
    ?prom_arity:int ->
    ?prom_window:bool ->
    ?prom_retaddr:Tid.Set.t ->
    ?prom_sites:call_site Tid.Map.t ->
    ?prom_resolved:Tid.t option Tid.Map.t ->
    ?sp_extents:(int64 * int64) list ->
    offsets:vsa_kind Tid.Map.t ->
    regions:region list ->
    stack_plan:split_plan ->
    degraded:bool ->
    vla_alloc_tids:Tid.Set.t ->
    unit ->
    vsa_info

  (** Builds info from lists. *)
  val mk_vsa_info :
    ?prom_slots:int Tid.Map.t ->
    ?prom_arity:int ->
    ?prom_window:bool ->
    ?prom_retaddr:Tid.Set.t ->
    ?prom_sites:call_site Tid.Map.t ->
    ?prom_resolved:Tid.t option Tid.Map.t ->
    ?sp_extents:(int64 * int64) list ->
    offsets:(Tid.t * vsa_kind) list ->
    regions:region list ->
    stack_plan:split_plan ->
    degraded:bool ->
    vla_alloc_tids:Tid.Set.t ->
    unit ->
    vsa_info

  (** Structural equalities (fixture/diagnostic use). *)
  val equal_vsa_kind : vsa_kind -> vsa_kind -> bool
  val equal_region : region -> region -> bool
  val equal_split_plan : split_plan -> split_plan -> bool
  val equal_call_site : call_site -> call_site -> bool
  val equal_vsa_info : vsa_info -> vsa_info -> bool

  (** Merges overlapping ranges into regions; a region's facts (span,
      membership, storage class) derive from the tags alone (T4: the
      servability clause is deleted — the SP Slot anchor makes every
      sub's SP neighborhood private, so the partition is geometric). *)
  val regions_of_sub : sub term -> vsa_info -> region list

  (** The plan IS the convertible regions — no refusals.  An oversized
      region joins to Frame storage with a diagnostic naming it. *)
  val split_plan : sub term -> vsa_info -> split_plan

  (** Returns the region alloca size. *)
  val region_bytes : region -> int64

  (** Mints and recognizes fission vars. *)
  val region_mem : int -> var
  val region_base : int -> var

  (** The promoted incoming stack-slot parameter of index [i] (T4). *)
  val arg_slot : int -> var
end

(** Stack-to-locals rewrite. *)
module Stack_to_locals : sig
  (** Rewrites stack accesses to locals. *)
  val stack_to_locals : Theory.Target.t -> var -> sub term -> sub term
end

(** Per-sub VSA result store. *)
module Kb = Hike_kb

(** LLVM emitter. *)
module Bil2llvm = Bil2llvm

(** Copy-relocated BSS slots needing fresh values, pure in (relocs,
    program). Exported for direct fixture tests. *)
val copy_reloc_slots :
  bss_addr:int64 -> (int * string) list -> program term -> int64 list
