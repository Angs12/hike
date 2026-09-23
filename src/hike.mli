(* Public interface. Consumers use [Hike.Abi], [Hike.Vsa], etc. *)

open Bap.Std
open Bap_core_theory

(** Register and convention facts. [Abi.sp] is the stack pointer. *)
module Abi = Hike_abi

(** The production diagnostic channel: [hike: ...] lines on stderr. *)
module Diag = Hike_diag

module Vsa : sig
  (** Arms the classifier's address width; analysis entries self-arm. *)
  val set_addr_bits : int -> unit

  (** An image-backed section: inclusive bounds plus static content. *)
  type section_image = Cbat_vsa.section_image = {
    img_lo : int64;
    img_hi : int64;
    img_bytes : Bytes.t;
  }

  (** The fused solve: phases of solve + resolution growth until
      stable, materialization once at drain.  Returns the per-block
      (pre, post) environments, the rewritten sub, and the grown
      block-address map; [None] = non-convergence (readers take the
      top identity).  [prog] is the whole program; [images] arm the
      resolver's denotations only; [written] is the program's
      kill-summary pass, computed once at the boundary. *)
  val fixpoint :
    Theory.Target.t ->
    prog:program term ->
    symtab:Symtab.t option ->
    images:section_image list ->
    written:Var.Set.t option Tid.Map.t ->
    lift_at:(Addr.t -> blk term list option) ->
    block_addrs:Tid.t Addr.Map.t ->
    sub term ->
    ((Cbat_vsa.AI.t * Cbat_vsa.AI.t) Tid.Map.t * sub term *
     Tid.t Addr.Map.t) option

  (** The program's kill summaries (every subs' transitive written
      register set); computed once per program at the boundary and
      consumed by the fixpoint. *)
  val kill_summaries :
    abi:Abi.t -> program term -> Var.Set.t option Tid.Map.t
end

(** The CFG completion, fused into the solver's loop: resolution is an
    in-loop step of the fixpoint, materialization runs once at drain. *)
module Cfg_complete : sig
  (** The seam the solver passes in: [exp] denotes in [blk] (in the
      target def's before-env when [~def] is given). *)
  type denote =
    blk:blk term -> ?def:def term -> exp ->
    (Cbat_vsa.WordSet.t, Type.error) Result.t

  (** The defs whose load address denotates, in the def's own
      before-env, to the stack-symbolic entry-RSP cell. *)
  val retaddr_defs :
    abi:Abi.t -> sol:Cbat_vsa.vsa_sol -> sub term -> Tid.Set.t

  (** One resolution pass on the phase's solution: resolvable case
      words land on the run's map (mid-block entries split their
      block, additively) and resolved dispatches grow the extra
      edges.  Returns the sub, the edge set, the fresh entry blocks,
      the grown block-address map, and whether anything grew. *)
  val resolve_phase :
    abi:Abi.t ->
    sol:Cbat_vsa.vsa_sol ->
    images:Cbat_vsa.section_image list ->
    lift_at:(Addr.t -> blk term list option) ->
    block_addrs:Tid.t Addr.Map.t ->
    sub term ->
    Tid.Set.t Tid.Map.t ->
    sub term * Tid.Set.t Tid.Map.t * Tid.Set.t * Tid.t Addr.Map.t * bool

  (** The exit materialization at drain: canonical returns,
      complete-only guarded-goto series, and the prune retracts split
      structure the materialization didn't claim. *)
  val materialize :
    abi:Abi.t ->
    sol:Cbat_vsa.vsa_sol ->
    images:Cbat_vsa.section_image list ->
    block_addrs:Tid.t Addr.Map.t ->
    fresh:Tid.Set.t ->
    sub term -> sub term
end

(** Indirect-target resolution, read from the target's denotation. *)
module Resolve : sig
  (** A singleton whose word names a lifted sub resolves ([Some tid]);
      a bounded multi-target set, a foreign singleton, and TOP take
      the pointer call ([None]). *)
  val resolve_target :
    lookup:(int64 -> Tid.t option) -> Cbat_vsa.WordSet.t -> Tid.t option
end

(** Dead-code elimination. *)
module Dce : sig
  (** Rewrites the return epilogue, then sweeps unused defs. [roots]
      names storage mem vars whose bytes escape this sub. *)
  val dce :
    ?roots:Var.Set.t -> target:Theory.Target.t -> sub term -> sub term
end

(** The jump compiler: jcc flag idioms become value comparisons. *)
module Jump : sig
  (** Rewrites jcc flag idioms into equivalent value comparisons;
      identity on the residual. *)
  val compile_sub : Theory.Target.t -> sub term -> sub term
end

(** The sub filter: named exclusions, stub/extern/intrinsic removal,
    the symbol-table check. *)
    module Filter : sig
      val filter_subs : Project.t -> Project.t
    end

    (** Node fission: every def keeps exactly one memory node inline —
        the per-def tag is then the complete proof of that node. *)
    module Split_mem : sig
  val split_sub : sub term -> sub term
  val normalize : program term -> program term
end

(** Stack split decision and helpers, and the shared section
    vocabulary: the producer/emitter contract point. *)
module Stack_model : sig
  (** The sections in declaration order. *)
  type sec = Hike_stack_model.sec =
    | Stack
    | Args
    | Text
    | Rodata
    | Data
    | Got
    | Gotplt
    | Datarelro
    | Bss
  [@@deriving equal, compare, sexp]

  (** The slim def-carried classification. *)
  module Tag = Hike_stack_model.Tag

  type sec_tag = Hike_stack_model.sec_tag

  val sec_tag : def term -> sec_tag option
  val set_sec_tag : sec_tag -> def term -> def term
  (** The model segment's base (2^62 + 8: the ABI entry residue): the
      ABSOLUTE position of the entry RSP on the segment line; tag
      positions are absolute, so a frame offset [o] sits at
      [segment_base + o]. *)
  val segment_base : int64

  (** The base's certified width: the low nibble is the ABI entry
      residue (8 (mod 16)), the only bits that are a fact. *)
  val certified_bits : int

  (** The plain-arm stack band's lower bound; the band is
      [stack_band_lo, 2^63). *)
  val stack_band_lo : int64

  (** The denotation's single absolute stack position, when it
      denotates to exactly one — the cell-identity predicate. *)
  val singleton_stack_position : Cbat_vsa.WordSet.t -> int64 option

  (** THE return-address fact: the stack-symbolic singleton at the
      entry-RSP cell, in its three spellings (denotation, stamped tag,
      pre-solve shape). *)
  val is_return_address : Cbat_vsa.WordSet.t -> bool
  val is_return_address_tag : sec_tag -> bool
  val is_return_address_shape : abi:Abi.t -> exp -> bool

  (** One emitted section component: the word range of the span
      it covers plus the typed-emission decision. *)
  type sec_comp = Hike_stack_model.sec_comp = {
    comp_id : int;
    sec_lo : int64;
    sec_hi : int64;
    lo_w : int;
    hi_w : int;
    typed_w : int;
  }

  (** A word of a section image is string text iff a printable run
      crosses its start boundary. *)
  val string_text_word : arr:Bytes.t -> off:int -> bool

  (** The stack-address / store-data readers over the one mem-node scan. *)
  val addr_of_rhs : exp -> (exp * Size.t) option
  val store_data_of_rhs : exp -> (exp * (exp -> exp)) option

  (** Mints and recognizes fission vars. *)
  val region_mem : int -> var
  val is_region_mem : var -> bool

  (** The incoming-window memory var (the caller's world) and its test. *)
  val window_mem : var
  val is_window_mem : var -> bool

  (** Mints and recognizes the section-component fission vars. *)
  val sec_comp_mem : int -> var
  val is_sec_comp_mem : var -> bool
  val sec_comp_name : int -> string
  val sec_res_name : int -> string

  val is_true_cond : exp -> bool

  (** The SIGNATURE CONTRACT: which subs keep their pre-promotion
      signature (the emittable intrinsics and @main). *)
  val is_intrinsic : sub term -> bool
  val is_emittable_intrinsic : sub term -> bool
  val is_intrinsic_name : string -> bool
  val fixed_signature : sub term -> bool

  (** The promoted incoming stack-slot parameter of index [i]. *)
  val arg_slot : word:int -> int -> var

  (** Every alloca of the sub and the entry RSP's runtime position —
      (region id, byte index); rides the sub term. *)
  type sub_layout = Hike_stack_model.sub_layout = {
    regions : (int * (int64 * int64) * int64) list;
    anchor : (int * int64) option;
    window_param : bool;
  }

  (** Computed once by the producer; the emitter reads it off the term. *)
  val set_layout : sub_layout -> sub term -> sub term


  (** Per-def tags: the dynamic-allocation fact rides the def's value. *)
  val stamp_dyn_allocs : dynamic_alloc_tids:Tid.Set.t -> sub term -> sub term
  val stamp_window_values : window_values:Tid.Set.t -> sub term -> sub term
  val def_is_window_value : def term -> bool
  val def_is_dyn_alloc : def term -> bool

  (** The call-argument temps the promotion creates at call sites. *)
  val call_arg : word:int -> int -> var
  val is_call_arg : var -> bool
end

(** The project's data-section facts and the slim def-carried section
    tag. *)
module Image = Hike_image

module Sections = Hike_sections

(** The Stack-Arg PROMOTION: the layout's slots become the sub's
    promoted parameters and call sites bind the stored values. *)
module Promote = Hike_promote

(** The analysis closure: the run's facts as ONE value, built by
    [Kb.build] at the pass_vsa boundary, installed once, and threaded
    through every consumer as a parameter.  Also the term-carried KB
    value slots' home. *)
module Kb = Hike_kb

(** The canary-strip pass: proven canary compositions delete before
    the fission. *)
module Strip_canaries : sig
  (** [strip_sub ~facts ~names sub] removes every proven canary
      composition; an unrecognized composition is the identity. *)
  val strip_sub :
    facts:Hike_kb.facts -> names:string Tid.Map.t -> sub term -> sub term
end

(** LLVM emitter. *)
module Bil2llvm = Bil2llvm
