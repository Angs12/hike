(* Public interface. Consumers use [Hike.Abi], [Hike.Vsa], etc. *)

open Bap.Std
open Bap_core_theory

(** Register and convention facts. [Abi.sp] is the stack pointer. *)
module Abi = Hike_abi

(** The production diagnostic channel: [hike: ...] lines on stderr. *)
module Diag = Hike_diag

module Vsa : sig
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
      block-address map.  [images] arm the resolver's denotations
      only; [written] is the program's kill-summary pass, computed
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
    abi:Abi.t -> program term -> Core.Int.Set.t option Tid.Map.t
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
    lift_at:(Addr.t -> block_addrs:Tid.t Addr.Map.t -> blk term list option) ->
    block_addrs:Tid.t Addr.Map.t ->
    sub_addrs:Tid.t Addr.Map.t ->
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

(** Node fission: every def keeps exactly one memory node inline —
    the per-def tag is then the complete proof of that node. *)
module Split_mem : sig
  val split_sub : sub term -> sub term
  val normalize : program term -> program term
end

(** The block/jmp-series split: one jmp per block, pieces consecutive
    in term order — the BIR CFG equals the CFG the emitter renders. *)
module Split_blocks : sig
  val split_sub : sub term -> sub term
  val normalize : program term -> program term

  (** The BIR's free registers over its explicit edges, memory vars
      dropped. *)
  val free_regs : sub term -> var list
end

(** SSA materialization: cross-block register values flow through BIR
    phi terms; call rets mint versions stamped per block. *)
module Ssa : sig
  val ssa_program :
    target:Theory.Target.t -> program term -> program term

  (** The input lanes of an SSA sub: its index-0 reads. *)
  val free_regs_ssa : sub term -> var list
end

(** The width-coercion pass: every exp the later passes read is made
    width-honest once, so the VSA and the emitter read uniform widths. *)
module Coerce : sig
  val coerce_exp : exp -> exp
  val coerce_block : blk term -> blk term
  val coerce_program : program term -> program term
end

(** The FP temp widths: every [intrinsic:xN]/[intrinsic:yN] occurrence
    carries its own width, and a mapped FP call's target names its
    operand width in the model's sized spelling. *)
module Fp : sig
  val run_program : program term -> program term
end

(** Stack split decision and helpers, and the shared section
    vocabulary: the producer/emitter contract point. *)
module Stack_model : sig
  (** The SSA block stamp: base var -> live version at block end. *)
  module Versions : sig
    type t =
      { args : (var * var) list
      ; rets : (var * var) list
      ; entry : (var * var) list
      }
  end

  val versions_tag : Versions.t Value.Tag.t
  val ssa_tag : unit Value.Tag.t
  val is_ssa : sub term -> bool

  (** The sections in declaration order. *)
  type sec = Hike_stack_model.sec =
    | Stack
    | Args
    | Vla
    | Text
    | Rodata
    | Data
    | Got
    | Gotplt
    | Datarelro
    | Bss
  [@@deriving equal, compare, sexp]

  (** The section's ELF name — the one spelling of the name grammar. *)
  val sec_name : sec -> string

  (** The slim def-carried classification. *)
  module Tag = Hike_stack_model.Tag

  type sec_tag = Hike_stack_model.sec_tag

  (** The model segment's base (2^62 + 8: the ABI entry residue): the
      ABSOLUTE position of the entry RSP on the segment line; tag
      positions are absolute, so a frame offset [o] sits at
      [segment_base + o]. *)
  val segment_base : int64

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
      crosses its start boundary; one backward prepass answers every
      offset. *)
  val string_text_table : Bytes.t -> int -> bool

  (** The stack-address / store-data readers over the one mem-node scan. *)
  val addr_of_rhs : exp -> (exp * Size.t) option
  val store_data_of_rhs : exp -> exp option

  (** Mints and recognizes fission vars. *)
  val region_mem : int -> var
  val is_region_mem : var -> bool

  (** The storage base vars: one Mem-typed value per storage, minted by
     the attribution's rewrite; a rewritten address def's value is
     [base + displacement]. *)
  val region_ptr : addr_bits:int -> int -> var
  val is_region_ptr : var -> bool
  val region_ptr_id_of : var -> int option

  (** The VLA storage base vars (one per allocation, keyed by the
      decrement def's tid) and the storage-base predicate. *)
  val vla_ptr : addr_bits:int -> Tid.t -> var
  val is_vla_ptr : var -> bool
  val is_storage_base : var -> bool

  (** The section-component storage base vars. *)
  val sec_comp_ptr : addr_bits:int -> int -> var
  val is_sec_comp_ptr : var -> bool

  (** The incoming-window memory var (the caller's world) and its test. *)
  val window_mem : var
  val is_window_mem : var -> bool

  (** The caller-window base parameter and its test. *)
  val hike_window_var : word:int -> var
  val is_window_var : var -> bool

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
  val fixed_signature : sub term -> bool

  (** The promoted incoming stack-slot parameter of index [i]. *)
  val arg_slot : word:int -> int -> var

  (** Every alloca of the sub; rides the sub term. *)
  type sub_layout = Hike_stack_model.sub_layout = {
    regions : (int * (int64 * int64) * int64) list;
    window_param : bool;
  }

  (** Computed once by the producer; the emitter reads it off the term. *)
  val set_layout : sub_layout -> sub term -> sub term


  (** The call-argument temps the promotion creates at call sites. *)
  val call_arg : word:int -> int -> var
  val is_call_arg : var -> bool
end

(** The def-carried KB value slots: the producer stamps each def's
    value, the emitter reads the tags off the term. *)
module Def_slots = Hike_def_slots

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
(** The canary-strip pass (after the solve, before the attribution):
    proven canary compositions delete before the sections pass. *)
module Strip_canaries : sig
  (** [strip_sub ~facts ~names sub] removes every proven canary
      composition; an unrecognized composition is the identity. *)
  val strip_sub :
    facts:Hike_kb.facts -> names:string Tid.Map.t -> sub term -> sub term
end

(** LLVM emitter. *)
module Bil2llvm = Bil2llvm
