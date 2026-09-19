(* Public interface. Consumers use [Hike.Abi], [Hike.Vsa], etc. *)

open Bap.Std
open Bap_core_theory

(** Register and convention facts. [Abi.sp] is the stack pointer. *)
module Abi = Hike_abi

(** The production diagnostic channel — [hike: ...] lines on stderr.
    The one output route for the batch driver. *)
module Diag = Hike_diag

(** Per-sub stack offset ranges. *)
module Vsa : sig
  (** An image-backed section: the span's inclusive bounds plus the
      section's static content. *)
  type section_image = Cbat_vsa.section_image = {
    img_lo : int64;
    img_hi : int64;
    img_bytes : int array;
  }

  (** The engine run with its CFG-completion loop: solve -> complete
      the CFG in the BIL -> re-solve while the sub changes.  The
      products are the per-block (pre, post) environments — the ONLY
      cross-pass fact — and the FINAL REWRITTEN SUB (real [Ret] jmps,
      guarded-goto dispatch series).  [None] = non-convergence: no
      environments, no rewrite — every reader takes the
      [Cbat_vsa.AI.top] identity and the sub stays as it came.  [prog]
      is the whole program: the call abstraction's written-register
      summaries are computed from it, inside.  [images] — the sections
      whose runtime content is the static image — arm the completion's
      target denotation only. *)
  val fixpoint :
    Theory.Target.t ->
    var ->
    prog:program term ->
    images:section_image list ->
    block_addrs:(int64 * tid) list ->
    sub term ->
    ((Cbat_vsa.AI.t * Cbat_vsa.AI.t) Tid.Map.t * sub term) option

  (** The one denotation access: [exp] denotes in the before-env of
      [def] — the block's defs replay the transfer from the block's
      precondition tag up to [def], the target def's own transfer not
      run — or, with no [def], in the block's postcondition (the full
      replay; the state a jmp reads).  A [def] outside its block
      denotes in [Cbat_vsa.AI.top]. *)
  val denote_exp_at :
    blk:blk term ->
    ?def:def term ->
    exp ->
    (Cbat_vsa.WordSet.t, Type.error) Result.t
end

(** The CFG completion: a BIR-to-BIR rewrite driven by the VSA's own
    denotations.  A consumer of the VSA — the solver passes the seam
    and the round's solution in; no pass after the VSA reads it. *)
module Cfg_complete : sig
  (** The seam the solver passes in: [exp] denotes in [blk] (in the
      target def's before-env when [~def] is given). *)
  type denote =
    blk:blk term -> ?def:def term -> exp ->
    (Cbat_vsa.WordSet.t, Type.error) Result.t

  (** The retaddr proof, re-derived through the denotation: the defs
      whose load address denotates — at the def's own before-env — to
      the stack-symbolic singleton at the entry-RSP cell. *)
  val retaddr_defs :
    abi:Abi.t -> sol:Cbat_vsa.vsa_sol -> sub term -> Tid.Set.t

  (** One completion round on the round's own solution: the return
      epilogues (the target denotating to the entry-RSP retaddr cell)
      land in the BIR's canonical return shape (a var-free return-less
      call — the fork's readable form of [Ret]), the resolvable
      dispatches (every case word naming an in-sub block) become
      guarded-goto series in the existing blocks.  The product is the
      REWRITTEN SUB and whether anything changed; the loop ends at the
      first unchanged round (the rewritten BIR is the memory). *)
  val complete :
    denote:denote ->
    abi:Abi.t ->
    sol:Cbat_vsa.vsa_sol ->
    images:Cbat_vsa.section_image list ->
    blocks:(int64 * tid) list ->
    sub term -> sub term * bool
end

(** Indirect-target resolution: the class of every indirect jmp and
    call, read from the target's denotation. *)
module Resolve : sig
  (** The target-resolution predicate: a singleton whose word
      names a lifted sub resolves ([Some tid] — the Resolved Call
      Site); a bounded multi-target set, a foreign singleton, and TOP
      take the pointer call ([None]). *)
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

(** The jump compiler (construction): jcc flag idioms become value
    comparisons. *)
module Jump : sig
  (** Rewrites jcc flag idioms into the simplest equivalent value
      comparisons; the flags are the vars [target] registers for the
      core-theory flag roles; identity on the residual. *)
  val compile_sub : Theory.Target.t -> sub term -> sub term
end

(** The node fission: every def keeps exactly one memory node inline —
    the later nodes of a multi-node rhs become fresh virtual load defs
    before it — so the per-def tag is the complete proof of the def's
    only memory node. *)
module Split_mem : sig
  val split_sub : sub term -> sub term
  val normalize : program term -> program term
end

(** Stack split decision and helpers.  Also the home of the Vsa record
    and the shared section vocabulary (the sections, the slim tag):
    the producer/emitter contract point. *)
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
  (** The model segment's base (2^62): the ABSOLUTE position of the
      entry RSP on the segment line — the tag positions are
      absolute, so a frame offset o sits at [segment_base + o]). *)
  val segment_base : int64

  (** The denotation's single stack position (absolute, on the
      segment line), when it denotates to exactly one — the
      cell-identity predicate. *)
  val singleton_stack_position : Cbat_vsa.WordSet.t -> int64 option

  (** THE return-address fact: an address that denotes to the
      stack-symbolic singleton at the entry-RSP cell, and its two
      projections — the stamped Section Tag form and the pre-solve
      exact-pop shape form. *)
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
      crosses its start boundary (see [Hike_stack_model] for the
      rule); the one home of the string-text predicate. *)
  val string_text_word : arr:int array -> off:int -> bool

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

  (** The promoted incoming stack-slot parameter of index [i]. *)
  val arg_slot : word:int -> int -> var

  (** The fold's product (D3): every alloca of the sub, and the entry
      RSP's runtime position — (region id, byte index).  Rides the sub
      term. *)
  type sub_layout = Hike_stack_model.sub_layout = {
    regions : (int * (int64 * int64) * int64) list;
    anchor : (int * int64) option;
    window_param : bool;
  }

  (** The layout rides the SUB TERM: the producer computes it once;
      the emitter reads it off the term. *)
  val set_layout : sub_layout -> sub term -> sub term


  (** Per-def tags: the dynamic-allocation fact rides the def's value. *)
  val stamp_dyn_allocs : dynamic_alloc_tids:Tid.Set.t -> sub term -> sub term
  val stamp_window_values : window_values:Tid.Set.t -> sub term -> sub term
  val def_is_window_value : def term -> bool
  val def_is_dyn_alloc : def term -> bool

  (** The call-argument temps the promotion rewrite creates at the
      call sites. *)
  val call_arg : word:int -> int -> var
  val is_call_arg : var -> bool
end

(** The section home: the project's data-section facts, the one
    denotation-to-range mechanism, the immutable visitor, the two
    finalized interval trees, and the slim def-carried section tag. *)
module Sections = Hike_sections

(** Per-sub VSA result store. *)
module Kb = Hike_kb

(** The canary-strip pass: the proven canary composition (the TLS read,
    the same-cell store/reload, the not-equal edge to a symtab-resolved
    [__stack_chk_fail]) deletes before the fission — the emission loses
    the TLS reads, the store, the second exit, and the foreign
    fail-call shape; the FS/anchor render stays in the emitter. *)
module Strip_canaries : sig
  (** [strip_sub ~abi ~names sub] removes every proven canary
      composition; an unrecognized composition is the identity. *)
  val strip_sub :
    abi:Abi.t -> names:string Tid.Map.t -> sub term -> sub term
end

(** LLVM emitter. *)
module Bil2llvm = Bil2llvm

(** Every copy-relocated slot address (absolute) — the emitter's
    through lane serves every access at one. *)
val copy_reloc_slot_addrs : Project.t -> int64 list

(** The attribution's data spans: each reserved section's section,
    native bounds, and copy-relocated slot addresses, in the fixed
    table order; [word] is the target's word size in bytes. *)
val attrib_spans : word:int -> Project.t -> Sections.data_span list

(** The emitter's section spec: the images from the project, the
    Global components from the finalized data tree, and the spans
    served whole (each (id, lo, hi) — the section's own image global
    is the id's storage), in the fixed table order. *)
val section_spec_of :
  word:int ->
  comps:Hike_stack_model.sec_comp list ->
  whole:(int * int64 * int64) list ->
  Project.t -> Bil2llvm.section_spec
