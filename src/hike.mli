(* Public interface. Consumers use [Hike.Abi], [Hike.Vsa], etc. *)

open Bap.Std
open Bap_core_theory

(** Register and convention facts. [Abi.sp] is the stack pointer. *)
module Abi = Hike_abi

(** The production diagnostic channel: [hike: ...] lines on stderr. *)
module Diag = Hike_diag

module Vsa = Hike_vsa

(** The CFG completion, fused into the solver's loop: resolution is an
    in-loop step of the fixpoint, materialization runs once at drain. *)
module Cfg_complete = Hike_cfg_complete

(** Indirect-target resolution, read from the target's denotation. *)
module Resolve = Hike_resolve

(** Dead-code elimination. *)
module Dce = Hike_dce

(** The jump compiler: jcc flag idioms become value comparisons. *)
module Jump = Hike_jump

(** Node fission: every def keeps exactly one memory node inline —
    the per-def tag is then the complete proof of that node. *)
module Split_mem = Hike_split_mem

(** The block/jmp-series split: one jmp per block, pieces consecutive
    in term order — the BIR CFG equals the CFG the emitter renders. *)
module Split_blocks = Hike_split_blocks

(** SSA materialization: cross-block register values flow through BIR
    phi terms; call rets mint versions stamped per block. *)
module Ssa = Hike_ssa

(** The width-coercion pass: every exp the later passes read is made
    width-honest once, so the VSA and the emitter read uniform widths. *)
module Coerce = Hike_coerce

(** The FP temp widths: every [intrinsic:xN]/[intrinsic:yN] occurrence
    carries its own width, and a mapped FP call's target names its
    operand width in the model's sized spelling. *)
module Fp = Hike_fp

(** Stack split decision and helpers, and the shared section
    vocabulary: the producer/emitter contract point. *)
module Stack_model = Hike_stack_model

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

(** The section ownership and promotion protocol used by the production pass. *)
module Attribution = Hike_attribution

(** The analysis closure: the run's facts as ONE value, built by
    [Kb.build] at the pass_vsa boundary, installed once, and threaded
    through every consumer as a parameter.  Also the term-carried KB
    value slots' home. *)
module Kb = Hike_kb

(** The type inference: every value typed from the denotation and the
    use graph; the lane kinds stamped; runs after [Ssa]. *)
module Types = Hike_types

(** LLVM emitter. *)
module Bil2llvm = Bil2llvm
