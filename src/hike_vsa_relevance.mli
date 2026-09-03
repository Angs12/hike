(* Tags stack accesses and contributing defs. *)

open Bap.Std
open Bap_core_theory

(** Tags a stack access def. *)
val stack_access : unit tag

(** Tags defs feeding a stack access address. *)
val relevant : unit tag

(** Tags runtime-sized SP decrements. *)
val dynamic_alloc : unit tag

(** Checks the [stack_access] tag. *)
val has_stack_access : def term -> bool

(** Tests for the stack pointer. *)
val is_sp : Theory.Target.t -> var -> bool

(** Tests for a stack access expression. *)
val is_stack_load_store : Var.Set.t -> exp -> bool

(** Tests for any memory access. *)
val is_memory_side_effect : exp -> bool

(** Tags [sub] with all three tags. *)
val analyze : var -> sub term -> sub term
