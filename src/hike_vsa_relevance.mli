(* Hike_vsa_relevance — relevance analysis and stack access tagging.

   Contracts:
   - [stack_access]: tags a def whose RHS is a memory Load or Store whose address
     is derived from the Stack Pointer (SP).
   - [relevant]: the exact set of defs and phis that transitively contribute
     a value to the address of a Stack Access (re-exported from Cbat_vsa_utils).
   - [dynamic_alloc]: tags a def that decrements the Stack Pointer by a non-literal
     runtime size (VLA / alloca).
*)

open Bap.Std
open Bap_core_theory

(** [stack_access] tags a def whose address is derived from the Stack Pointer. *)
val stack_access : unit tag

(** [relevant] tags defs and phis that contribute to a stack access address. *)
val relevant : unit tag

(** [dynamic_alloc] tags runtime-sized SP decrements (VLA / alloca). *)
val dynamic_alloc : unit tag

(** [has_stack_access def] checks whether [def] is tagged with [stack_access]. *)
val has_stack_access : def term -> bool

(** [is_sp target var] tests if [var] is the stack pointer for [target]. *)
val is_sp : Theory.Target.t -> var -> bool

(** [is_stack_load_store sp_derived exp] checks if [exp] is a Stack
    Access: a memory Load or Store whose address contains at least
    one var in [sp_derived] (base-normalized). The shape-only check
    (any memory Load/Store) is done by [is_memory_side_effect]. *)
val is_stack_load_store : Var.Set.t -> exp -> bool

(** [is_memory_side_effect exp] checks if [exp] is a memory Load or
    Store (any memory access, regardless of address derivation).
    Returns true if the expression's free vars include a memory-typed
    var (the [mem] variable that all Loads/Stores read or write). *)
val is_memory_side_effect : exp -> bool

(** [analyze sp sub] performs forward reachability from [sp] followed by
    backward slice to tag defs in [sub] with [stack_access], [relevant],
    and [dynamic_alloc]. *)
val analyze : var -> sub term -> sub term
