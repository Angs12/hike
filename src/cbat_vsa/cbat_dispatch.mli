(* Guard construction for an in-VSA dispatch.  The caller (the Hike
   worklist) enumerates the target words and recovers the optional base;
   this module binds the target expression once and builds the ordered
   arms.  It never mutates the sub. *)

open Bap.Std

(* A table base: the summand expression (already bound at its site when
   needed) and its link-time values. *)
type base = {
  summand : exp;
  values : int64 list;
}

(* One materialized transfer: the ordered, exact targets and the base
   the caller could recover.  [sub] is the caller's sub view; it is read
   only, never mutated. *)
type materialized = {
  base : base option;
  targets : (Cbat_word.t * Tid.t) list;
  sub : Sub.t;
  module_addr : int64 -> exp;
}

type arm_kind = Jump | Call

(* One arm: [guard] is the original condition AND the case test. *)
type arm = {
  guard : exp;
  target : Tid.t;
  kind : arm_kind;
}

(* Bind the transfer's target expression once.  A [Bil.Var] is a stable
   SSA value (a def or a phi result), so it is reused as-is; every other
   expression gets one fresh binding [t := e] whose def the caller
   prepends to the source block.  Returns the expression every guard must
   read and, when it introduced one, the variable and its def. *)
val bind_target : exp -> exp * (var * def term) option

(* The ordered arms over an already-bound [target], one per target word
   in input order.  [cond] is the transfer's original condition; [None]
   (or the constant true) makes every guard the case test alone.  With a
   usable [base] the case test is the table-offset form
   [(target - summand) == word - value], guarded by [summand == value]
   when there are several values; without one it is [target == word]. *)
val arms :
  kind:arm_kind ->
  cond:exp option ->
  target:exp ->
  base:base option ->
  module_addr:(int64 -> exp) ->
  targets:(Cbat_word.t * Tid.t) list ->
  arm list

(* [bind_target] followed by [arms] over the materialized transfer.
   Returns the fresh binding (for the caller to prepend) and the ordered
   arms.  The materialized sub is left untouched. *)
val materialize :
  materialized ->
  kind:arm_kind ->
  cond:exp option ->
  target:exp ->
  (var * def term) option * arm list

(* One arm's transfer.  [kind] only selects the transfer form; the arm
   layout is shared. *)
val arm_jmp :
  kind:arm_kind ->
  return:label option ->
  is_intra:(Tid.t -> bool) ->
  arm ->
  jmp term

(* The transfer's indirect target expression, if its target is indirect. *)
val indirect_target : jmp term -> exp option

(* Rewrite one source block for a complete materialization: bind the target
   once, replace the indirect transfer with the ordered arm chain, append
   the no-match trap block of a call set, and add the explicit false edge
   of a conditional transfer.  [is_intra] classifies a jump target as a
   block of the current sub (a direct goto) or a function entry (a tail
   call).  [false_target] is the source's term-order continuation.  The
   input block is read only; the result is the rewritten block and the
   optional fresh trap block. *)
val rewrite_source :
  materialized ->
  kind:arm_kind ->
  blk:blk term ->
  jmp:jmp term ->
  is_intra:(Tid.t -> bool) ->
  false_target:Tid.t option ->
  blk term * blk term option
