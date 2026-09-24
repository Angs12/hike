(* The classification vocabulary: the def-carried stack classification
   and its address reader.  Lives beside the composite domain whose
   [kind] it re-exports. *)

open Bap.Std

module WordSet = Cbat_clp_set_composite

(* Classification vocabulary: the (lo,hi) pair is the denotation's
   position interval on the model's ABSOLUTE segment line (see
   [classify]); "below/above the entry RSP" reads as below/above the
   segment base.
   - [Range]/[Infinite]: entirely below the entry RSP — this sub's
     own frame.
   - [Caller]: entirely at/above — ABI-visible caller-window traffic.
   - [Mixed]: two-sided or wrapped — the runtime address is GENUINELY
     either-based; the emitter's rule is the two-base select. *)
(* Re-exported from cbat_clp_set_composite for the seam's consumers. *)
type kind = WordSet.kind =
  | Range of int64 * int64
  | Infinite of int64 * int64
  | Caller of int64 * int64
  | Mixed of int64 * int64
  | Dead

let unbounded_span = Cbat_clp_set_composite.unbounded_span
let is_unbounded_span = Cbat_clp_set_composite.is_unbounded_span
let caller_split = Cbat_clp_set_composite.caller_split
let position_of_offset = Cbat_clp_set_composite.position_of_offset
let classify = Cbat_clp_set_composite.classify
let equal_kind = Cbat_clp_set_composite.equal_kind

(* Address of a stack-access rhs using Exp.visitor. *)
let stack_address_of_rhs (rhs : Bil.exp) : Bil.exp option =
  let vis =
    object
      inherit [ Bil.exp option ] Exp.visitor
      method! visit_load ~mem:_ ~addr _ _ acc =
        Base.Option.first_some acc (Some addr)
      method! visit_store ~mem:_ ~addr ~exp:_ _ _ acc =
        Base.Option.first_some acc (Some addr)
    end
  in
  vis#visit_exp rhs None
