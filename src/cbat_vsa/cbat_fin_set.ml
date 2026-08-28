(* ************************************************************************* *)
(*  *)
(* Copyright (C) Draper Laboratory. Licensed under project LICENSE. *)
(*  *)
(* This file is provided under the license found in the LICENSE file in *)
(* the top-level directory of this project. *)
(*  *)
(* This work is funded in part by ONR/NAWC Contract N6833518C0107. Its *)
(* content does not necessarily reflect the position or policy of the US *)
(* Government and no official endorsement should be inferred. *)
(*  *)
(* ************************************************************************* *)

open !Core_kernel
open Bap.Std

(* Included to implement create more easily; This indicates that create may not be the right interface *)
module WordSet = Cbat_wordset_intf
module WSet = Set.Make_binable(Word)

type t =  WSet.t * int [@@deriving bin_io, sexp]
type idx = int



let of_list ~width l = WSet.of_list l, width
let singleton w =
  let bw = Word.bitwidth w in
  WSet.singleton w, bw

let bitwidth (_, bw) : int = bw

(* The element count wrapped at the set's bitwidth — a full domain (length 2^width) read cardn 0 = empty. *)
let cardinality (s, width) : word =
  Core.Set.length s
  |> Word.of_int ~width:(width + 1)

let signed (s, bw) =
  let signed_s = WSet.map s ~f:Word.signed in
  (signed_s, bw)

let min_elem = Fn.compose Core.Set.min_elt fst
let max_elem = Fn.compose Core.Set.max_elt fst

let max_elem_signed t = max_elem (signed t)
let min_elem_signed t = min_elem (signed t)

let elem w (s, bw) : bool =
  (* A word of a different bitwidth cannot be a member of this set; return false rather than asserting (same pattern as the Phase-1 lift2_pred fix above). *)
  if Word.bitwidth w <> bw then false
  else Core.Set.mem s w

let iter = Fn.compose Core.Set.elements fst

let lift ?(width=fun x->x) (f : WSet.t -> WSet.t) (s, bw : t) : t = (f s, width bw)

(* The default width function now widens both sets to the MAX width instead of asserting on a mismatch — the fixpoint's join/meet/add&c. *)
let lift2 ?(width=fun w1 w2 -> Stdlib.max w1 w2)
    (f : WSet.t -> WSet.t -> WSet.t)
    (s1, bw) (s2, bw') : t =
  f s1 s2, width bw bw'

let lift2_pred (f : WSet.t -> WSet.t -> bool)
    (s1, bw) (s2, bw') : bool =
  (* Ported from the prior-art cbat_value_set fork (totality fix): two value-sets of differing bitwidths cannot be compared; treat them as not provably related (false) rather than asserting, which would abort the whole analysis. *)
  if bw <> bw' then false
  else f s1 s2

let lift_unop (op : word -> word) : WSet.t -> WSet.t = WSet.map ~f:op

(* [lift_binop' elem_op s1 s2]: the cartesian fold of [elem_op] over the two sets — the pointwise-lift body shared by the unsigned and signed binops. *)
let lift_binop' (elem_op : word -> word -> word) s1 s2 : WSet.t =
  Core.Set.fold_right s1 ~init:WSet.empty ~f:begin fun w1 init ->
    Core.Set.fold_right s2 ~init ~f:begin fun w2 s ->
      Core.Set.add s (elem_op w1 w2)
    end
  end

let lift_binop (op : word -> word -> word)
    s1 s2 : WSet.t =
  lift_binop' op s1 s2

let lift_binop_signed (op : word -> word -> word)
    s1 s2 : WSet.t =
  lift_binop' (fun w1 w2 -> op (Word.signed w1) (Word.signed w2)) s1 s2

let equal = lift2_pred WSet.equal

let overlap (s1, bw) (s2, bw') : bool =
  (* Width-mismatched sets cannot share an element; return false instead of asserting (see elem). *)
  if bw <> bw' then false
  else Core.Set.exists s1 ~f:(fun w -> Core.Set.mem s2 w)

let union = lift2 Core.Set.union
let intersection = lift2 Core.Set.inter

(* [diff]: the set difference — exact (the right set's elements removed from the left). A width-mismatched pair shares no elements (the [elem] / [lift2_pred] convention): the difference is the left set unchanged, its width kept. *)
let diff (s1, bw) (s2, bw') : t =
  if bw <> bw' then (s1, bw)
  else Core.Set.diff s1 s2, bw

let add = lift2 (lift_binop Word.add)
let sub = lift2 (lift_binop Word.sub)
let mul = lift2 (lift_binop Word.mul)
(* TODO: how to handle division-by-zero? *)
let div = lift2 (lift_binop Word.div)
let sdiv = lift2 (lift_binop_signed Word.div)
let modulo = lift2 (lift_binop Word.modulo)
let smodulo = lift2 (lift_binop_signed Word.modulo)

let arshift = lift2 ~width:Fn.const (lift_binop Word.arshift)
let rshift  = lift2 ~width:Fn.const (lift_binop Word.rshift)
let lshift = lift2 ~width:Fn.const (lift_binop Word.lshift)

let logand : t -> t -> t = lift2 (lift_binop Word.logand)
let logor : t -> t -> t = lift2 (lift_binop Word.logor)
let logxor : t -> t -> t = lift2 (lift_binop Word.logxor)

let lnot = lift (lift_unop Word.lnot)
let neg = lift (lift_unop Word.neg)

let nearest_pred w (s, bw) : word option =
  (* A word of a different bitwidth has no predecessor in this set; return None instead of asserting (see elem). *)
  if Word.bitwidth w <> bw then None
  else Core.Set.fold s ~init:None ~f:(fun mmin w' ->
      let diff = Word.sub w w' in
      Option.value_map mmin ~default:(Some diff) ~f:(fun m ->
          if Word.(<=) m diff then Some m else Some diff))

let nearest_succ (i : word) (s : t) : word option =
  Option.map ~f:Word.lnot (nearest_pred (Word.lnot i) (lnot s))

(* Determines whether the set is spaced by a multiple of w when considered as an interval in the range [0..2^sz) *)
let splits_by (s, _ : t) (w : word) : bool =
  (* Core_kernel's List lacks [map2_shortest] (only the full [core] package has it) — the local pairwise fold stays. *)
  let rec map2_shortest ~f l1 l2 = match l1,l2 with
    | [], _
    | _, [] -> []
    | e1::l1', e2::l2' -> f e1 e2 :: (map2_shortest ~f l1' l2') in
  let elems = Core.Set.elements s
              |> List.sort ~compare:Word.compare in
  let open Monads.Std.Monad.Option.Syntax in
  Option.value ~default:true begin
    List.tl elems >>| fun tl ->
    map2_shortest tl elems ~f:Word.sub
    |> List.for_all ~f:(fun diff -> Word.is_zero (Word.modulo diff w))
  end

(* TODO: should we be burying errors like this? *)
let extract ?hi ?(lo=0) ((s, bw) : t) : t =
  let new_bw w =
    let hi = Option.value ~default:(w-1) hi in
    hi - lo + 1 in
  if new_bw bw <= 0 then (s, bw)
  else lift ~width:new_bw (lift_unop (Word.extract_exn ?hi ~lo)) (s, bw)

let cast ct (sz : int) ((s, bw) : t) : t =
  if sz <= 0 then (s, bw)
  else lift ~width:(Fn.const sz) (lift_unop (Bil.Apply.cast ct sz)) (s, bw)

let concat = lift2 ~width:(fun w1 w2 -> w1 + w2) (lift_binop Word.concat)

(* Lattice implementation *)
let precedes = lift2_pred (fun s1 s2 -> Core.Set.is_subset s1 ~of_:s2)
(* E2e-A, ora-7 — the [widen_join] stub below is interface-mandated (Lattice.S) and unreachable via the composite (Cbat_clp_set_composite is CLP-backed; it never routes widen through the FinSet arm). Do not delete. *)
let widen_join _ _ = failwith "widen not implemented; usually impractical"
let join = union
let meet = intersection
let bottom bw = WSet.empty, bw
(* TODO: implement top and error on high values; used for some small bitwidths *)
(* E2e-A, ora-7 — the [top] stub below is interface-mandated (Lattice.S) and unreachable via the composite (CLP-backed); the composite's top is [Clp.top]. Do not delete. *)
let top _ = failwith "top not implemented; usually impractical"
let get_idx = snd

let pp ppf (s, _) =
  Format.fprintf ppf "@[{@ ";
  Set.iter s ~f:(Format.fprintf ppf "%a@ " Word.pp);
  Format.fprintf ppf "}@]"

let compare (s1, bw1) (s2, bw2) =
  if bw1 < bw2 then -1
  else if bw1 > bw2 then 1
  else WSet.compare s1 s2

(* Actions of a FinSet on a WordSet from a potentially different module *)

let intersect_generic (type ws) (module WS : WordSet.S with type t = ws)
    (s, bw : t) (s' : ws) : t =
  (* A width-mismatched generic set cannot share any element; the sound conservative result is the input unchanged (an over-approximation of the empty intersection, so e.g. *)
  if WS.bitwidth s' <> bw then (s, bw)
  else
    let keep_set = Core.Set.filter s ~f:(fun w -> WS.elem w s') in
    keep_set, bw

let overlap_generic (type ws) (module WS : WordSet.S with type t = ws)
    (s, bw : t) (s' : ws) : bool =
  (* a width mismatch means no shared element, but the [intersect_generic] convention answers "may overlap" (the input unchanged, non-empty); the same-width case short-circuits on the first shared element. *)
  if WS.bitwidth s' <> bw then not (Core.Set.is_empty s)
  else Core.Set.exists s ~f:(fun w -> WS.elem w s')
