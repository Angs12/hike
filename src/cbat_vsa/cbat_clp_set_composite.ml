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

module Word_ops = Cbat_word_ops
module Utils = Cbat_vsa_utils
module Clp = Cbat_clp
module FinSet = Cbat_fin_set

type clp = Clp.t
type fset = FinSet.t

(* INVARIANT: Clps have cardinality > Utils.fin_set_size INVARIANT: FinSets have cardinality <= Utils.fin_set_size *)
type t = Clp of Clp.t | FinSet of FinSet.t [@@deriving bin_io, sexp, compare]
type idx = int

let of_list ~width l : t =
  if List.length l > Utils.fin_set_size
  then Clp (Clp.of_list ~width l)
  else FinSet (FinSet.of_list ~width l)

let singleton w = FinSet (FinSet.singleton w)

let lift_consume (f_clp : clp -> 'a) (f_fs : fset -> 'a) : t -> 'a = function
  | Clp p -> f_clp p
  | FinSet s -> f_fs s

let clp_of_finset fs : clp =
  let width = FinSet.bitwidth fs in
  FinSet.iter fs
  |> Clp.of_list ~width

let finset_of_clp p : fset =
  let width = Clp.bitwidth p in
  Clp.iter p
  |> FinSet.of_list ~width

let as_clp = function
  | Clp p -> p
  | FinSet s -> clp_of_finset s

(* TODO: rename to canonize? *)
let bound_set_size = function
  | Clp p -> if Word_ops.gt_int (Clp.cardinality p) Utils.fin_set_size
    then Clp p
    else FinSet (finset_of_clp p)
  | FinSet s -> if Word_ops.gt_int (FinSet.cardinality s) Utils.fin_set_size
    then Clp (clp_of_finset s)
    else FinSet s

let lift_binop (f_clp : clp -> clp -> clp) (f_fs : fset -> fset -> fset)
    t1 t2 : t = bound_set_size @@ match t1, t2 with
  | Clp p1, Clp p2 -> Clp (f_clp p1 p2)
  | FinSet s1, FinSet s2 -> FinSet (f_fs s1 s2)
  | Clp p, FinSet s -> Clp (f_clp p (clp_of_finset s))
  | FinSet s, Clp p -> Clp (f_clp (clp_of_finset s) p)

let lift_unop (f_clp : clp -> clp) (f_fs : fset -> fset) : t -> t = function
  | Clp p -> bound_set_size @@ Clp (f_clp p)
  | FinSet s -> bound_set_size @@ FinSet (f_fs s)

let of_clp (p : clp) : t = bound_set_size (Clp p)

let bitwidth = lift_consume Clp.bitwidth FinSet.bitwidth

let cardinality = lift_consume Clp.cardinality FinSet.cardinality

let min_elem = lift_consume Clp.min_elem FinSet.min_elem
let max_elem = lift_consume Clp.max_elem FinSet.max_elem
let min_elem_signed = lift_consume Clp.min_elem_signed FinSet.min_elem_signed
let max_elem_signed = lift_consume Clp.max_elem_signed FinSet.max_elem_signed
let nearest_pred w = lift_consume (Clp.nearest_pred w) (FinSet.nearest_pred w)
let nearest_succ w = lift_consume (Clp.nearest_succ w) (FinSet.nearest_succ w)
let splits_by = lift_consume Clp.splits_by FinSet.splits_by

let elem w = lift_consume (Clp.elem w) (FinSet.elem w)
let iter = lift_consume Clp.iter FinSet.iter

let equal t1 t2 : bool = match t1, t2 with
  | Clp p1, Clp p2 -> Clp.equal p1 p2
  | FinSet s1, FinSet s2 -> FinSet.equal s1 s2
  | Clp _, FinSet _
  | FinSet _, Clp _ -> false

let overlap t1 t2 : bool = match t1, t2 with
  | Clp p1, Clp p2 -> Clp.overlap p1 p2
  | FinSet s1, FinSet s2 -> FinSet.overlap s1 s2
  | Clp p, FinSet s
  | FinSet s, Clp p -> FinSet.overlap_generic (module Clp) s p

let union = lift_binop Clp.union FinSet.union
(* The definition below is more precise than 'lift_binop Clp.intersection FinSet.intersection' *)
let intersection (t1 : t) (t2 : t) : t =
  (* A width-mismatched meet is an index error — return the wider (larger-bitwidth, hence less-precise) operand instead of asserting: a sound over-approximation of the (empty) intersection, never bottom on a live path (see cbat_fin_set.elem). *)
  if bitwidth t1 <> bitwidth t2 then
    (if bitwidth t1 > bitwidth t2 then t1 else t2)
  else match t1, t2 with
  | Clp p1, Clp p2 -> Clp (Clp.intersection p1 p2)
  | FinSet s1, FinSet s2 -> FinSet (FinSet.intersection s1 s2)
  | Clp p, FinSet s
  | FinSet s, Clp p -> FinSet (FinSet.intersect_generic (module Clp) s p)

(* [clp_diff_finset p s]: The CLP minus the finite set's elements — the contiguous-arc removal: the elements of [s] that lie in [p], when they form a contiguous arc of [p]'s circular progression (the circular consecutive pairs — EXACTLY ONE pair. *)
let clp_diff_finset (p : clp) (s : fset) : clp =
  if Clp.bitwidth p <> FinSet.bitwidth s then p
  else if Clp.is_bottom p then p
  else
    let width = Clp.bitwidth p in
    let es =
      List.sort ~compare:Word.compare
        (List.filter ~f:(fun w -> Clp.elem w p) (FinSet.iter s)) in
    match es with
    | [] -> p
    | _ ->
      let n = List.length es in
      let cnt = Word.of_int ~width:(width + 1) n in
      let c1 = Clp.cardinality p in
      if Word.(>=) cnt c1 then Clp.bottom width
      else begin
        (* The STRICT successor of [e] in [p]'s circular order — the CLP's [nearest_succ] returns [e] itself when [e] ∈ [p] (the closest-≥ semantics), so the adjacency steps one past: the lnot-side predecessor of (lnot e − 1). *)
        let strict_succ (e : word) : word option =
          match Clp.nearest_pred (Word.pred (Word.lnot e)) (Clp.lnot p) with
          | Some w -> Some (Word.lnot w)
          | None -> None in
        (* the circular consecutive pairs: the linear pairs plus the wrap pair (last, first); the singleton's pair is (x, x) *)
        let pairs =
          match es with
          | [] -> []
          | [ single ] -> [ (single, single) ]
          | first :: rest ->
            let rec go acc prev = function
              | [] -> List.rev ((prev, first) :: acc)
              | e :: tl -> go ((prev, e) :: acc) e tl in
            go [] first rest in
        let adj (e1, e2) : bool =
          match strict_succ e1 with
          | Some nxt -> Word.(=) nxt e2
          | None -> false in
        let non_adj, adj_pairs =
          List.partition_tf ~f:(fun pr -> not (adj pr)) pairs in
        match non_adj, adj_pairs with
        | [ (arc_end, arc_start) ], (e1', e2') :: _ ->
          (* one gap pair: the arc from [arc_start] around to [arc_end]; the step = the first adjacent pair's difference *)
          let step = Word.sub e2' e1' in
          let cardn = Word.sub c1 cnt in
          if Clp.is_infinite p then
            Clp.create (Word.add arc_end step) ~step ~cardn
          else if Word.(>) arc_start arc_end then
            (* the wrapping arc (crosses the seam): the remainder [arc_end+step, arc_start−step] — one interval *)
            Clp.create (Word.add arc_end step) ~step ~cardn
          else
            (match Clp.min_elem p, Clp.max_elem p with
             | Some p_min, Some p_max ->
               if Word.(=) arc_start p_min then
                 Clp.create (Word.add arc_end step) ~step ~cardn
               else if Word.(=) arc_end p_max then
                 Clp.create p_min ~step ~cardn
               else p
             | _ -> p)
        | [ (arc_end, arc_start) ], [] ->
          (* the singleton run (n = 1): the step = the strict successor distance — the successor exists (c1 > n ≥ 1); the removal is one CLP when the element touches the arc's start/end or [p] is the full circle *)
          (match strict_succ arc_end with
           | Some nxt ->
             let step = Word.sub nxt arc_end in
             let cardn = Word.sub c1 cnt in
             if Clp.is_infinite p then
               Clp.create (Word.add arc_end step) ~step ~cardn
             else
               (match Clp.min_elem p, Clp.max_elem p with
                | Some p_min, Some p_max ->
                  if Word.(=) arc_start p_min then
                    Clp.create (Word.add arc_end step) ~step ~cardn
                  else if Word.(=) arc_end p_max then
                    Clp.create p_min ~step ~cardn
                  else p
                | _ -> p)
           | None -> p)
        | _ ->
          (* 0 gaps (the full circle — impossible here: n < c1) or 2+ gaps (not one arc): the identity — the sound over-approximation *)
          p
      end

(* [diff]: The set difference — the FinSet cases exact; the Clp\Clp case via [Clp.diff] (the contiguous-run removal, else the identity); the mixed cases are NOT the [lift_binop] shape: the Clp\FinSet case removes only the FINITE. *)
let diff (t1 : t) (t2 : t) : t = match t1, t2 with
  | Clp p1, Clp p2 -> bound_set_size (Clp (Clp.diff p1 p2))
  | FinSet s1, FinSet s2 -> FinSet (FinSet.diff s1 s2)
  | Clp p, FinSet s -> bound_set_size (Clp (clp_diff_finset p s))
  | FinSet s, Clp p ->
    if FinSet.bitwidth s <> Clp.bitwidth p then t1
    else
      let width = FinSet.bitwidth s in
      FinSet (FinSet.of_list ~width
        (List.filter ~f:(fun w -> not (Clp.elem w p)) (FinSet.iter s)))

let add = lift_binop Clp.add FinSet.add
let sub = lift_binop Clp.sub FinSet.sub
let mul = lift_binop Clp.mul FinSet.mul
let div = lift_binop Clp.div FinSet.div
let sdiv = lift_binop Clp.sdiv FinSet.sdiv
let modulo = lift_binop Clp.modulo FinSet.modulo
let smodulo = lift_binop Clp.smodulo FinSet.smodulo
let arshift = lift_binop Clp.arshift FinSet.arshift
let rshift = lift_binop Clp.rshift FinSet.rshift
let lshift = lift_binop Clp.lshift FinSet.lshift
let logand : t -> t -> t = lift_binop Clp.logand FinSet.logand
let logor = lift_binop Clp.logor FinSet.logor
let logxor = lift_binop Clp.logxor FinSet.logxor

let lnot = lift_unop Clp.lnot FinSet.lnot
let neg = lift_unop Clp.neg FinSet.neg

let concat = lift_binop Clp.concat FinSet.concat

let is_top = lift_consume Clp.is_top (fun _ -> false)
let is_bottom = lift_consume (fun _ -> false) (Fn.compose Word.is_zero FinSet.cardinality)
let is_infinite = lift_consume Clp.is_infinite (fun _ -> false)

(* Lattice implementation *)
let precedes t1 t2 : bool = match t1, t2 with
  | Clp p1, Clp p2 -> Clp.precedes p1 p2
  | FinSet s1, FinSet s2 -> FinSet.precedes s1 s2
  | Clp _, FinSet _ -> false
  | FinSet s, Clp p -> Clp.precedes (clp_of_finset s) p

let widen_join t1 t2 : t = bound_set_size @@
  Clp (Clp.widen_join (as_clp t1) (as_clp t2))

(* Thresholded widening (docs/widening-thresholds-plan.md) — the composite-level mirror of [Clp.widen_join_threshold]; the bounded result collapses back to a FinSet via [bound_set_size] when it has <= [Utils.fin_set_size] elements (exact-ish), preserving the composite invariant. *)
let widen_join_threshold (ladder : word list) t1 t2 : t =
  bound_set_size @@
  Clp (Clp.widen_join_threshold ladder (as_clp t1) (as_clp t2))

let join = union
let meet = intersection
let bottom i = FinSet (FinSet.bottom i)
let top i = bound_set_size @@ Clp (Clp.top i)

(* D7, ora-6 — degenerate cast/extract guard. *)
let extract ?hi ?lo t =
  let lo_v = Option.value ~default:0 lo in
  if (match hi with Some h -> h < lo_v | None -> false)
  then top (bitwidth t)
  else lift_unop (Clp.extract ?hi ?lo) (FinSet.extract ?hi ?lo) t

let cast c sz t =
  if sz <= 0 then top (bitwidth t)
  else lift_unop (Clp.cast c sz) (FinSet.cast c sz) t

let get_idx = lift_consume Clp.get_idx FinSet.get_idx

let pp ppf = lift_consume (Clp.pp ppf) (FinSet.pp ppf)

