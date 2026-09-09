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

module Word_ops = Cbat_word
module Utils = Cbat_vsa_utils
module Clp = Cbat_clp
module FinSet = Cbat_fin_set

type clp = Clp.t
type word = Cbat_word.t
type fset = FinSet.t

(* Large sets are Clps; small ones FinSets. *)
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

(* Small sets skip the sorted-list round trip: the element list is already
   materialized, so empty and singleton convert directly. Singletons are the
   common case (immediates and single-point guards). *)
let clp_of_finset fs : clp =
  let width = FinSet.bitwidth fs in
  match FinSet.iter fs with
  | [] -> Clp.bottom width
  | [ x ] -> Clp.singleton x
  | l -> Clp.of_list ~width l

let finset_of_clp p : fset =
  let width = Clp.bitwidth p in
  match Clp.iter p with
  | [] -> FinSet.of_list ~width []
  | [ x ] -> FinSet.singleton x
  | l -> FinSet.of_list ~width l

let as_clp = function
  | Clp p -> p
  | FinSet s -> clp_of_finset s


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

let nearest_pred w = lift_consume (Clp.nearest_pred w) (FinSet.nearest_pred w)
let nearest_succ w = lift_consume (Clp.nearest_succ w) (FinSet.nearest_succ w)

let min_elem = lift_consume Clp.min_elem FinSet.min_elem
let max_elem = lift_consume Clp.max_elem FinSet.max_elem
let min_elem_signed = lift_consume Clp.min_elem_signed FinSet.min_elem_signed
let max_elem_signed = lift_consume Clp.max_elem_signed FinSet.max_elem_signed
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
(* Precise meet across representations. *)
let intersection (t1 : t) (t2 : t) : t =
  (* Width mismatch returns the wider operand. *)
  if bitwidth t1 <> bitwidth t2 then
    (if bitwidth t1 > bitwidth t2 then t1 else t2)
  else match t1, t2 with
  | Clp p1, Clp p2 -> Clp (Clp.intersection p1 p2)
  | FinSet s1, FinSet s2 -> FinSet (FinSet.intersection s1 s2)
  | Clp p, FinSet s
  | FinSet s, Clp p -> FinSet (FinSet.intersect_generic (module Clp) s p)

(* CLP minus finite elements; exact for one contiguous arc. *)
let clp_diff_finset (p : clp) (s : fset) : clp =
  if Clp.bitwidth p <> FinSet.bitwidth s then p
  else if Clp.is_bottom p then p
  else
    let width = Clp.bitwidth p in
    let es =
      List.sort ~compare:Cbat_word.compare
        (List.filter ~f:(fun w -> Clp.elem w p) (FinSet.iter s)) in
    match es with
    | [] -> p
    | _ ->
      let n = List.length es in
      let cnt = Cbat_word.of_int ~width:(width + 1) n in
      let c1 = Clp.cardinality p in
      if Cbat_word.(>=) cnt c1 then Clp.bottom width
      else begin
        (* Strict successor in [p]'s circular order. *)
        let strict_succ (e : word) : word option =
          match Clp.nearest_pred (Cbat_word.pred (Cbat_word.lnot e)) (Clp.lnot p) with
          | Some w -> Some (Cbat_word.lnot w)
          | None -> None in
        (* Consecutive pairs including the wrap pair. *)
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
          | Some nxt -> Cbat_word.(=) nxt e2
          | None -> false in
        let non_adj, adj_pairs =
          List.partition_tf ~f:(fun pr -> not (adj pr)) pairs in
        match non_adj, adj_pairs with
        | [ (arc_end, arc_start) ], (e1', e2') :: _ ->
          (* One gap: remainder is one CLP. *)
          let step = Cbat_word.sub e2' e1' in
          let cardn = Cbat_word.sub c1 cnt in
          if Clp.is_ascending p then
            match Clp.min_elem p with
            | Some p_min when Cbat_word.(=) arc_start p_min ->
              let new_base = Cbat_word.add arc_end step in
              if Cbat_word.(<) new_base arc_end then Clp.bottom width
              else Clp.create_ascending ~width ~base:new_base ~step
            | _ -> p
          else if Clp.is_descending p then
            match Clp.max_elem p with
            | Some p_max when Cbat_word.(=) arc_end p_max ->
              let new_base = Cbat_word.sub arc_start step in
              if Cbat_word.(>) new_base arc_start then Clp.bottom width
              else Clp.create_descending ~width ~base:new_base ~step
            | _ -> p
          else if Clp.is_circular p then
            Clp.create (Cbat_word.add arc_end step) ~step ~cardn
          else if Cbat_word.(>) arc_start arc_end then
            (* Wrapping remainder is one interval. *)
            Clp.create (Cbat_word.add arc_end step) ~step ~cardn
          else
            (match Clp.min_elem p, Clp.max_elem p with
             | Some p_min, Some p_max ->
               if Cbat_word.(=) arc_start p_min then
                 Clp.create (Cbat_word.add arc_end step) ~step ~cardn
               else if Cbat_word.(=) arc_end p_max then
                 Clp.create p_min ~step ~cardn
               else p
             | _ -> p)
        | [ (arc_end, arc_start) ], [] ->
          (* Singleton run. *)
          (match strict_succ arc_end with
           | Some nxt ->
             let step = Cbat_word.sub nxt arc_end in
             let cardn = Cbat_word.sub c1 cnt in
             if Clp.is_ascending p then
               match Clp.min_elem p with
               | Some p_min when Cbat_word.(=) arc_start p_min ->
                 let new_base = Cbat_word.add arc_end step in
                 if Cbat_word.(<) new_base arc_end then Clp.bottom width
                 else Clp.create_ascending ~width ~base:new_base ~step
               | _ -> p
             else if Clp.is_descending p then
               match Clp.max_elem p with
               | Some p_max when Cbat_word.(=) arc_end p_max ->
                 let new_base = Cbat_word.sub arc_start step in
                 if Cbat_word.(>) new_base arc_start then Clp.bottom width
                 else Clp.create_descending ~width ~base:new_base ~step
               | _ -> p
             else if Clp.is_circular p then
               Clp.create (Cbat_word.add arc_end step) ~step ~cardn
             else
               (match Clp.min_elem p, Clp.max_elem p with
                | Some p_min, Some p_max ->
                  if Cbat_word.(=) arc_start p_min then
                    Clp.create (Cbat_word.add arc_end step) ~step ~cardn
                  else if Cbat_word.(=) arc_end p_max then
                    Clp.create p_min ~step ~cardn
                  else p
                | _ -> p)
           | None -> p)
        | _ ->
          (* Otherwise the identity. *)
          p
      end

(* Set difference; inexact cases return the identity. *)
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
let is_bottom = lift_consume (fun _ -> false) (Fn.compose Cbat_word.is_zero FinSet.cardinality)
let is_infinite = lift_consume Clp.is_infinite (fun _ -> false)
let is_ascending = lift_consume Clp.is_ascending (fun _ -> false)
let is_descending = lift_consume Clp.is_descending (fun _ -> false)
let is_circular = lift_consume Clp.is_circular (fun _ -> false)

(* Lattice. *)
let precedes t1 t2 : bool = match t1, t2 with
  | Clp p1, Clp p2 -> Clp.precedes p1 p2
  | FinSet s1, FinSet s2 -> FinSet.precedes s1 s2
  | Clp _, FinSet _ -> false
  | FinSet s, Clp p -> Clp.precedes (clp_of_finset s) p

let widen_join t1 t2 : t = bound_set_size @@
  Clp (Clp.widen_join (as_clp t1) (as_clp t2))

let extrapolate_steps ~steps t1 t2 : t = bound_set_size @@
  Clp (Clp.extrapolate_steps ~steps (as_clp t1) (as_clp t2))

let join = union
let meet = intersection
let bottom i = FinSet (FinSet.bottom i)
let top i = bound_set_size @@ Clp (Clp.top i)

(* Degenerate cast keeps top. *)
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

