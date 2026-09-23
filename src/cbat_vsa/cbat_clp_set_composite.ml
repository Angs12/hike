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

open !Core
open Bap.Std

module Word_ops = Cbat_word
module Utils = Cbat_vsa_utils
module Clp = Cbat_clp
module FinSet = Cbat_fin_set

type clp = Clp.t
type word = Cbat_word.t
type fset = FinSet.t

(* Large sets are Clps; small ones FinSets; stack addresses carry the
   symbolic segment base: [StackOff offs] = the base plus the exact
   offset set [offs].  Extrema answer from the offsets; shape-losing
   ops degrade to that plain hull; ops keeping unknown base bits
   answer top — the base is a tag except its certified low nibble. *)
type t =
  | Clp of Clp.t
  | FinSet of FinSet.t
  | StackOff of Clp.t
[@@deriving bin_io, sexp, compare]
type idx = int

(* Base 2^62 + 8: the +8 is the ABI entry residue — a call-entered
   RSP is 8 (mod 16). *)
let stack_base =
  Stdlib.Int64.add (Stdlib.Int64.shift_left 1L 62) 8L
let stack_span = Stdlib.Int64.shift_left 1L 23

let stack_word (offs : Clp.t) : t = StackOff offs

let stack_word_i64 (k : int64) : t =
  StackOff (Clp.singleton (Cbat_word.of_word (Word.of_int64 ~width:64 k)))

(* The offset set of a stack-symbolic value — answers ONLY for the
   symbolic arm; a plain in-band set is None. *)
let stack_offsets (t : t) : Clp.t option = match t with
  | StackOff offs -> Some offs
  | Clp _ | FinSet _ -> None

(* The progression's own stride: a bounded Clp/stack-offset set with
   step > 1 carries that step; a FinSet whose elements share one
   common difference carries it; everything else is 1. *)
let stride (t : t) : int =
  let of_clp c =
    if Clp.is_infinite c || Clp.is_bottom c then 1
    else
      match Cbat_word.to_int64 (Clp.step_of c) with
      | Ok s ->
        let i = Stdlib.Int64.to_int s in
        if i > 1 then i else 1
      | Error _ -> 1
  in
  (* The one common difference of consecutive elements, if uniform. *)
  let rec common_diff prev d (ws : Cbat_word.t list) : Cbat_word.t option =
    match ws with
    | [] -> d
    | w :: rest ->
      let d' = Cbat_word.sub w prev in
      if Cbat_word.compare d' Cbat_word.b0 = 0 then None
      else
        match d with
        | None -> common_diff w (Some d') rest
        | Some d0 ->
          if Cbat_word.equal d0 d' then common_diff w d rest else None
  in
  let of_finset s =
    match FinSet.iter s with
    | [] | [_] -> 1
    | w1 :: rest ->
      (match common_diff w1 None rest with
       | Some d when Cbat_word.compare d Cbat_word.b1 > 0 ->
         (match Cbat_word.to_int64 d with
          | Ok i -> let v = Stdlib.Int64.to_int i in if v > 1 then v else 1
          | Error _ -> 1)
       | _ -> 1)
  in
  match t with
  | Clp c -> of_clp c
  | StackOff offs -> of_clp offs
  | FinSet s -> of_finset s

let w64_of_i64 (i : int64) : Cbat_word.t =
  Cbat_word.of_word (Word.of_int64 ~width:64 i)

(* a + b + c with int64 overflow check. *)
let checked_add3 (a : int64) (b : int64) (c : int64) : int64 option =
  let pos x = Stdlib.Int64.compare x 0L >= 0 in
  let ab = Stdlib.Int64.add a b in
  if Bool.equal (pos a) (pos b) && not (Bool.equal (pos ab) (pos a)) then None
  else
    let abc = Stdlib.Int64.add ab c in
    if Bool.equal (pos ab) (pos c) && not (Bool.equal (pos abc) (pos ab))
    then None
    else Some abc

(* The exact hull [base + offs_lo, base + offs_hi]; a missing
   direction clamps to the segment extent — a stack address is
   in-segment by definition. *)
let plain_bounds (offs : Clp.t) : (int64 * int64) option =
  let floor = Stdlib.Int64.sub stack_base stack_span in
  let ceil = Stdlib.Int64.add stack_base stack_span in
  let side = function
    | Some w ->
      (match Cbat_word.to_int64 w with
       | Ok v -> checked_add3 stack_base 0L v
       | Error _ -> None)
    | None -> None
  in
  let lo = match Clp.min_elem offs with
    | Some w -> side (Some w)
    | None -> Some floor in
  let hi = match Clp.max_elem offs with
    | Some w -> side (Some w)
    | None -> Some ceil in
  match lo, hi with
  | Some lo, Some hi when Stdlib.Int64.compare hi lo >= 0 -> Some (lo, hi)
  | _ -> None

(* The plain twin: the exact hull as a step-1 interval; the lifts
   route every StackOff they cannot handle precisely through it. *)
let rec to_plain (t : t) : t =
  match t with
  | StackOff offs ->
    (match plain_bounds offs with
     | Some (cmin, cmax)
       when Stdlib.Int64.compare cmin 0L >= 0 && Stdlib.Int64.compare cmax cmin >= 0 ->
       Clp (Clp.interval ~width:64 (w64_of_i64 cmin) (w64_of_i64 cmax))
     | _ -> Clp (Clp.top 64))
  | Clp _ | FinSet _ -> t

(* Plain-operand top test (the composite [is_top] is defined later). *)
let plain_is_top (t : t) : bool =
  match t with
  | Clp p -> Clp.is_top p
  | FinSet _ -> false
  | StackOff offs -> Clp.is_top offs

let of_list ~width l : t =
  if List.length l > Utils.fin_set_size
  then Clp (Clp.of_list ~width l)
  else FinSet (FinSet.of_list ~width l)

let singleton w = FinSet (FinSet.singleton w)

let rec lift_consume (f_clp : clp -> 'a) (f_fs : fset -> 'a) : t -> 'a = fun t ->
  match t with
  | Clp p -> f_clp p
  | FinSet s -> f_fs s
  | StackOff _ -> lift_consume f_clp f_fs (to_plain t)

(* Small sets convert directly from the materialized element list. *)
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

let rec as_clp (t : t) : clp =
  match t with
  | Clp p -> p
  | FinSet s -> clp_of_finset s
  | StackOff _ -> as_clp (to_plain t)

let rec bound_set_size (t : t) : t =
  match t with
  | Clp p ->
    if Word_ops.gt_int (Clp.cardinality p) Utils.fin_set_size
    then Clp p
    else FinSet (finset_of_clp p)
  | FinSet s ->
    if Word_ops.gt_int (FinSet.cardinality s) Utils.fin_set_size
    then Clp (clp_of_finset s)
    else FinSet s
  | StackOff _ -> bound_set_size (to_plain t)

(* The plain binops as immediate tags: the lift's one op-aware choke
   point — every arm applies its op directly, no first-class function
   crosses the lift. *)
type binop =
  | Union
  | Add
  | Sub
  | Mul
  | Div
  | Sdiv
  | Modulo
  | Smodulo
  | Lshift
  | Rshift
  | Arshift
  | Logand
  | Logor
  | Logxor
  | Concat

let binop_clp (op : binop) (p1 : clp) (p2 : clp) : clp =
  match op with
  | Union -> Clp.union p1 p2
  | Add -> Clp.add p1 p2
  | Sub -> Clp.sub p1 p2
  | Mul -> Clp.mul p1 p2
  | Div -> Clp.div p1 p2
  | Sdiv -> Clp.sdiv p1 p2
  | Modulo -> Clp.modulo p1 p2
  | Smodulo -> Clp.smodulo p1 p2
  | Lshift -> Clp.lshift p1 p2
  | Rshift -> Clp.rshift p1 p2
  | Arshift -> Clp.arshift p1 p2
  | Logand -> Clp.logand p1 p2
  | Logor -> Clp.logor p1 p2
  | Logxor -> Clp.logxor p1 p2
  | Concat -> Clp.concat p1 p2

let binop_fs (op : binop) (s1 : fset) (s2 : fset) : fset =
  match op with
  | Union -> FinSet.union s1 s2
  | Add -> FinSet.add s1 s2
  | Sub -> FinSet.sub s1 s2
  | Mul -> FinSet.mul s1 s2
  | Div -> FinSet.div s1 s2
  | Sdiv -> FinSet.sdiv s1 s2
  | Modulo -> FinSet.modulo s1 s2
  | Smodulo -> FinSet.smodulo s1 s2
  | Lshift -> FinSet.lshift s1 s2
  | Rshift -> FinSet.rshift s1 s2
  | Arshift -> FinSet.arshift s1 s2
  | Logand -> FinSet.logand s1 s2
  | Logor -> FinSet.logor s1 s2
  | Logxor -> FinSet.logxor s1 s2
  | Concat -> FinSet.concat s1 s2

let rec lift_binop (op : binop) (t1 : t) (t2 : t) : t =
  bound_set_size @@ match t1, t2 with
  | Clp p1, Clp p2 -> Clp (binop_clp op p1 p2)
  | FinSet s1, FinSet s2 -> FinSet (binop_fs op s1 s2)
  | Clp p, FinSet s -> Clp (binop_clp op p (clp_of_finset s))
  | FinSet s, Clp p -> Clp (binop_clp op (clp_of_finset s) p)
  | StackOff _, _ | _, StackOff _ -> lift_binop op (to_plain t1) (to_plain t2)

let lift_unop (f_clp : clp -> clp) (f_fs : fset -> fset) : t -> t = fun t ->
  let rec go t =
    match t with
    | Clp p -> Clp (f_clp p)
    | FinSet s -> FinSet (f_fs s)
    | StackOff _ -> go (to_plain t)
  in
  bound_set_size @@ go t

let of_clp (p : clp) : t = bound_set_size (Clp p)

let bottom i = FinSet (FinSet.bottom i)
let top i = bound_set_size @@ Clp (Clp.top i)

(* The plain-arm band: signed-positive [2^61, 2^63); no real x86-64
   address can be there, so re-tagging a bounded set inside it stack is
   sound. *)
let stack_band_lo = Stdlib.Int64.shift_left 1L 61

(* Band test on concrete extrema: every extremum at least
   [stack_band_lo]; int64 has no [2^63), so the upper end reads as
   "not negative". *)
let in_band_words (lo : Cbat_word.t) (hi : Cbat_word.t) : bool =
  match Cbat_word.to_int64 lo, Cbat_word.to_int64 hi with
  | Ok loi, Ok hii ->
    Stdlib.Int64.compare loi stack_band_lo >= 0
    && Stdlib.Int64.compare hii stack_band_lo >= 0
  | _ -> false

(* Tests stack residency: the symbolic arm, or the plain degraded arm. *)
let in_stack_segment (t : t) : bool =
  match t with
  | StackOff _ -> true
  | Clp p ->
    (not (Clp.is_top p)) && (not (Clp.is_circular p))
    && (match Clp.min_elem p, Clp.max_elem p with
        | Some lo, Some hi -> in_band_words lo hi
        | _ -> false)
  | FinSet s ->
    (match FinSet.min_elem s, FinSet.max_elem s with
     | Some lo, Some hi -> in_band_words lo hi
     | _ -> false)

(* Segment-relative bounds: StackOff keeps its exact offsets; a plain
   in-band set maps to its own hull. *)
let stack_bounds (t : t) : (int64 * int64) option =
  let of_words (lo : Cbat_word.t) (hi : Cbat_word.t) =
    match Cbat_word.to_int64 lo, Cbat_word.to_int64 hi with
    | Ok loi, Ok hii ->
      (match checked_add3 (Stdlib.Int64.neg stack_base) 0L loi,
              checked_add3 (Stdlib.Int64.neg stack_base) 0L hii with
       | Some rlo, Some rhi -> Some (rlo, rhi)
       | _ -> None)
    | _ -> None in
  match t with
  | StackOff offs ->
    (match Clp.min_elem offs, Clp.max_elem offs with
     | Some lo, Some hi ->
       (match Cbat_word.to_int64 lo, Cbat_word.to_int64 hi with
        | Ok loi, Ok hii -> Some (loi, hii)
        | _ -> None)
     | _ -> None)
  | Clp p ->
    if in_stack_segment t then
      match Clp.min_elem p, Clp.max_elem p with
      | Some lo, Some hi -> of_words lo hi
      | _ -> None
    else None
  | FinSet s ->
    if in_stack_segment t then
      match FinSet.min_elem s, FinSet.max_elem s with
      | Some lo, Some hi -> of_words lo hi
      | _ -> None
    else None

let bitwidth (t : t) : int = match t with
  | StackOff _ -> 64
  | Clp p -> Clp.bitwidth p
  | FinSet s -> FinSet.bitwidth s

(* |segment| * |offs| at width 65.  The product SATURATES: a wrapped
   product would under-report. *)
let cardinality (t : t) = match t with
  | StackOff offs ->
    let width = 65 in
    let a = Cbat_word.of_int ~width (Stdlib.Int64.to_int stack_span + 1) in
    let b = Cbat_word.cap_at_width ~width (Clp.cardinality offs) in
    if Cbat_word.is_zero a || Cbat_word.is_zero b then
      Cbat_word.zero width
    else if Cbat_word.is_one a then b
    else if Cbat_word.is_one b then a
    else
      (* a = 2^23 + 1, so [b <= 2^39] keeps the exact product below
         2^63; anything larger saturates. *)
      if Cbat_word.leq_int b 0x8000000000 then Cbat_word.mul a b
      else Cbat_word.ones width
  | Clp p -> Clp.cardinality p
  | FinSet s -> FinSet.cardinality s

(* Smear-bounds queries: the concrete twin decides. *)
let nearest_pred w (t : t) =
  lift_consume (Clp.nearest_pred w) (FinSet.nearest_pred w) (to_plain t)
let nearest_succ w (t : t) =
  lift_consume (Clp.nearest_succ w) (FinSet.nearest_succ w) (to_plain t)

let min_elem (t : t) = match t with
  | StackOff offs ->
    Option.map (plain_bounds offs) ~f:(fun (cmin, _) -> w64_of_i64 cmin)
  | Clp p -> Clp.min_elem p
  | FinSet s -> FinSet.min_elem s

let max_elem (t : t) = match t with
  | StackOff offs ->
    Option.map (plain_bounds offs) ~f:(fun (_, cmax) -> w64_of_i64 cmax)
  | Clp p -> Clp.max_elem p
  | FinSet s -> FinSet.max_elem s

(* The SEGMENT-RELATIVE extrema of a stack value: a [StackOff]'s offset
   set, or a plain in-band set's segment-relative hull. *)
let offset_extrema (t : t) : (Cbat_word.t * Cbat_word.t) option =
  let twin = match t with
    | StackOff offs -> Some (of_clp offs)
    | Clp _ | FinSet _ ->
      Option.map (stack_bounds t) ~f:(fun (lo, hi) ->
          of_clp (Clp.interval ~width:64 (w64_of_i64 lo) (w64_of_i64 hi)))
  in
  Option.bind twin ~f:(fun t' ->
    Option.map2 (min_elem t') (max_elem t') ~f:(fun lo hi -> (lo, hi)))

(* Signed extrema: the projection is signed-positive, so its signed
   and unsigned extrema agree; a set spanning the sign boundary has
   no signed extremum. *)
let min_elem_signed (t : t) = match t with
  | StackOff _ -> min_elem t
  | Clp p -> (
    match Clp.min_elem_signed p with
    | Some _ as r -> r
    | None -> (
      (* All-positive set: the unsigned min IS the signed min. *)
      match Clp.max_elem p with
      | Some mx when Cbat_word.(<) mx (Word_ops.half (Cbat_word.bitwidth mx)) ->
        Clp.min_elem p
      | _ -> None))
  | FinSet s -> FinSet.min_elem_signed s

let max_elem_signed (t : t) = match t with
  | StackOff _ -> max_elem t
  | Clp p -> (
    match Clp.max_elem_signed p with
    | Some _ as r -> r
    | None -> (
      (* All-negative set: the unsigned max IS the signed max. *)
      match Clp.min_elem p with
      | Some mn when Cbat_word.(>=) mn (Word_ops.half (Cbat_word.bitwidth mn)) ->
        Clp.max_elem p
      | _ -> None))
  | FinSet s -> FinSet.max_elem_signed s

(* Offset space: the per-sub cell-key universe keys by offsets. *)
let splits_by (t : t) (w : Cbat_word.t) = match t with
  | StackOff offs -> Clp.splits_by offs w
  | Clp p -> Clp.splits_by p w
  | FinSet s -> FinSet.splits_by s w

(* Hull test: an over-approximation of membership in the projection. *)
let elem w (t : t) = match t with
  | StackOff offs ->
    (match plain_bounds offs with
     | Some (cmin, cmax) ->
       (match Cbat_word.to_int64 w with
        | Ok wi ->
          Stdlib.Int64.compare wi cmin >= 0 && Stdlib.Int64.compare wi cmax <= 0
        | _ -> false)
     | None -> false)
  | Clp p -> Clp.elem w p
  | FinSet s -> FinSet.elem w s

(* Materializes the base-0 slice only; the full projection is
   8 MiB of elements. *)
let iter (t : t) = match t with
  | StackOff offs ->
    List.map ~f:(fun w -> Cbat_word.add (w64_of_i64 stack_base) w)
      (Clp.iter offs)
  | Clp p -> Clp.iter p
  | FinSet s -> FinSet.iter s

let equal t1 t2 : bool = match t1, t2 with
  | StackOff o1, StackOff o2 -> Clp.equal o1 o2
  | StackOff _, _ | _, StackOff _ -> false
  | Clp p1, Clp p2 -> Clp.equal p1 p2
  | FinSet s1, FinSet s2 -> FinSet.equal s1 s2
  | Clp _, FinSet _
  | FinSet _, Clp _ -> false

let rec overlap t1 t2 : bool = match t1, t2 with
  (* Same sub, same base symbol: offset-space overlap is exact. *)
  | StackOff o1, StackOff o2 -> Clp.overlap o1 o2
  | StackOff _, _ | _, StackOff _ ->
    overlap (to_plain t1) (to_plain t2)
  | Clp p1, Clp p2 -> Clp.overlap p1 p2
  | FinSet s1, FinSet s2 -> FinSet.overlap s1 s2
  | Clp p, FinSet s
  | FinSet s, Clp p -> FinSet.overlap_generic (module Clp) s p

let union t1 t2 : t = match t1, t2 with
  | StackOff o1, StackOff o2 -> StackOff (Clp.union o1 o2)
  | StackOff _, _ | _, StackOff _ ->
    lift_binop Union (to_plain t1) (to_plain t2)
  | Clp _, Clp _ | FinSet _, FinSet _ | Clp _, FinSet _ | FinSet _, Clp _ ->
    lift_binop Union t1 t2

(* The plain side of a mixed meet, translated into the offset space
   (positions minus the base): the meet stays stack-symbolic. *)
let plain_offsets (p : t) : Clp.t option =
  let base = Cbat_word.of_int64 ~width:64 stack_base in
  match p with
  | Clp c when not (Clp.is_bottom c) ->
    Some (Clp.translate c (Cbat_word.neg base))
  | FinSet s ->
    let ws = List.map ~f:(fun w -> Cbat_word.sub w base) (FinSet.iter s) in
    (match ws with
     | [] -> Some (Clp.bottom 64)
     | lo :: _ ->
       let min_w = List.fold ~init:lo ~f:(fun a w -> if Cbat_word.compare w a < 0 then w else a) ws in
       let max_w = List.fold ~init:lo ~f:(fun a w -> if Cbat_word.compare a w < 0 then w else a) ws in
       Some (Clp.interval ~width:64 min_w max_w))
  | _ -> None

(* Precise meet across representations. *)
let rec intersection (t1 : t) (t2 : t) : t =
  (* Width mismatch returns the wider operand. *)
  if bitwidth t1 <> bitwidth t2 then
    (if bitwidth t1 > bitwidth t2 then t1 else t2)
  else match t1, t2 with
  | StackOff _, _ when plain_is_top t2 -> t1
  | _, StackOff _ when plain_is_top t1 -> t2
  | StackOff o1, StackOff o2 -> StackOff (Clp.intersection o1 o2)
  | StackOff o1, (Clp _ as p) | (Clp _ as p), StackOff o1 ->
    (match plain_offsets p with
     | Some o2 -> StackOff (Clp.intersection o1 o2)
     | None -> intersection (to_plain t1) (to_plain t2))
  | StackOff _, _ | _, StackOff _ ->
    intersection (to_plain t1) (to_plain t2)
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
        (* Strict successor in [p]'s circular order: [nearest_succ]
           off by one succ (its inverse runs through [lnot]). *)
        let strict_succ (e : word) : word option =
          Clp.nearest_succ (Cbat_word.succ e) p in
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
          Option.value_map (strict_succ e1) ~default:false
            ~f:(fun nxt -> Cbat_word.( = ) nxt e2) in
        let non_adj, adj_pairs =
          List.partition_tf ~f:(fun pr -> not (adj pr)) pairs in
        (* The remainder of [p] after one removed arc [arc_start..arc_end]
           (stepping by [step]): its direction decides the constructor
           family. *)
        let remainder ~(arc_end : word) ~(arc_start : word) ~(step : word) : clp =
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
        in
        match non_adj, adj_pairs with
        | [ (arc_end, arc_start) ], (e1', e2') :: _ ->
          (* One gap: remainder is one CLP stepping by the surviving
             arc's stride. *)
          remainder ~arc_end ~arc_start ~step:(Cbat_word.sub e2' e1')
        | [ (arc_end, arc_start) ], [] ->
          (* Singleton run: the remainder starts at the strict
             successor of the run's end. *)
          (match strict_succ arc_end with
           | Some nxt ->
             remainder ~arc_end ~arc_start ~step:(Cbat_word.sub nxt arc_end)
           | None -> p)
        | _ ->
          p
      end

(* Set difference; inexact cases return the identity. *)
let rec diff (t1 : t) (t2 : t) : t = match t1, t2 with
  | StackOff _, _ | _, StackOff _ ->
    diff (to_plain t1) (to_plain t2)
  | Clp p1, Clp p2 ->
    (* G2a: within the budget the enumerated difference is exact, two
       runs included; past it the bound identity stands. *)
    if Clp.bitwidth p1 <> Clp.bitwidth p2
       || Word_ops.gt_int (Clp.cardinality p1) Utils.fin_set_size
    then bound_set_size (Clp (Clp.diff p1 p2))
    else
      FinSet
        (FinSet.of_list ~width:(Clp.bitwidth p1)
           (List.filter ~f:(fun x -> not (Clp.elem x p2)) (Clp.iter p1)))
  | FinSet s1, FinSet s2 -> FinSet (FinSet.diff s1 s2)
  | Clp p, FinSet s ->
    if Clp.bitwidth p <> FinSet.bitwidth s
       || Word_ops.gt_int (Clp.cardinality p) Utils.fin_set_size
    then bound_set_size (Clp (clp_diff_finset p s))
    else
      FinSet
        (FinSet.of_list ~width:(Clp.bitwidth p)
           (List.filter ~f:(fun x -> not (FinSet.elem x s)) (Clp.iter p)))
  | FinSet s, Clp p ->
    if FinSet.bitwidth s <> Clp.bitwidth p then t1
    else
      let width = FinSet.bitwidth s in
      FinSet (FinSet.of_list ~width
        (List.filter ~f:(fun w -> not (Clp.elem w p)) (FinSet.iter s)))

(* Adds a base-free operand to a stack word: the offsets shift exactly. *)
let stack_lift2 (f : clp -> clp -> clp) (t1 : t) (t2 : t) : t option =
  match t1, t2 with
  | StackOff o1, _ when bitwidth t2 = 64 ->
    Some (StackOff (f o1 (as_clp t2)))
  | _, StackOff o2 when bitwidth t1 = 64 ->
    Some (StackOff (f (as_clp t1) o2))
  | _ -> None

let add t1 t2 : t = match t1, t2 with
  (* Two stack words: the base appears twice — the plain hulls. *)
  | StackOff _, StackOff _ ->
    lift_binop Add (to_plain t1) (to_plain t2)
  | _ ->
    (match stack_lift2 Clp.add t1 t2 with
     | Some t -> t
     | None -> lift_binop Add t1 t2)

let sub t1 t2 : t = match t1, t2 with
  (* Two stack words: the base cancels — the exact offset difference. *)
  | StackOff o1, StackOff o2 -> bound_set_size (Clp (Clp.sub o1 o2))
  | _ ->
    (match stack_lift2 Clp.sub t1 t2 with
     | Some t -> t
     | None -> lift_binop Sub t1 t2)

(* Only the base's low nibble is a fact (the ABI entry residue): an
   op confined to it computes; an op keeping unknown bits answers
   top.  The relative ops (add, sub, comparisons) keep exact offsets. *)
let certified_bits = 4

let blind_binop (op : binop) (t1 : t) (t2 : t) : t =
  match t1, t2 with
  | StackOff _, _ | _, StackOff _ -> top (bitwidth t1)
  | _ -> lift_binop op t1 t2

let blind_unop (f_clp : clp -> clp) (f_fs : fset -> fset) (t : t) : t =
  match t with
  | StackOff _ -> top (bitwidth t)
  | _ -> lift_unop f_clp f_fs t

(* The stack-symbolic side of a mixed pair, with its plain other. *)
let mixed (t1 : t) (t2 : t) : (t * t) option =
  match t1, t2 with
  | StackOff _, (Clp _ | FinSet _) -> Some (t1, t2)
  | (Clp _ | FinSet _), StackOff _ -> Some (t2, t1)
  | _ -> None

(* The singleton word of a plain operand, if it is one. *)
let singleton_of (t : t) : word option =
  let pair a b = if Cbat_word.equal a b then Some a else None in
  match t with
  | Clp p -> (match Clp.min_elem p, Clp.max_elem p with
      | Some a, Some b -> pair a b
      | _ -> None)
  | FinSet s -> (match FinSet.min_elem s, FinSet.max_elem s with
      | Some a, Some b -> pair a b
      | _ -> None)
  | StackOff _ -> None

(* [f] over the offsets while enumerable; top past the budget. *)
let certified_image ~(width : int) (f : word -> word) (offs : clp) : t =
  let base = w64_of_i64 stack_base in
  match Cbat_word.to_int (Clp.cardinality offs) with
  | Ok n when n > 0 && n <= Utils.fin_set_size ->
    of_list ~width
      (List.map (Clp.iter offs)
         ~f:(fun o ->
             Cbat_word.cast Bil.UNSIGNED width (f (Cbat_word.add base o))))
  | _ -> top width

let mul t1 t2 = blind_binop Mul t1 t2
let div t1 t2 = blind_binop Div t1 t2
let sdiv t1 t2 = blind_binop Sdiv t1 t2
let modulo t1 t2 = blind_binop Modulo t1 t2
let smodulo t1 t2 = blind_binop Smodulo t1 t2
let arshift t1 t2 = blind_binop Arshift t1 t2
let rshift t1 t2 = blind_binop Rshift t1 t2
let lshift t1 t2 = blind_binop Lshift t1 t2
(* A mask confined to the certified nibble computes; a wider mask
   keeps unknown bits and answers top. *)
let logand t1 t2 : t =
  match mixed t1 t2 with
  | Some (t, m) ->
    (match t, singleton_of m with
     | StackOff offs, Some k when Cbat_word.leq_int k ((1 lsl certified_bits) - 1) ->
       let k64 = Cbat_word.cast Bil.UNSIGNED (bitwidth t) k in
       certified_image ~width:(bitwidth t)
         (fun v -> Cbat_word.logand v k64) offs
     | _ -> top (bitwidth t))
  | None ->
    (match t1, t2 with
     | StackOff _, StackOff _ -> top (bitwidth t1)
     | _ -> lift_binop Logand t1 t2)
let logor t1 t2 = blind_binop Logor t1 t2
let logxor t1 t2 = blind_binop Logxor t1 t2

let lnot t = blind_unop Clp.lnot FinSet.lnot t
let neg t = blind_unop Clp.neg FinSet.neg t

let concat t1 t2 =
  match t1, t2 with
  | StackOff _, _ | _, StackOff _ -> top (bitwidth t1 + bitwidth t2)
  | _ -> lift_binop Concat t1 t2

(* The offsets arm and the plain arm answer the same Clp query. *)
let on_offs (f : clp -> bool) (t : t) : bool =
  match t with
  | StackOff offs | Clp offs -> f offs
  | FinSet _ -> false

let is_top t = on_offs Clp.is_top t

let is_bottom (t : t) = match t with
  | StackOff offs -> Clp.is_bottom offs
  | Clp _ -> false
  | FinSet s -> Cbat_word.is_zero (FinSet.cardinality s)

let is_infinite t = on_offs Clp.is_infinite t
let is_ascending t = on_offs Clp.is_ascending t
let is_descending t = on_offs Clp.is_descending t
let is_circular t = on_offs Clp.is_circular t

let rec precedes t1 t2 : bool = match t1, t2 with
  | StackOff o1, StackOff o2 -> Clp.precedes o1 o2
  | StackOff _, _ | _, StackOff _ ->
    precedes (to_plain t1) (to_plain t2)
  | Clp p1, Clp p2 -> Clp.precedes p1 p2
  | FinSet s1, FinSet s2 -> FinSet.precedes s1 s2
  | Clp _, FinSet _ -> false
  | FinSet s, Clp p -> Clp.precedes (clp_of_finset s) p

(* Widening lives in the offsets; mixed pairs degrade via [as_clp]. *)
let widen_join t1 t2 : t = match t1, t2 with
  | StackOff o1, StackOff o2 -> StackOff (Clp.widen_join o1 o2)
  | _ -> bound_set_size @@ Clp (Clp.widen_join (as_clp t1) (as_clp t2))

let extrapolate_steps ~steps t1 t2 : t = match t1, t2 with
  | StackOff o1, StackOff o2 -> StackOff (Clp.extrapolate_steps ~steps o1 o2)
  | _ -> bound_set_size @@ Clp (Clp.extrapolate_steps ~steps (as_clp t1) (as_clp t2))

let join = union
let meet = intersection

(* Degenerate cast keeps top. *)
let extract ?hi ?lo t =
  let lo_v = Option.value ~default:0 lo in
  if (match hi with Some h -> h < lo_v | None -> false)
  then top (bitwidth t)
  else match t with
    | StackOff _ when lo_v = 0 && (match hi with Some 63 -> true | _ -> false) ->
      (* The full-width extract is the identity. *)
      t
    | StackOff offs when Option.value ~default:63 hi < certified_bits ->
      let hi_v = Option.value ~default:63 hi in
      certified_image ~width:(hi_v - lo_v + 1)
        (Cbat_word.extract_exn ~hi:hi_v ~lo:lo_v) offs
    | StackOff _ ->
      let hi_v = Option.value ~default:(bitwidth t - 1) hi in
      top (hi_v - lo_v + 1)
    | Clp _ | FinSet _ ->
      lift_unop (Clp.extract ?hi ?lo) (FinSet.extract ?hi ?lo) t

let cast c sz t =
  if sz <= 0 then top (bitwidth t)
  else
    (* A cast at the operand's width is the identity; width changes
       follow the certified-nibble law. *)
    match t with
    | StackOff _ when sz = 64 -> t
    | StackOff offs when sz <= certified_bits && not (match c with Bil.HIGH -> true | _ -> false) ->
      certified_image ~width:sz (Cbat_word.cast c sz) offs
    | StackOff _ -> top sz
    | Clp _ | FinSet _ -> lift_unop (Clp.cast c sz) (FinSet.cast c sz) t

let get_idx (t : t) : idx = match t with
  | StackOff _ -> 64
  | Clp p -> Clp.get_idx p
  | FinSet s -> FinSet.get_idx s

let pp ppf (t : t) = match t with
  | StackOff offs -> Format.fprintf ppf "@[stk%a@]" Clp.pp offs
  | Clp p -> Clp.pp ppf p
  | FinSet s -> FinSet.pp ppf s


(* The def-carried classification of a set on the model's ABSOLUTE
   segment line — the entry RSP is the segment base, so a frame offset
   o has absolute position [stack_base + o]. *)

type kind =
  | Range of int64 * int64
  | Infinite of int64 * int64
  | Caller of int64 * int64
  | Mixed of int64 * int64
  | Dead
[@@deriving equal]

(* The fully-infinite span: the whole position line.  A TOP denotation
   IS this span — the degenerate [Infinite], carrying no bound. *)
let unbounded_span : kind = Infinite (Stdlib.Int64.min_int, Stdlib.Int64.max_int)

let is_unbounded_span (lo : int64) (hi : int64) : bool =
  Int64.equal lo Stdlib.Int64.min_int && Int64.equal hi Stdlib.Int64.max_int

(* Overflow-checked absolute position of one frame offset. *)
let position_of_offset (o : int64) : int64 option =
  let r = Stdlib.Int64.add stack_base o in
  if Stdlib.Int64.compare o 0L > 0 && Stdlib.Int64.compare r o < 0 then None
  else Some r

let int64_pair_of (lo : Cbat_word.t) (hi : Cbat_word.t)
  : (int64 * int64) option =
  match Cbat_word.to_int64 lo, Cbat_word.to_int64 hi with
  | Ok lo, Ok hi -> Some (lo, hi)
  | _ -> None

(* Split over ABSOLUTE positions: entirely at/above the entry RSP ->
   Caller; entirely below -> Range; otherwise Mixed.  The unbounded
   span names no side of the entry line, so it keeps itself. *)
let caller_split (k : kind) : kind =
  let cmp = Stdlib.Int64.compare in
  let ordered lo hi = cmp lo hi <= 0 in
  let entry = stack_base in
  match k with
  | Range (lo, hi) | Infinite (lo, hi) when not (is_unbounded_span lo hi) ->
    if ordered lo hi && cmp lo entry >= 0 then Caller (lo, hi)
    else if ordered lo hi && cmp hi entry <= 0 then k
    else Mixed (lo, hi)
  | k -> k

let classify (t : t) : kind =
  if is_top t then unbounded_span
  else if is_bottom t then Dead
  else
    let bounds =
      match offset_extrema t with
      | Some (lo, hi) ->
        Base.Option.bind (int64_pair_of lo hi) ~f:(fun (lo, hi) ->
            Base.Option.bind (position_of_offset lo) ~f:(fun lo ->
                Base.Option.map (position_of_offset hi) ~f:(fun hi -> (lo, hi))))
      | None ->
        (match min_elem t, max_elem t with
         | Some lo, Some hi -> int64_pair_of lo hi
         | _ -> None)
    in
    match bounds with
    | Some (lo, hi) ->
      let is_inf = is_infinite t || Stdlib.Int64.compare lo hi > 0 in
      if is_inf then Infinite (lo, hi) else Range (lo, hi)
    | None -> unbounded_span

(* The elements, when the set is enumerable within [cap]; [None] = the
   count exceeds the budget, the caller takes its sound identity. *)
let enumerate ~(cap : int) (t : t) : word list option =
  if Cbat_word.gt_int (cardinality t) cap then None else Some (iter t)
