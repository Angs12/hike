(* ************************************************************************* *)
(*  *)
(* Copyright (C) Draper Laboratory. Licensed under project LICENSE. *)
(*  *)
(* This file is provided under the license found in the LICENSE file in *)
(* the top-level directory of this project. *)
(*  *)
(* This work is funded in part by the ONR/NAWC Contract N6833518C0107. Its *)
(* content does not necessarily reflect the position or policy of the US *)
(* Government and no official endorsement should be inferred. *)
(*  *)
(* ************************************************************************* *)

open !Core
open Bap.Std

module Word_ops = Cbat_word
module Utils = Cbat_vsa_utils
module Clp = Cbat_clp
module P = Clp.Pieces
module FinSet = Cbat_fin_set

type clp = Clp.t
type word = Cbat_word.t
type fset = FinSet.t

(* Large sets are one Clp piece union; small ones FinSets; stack
   addresses carry the symbolic segment base: [StackOff offs] = the
   base plus the exact offset piece union [offs].  A value is ONE of
   those (the common case — no list cell), or [Many] of the canonical
   multi-piece list ([Many] never nests: [canonical] flattens).
   Extrema answer from the offsets; shape-losing ops degrade to that
   plain hull; ops keeping unknown base bits answer top — the base is
   a tag except its certified low nibble. *)
type t =
  | Clp of P.t
  | FinSet of FinSet.t
  | StackOff of P.t
  | Many of t list
[@@deriving bin_io, sexp, compare]
type idx = int

(* Base 2^62 + 8: the +8 is the ABI entry residue — a call-entered
   RSP is 8 (mod 16). *)
let stack_base =
  Stdlib.Int64.add (Stdlib.Int64.shift_left 1L 62) 8L
(* The symbolic stack segment spans 8 MiB above the base — a TOP
   stack claim covers at most [stack_span] bytes. *)
let stack_span = Stdlib.Int64.shift_left 1L 23

let w64_of_i64 (i : int64) : Cbat_word.t =
  Cbat_word.of_word (Word.of_int64 ~width:64 i)

(* ---------------- leaf views (total over [Many]) ---------------- *)

let rec bitwidth (t : t) : int =
  match t with
  | StackOff _ -> 64
  | Clp ps -> P.bitwidth ps
  | FinSet s -> FinSet.bitwidth s
  | Many ps -> List.fold ps ~init:0 ~f:(fun a q -> Stdlib.max a (bitwidth q))

let rec is_bottom (t : t) : bool =
  match t with
  | Clp ps | StackOff ps -> P.is_bottom ps
  | FinSet s -> Cbat_word.is_zero (FinSet.cardinality s)
  | Many ps -> List.for_all ps ~f:is_bottom

(* |segment| * |offs| at width 65.  The product SATURATES: a wrapped
   product would under-report. *)
let stack_cardinality (offs : P.t) : word =
  let width = 65 in
  let a = Cbat_word.of_int ~width (Stdlib.Int64.to_int stack_span + 1) in
  let b = Cbat_word.cap_at_width ~width (P.cardinality offs) in
  if Cbat_word.is_zero a || Cbat_word.is_zero b then
    Cbat_word.zero width
  else if Cbat_word.is_one a then b
  else if Cbat_word.is_one b then a
  else
    (* a = 2^23 + 1, so [b <= 2^39] keeps the exact product below
       2^63; anything larger saturates. *)
    if Cbat_word.leq_int b 0x8000000000 then Cbat_word.mul a b
    else Cbat_word.ones width

(* The single-progression hull of a piece union. *)
let hull_of_pieces (ps : P.t) : clp option =
  match P.to_list ps with
  | [] -> None
  | p :: rest -> Some (List.fold rest ~init:p ~f:Clp.union)

let pieces_of_words ~width (l : word list) : P.t = P.of_list ~width l

let pieces_of_finset (s : fset) : P.t =
  pieces_of_words ~width:(FinSet.bitwidth s) (FinSet.iter s)

let clp_of_finset fs : clp =
  let width = FinSet.bitwidth fs in
  match FinSet.iter fs with
  | [] -> Clp.bottom width
  | [ x ] -> Clp.singleton x
  | l -> Clp.of_list ~width l

(* ---------------- canonicalization ---------------- *)

(* The canonical value: one leaf, or [Many] of the canonical leaf list
   in the fixed order Clp, FinSet, StackOff (no nesting); bottoms drop
   (an all-bottom value keeps one empty FinSet so the width survives);
   an over-budget FinSet pool promotes to its exact piece runs; a lone
   small plain piece union keeps its exact FinSet twin (the tier). *)
let canonical (ps : t list) : t =
  let alive = List.filter ps ~f:(fun q -> not (is_bottom q)) in
  let sos =
    List.filter_map ps ~f:(function StackOff x -> Some x | _ -> None) in
  let so_pool =
    match sos with
    | [] -> None
    | x :: rest -> Some (List.fold rest ~init:x ~f:P.union)
  in
  (match alive, so_pool with
  | [], Some offs ->
    (* The symbolic bottom keeps its kind: an empty offset set is still a
       stack value (its consumers span the full key line). *)
    StackOff offs
  | [], None ->
    (match ps with
     | [] -> FinSet (FinSet.bottom 1)
     | _ ->
       let w =
         List.fold ps ~init:1 ~f:(fun a q -> Stdlib.max a (bitwidth q)) in
       FinSet (FinSet.bottom w))
  | _ ->
    let clps =
      List.filter_map ps ~f:(function Clp x -> Some x | _ -> None) in
    let fss =
      List.filter_map ps ~f:(function FinSet x -> Some x | _ -> None) in
    let fs_total =
      List.fold fss ~init:0 ~f:(fun a s ->
          a
          + (match Cbat_word.to_int (FinSet.cardinality s) with
             | Ok n -> n
             | Error _ -> Stdlib.max_int))
    in
    let promote = fs_total > Utils.fin_set_size in
    let clp_sources =
      List.append clps
        (if promote then List.map fss ~f:pieces_of_finset else [])
    in
    (* A pool of mixed widths has no progression union: it is top at
       the widest (sound; extract/cast over a Many produce leaves of
       the op's own width). *)
    let clp_piece =
      match clp_sources with
      | [] -> None
      | x :: rest ->
        let w = P.bitwidth x in
        if List.for_all rest ~f:(fun q -> Stdlib.Int.equal (P.bitwidth q) w)
        then Some (List.fold rest ~init:x ~f:P.union)
        else Some (P.top (List.fold rest ~init:w ~f:(fun a q -> Stdlib.max a (P.bitwidth q))))
    in
    let fs_piece =
      if promote then None
      else
        match fss with
        | [] -> None
        | x :: rest -> Some (List.fold rest ~init:x ~f:FinSet.union)
    in
    let clp_piece, fs_piece =
      match clp_piece, fs_piece with
      | Some cps, None
        when not (P.is_top cps)
             && not (Cbat_word.gt_int (P.cardinality cps) Utils.fin_set_size)
        -> None, Some (FinSet.of_list ~width:(P.bitwidth cps) (P.elements cps))
      | c, f -> c, f
    in
    (* A bottom stack pool drops against live plain pieces. *)
    let so_piece =
      match so_pool with
      | Some offs when not (P.is_bottom offs) -> Some offs
      | _ -> None
    in
    let leaves =
      List.filter_map
        [ Option.map clp_piece ~f:(fun x -> Clp x);
          Option.map fs_piece ~f:(fun x -> FinSet x);
          Option.map so_piece ~f:(fun x -> StackOff x) ]
        ~f:(fun q -> q)
    in
    (match leaves with
     | [ q ] -> q
     | ps -> Many ps))

(* ---------------- constructors ---------------- *)

let stack_word (offs : Clp.t) : t = StackOff (P.of_progression offs)

let stack_word_i64 (k : int64) : t =
  StackOff (P.singleton (w64_of_i64 k))

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
let plain_bounds (offs : P.t) : (int64 * int64) option =
  let floor = Stdlib.Int64.sub stack_base stack_span in
  let ceil = Stdlib.Int64.add stack_base stack_span in
  let side = function
    | Some w ->
      (match Cbat_word.to_int64 w with
       | Ok v -> checked_add3 stack_base 0L v
       | Error _ -> None)
    | None -> None
  in
  let lo = match P.min_elem offs with
    | Some w -> side (Some w)
    | None -> Some floor in
  let hi = match P.max_elem offs with
    | Some w -> side (Some w)
    | None -> Some ceil in
  match lo, hi with
  | Some lo, Some hi when Stdlib.Int64.compare hi lo >= 0 -> Some (lo, hi)
  | _ -> None

(* The StackOff piece's plain twin: the exact hull as a step-1 piece. *)
let rec to_plain (t : t) : t =
  match t with
  | StackOff offs ->
    (match plain_bounds offs with
     | Some (cmin, cmax)
       when Stdlib.Int64.compare cmin 0L >= 0
            && Stdlib.Int64.compare cmax cmin >= 0 ->
       Clp (P.of_progression
              (Clp.interval ~width:64 (w64_of_i64 cmin) (w64_of_i64 cmax)))
     | _ -> Clp (P.top 64))
  | Many ps ->
    (match canonical (List.map ps ~f:to_plain) with
     | Clp _ | FinSet _ | StackOff _ as q -> q
     | Many ps' -> Many ps')
  | Clp _ | FinSet _ -> t

(* Plain-operand top test. *)
let rec plain_is_top (t : t) : bool =
  match t with
  | Clp ps -> P.is_top ps
  | FinSet _ -> false
  | StackOff offs -> P.is_top offs
  | Many ps -> List.exists ps ~f:plain_is_top

(* The plain single-progression hull of the whole value. *)
let as_clp (t : t) : clp =
  match to_plain t with
  | Clp ps ->
    (match hull_of_pieces ps with
     | Some p -> p
     | None -> Clp.top (Stdlib.max 1 (P.bitwidth ps)))
  | FinSet s -> clp_of_finset s
  | StackOff _ -> Clp.top 64
  | Many ps ->
    let hulls =
      List.filter_map ps ~f:(function
        | FinSet s -> Some (clp_of_finset s)
        | Clp hps -> hull_of_pieces hps
        | StackOff _ -> None
        | Many _ -> None)
    in
    (match hulls with
     | [] -> Clp.top 64
     | p :: rest -> List.fold rest ~init:p ~f:Clp.union)

let of_list ~width l : t =
  canonical
    [ (if List.length l > Utils.fin_set_size then Clp (P.of_list ~width l)
       else FinSet (FinSet.of_list ~width l)) ]

let singleton w : t = FinSet (FinSet.singleton w)

let of_clp (p : clp) : t = canonical [ Clp (P.of_progression p) ]

let bottom i = FinSet (FinSet.bottom i)
let top i = canonical [ Clp (P.top i) ]

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

(* The concrete extrema of a set, before any stack projection. *)
let extrema (t : t) : (Cbat_word.t * Cbat_word.t) option =
  let leaf (q : t) : (Cbat_word.t * Cbat_word.t) option =
    let pair lo hi = Option.map2 lo hi ~f:(fun lo hi -> (lo, hi)) in
    match q with
    | StackOff offs ->
      (match plain_bounds offs with
       | Some (cmin, cmax) -> Some (w64_of_i64 cmin, w64_of_i64 cmax)
       | None -> None)
    | Clp ps -> pair (P.min_elem ps) (P.max_elem ps)
    | FinSet s -> pair (FinSet.min_elem s) (FinSet.max_elem s)
    | Many _ -> None
  in
  let rec go acc (t : t) =
    match t with
    | Many ps -> List.fold ps ~init:acc ~f:go
    | q ->
      (match leaf q, acc with
       | None, acc -> acc
       | Some (lo, hi), None -> Some (lo, hi)
       | Some (lo, hi), Some (alo, ahi) ->
         Some
           ((if Cbat_word.compare lo alo < 0 then lo else alo),
            (if Cbat_word.compare hi ahi > 0 then hi else ahi)))
  in
  go None t

(* Plain extrema are stack facts only when the whole hull is in the
   positive stack band; symbolic offsets are handled separately. *)
let stack_extrema (t : t) : (Cbat_word.t * Cbat_word.t) option =
  let leaves = match t with Many ps -> ps | q -> [ q ] in
  if List.exists leaves ~f:(function StackOff _ -> true | _ -> false) then None
  else
    let circular =
      List.exists leaves ~f:(function
        | Clp ps -> List.exists (P.to_list ps) ~f:Clp.is_circular
        | _ -> false)
    in
    if circular then None
    else
      Option.bind (extrema t) ~f:(fun (lo, hi) ->
          if in_band_words lo hi then Some (lo, hi) else None)

(* Tests stack residency: the symbolic arm, or the plain degraded arm. *)
let in_stack_segment (t : t) : bool =
  match t with
  | StackOff _ -> true
  | Many ps ->
    List.exists ps ~f:(function StackOff _ -> true | _ -> false)
    || Option.is_some (stack_extrema t)
  | _ -> Option.is_some (stack_extrema t)

let relative_bounds (lo : Cbat_word.t) (hi : Cbat_word.t)
    : (int64 * int64) option =
  match Cbat_word.to_int64 lo, Cbat_word.to_int64 hi with
  | Ok loi, Ok hii ->
    (match checked_add3 (Stdlib.Int64.neg stack_base) 0L loi,
            checked_add3 (Stdlib.Int64.neg stack_base) 0L hii with
     | Some rlo, Some rhi -> Some (rlo, rhi)
     | _ -> None)
  | _ -> None

(* Segment-relative bounds: StackOff keeps its exact offsets; a plain
   in-band set maps to its own hull. *)
let stack_bounds (t : t) : (int64 * int64) option =
  match t with
  | StackOff offs ->
    (match P.min_elem offs, P.max_elem offs with
     | Some lo, Some hi ->
       (match Cbat_word.to_int64 lo, Cbat_word.to_int64 hi with
        | Ok loi, Ok hii -> Some (loi, hii)
        | _ -> None)
     | _ -> None)
  | _ ->
    Option.bind (stack_extrema t) ~f:(fun (lo, hi) ->
        relative_bounds lo hi)

let rec cardinality (t : t) : word =
  match t with
  | Clp ps -> P.cardinality ps
  | FinSet s -> FinSet.cardinality s
  | StackOff offs -> stack_cardinality offs
  | Many ps ->
    let width = Stdlib.max 65 (bitwidth t + 1) in
    List.fold ps ~init:(Cbat_word.zero width) ~f:(fun acc q ->
        let c = Cbat_word.cast Bil.UNSIGNED width (cardinality q) in
        let s = Cbat_word.add acc c in
        if Cbat_word.(<) s acc then Cbat_word.ones width else s)

let min_elem (t : t) : word option =
  let leaf (q : t) : word option =
    match q with
    | StackOff offs ->
      Option.map (plain_bounds offs) ~f:(fun (cmin, _) -> w64_of_i64 cmin)
    | Clp ps -> P.min_elem ps
    | FinSet s -> FinSet.min_elem s
    | Many _ -> None
  in
  let rec go acc (t : t) =
    match t with
    | Many ps -> List.fold ps ~init:acc ~f:go
    | q ->
      (match leaf q, acc with
       | None, acc -> acc
       | Some m, None -> Some m
       | Some m, Some a -> Some (if Cbat_word.compare m a < 0 then m else a))
  in
  go None t

let max_elem (t : t) : word option =
  let leaf (q : t) : word option =
    match q with
    | StackOff offs ->
      Option.map (plain_bounds offs) ~f:(fun (_, cmax) -> w64_of_i64 cmax)
    | Clp ps -> P.max_elem ps
    | FinSet s -> FinSet.max_elem s
    | Many _ -> None
  in
  let rec go acc (t : t) =
    match t with
    | Many ps -> List.fold ps ~init:acc ~f:go
    | q ->
      (match leaf q, acc with
       | None, acc -> acc
       | Some m, None -> Some m
       | Some m, Some a -> Some (if Cbat_word.compare m a > 0 then m else a))
  in
  go None t

(* The SEGMENT-RELATIVE extrema of a stack value: a [StackOff]'s offset
   set, or a plain in-band set's segment-relative hull. *)
let offset_extrema (t : t) : (Cbat_word.t * Cbat_word.t) option =
  match t with
  | StackOff offs ->
    (match P.min_elem offs, P.max_elem offs with
     | Some lo, Some hi -> Some (lo, hi)
     | _ -> None)
  | _ ->
    Option.bind (stack_extrema t) ~f:(fun (lo, hi) ->
        Option.map (relative_bounds lo hi) ~f:(fun (rlo, rhi) ->
            (w64_of_i64 rlo, w64_of_i64 rhi)))

(* Signed extrema: the projection is signed-positive, so its signed
   and unsigned extrema agree; a set spanning the sign boundary has
   no signed extremum. *)
let min_elem_signed (t : t) : word option =
  let leaf (q : t) : word option =
    match q with
    | StackOff offs ->
      Option.map (plain_bounds offs) ~f:(fun (cmin, _) -> w64_of_i64 cmin)
    | Clp ps ->
      List.fold (P.to_list ps) ~init:None ~f:(fun acc p ->
          let r =
            match Clp.min_elem_signed p with
            | Some _ as r -> r
            | None ->
              (match Clp.max_elem p with
               | Some mx
                 when Cbat_word.(<) mx (Word_ops.half (Cbat_word.bitwidth mx)) ->
                 Clp.min_elem p
               | _ -> None)
          in
          match r, acc with
          | None, acc -> acc
          | Some m, None -> Some m
          | Some m, Some a ->
            Some
              (if Cbat_word.compare (Cbat_word.signed m) (Cbat_word.signed a) < 0
               then m else a))
    | FinSet s -> FinSet.min_elem_signed s
    | Many _ -> None
  in
  let rec go acc (t : t) =
    match t with
    | Many ps -> List.fold ps ~init:acc ~f:go
    | q ->
      (match leaf q, acc with
       | None, acc -> acc
       | Some m, None -> Some m
       | Some m, Some a ->
         Some
           (if Cbat_word.compare (Cbat_word.signed m) (Cbat_word.signed a) < 0
            then m else a))
  in
  go None t

let max_elem_signed (t : t) : word option =
  let leaf (q : t) : word option =
    match q with
    | StackOff offs ->
      Option.map (plain_bounds offs) ~f:(fun (_, cmax) -> w64_of_i64 cmax)
    | Clp ps ->
      List.fold (P.to_list ps) ~init:None ~f:(fun acc p ->
          let r =
            match Clp.max_elem_signed p with
            | Some _ as r -> r
            | None ->
              (match Clp.min_elem p with
               | Some mn
                 when Cbat_word.(>=) mn (Word_ops.half (Cbat_word.bitwidth mn)) ->
                 Clp.max_elem p
               | _ -> None)
          in
          match r, acc with
          | None, acc -> acc
          | Some m, None -> Some m
          | Some m, Some a ->
            Some
              (if Cbat_word.compare (Cbat_word.signed m) (Cbat_word.signed a) > 0
               then m else a))
    | FinSet s -> FinSet.max_elem_signed s
    | Many _ -> None
  in
  let rec go acc (t : t) =
    match t with
    | Many ps -> List.fold ps ~init:acc ~f:go
    | q ->
      (match leaf q, acc with
       | None, acc -> acc
       | Some m, None -> Some m
       | Some m, Some a ->
         Some
           (if Cbat_word.compare (Cbat_word.signed m) (Cbat_word.signed a) > 0
            then m else a))
  in
  go None t

(* Offset space: the per-sub cell-key universe keys by offsets. *)
let rec splits_by (t : t) (w : Cbat_word.t) =
  match t with
  | StackOff offs | Clp offs -> P.splits_by offs w
  | FinSet s -> FinSet.splits_by s w
  | Many ps -> List.for_all ps ~f:(fun q -> splits_by q w)

(* Hull test: an over-approximation of membership in the projection. *)
let rec elem w (t : t) =
  match t with
  | StackOff offs ->
    (match plain_bounds offs with
     | Some (cmin, cmax) ->
       (match Cbat_word.to_int64 w with
        | Ok wi ->
          Stdlib.Int64.compare wi cmin >= 0
          && Stdlib.Int64.compare wi cmax <= 0
        | _ -> false)
     | None -> false)
  | Clp ps -> P.elem w ps
  | FinSet s -> FinSet.elem w s
  | Many ps -> List.exists ps ~f:(fun q -> elem w q)

(* Materializes the base-0 slice only; the full projection is
   8 MiB of elements. *)
let rec iter (t : t) : word list =
  match t with
  | StackOff offs ->
    List.map (P.elements offs)
      ~f:(fun w -> Cbat_word.add (w64_of_i64 stack_base) w)
  | Clp ps -> P.elements ps
  | FinSet s -> FinSet.iter s
  | Many ps -> List.concat_map ps ~f:iter

(* The fixpoint's convergence check calls this on every var of every
   visit: the leaf arms avoid the derived compare's list machinery. *)
let rec equal (t1 : t) (t2 : t) : bool =
  match t1, t2 with
  | Clp a, Clp b -> P.equal a b
  | FinSet a, FinSet b -> FinSet.equal a b
  | StackOff a, StackOff b -> P.equal a b
  | Many a, Many b ->
    List.length a = List.length b
    && List.for_all2_exn a b ~f:equal
  | _ -> false

let overlap (t1 : t) (t2 : t) : bool =
  let hull (ps : P.t) : clp =
    match hull_of_pieces ps with Some p -> p | None -> Clp.bottom 1 in
  let leaf_pair q1 q2 =
    match q1, q2 with
    | FinSet s1, FinSet s2 -> FinSet.overlap s1 s2
    | FinSet s1, Clp ps2 -> FinSet.overlap_generic (module Clp) s1 (hull ps2)
    | Clp ps1, FinSet s2 -> FinSet.overlap_generic (module Clp) s2 (hull ps1)
    | Clp ps1, Clp ps2 -> P.overlap ps1 ps2
    | _ -> false
  in
  let plain (q : t) : t =
    match q with StackOff _ -> to_plain q | q -> q in
  match plain t1, plain t2 with
  | Many a, Many b ->
    List.exists a ~f:(fun q1 -> List.exists b ~f:(fun q2 -> leaf_pair q1 q2))
  | Many a, q2 -> List.exists a ~f:(fun q1 -> leaf_pair q1 q2)
  | q1, Many b -> List.exists b ~f:(fun q2 -> leaf_pair q1 q2)
  | q1, q2 -> leaf_pair q1 q2

(* ---------------- the plain binop distribution ---------------- *)

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

(* The distributed arithmetic collapses to one progression: multi-piece
   results churn the fixpoint — the 4-piece cap is not associative
   under repeated joins, and in-loop values oscillate between
   incomparable capped forms (measured: five fresh fixpoint backstops on
   du and expr). *)
let binop_pieces (op : binop) (a : P.t) (b : P.t) : P.t =
  let collapse (ps : P.t) : P.t =
    match hull_of_pieces ps with
    | Some p -> P.of_progression p
    | None -> ps
  in
  collapse @@ (match op with
  | Union -> P.union a b
  | Add -> P.add a b
  | Sub -> P.sub a b
  | Mul -> P.mul a b
  | Div -> P.div a b
  | Sdiv -> P.sdiv a b
  | Modulo -> P.modulo a b
  | Smodulo -> P.smodulo a b
  | Lshift -> P.lshift a b
  | Rshift -> P.rshift a b
  | Arshift -> P.arshift a b
  | Logand -> P.logand a b
  | Logor -> P.logor a b
  | Logxor -> P.logxor a b
  | Concat -> P.concat a b)

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

(* One op over one leaf pair; mixed kinds take the piece union of the
   FinSet's elements (exact runs). *)
let op_pair (op : binop) (q1 : t) (q2 : t) : t list =
  match q1, q2 with
  | FinSet s1, FinSet s2 -> [ FinSet (binop_fs op s1 s2) ]
  | Clp ps1, Clp ps2 -> [ Clp (binop_pieces op ps1 ps2) ]
  | Clp ps1, FinSet s2 | FinSet s2, Clp ps1 ->
    [ Clp (binop_pieces op ps1 (pieces_of_finset s2)) ]
  | StackOff _, _ | _, StackOff _ ->
    (* The generic lift is blind to the base; the stack-aware ops route
       around it. *)
    [ Clp (P.top (Stdlib.max (bitwidth q1) (bitwidth q2))) ]
  | Many _, _ | _, Many _ ->
    [ Clp (P.top (Stdlib.max (bitwidth q1) (bitwidth q2))) ]

let lift_binop (op : binop) (t1 : t) (t2 : t) : t =
  match to_plain t1, to_plain t2 with
  | ((Clp _ | FinSet _ | StackOff _) as q1),
    ((Clp _ | FinSet _ | StackOff _) as q2) ->
    canonical (op_pair op q1 q2)
  | p1, p2 ->
    let l1 = match p1 with Many ps -> ps | q -> [ q ] in
    let l2 = match p2 with Many ps -> ps | q -> [ q ] in
    canonical
      (List.concat_map l1 ~f:(fun q1 ->
           List.concat_map l2 ~f:(fun q2 -> op_pair op q1 q2)))

let rec lift_unop (f_clp : P.t -> P.t) (f_fs : fset -> fset) : t -> t = fun t ->
  match t with
  | Clp ps -> canonical [ Clp (f_clp ps) ]
  | FinSet s -> canonical [ FinSet (f_fs s) ]
  | StackOff offs ->
    (match to_plain (StackOff offs) with
     | Clp ps -> canonical [ Clp (f_clp ps) ]
     | FinSet s -> canonical [ FinSet (f_fs s) ]
     | StackOff _ | Many _ -> t)
  | Many ps -> canonical (List.map ps ~f:(fun q -> lift_unop f_clp f_fs q))

(* ---------------- stack queries ---------------- *)

(* The offset piece union of a stack-symbolic value — answers ONLY for
   the symbolic arm; a plain in-band set is None.  The single-progression
   view is the hull (the exact union is the piece list itself). *)
let stack_offsets (t : t) : Clp.t option =
  match t with
  | StackOff offs ->
    (match hull_of_pieces offs with
     | Some p -> Some p
     | None -> Some (Clp.bottom 64))
  | _ -> None

(* The address pieces a memory key fans over: the symbolic offsets'
   piece union, a plain in-band value's segment-relative translation,
   or a plain out-of-band value's own pieces.  None when the value
   names no bounded address line. *)
let address_pieces (t : t) : P.t option =
  match t with
  | StackOff offs -> Some offs
  | _ ->
    (match stack_extrema t with
     | Some (lo, hi) ->
       (match relative_bounds lo hi with
        | Some (rlo, rhi) ->
          Some
            (P.of_progression
               (Clp.interval ~width:64 (w64_of_i64 rlo) (w64_of_i64 rhi)))
        | None -> None)
     | None ->
       (* Out-of-band plain: its own absolute pieces. *)
       (match t with
        | Clp ps -> Some ps
        | FinSet s -> Some (pieces_of_finset s)
        | _ -> None))

(* The value's own address stride: > 1 only when every piece shares one
   bounded stride; everything else is 1. *)
let stride (t : t) : int =
  let of_clp_pieces (ps : P.t) : int option =
    match P.to_list ps with
    | [] -> None
    | p :: rest ->
      if List.exists (p :: rest) ~f:Clp.is_infinite then None
      else
        let s = Clp.step_of p in
        if List.for_all rest ~f:(fun q -> Cbat_word.equal (Clp.step_of q) s)
        then
          (match Cbat_word.to_int64 s with
           | Ok i
             when Stdlib.Int64.compare i 1L > 0
                  && Stdlib.Int64.compare i
                       (Stdlib.Int64.of_int Stdlib.max_int) <= 0 ->
             Some (Stdlib.Int64.to_int i)
           | _ -> None)
        else None
  in
  let leaf_stride (q : t) : int option =
    match q with
    | Clp ps | StackOff ps -> of_clp_pieces ps
    | FinSet s ->
      (match FinSet.iter s with
       | [] | [ _ ] -> Some 1
       | w1 :: rest ->
         let rec common_diff prev d = function
           | [] -> d
           | w :: tl ->
             let d' = Cbat_word.sub w prev in
             if Cbat_word.is_zero d' then None
             else
               match d with
               | None -> common_diff w (Some d') tl
               | Some d0 ->
                 if Cbat_word.equal d0 d' then common_diff w d tl else None
         in
         (match common_diff w1 None rest with
          | Some d ->
            (match Cbat_word.to_int64 d with
             | Ok i ->
               let v = Stdlib.Int64.to_int i in
               if v > 1 then Some v else Some 1
             | Error _ -> Some 1)
          | None -> Some 1))
    | Many _ -> None
  in
  match t with
  | Many ps ->
    (match List.map ps ~f:leaf_stride with
     | [] -> 1
     | strides ->
       if List.for_all strides ~f:(function Some _ -> true | None -> false)
       then
         let s =
           match
             List.find strides ~f:(function
               | Some _ -> true | None -> false)
           with
           | Some (Some s) -> s
           | _ -> 1
         in
         if
           List.for_all strides ~f:(function
             | Some s' -> Stdlib.( = ) s s'
             | None -> false)
         then s
         else 1
       else 1)
  | q ->
    (match leaf_stride q with
     | Some s -> s
     | None -> 1)

let union t1 t2 : t =
  match t1, t2 with
  (* Same sub, same base symbol: the offsets union stays symbolic. *)
  | StackOff o1, StackOff o2 -> canonical [ StackOff (P.union o1 o2) ]
  | StackOff _, _ | _, StackOff _ ->
    lift_binop Union (to_plain t1) (to_plain t2)
  | _ ->
    let l1 = match t1 with Many ps -> ps | q -> [ q ] in
    let l2 = match t2 with Many ps -> ps | q -> [ q ] in
    canonical
      (List.concat_map l1 ~f:(fun q1 ->
           List.concat_map l2 ~f:(fun q2 -> op_pair Union q1 q2)))

(* The plain side of a mixed meet, translated into the offset space
   (positions minus the base): the meet stays stack-symbolic. *)
let plain_offsets (p : t) : P.t option =
  let base = Cbat_word.of_int64 ~width:64 stack_base in
  match p with
  | Clp ps when not (P.is_bottom ps) ->
    Some (P.translate ps (Cbat_word.neg base))
  | FinSet s ->
    let ws = List.map ~f:(fun w -> Cbat_word.sub w base) (FinSet.iter s) in
    (match ws with
     | [] -> Some (P.bottom 64)
     | _ -> Some (pieces_of_words ~width:64 ws))
  | _ -> None

(* Precise meet across representations. *)
let rec intersection (t1 : t) (t2 : t) : t =
  (* Width mismatch returns the wider operand. *)
  if bitwidth t1 <> bitwidth t2 then
    (if bitwidth t1 > bitwidth t2 then t1 else t2)
  else match t1, t2 with
  | StackOff _, q2 when plain_is_top q2 -> t1
  | q1, StackOff _ when plain_is_top q1 -> t2
  | StackOff o1, StackOff o2 ->
    canonical [ StackOff (P.intersection o1 o2) ]
  | StackOff o1, (Clp _ | FinSet _ as plain)
  | (Clp _ | FinSet _ as plain), StackOff o1 ->
    (match plain_offsets plain with
     | Some o2 -> canonical [ StackOff (P.intersection o1 o2) ]
     | None -> intersection (to_plain t1) (to_plain t2))
  | StackOff _, _ | _, StackOff _ ->
    intersection (to_plain t1) (to_plain t2)
  | _ ->
    (* Plain leaves meet pairwise; results merge. *)
    let pair q1 q2 =
      match q1, q2 with
      | FinSet s1, FinSet s2 -> [ FinSet (FinSet.intersection s1 s2) ]
      | FinSet s, Clp ps | Clp ps, FinSet s ->
        [ FinSet
            (FinSet.of_list ~width:(FinSet.bitwidth s)
               (List.filter (FinSet.iter s)
                  ~f:(fun w -> P.elem w ps))) ]
      | Clp ps1, Clp ps2 -> [ Clp (P.intersection ps1 ps2) ]
      | _ -> []
    in
    let l1 = match t1 with Many ps -> ps | q -> [ q ] in
    let l2 = match t2 with Many ps -> ps | q -> [ q ] in
    canonical
      (List.concat_map l1 ~f:(fun q1 ->
           List.concat_map l2 ~f:(fun q2 -> pair q1 q2)))

(* Set difference; the piece union keeps the survivors when the cheap
   side enumerates, the sound identity otherwise. *)
let rec diff (t1 : t) (t2 : t) : t =
  match t1, t2 with
  | StackOff _, _ | _, StackOff _ ->
    diff (to_plain t1) (to_plain t2)
  | _ ->
    let pair q1 q2 =
      if bitwidth q1 <> bitwidth q2 then [ q1 ]
      else
        match q1, q2 with
        | FinSet s1, FinSet s2 -> [ FinSet (FinSet.diff s1 s2) ]
        | FinSet s, Clp ps ->
          [ FinSet
              (FinSet.of_list ~width:(FinSet.bitwidth s)
                 (List.filter (FinSet.iter s)
                    ~f:(fun w -> not (P.elem w ps)))) ]
        | Clp ps, FinSet s -> [ Clp (P.diff ps (pieces_of_finset s)) ]
        | Clp ps1, Clp ps2 -> [ Clp (P.diff ps1 ps2) ]
        | _ -> []
    in
    let l1 = match t1 with Many ps -> ps | q -> [ q ] in
    let l2 = match t2 with Many ps -> ps | q -> [ q ] in
    canonical
      (List.concat_map l1 ~f:(fun q1 ->
           List.concat_map l2 ~f:(fun q2 -> pair q1 q2)))

(* Adds a base-free operand to a stack word: the offsets shift exactly;
   the shift runs progression-level on the hulls (single-progression
   result, one normalization). *)
let stack_lift2 (f : clp -> clp -> clp) (t1 : t) (t2 : t) : t option =
  let hull_of_plain (q : t) : clp option =
    match q with
    | Clp ps -> hull_of_pieces ps
    | FinSet s -> Some (clp_of_finset s)
    | StackOff _ -> None
    | Many _ -> None
  in
  let hull (ps : P.t) : clp =
    match hull_of_pieces ps with
    | Some p -> p
    | None -> Clp.bottom 64
  in
  match t1, t2 with
  | StackOff o1, q2 when bitwidth q2 = 64 ->
    Option.map (hull_of_plain q2)
      ~f:(fun p2 -> StackOff (P.of_progression (f (hull o1) p2)))
  | q1, StackOff o2 when bitwidth q1 = 64 ->
    Option.map (hull_of_plain q1)
      ~f:(fun p1 -> StackOff (P.of_progression (f p1 (hull o2))))
  | _ -> None

let add t1 t2 : t =
  match t1, t2 with
  (* Two stack words: the base appears twice — the plain hulls. *)
  | StackOff _, StackOff _ ->
    lift_binop Add (to_plain t1) (to_plain t2)
  | _ ->
    (match stack_lift2 Clp.add t1 t2 with
     | Some t -> t
     | None -> lift_binop Add t1 t2)

let sub t1 t2 : t =
  match t1, t2 with
  (* Two stack words: the base cancels — the exact offset difference. *)
  | StackOff o1, StackOff o2 -> canonical [ Clp (P.sub o1 o2) ]
  | _ ->
    (match stack_lift2 Clp.sub t1 t2 with
     | Some t -> t
     | None -> lift_binop Sub t1 t2)

(* Only the base's low nibble is a fact (the ABI entry residue): an
   op confined to it computes; an op keeping unknown bits answers
   top.  The relative ops (add, sub, comparisons) keep exact offsets. *)
let certified_bits = 4

let has_stack (t : t) : bool =
  match t with
  | StackOff _ -> true
  | Many ps ->
    List.exists ps ~f:(function StackOff _ -> true | _ -> false)
  | _ -> false

let blind_binop (op : binop) (t1 : t) (t2 : t) : t =
  if has_stack t1 || has_stack t2 then
    top (Stdlib.max (bitwidth t1) (bitwidth t2))
  else lift_binop op t1 t2

let blind_unop (f_clp : P.t -> P.t) (f_fs : fset -> fset) (t : t) : t =
  if has_stack t then top (Stdlib.max 1 (bitwidth t))
  else lift_unop f_clp f_fs t

(* The singleton word of a plain operand, if it is one. *)
let singleton_of (q : t) : word option =
  let pair a b = if Cbat_word.equal a b then Some a else None in
  match q with
  | Clp ps ->
    (match P.min_elem ps, P.max_elem ps with
     | Some a, Some b -> pair a b
     | _ -> None)
  | FinSet s ->
    (match FinSet.min_elem s, FinSet.max_elem s with
     | Some a, Some b -> pair a b
     | _ -> None)
  | StackOff _ | Many _ -> None

(* [f] over the offsets while enumerable; top past the budget. *)
let certified_image ~(width : int) (f : word -> word) (offs : P.t) : t =
  let base = w64_of_i64 stack_base in
  match Cbat_word.to_int (P.cardinality offs) with
  | Ok n when n > 0 && n <= Utils.fin_set_size ->
    of_list ~width
      (List.map (P.elements offs)
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
  match t1, t2 with
  | StackOff offs, (Clp _ | FinSet _ as plain)
  | (Clp _ | FinSet _ as plain), StackOff offs ->
    (match singleton_of plain with
     | Some k when Cbat_word.leq_int k ((1 lsl certified_bits) - 1) ->
       let k64 = Cbat_word.cast Bil.UNSIGNED 64 k in
       certified_image ~width:64 (fun v -> Cbat_word.logand v k64) offs
     | _ -> top 64)
  | StackOff _, _ | _, StackOff _ ->
    top (Stdlib.max (bitwidth t1) (bitwidth t2))
  | _ -> lift_binop Logand t1 t2
let logor t1 t2 = blind_binop Logor t1 t2
let logxor t1 t2 = blind_binop Logxor t1 t2

let lnot t = blind_unop P.lnot FinSet.lnot t
let neg t = blind_unop P.neg FinSet.neg t

let concat t1 t2 =
  if has_stack t1 || has_stack t2 then
    top (bitwidth t1 + bitwidth t2)
  else lift_binop Concat t1 t2

(* ---------------- predicates ---------------- *)

let is_top t =
  match t with
  | Clp ps | StackOff ps -> P.is_top ps
  | FinSet _ -> false
  | Many ps ->
    List.for_all ps ~f:(function
      | Clp ps | StackOff ps -> P.is_top ps
      | _ -> false)
    && List.exists ps ~f:(function
        | Clp _ | StackOff _ -> true
        | _ -> false)

let piece_is_infinite (q : t) =
  match q with
  | Clp ps | StackOff ps -> List.exists (P.to_list ps) ~f:Clp.is_infinite
  | FinSet _ -> false
  | Many _ -> false

let is_infinite t =
  match t with
  | Many ps ->
    (match ps with
     | [] -> false
     | _ -> List.for_all ps ~f:piece_is_infinite)
  | q -> piece_is_infinite q

let shape_pred (which : Clp.t -> bool) (t : t) : bool =
  let leaf q =
    match q with
    | Clp ps | StackOff ps -> List.for_all (P.to_list ps) ~f:which
    | FinSet _ -> false
    | Many _ -> false
  in
  match t with
  | Many ps ->
    (match ps with
     | [] -> false
     | _ -> List.for_all ps ~f:leaf)
  | q -> leaf q

let is_ascending t = shape_pred Clp.is_ascending t
let is_descending t = shape_pred Clp.is_descending t
let is_circular t = shape_pred Clp.is_circular t

let rec precedes t1 t2 : bool =
  match t1, t2 with
  | StackOff o1, StackOff o2 -> P.precedes o1 o2
  | StackOff _, _ | _, StackOff _ ->
    precedes (to_plain t1) (to_plain t2)
  | Clp p1, Clp p2 -> P.precedes p1 p2
  | FinSet s1, FinSet s2 -> FinSet.precedes s1 s2
  | Clp _, FinSet _ -> false
  | FinSet s, Clp _ -> Clp.precedes (clp_of_finset s) (as_clp t2)
  | _ -> Clp.precedes (as_clp t1) (as_clp t2)

(* Widening lives in the offsets, HULLED to one progression: the
   positional piece widen lets the offsets' hull wiggle while pieces
   churn, and the memory keys derived from the hulls never stabilize
   (measured: four fresh fixpoint backstops on expr's regex subs).
   Mixed pairs degrade via the plain hull. *)
let widen_join t1 t2 : t =
  canonical
    [ (match t1, t2 with
      | StackOff o1, StackOff o2 ->
        let hull ps =
          match hull_of_pieces ps with
          | Some p -> p
          | None -> Clp.bottom 64 in
        StackOff (P.of_progression (Clp.widen_join (hull o1) (hull o2)))
      | _ ->
        Clp (P.of_progression (Clp.widen_join (as_clp t1) (as_clp t2)))) ]

let extrapolate_steps ~steps t1 t2 : t =
  canonical
    [ (match t1, t2 with
      | StackOff o1, StackOff o2 ->
        let hull ps =
          match hull_of_pieces ps with
          | Some p -> p
          | None -> Clp.bottom 64 in
        StackOff
          (P.of_progression (Clp.extrapolate_steps ~steps (hull o1) (hull o2)))
      | _ ->
        Clp
          (P.of_progression
             (Clp.extrapolate_steps ~steps (as_clp t1) (as_clp t2)))) ]

let join = union
let meet = intersection

(* Degenerate cast keeps top. *)
let extract ?hi ?lo t =
  let lo_v = Option.value ~default:0 lo in
  if (match hi with Some h -> h < lo_v | None -> false)
  then top (Stdlib.max 1 (bitwidth t))
  else
    match t with
    | StackOff _
      when lo_v = 0 && (match hi with Some 63 -> true | _ -> false) ->
      (* The full-width extract is the identity. *)
      t
    | StackOff offs when Option.value ~default:63 hi < certified_bits ->
      let hi_v = Option.value ~default:63 hi in
      certified_image ~width:(hi_v - lo_v + 1)
        (Cbat_word.extract_exn ~hi:hi_v ~lo:lo_v) offs
    | StackOff _ ->
      let hi_v = Option.value ~default:(bitwidth t - 1) hi in
      top (hi_v - lo_v + 1)
    | _ ->
      lift_unop (P.extract ?hi ?lo) (FinSet.extract ?hi ?lo) t

let cast c sz t =
  if sz <= 0 then top (Stdlib.max 1 (bitwidth t))
  else
    (* A cast at the operand's width is the identity; width changes
       follow the certified-nibble law. *)
    match t with
    | StackOff _ when sz = 64 -> t
    | StackOff offs
      when sz <= certified_bits && not (match c with Bil.HIGH -> true | _ -> false) ->
      certified_image ~width:sz (Cbat_word.cast c sz) offs
    | StackOff _ -> top sz
    | _ -> lift_unop (P.cast c sz) (FinSet.cast c sz) t

let rec get_idx (t : t) : idx =
  match t with
  | StackOff _ -> 64
  | Clp ps ->
    (match hull_of_pieces ps with
     | Some p -> Clp.get_idx p
     | None -> 0)
  | FinSet s -> FinSet.get_idx s
  | Many ps ->
    List.fold ps ~init:0 ~f:(fun a q -> Stdlib.max a (get_idx q))

let pp_leaf ppf (t : t) =
  match t with
  | StackOff offs ->
    Format.fprintf ppf "@[stk%a@]" (fun ppf ps ->
        match hull_of_pieces ps with
        | Some p -> Clp.pp ppf p
        | None -> ())
    offs
  | Clp ps ->
    (match hull_of_pieces ps with
     | Some p -> Clp.pp ppf p
     | None -> Format.fprintf ppf "_|_")
  | FinSet s -> FinSet.pp ppf s
  | Many _ -> ()

let pp ppf (t : t) =
  match t with
  | Many ps ->
    Format.fprintf ppf "@[<1>(%a)@]"
      (fun ppf ts ->
        List.iter ts ~f:(fun q -> Format.fprintf ppf "@;%a" pp_leaf q))
      ps
  | q -> pp_leaf ppf q


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
  checked_add3 stack_base 0L o

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
