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

(* Memory-cell keys: address-range intervals with hull/overlap algebra.
   Split from the memmap (pure interval facts; zero memory-domain deps). *)

open !Core
include Bap.Std

module WordSet = Cbat_clp_set_composite

(* Invariant: lo <= hi. *)
(* Points fit in 64 bits; no big-int key. *)
type point = {pwidth : int; pvalue : int64} [@@deriving bin_io, sexp]

(* The byte hull plus the address stride: step 1 claims every byte
   of the hull; step > 1 claims only the grid lo + i*step.  The origin
   namespaces the key: cells of different origins are disjoint (a VLA
   cell can never collide with a frame/window/rip cell). *)
type t = {origin : Hike_origin.t; lo : point; hi : point; step : int}
[@@deriving bin_io, sexp]
let compare_point (p1 : point) (p2 : point) : int =
    let c = Int.compare p1.pwidth p2.pwidth in
    if c <> 0 then c else Stdlib.Int64.unsigned_compare p1.pvalue p2.pvalue

let equal (p1 : point) (p2 : point) : bool = compare_point p1 p2 = 0
let lt (p1 : point) (p2 : point) : bool = compare_point p1 p2 < 0
let le (p1 : point) (p2 : point) : bool = compare_point p1 p2 <= 0
let gt (p1 : point) (p2 : point) : bool = compare_point p1 p2 > 0
let ge (p1 : point) (p2 : point) : bool = compare_point p1 p2 >= 0
let min (p1 : point) (p2 : point) : point = if le p1 p2 then p1 else p2
let max (p1 : point) (p2 : point) : point = if ge p1 p2 then p1 else p2
(* Int64 equality must be qualified. *)
let is_zero (p : point) : bool = Stdlib.Int64.equal p.pvalue 0L

(* Low [w]-bit mask. *)
let mask (w : int) : int64 =
    if w >= 64 then -1L else Stdlib.Int64.pred (Stdlib.Int64.shift_left 1L w)

(* Wrapping successor/predecessor. *)
let succ (p : point) : point =
    {pwidth = p.pwidth;
     pvalue = if p.pwidth >= 64 then Stdlib.Int64.succ p.pvalue
              else Stdlib.Int64.logand (Stdlib.Int64.succ p.pvalue) (mask p.pwidth)}
let pred (p : point) : point =
    {pwidth = p.pwidth;
     pvalue = if p.pwidth >= 64 then Stdlib.Int64.pred p.pvalue
              else Stdlib.Int64.logand (Stdlib.Int64.pred p.pvalue) (mask p.pwidth)}

(* Point from an address word. *)
let of_word (w : Cbat_word.t) : point option =
    let bw = Cbat_word.bitwidth w in
    if bw <= 64 then
      match Cbat_word.to_int64 w with
      | Ok i -> Some {pwidth = bw; pvalue = Stdlib.Int64.logand i (mask bw)}
      | Error _ -> None
    else None

(* Alignment check for [find']. *)
let aligned_mod (lo : point) (hi : point) (m : int) : bool =
    Stdlib.Int64.equal
      (Stdlib.Int64.logand (Stdlib.Int64.sub hi.pvalue lo.pvalue) (mask m)) 0L

(* Last writable byte. *)
let upper (k : t) : point = k.hi

(* First writable byte. *)
let lower (k : t) : point = k.lo

(* The key's origin namespace. *)
let origin (k : t) : Hike_origin.t = k.origin

(* The cell's stride (>= 1). *)
let step (k : t) : int = k.step

(* The key the landmark table records this cell under. *)
let cell_key (k : t) : Cbat_landmarks.cell_desc =
    let lo = lower k and hi = upper k in
    { Cbat_landmarks.origin = k.origin;
      lo_width = lo.pwidth;
      lo_value = lo.pvalue;
      hi_width = hi.pwidth; hi_value = hi.pvalue; stride = k.step }

(* Strides survive a combination only when both keys name the same
     grid (equal step, congruent lows); any mix demotes to the hull. *)
let combined_step (k1 : t) (k2 : t) : int =
    let s = k1.step in
    if s > 1 && s = k2.step
       && Int.equal k1.lo.pwidth k2.lo.pwidth
       && Stdlib.Int64.equal
            (Stdlib.Int64.rem
               (Stdlib.Int64.sub k1.lo.pvalue k2.lo.pvalue)
               (Stdlib.Int64.of_int s)) 0L
    then s else 1

(* The touched byte hull of a read anchored at [k]: the address set's
   hull grown by the access size — the bytes the read may land on. *)
let expand (k : t) ~(bytes : int) : t =
  if bytes <= 1 then k
  else
    let n = Stdlib.Int64.of_int (bytes - 1) in
    let hi =
      { k.hi with
        pvalue =
          if k.hi.pwidth >= 64 then Stdlib.Int64.add k.hi.pvalue n
          else Stdlib.Int64.logand (Stdlib.Int64.add k.hi.pvalue n) (mask k.hi.pwidth) }
    in
    { k with hi }

(* Whether every point [p] claims is also claimed by [k]: a step-1
   key claims its whole hull; a strided key claims its grid only. *)
let covers (k : t) (p : t) : bool =
    if p.step > 1 then
      k.step = 1 || combined_step k p > 1
    else
      k.step = 1
      || (compare_point p.lo p.hi = 0
          && Int.equal p.lo.pwidth k.lo.pwidth
          && Stdlib.Int64.equal
               (Stdlib.Int64.rem
                  (Stdlib.Int64.sub p.lo.pvalue k.lo.pvalue)
                  (Stdlib.Int64.of_int k.step)) 0L)

(* Sub-range of one owner key: the owner's stride carries. *)
let piece (k : t) ~lo ~hi : t = {origin = k.origin; lo; hi; step = k.step}

(* Orders by origin, then point width, then unsigned value. *)
let compare (k1 : t) (k2 : t) : int =
    let c = Hike_origin.compare k1.origin k2.origin in
    if c <> 0 then c else compare_point (lower k1) (lower k2)

let contains (k : t) (pt : point) : bool =
    le (lower k) pt && le pt (upper k)

(* Cells of different origins are disjoint namespaces. *)
let overlap (k1 : t) (k2 : t) : bool =
    Hike_origin.equal k1.origin k2.origin
    && (contains k1 (lower k2) || contains k2 (lower k1))

(* Cell keys are SEGMENT-RELATIVE for stack-symbolic denotations:
     the shared base makes the offset the per-sub cell identity.  A
     plain denotation keys by its segment-relative pieces or its own.
   The key FANS OUT per piece: each entry names one piece's line, the
   stride is that piece's own bounded progression, and every fanned
   entry stores the full value (the tree stays single-keyed). *)
let of_wordset (p : WordSet.t) : t list =
  let open Monads.Std.Monad.Option.Syntax in
  let of_piece (origin : Hike_origin.t) (q : WordSet.Clp.t) : t option =
    let stride =
      if WordSet.Clp.is_infinite q then 1
      else
        match Cbat_word.to_int64 (WordSet.Clp.step_of q) with
        | Ok i when Stdlib.Int64.compare i 1L > 0
                    && Stdlib.Int64.compare i
                         (Stdlib.Int64.of_int Stdlib.max_int) <= 0 ->
          Stdlib.Int64.to_int i
        | _ -> 1 in
    WordSet.Clp.min_elem q >>= fun lo_w ->
    WordSet.Clp.max_elem q >>= fun hi_w ->
    of_word lo_w >>= fun lo ->
    of_word hi_w >>= fun hi ->
    if le lo hi then Some {origin; lo; hi; step = stride}
    else Some {origin; lo = hi; hi = lo; step = stride}
  in
  match WordSet.address_pieces p with
  | None -> []
  | Some (origin, ps) ->
    List.filter_map (WordSet.Clp.Pieces.to_list ps) ~f:(of_piece origin)

(* Hull of both inputs.  Same-origin only: coalesce never unions across
   origins (the cells stay separate). *)
let union (k1 : t) (k2 : t) : t =
    {origin = k1.origin;
     lo = min (lower k1) (lower k2);
     hi = max (upper k1) (upper k2);
     step = combined_step k1 k2}

let intersection (k1 : t) (k2 : t) : t =
    {origin = k1.origin;
     lo = max (lower k1) (lower k2);
     hi = min (upper k1) (upper k2);
     step = combined_step k1 k2}

(* A read anchored at [q] may join a cell anchored at [c]: a hull
     cell by the width grid, a strided cell by its own stride grid. *)
let read_aligned ~(bits : int) ~(step : int) (c : point) (q : point) : bool =
    if step > 1 then
      Stdlib.Int64.equal
        (Stdlib.Int64.rem (Stdlib.Int64.sub q.pvalue c.pvalue)
           (Stdlib.Int64.of_int step)) 0L
    else aligned_mod c q bits


(* Results may be unordered.  A key of another origin is disjoint. *)
let interval_diff (k1 : t) (k2 : t) : t list =
  if not (Hike_origin.equal k1.origin k2.origin) then [ k1 ]
  else if lt (lower k1) (lower k2) then
    if lt (upper k1) (lower k2) then [ k1 ]
    else if contains k2 (upper k1) then
      [ piece k1 ~lo:k1.lo ~hi:(pred k2.lo) ]
    else
      [ piece k1 ~lo:k1.lo ~hi:(pred k2.lo);
        piece k1 ~lo:(succ k2.hi) ~hi:k1.hi ]
  else if contains k2 (lower k1) then
    if gt (upper k1) (upper k2) then
      [ piece k1 ~lo:(succ k2.hi) ~hi:k1.hi ]
    else []
  else [ k1 ] (* disjoint *)

(* Gaps between cells within [k]. *)
let gaps (v : 'a) (k : t) (s : (t * 'a) seq) : (t * 'a) seq =
    (* Only the same-origin cells can cover [k]'s bytes. *)
    let s = Seq.filter s ~f:(fun (k', _) -> Hike_origin.equal k'.origin k.origin) in
    (* Next point, if any. *)
    let next_pt pt =
      let next = succ pt in
      Option.some_if (not (is_zero next)) next in
    (* A gap ends before the next cell's first byte; after a cell the
       walk resumes past its last byte.  A cell at the zero point has no
       byte before it ([pred] would wrap). *)
    let running_step' pt (k',_) =
      if gt pt k.hi then Seq.Step.Done
      else
        let after =
          if ge (upper k') pt then next_pt (upper k') else Some pt in
        if is_zero (lower k') then Seq.Step.Skip {state = after}
        else
        let hi = min k.hi (pred (lower k')) in
        if le pt hi then Seq.Step.Yield
            {value = (piece k ~lo:pt ~hi:hi, v); state = after}
        else Seq.Step.Skip {state = after}
    in
    (* Final gap. *)
    let finishing_step' pt =
      if le pt k.hi then Seq.Step.Yield
          {value = (piece k ~lo:pt ~hi:(k.hi), v); state = next_pt k.hi}
      else Seq.Step.Done in
    Seq.unfold_with_and_finish s ~init:(Some k.lo)
      ~running_step:(Option.value_map
                       ~default:(fun _ -> Seq.Step.Done)
                       ~f:running_step')
      ~inner_finished:(fun x -> x)
      ~finishing_step:(Option.value_map
                         ~default:Seq.Step.Done
                         ~f:finishing_step')

type side = Left | Right | Both_sides
module Seq_ME = Seq.Merge_with_duplicates_element

type section =
    | Left_Mid of t * t
    | Left_Right of t * t
    | Mid_Right of t * t
    | Left_Mid_Right of t * t * t


(* [sections]: exclusive stretches keep their owner's stride; the
   shared stretch carries the combined stride (the demoted hull when
   the grids differ).  Ordered relations: disjoint either way, one
   hull containing the other's head, or shared bounds. *)
let sections (k1 : t) (k2 : t) : side * t * ((t, t) Seq_ME.t) option =
  let mix lo hi = {origin = k1.origin; lo; hi; step = combined_step k1 k2} in
  if not (Hike_origin.equal k1.origin k2.origin) then
    (* Disjoint namespaces. *)
    (if compare k1 k2 < 0 then Left, k1, Some (Seq_ME.Right k2)
     else Right, k2, Some (Seq_ME.Left k1))
  else if lt k1.hi k2.lo then Left, k1, Some (Seq_ME.Right k2)
  else if lt k2.hi k1.lo then Right, k2, Some (Seq_ME.Left k1)
  else if lt k1.lo k2.lo then
    (* k1's head is exclusive; the shared stretch merges. *)
    let res = piece k1 ~lo:k1.lo ~hi:(pred k2.lo) in
    let mid1 = mix k2.lo k1.hi in
    Left, res, Some (Seq_ME.Both (mid1, k2))
  else if lt k2.lo k1.lo then
    (* k2's head is exclusive; the shared stretch merges. *)
    let res = piece k2 ~lo:k2.lo ~hi:(pred k1.lo) in
    let mid2 = mix k1.lo k2.hi in
    Right, res, Some (Seq_ME.Both (k1, mid2))
  else if lt k1.hi k2.hi then
    (* Equal lows: k2's tail is exclusive. *)
    let mid2 = piece k2 ~lo:(succ k1.hi) ~hi:k2.hi in
    Both_sides, mix k1.lo k1.hi, Some (Seq_ME.Right mid2)
  else if lt k2.hi k1.hi then
    (* Equal lows: k1's tail is exclusive. *)
    let mid1 = piece k1 ~lo:(succ k2.hi) ~hi:k1.hi in
    Both_sides, mix k2.lo k2.hi, Some (Seq_ME.Left mid1)
  else (* equal highs: one shared stretch, nothing exclusive *)
    Both_sides, mix k1.lo k1.hi, None

(* Merge two key sequences with sides. *)
let seq_product (s1 : t seq) (s2 : t seq) : (side * t) seq =
    let combined = Seq.merge_with_duplicates s1 s2 ~compare:compare in
    Seq.unfold_step ~init:combined ~f:begin fun s ->
      Option.value_map ~default:Seq.Step.Done (Seq.next s) ~f: begin
        fun (hd, tl) -> match hd with
          | Seq_ME.Left k1 -> Seq.Step.Yield {value = (Left, k1); state = tl}
          | Seq_ME.Right k2 -> Seq.Step.Yield {value = (Right, k2); state = tl}
          | Seq_ME.Both (k1, k2) ->
            let s, k, mrest = sections k1 k2 in
            let tl' = Option.fold mrest ~init:tl ~f:Seq.shift_right in
            Seq.Step.Yield {value = (s, k); state = tl'}
      end
    end

let pp_point ppf (p : point) =
    Format.fprintf ppf "0x%Lx" p.pvalue
let pp ppf (k : t) = Format.fprintf ppf "@[[%a@ ...@ %a]@]" pp_point k.lo pp_point k.hi


