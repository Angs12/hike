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
   namespaces the key: [None] is the absolute line (plain and Rip
   addresses), Stack and Fs have their own. *)
type t = {origin : Hike_origin.t option; lo : point; hi : point; step : int}
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

(* [p] moved [n] along its line, wrapping. *)
let add (p : point) (n : int64) : point =
  let v = Stdlib.Int64.add p.pvalue n in
  { p with
    pvalue = (if p.pwidth >= 64 then v else Stdlib.Int64.logand v (mask p.pwidth)) }

let succ (p : point) : point = add p 1L
let pred (p : point) : point = add p (-1L)

(* Point from an address word. *)
let of_word (w : Cbat_word.t) : point option =
    let bw = Cbat_word.bitwidth w in
    if bw <= 64 then
      match Cbat_word.to_int64_opt w with
      | Some i -> Some {pwidth = bw; pvalue = Stdlib.Int64.logand i (mask bw)}
      | None -> None
    else None

(* Last writable byte. *)
let upper (k : t) : point = k.hi

(* First writable byte. *)
let lower (k : t) : point = k.lo

(* The key's origin namespace. *)
let origin (k : t) : Hike_origin.t option = k.origin

(* The cell's stride (>= 1). *)
let step (k : t) : int = k.step

(* The key the landmark table records this cell under. *)
let cell_key (k : t) : Cbat_landmarks.cell_desc =
    let lo = lower k and hi = upper k in
    { Cbat_landmarks.origin = k.origin;
      lo_width = lo.pwidth;
      lo_value = lo.pvalue;
      hi_width = hi.pwidth; hi_value = hi.pvalue; stride = k.step }

(* Two lows name one grid of step [s]: equal widths, values congruent
   modulo [s]. *)
let congruent (a : point) (b : point) (s : int) : bool =
  Int.equal a.pwidth b.pwidth
  && Stdlib.Int64.equal
       (Stdlib.Int64.rem (Stdlib.Int64.sub a.pvalue b.pvalue)
          (Stdlib.Int64.of_int s)) 0L

(* Strides survive a combination only when both keys name the same
     grid (equal step, congruent lows); any mix demotes to the hull. *)
let combined_step (k1 : t) (k2 : t) : int =
  let s = k1.step in
  if s > 1 && s = k2.step && congruent k1.lo k2.lo s then s else 1

(* The touched byte hull of a read anchored at [k]: the address set's
   hull grown by the access size — the bytes the read may land on. *)
let expand (k : t) ~(bytes : int) : t =
  if bytes <= 1 then k
  else
    { k with hi = add k.hi (Stdlib.Int64.of_int (bytes - 1)) }

(* Whether every point [p] claims is also claimed by [k]: a step-1
   key claims its whole hull; a strided key claims its grid only. *)
let covers (k : t) (p : t) : bool =
  if p.step > 1 then
    k.step = 1 || combined_step k p > 1
  else
    k.step = 1
    || (compare_point p.lo p.hi = 0 && congruent p.lo k.lo k.step)

(* [k] moved [bytes] up its line, stride kept; None when the move would
   wrap one bound past the other. *)
let shift (k : t) ~(bytes : int) : t option =
  let n = Stdlib.Int64.of_int bytes in
  let lo = add k.lo n and hi = add k.hi n in
  if le lo hi then Some { k with lo; hi } else None

(* [k] from the first point of its grid at or above [p]; None when no
   grid point remains. *)
let grid_from (k : t) (p : point) : t option =
  if le p k.lo then Some k
  else
    let lo =
      if k.step = 1 then Some p
      else
        let step = Stdlib.Int64.of_int k.step in
        let r = Stdlib.Int64.unsigned_rem (Stdlib.Int64.sub p.pvalue k.lo.pvalue) step in
        if Stdlib.Int64.equal r 0L then Some p
        else
          let up = add p (Stdlib.Int64.sub step r) in
          Option.some_if (ge up p) up in
    Option.bind lo ~f:(fun lo -> Option.some_if (le lo k.hi) {k with lo})

(* Sub-range of one owner key: the owner's stride carries and both ends
   sit on its grid, so a split key claims only points the owner claimed.
   None when no grid point lies in [lo, hi]. *)
let piece (k : t) ~lo ~hi : t option =
  Option.bind (grid_from k lo) ~f:(fun g ->
      if gt g.lo hi then None
      else if g.step = 1 || le g.hi hi then
        Some {g with hi = min g.hi hi}
      else
        let span = Stdlib.Int64.sub hi.pvalue g.lo.pvalue in
        let down = Stdlib.Int64.sub span
            (Stdlib.Int64.unsigned_rem span (Stdlib.Int64.of_int g.step)) in
        Some {g with hi = add g.lo down})

(* A TOTAL order (origin, then lower, upper, stride): the interval tree's
   [add] treats [compare = 0] as identity and replaces the node, so a
   partial order would silently drop a cell sharing origin+lower with a
   different extent. *)
let compare (k1 : t) (k2 : t) : int =
    let c = Option.compare Hike_origin.compare k1.origin k2.origin in
    let c = if c <> 0 then c else compare_point (lower k1) (lower k2) in
    let c = if c <> 0 then c else compare_point (upper k1) (upper k2) in
    if c <> 0 then c else Int.compare (step k1) (step k2)

let contains (k : t) (pt : point) : bool =
    le (lower k) pt && le pt (upper k)

(* Cells of different origins are disjoint namespaces. *)
let overlap (k1 : t) (k2 : t) : bool =
    Option.equal Hike_origin.equal k1.origin k2.origin
    && (contains k1 (lower k2) || contains k2 (lower k1))

(* Cell keys are SEGMENT-RELATIVE for stack-symbolic denotations:
     the shared base makes the offset the per-sub cell identity.  A
     plain denotation keys by its own absolute pieces.
   The key FANS OUT per piece of every leaf (a mixed value names each
   leaf's line): each entry names one piece's line, the stride is that
   piece's own bounded progression, and every fanned entry stores the
   full value (the tree stays single-keyed).  An empty piece names no
   address; a piece too wide for a point keys its whole line. *)
let of_wordset (p : WordSet.t) : t list =
  let of_piece (origin : Hike_origin.t option) (q : WordSet.Clp.t) : t option =
    let stride =
      if WordSet.Clp.is_infinite q then 1
      else
        match Cbat_word.to_int64_opt (WordSet.Clp.step_of q) with
        | Some i when Stdlib.Int64.compare i 1L > 0
                      && Stdlib.Int64.compare i
                           (Stdlib.Int64.of_int Stdlib.max_int) <= 0 ->
          Stdlib.Int64.to_int i
        | _ -> 1 in
    match WordSet.Clp.min_elem q, WordSet.Clp.max_elem q with
    | Some lo_w, Some hi_w -> (
      match of_word lo_w, of_word hi_w with
      | Some lo, Some hi ->
        if le lo hi then Some {origin; lo; hi; step = stride}
        else Some {origin; lo = hi; hi = lo; step = stride}
      | _ -> None)
    | _ -> None
  in
  let whole_line origin =
    { origin; lo = { pwidth = 64; pvalue = 0L }; hi = { pwidth = 64; pvalue = -1L };
      step = 1 } in
  List.concat_map (WordSet.address_groups p) ~f:(fun (origin, ps) ->
      List.filter_map (WordSet.Clp.Pieces.to_list ps) ~f:(fun q ->
          if WordSet.Clp.is_bottom q then None
          else
            match of_piece origin q with
            | Some _ as k -> k
            | None -> Some (whole_line origin)))

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


(* Results may be unordered.  A key of another origin is disjoint. *)
let interval_diff (k1 : t) (k2 : t) : t list =
  let pieces ps = List.filter_opt ps in
  if not (Option.equal Hike_origin.equal k1.origin k2.origin) then [ k1 ]
  else if lt (lower k1) (lower k2) then
    if lt (upper k1) (lower k2) then [ k1 ]
    else if contains k2 (upper k1) then
      pieces [ piece k1 ~lo:k1.lo ~hi:(pred k2.lo) ]
    else
      pieces [ piece k1 ~lo:k1.lo ~hi:(pred k2.lo);
               piece k1 ~lo:(succ k2.hi) ~hi:k1.hi ]
  else if contains k2 (lower k1) then
    if gt (upper k1) (upper k2) then
      pieces [ piece k1 ~lo:(succ k2.hi) ~hi:k1.hi ]
    else []
  else [ k1 ] (* disjoint *)

(* Gaps between cells within [k]. *)
let gaps (v : 'a) (k : t) (s : (t * 'a) seq) : (t * 'a) seq =
    (* Only the same-origin cells can cover [k]'s bytes. *)
    let s = Seq.filter s ~f:(fun (k', _) -> Option.equal Hike_origin.equal k'.origin k.origin) in
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
        match if le pt hi then piece k ~lo:pt ~hi else None with
        | Some gap -> Seq.Step.Yield {value = (gap, v); state = after}
        | None -> Seq.Step.Skip {state = after}
    in
    (* Final gap. *)
    let finishing_step' pt =
      if le pt k.hi then
        match piece k ~lo:pt ~hi:k.hi with
        | Some gap -> Seq.Step.Yield {value = (gap, v); state = next_pt k.hi}
        | None -> Seq.Step.Done
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

(* Sweep sorted region streams into exclusive prefixes and shared
   overlaps. Unconsumed tails keep their owner's grid and meet the next
   region of the other stream; only the shared stretch takes the
   combined stride. *)
let seq_product (s1 : t seq) (s2 : t seq) : (side * t) seq =
  let cons_tail tail rest = Option.fold tail ~init:rest ~f:(fun r t -> Seq.cons t r) in
  Seq.unfold_step ~init:(s1, s2) ~f:(fun (s1, s2) ->
      let emit side key s1 s2 =
        Seq.Step.Yield {value = (side, key); state = (s1, s2)} in
      match Seq.next s1, Seq.next s2 with
      | None, None -> Seq.Step.Done
      | Some (a, rest), None -> emit Left a rest s2
      | None, Some (b, rest) -> emit Right b s1 rest
      | Some (a, rest1), Some (b, rest2) ->
        if not (Option.equal Hike_origin.equal a.origin b.origin) then
          if compare a b < 0 then emit Left a rest1 s2
          else emit Right b s1 rest2
        else if lt a.hi b.lo then emit Left a rest1 s2
        else if lt b.hi a.lo then emit Right b s1 rest2
        else if lt a.lo b.lo then
          let rest1 = cons_tail (grid_from a b.lo) rest1 in
          (match piece a ~lo:a.lo ~hi:(pred b.lo) with
           | Some prefix -> emit Left prefix rest1 s2
           | None -> Seq.Step.Skip {state = (rest1, s2)})
        else if lt b.lo a.lo then
          let rest2 = cons_tail (grid_from b a.lo) rest2 in
          (match piece b ~lo:b.lo ~hi:(pred a.lo) with
           | Some prefix -> emit Right prefix s1 rest2
           | None -> Seq.Step.Skip {state = (s1, rest2)})
        else
          let hi = min a.hi b.hi in
          let shared = {a with hi; step = combined_step a b} in
          let remaining k rest =
            if equal k.hi hi then rest
            else cons_tail (grid_from k (succ hi)) rest in
          emit Both_sides shared (remaining a rest1) (remaining b rest2))

let pp_point ppf (p : point) =
    Format.fprintf ppf "0x%Lx" p.pvalue
let pp ppf (k : t) = Format.fprintf ppf "@[[%a@ ...@ %a]@]" pp_point k.lo pp_point k.hi


