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

open !Core_kernel
include Bap.Std

module WordSet = Cbat_clp_set_composite

  (* Invariant: lo <= hi. *)
  (* Points fit in 64 bits; no big-int key. *)
  type point = {pwidth : int; pvalue : int64} [@@deriving bin_io, sexp]

  type t = {lo : point; hi : point} [@@deriving bin_io, sexp]  (* Unsigned order: width, then value. *)
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

  let create ~lo ~hi : t Or_error.t =
    if le lo hi then Result.Ok {lo; hi}
    else Or_error.error "attempted to create key with lo above hi"
        (lo, hi) (fun (lo, hi) -> Sexp.List[sexp_of_point lo;
                                            sexp_of_point hi])

  (* Last writable byte. *)
  let upper (k : t) : point = k.hi

  (* First writable byte. *)
  let lower (k : t) : point = k.lo

  (* Compares lowest addresses; ignores widths. *)
  let compare (k1 : t) (k2 : t) : int =
    compare_point (lower k1) (lower k2)

  let contains (k : t) (pt : point) : bool =
    le (lower k) pt && le pt (upper k)

  let overlap (k1 : t) (k2 : t) : bool =
    contains k1 (lower k2) || contains k2 (lower k1)

  (* Cell keys are SEGMENT-RELATIVE for stack-symbolic denotations (T3):
     the shared base makes the offset the per-sub cell identity; plain
     denotations (foreign addresses, and the degraded in-band arm via
     its relativized hull) key by their own extrema. *)
  let of_wordset (p : WordSet.t) : t option =
    let p = match WordSet.relativize p with Some rel -> rel | None -> p in
    let open Monads.Std.Monad.Option.Syntax in
    WordSet.min_elem p >>= fun lo_w ->
    WordSet.max_elem p >>= fun hi_w ->
    (match of_word lo_w, of_word hi_w with
     | Some lo, Some hi when le lo hi -> Some {lo; hi}
     | Some lo, Some hi -> Some {lo = hi; hi = lo} (* order-independent hull *)
     | _ -> None)

  (* Hull of both inputs. *)
  let union (k1 : t) (k2 : t) : t =
    {lo = min (lower k1) (lower k2);
     hi = max (upper k1) (upper k2)}

  let intersection (k1 : t) (k2 : t) : t =
    {lo = max (lower k1) (lower k2);
     hi = min (upper k1) (upper k2)}


  type 'a up_to_two = [`none | `one of 'a | `two of 'a * 'a]

  (* Results may be unordered. *)
  let interval_diff (k1 : t) (k2 : t) : t up_to_two =
    if lt (lower k1) (lower k2) then
      if lt (upper k1) (lower k2) then `one k1
      else if contains k2 (upper k1) then
        `one {lo=k1.lo; hi=pred k2.lo}
      else `two ({lo=k1.lo; hi=pred k2.lo},
                 {lo=succ k2.hi; hi=k1.hi})
    else if contains k2 (lower k1) then
      if gt (upper k1) (upper k2) then
        `one {lo=succ k2.hi; hi=k1.hi}
      else `none
    else `one k1 (* disjoint *)

  (* Gaps between cells within [k]. *)
  let gaps (v : 'a) (k : t) (s : (t * 'a) seq) : (t * 'a) seq =
    (* Next point, if any. *)
    let next_pt pt =
      let next = succ pt in
      Option.some_if (not (is_zero next)) next in
    (* Next gap from a start point. *)
    let running_step' pt (k',_) =
      let hi = min k.hi k'.lo in
      if gt pt k.hi then Seq.Step.Done
      else if le pt hi then Seq.Step.Yield
          {value = ({lo=pt; hi}, v); state = next_pt hi}
      else Seq.Step.Skip {state = next_pt (max hi pt)} in
    (* Final gap. *)
    let finishing_step' pt =
      if le pt k.hi then Seq.Step.Yield
          {value = ({lo = pt; hi = k.hi}, v); state = next_pt k.hi}
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


  let sections (k1 : t) (k2 : t) : side * t * ((t, t) Seq_ME.t) option =
    if lt k1.hi k2.lo then Left, k1, Some (Seq_ME.Right k2)
    else if lt k2.hi k1.lo then Right, k2, Some (Seq_ME.Left k1)
    else if lt k1.lo k2.lo then
      let res = {lo=k1.lo;hi=pred k2.lo} in
      let newK1 = {lo=k2.lo;hi=k1.hi} in
      Left, res, Some (Seq_ME.Both (newK1, k2))
    else if lt k2.lo k1.lo then
      let res = {lo=k2.lo;hi=pred k1.lo} in
      let newK2 = {lo=k1.lo;hi=k2.hi} in
      Right, res, Some (Seq_ME.Both (k1, newK2))
    else if lt k1.hi k2.hi then (* equal lows *)
      let newK2 = {lo=succ k1.hi;hi=k2.hi} in
      Both_sides, k1, Some (Seq_ME.Right newK2)
    else if lt k2.hi k1.hi then
      let newK1 = {lo=succ k2.hi;hi=k1.hi} in
      Both_sides, k2, Some (Seq_ME.Left newK1)
    else (* equal highs *)
      Both_sides, k1, None

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


