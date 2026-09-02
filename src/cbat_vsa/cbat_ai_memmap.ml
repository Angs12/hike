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
include Bap.Std

module Fn = Core_kernel.Fn
module Sexp = Core_kernel.Sexp
module Option = Core_kernel.Option
module Or_error = Core_kernel.Or_error
module Result = Core_kernel.Result
module Binable = Core_kernel.Binable

module Lattice = Cbat_lattice_intf
module WordSet = Cbat_clp_set_composite
module Utils = Cbat_vsa_utils
module Map_lattice = Cbat_map_lattice
module Word_ops = Cbat_word_ops

(* * We assume that all memories are byte-addressable. *)
let addressable_width = 8

module Key = struct
  (* invariant: lo <= hi TODO: allow empty intervals? TODO: use Clps/WordSets? *)
  (* ALL address points are NATIVE — the program architecture's address size (the Target's [data_addr_size], set at production setup) is at most the host native word (64 bits): addresses cannot be larger, so no big-int key. *)
  type point = {pwidth : int; pvalue : int64} [@@deriving bin_io, sexp]

  type t = {lo : point; hi : point} [@@deriving bin_io, sexp]  (* the unsigned total order: width first (widths never mix within a map; the tiebreak is defensive), then the unsigned value. Uses the STDLIB Int64 (Stdlib.Int64) — Base's Int64 renames the bit ops and lacks [unsigned_compare]. *)
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
  (* NB: bare [=] is int-monomorphic in this scope (Base's top-level [include Int.O] shadows it) — int64 equality must be qualified. *)
  let is_zero (p : point) : bool = Stdlib.Int64.equal p.pvalue 0L

  (* the low [w]-bit mask (w <= 64; w = 64 -> all ones) *)
  let mask (w : int) : int64 =
    if w >= 64 then -1L else Stdlib.Int64.pred (Stdlib.Int64.shift_left 1L w)

  (* wrap-around successor/predecessor at [pwidth] (Word.succ/pred semantics: max succ -> 0, 0 pred -> max) *)
  let succ (p : point) : point =
    {pwidth = p.pwidth;
     pvalue = if p.pwidth >= 64 then Stdlib.Int64.succ p.pvalue
              else Stdlib.Int64.logand (Stdlib.Int64.succ p.pvalue) (mask p.pwidth)}
  let pred (p : point) : point =
    {pwidth = p.pwidth;
     pvalue = if p.pwidth >= 64 then Stdlib.Int64.pred p.pvalue
              else Stdlib.Int64.logand (Stdlib.Int64.pred p.pvalue) (mask p.pwidth)}

  (* [of_word w]: A native point from an address word. *)
  let of_word (w : word) : point option =
    let bw = Word.bitwidth w in
    if bw <= 64 then
      match Word.to_int64 w with
      | Ok i -> Some {pwidth = bw; pvalue = Stdlib.Int64.logand i (mask bw)}
      | Error _ -> None
    else None

  (* [(hi - lo) mod m = 0] — the [find'] key-alignment check. [m] is the cell index width (a power of two, <= 64), so the mod is the low-bit mask; the subtraction is the unsigned wrap subtraction (lo <= hi by construction — min/max of the same pair). *)
  let aligned_mod (lo : point) (hi : point) (m : int) : bool =
    Stdlib.Int64.equal
      (Stdlib.Int64.logand (Stdlib.Int64.sub hi.pvalue lo.pvalue) (mask m)) 0L

  let create ~lo ~hi : t Or_error.t =
    if le lo hi then Result.Ok {lo; hi}
    else Or_error.error "attempted to create key with lo above hi"
        (lo, hi) (fun (lo, hi) -> Sexp.List[sexp_of_point lo;
                                            sexp_of_point hi])

  (* The upper point is the last (byte) address that is writable at this key. *)
  let upper (k : t) : point = k.hi

  (* The first writable byte is at the lowest address in the key *)
  let lower (k : t) : point = k.lo

  (* This function does not consider the widths since it compares the lowest writable addresses in the keys. *)
  let compare (k1 : t) (k2 : t) : int =
    compare_point (lower k1) (lower k2)

  let contains (k : t) (pt : point) : bool =
    le (lower k) pt && le pt (upper k)

  let overlap (k1 : t) (k2 : t) : bool =
    contains k1 (lower k2) || contains k2 (lower k1)

  let of_wordset (p : WordSet.t) : t option =
    let open Monads.Std.Monad.Option.Syntax in
    WordSet.min_elem p >>= fun lo_w ->
    WordSet.max_elem p >>= fun hi_w ->
    (match of_word lo_w, of_word hi_w with
     | Some lo, Some hi when le lo hi -> Some {lo; hi}
     | Some lo, Some hi -> Some {lo = hi; hi = lo} (* hull is order-independent *)
     | _ -> None)

  (* Produces a key that contains all addresses in both inputs. *)
  let union (k1 : t) (k2 : t) : t =
    {lo = min (lower k1) (lower k2);
     hi = max (upper k1) (upper k2)}

  let intersection (k1 : t) (k2 : t) : t =
    {lo = max (lower k1) (lower k2);
     hi = min (upper k1) (upper k2)}


  type 'a up_to_two = [`none | `one of 'a | `two of 'a * 'a]

  (* resulting intervals may not be ordered *)
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
    else `one k1 (* lower k1 > upper k2 *)

  (* Takes an ordered sequence of key-value pairs and returns an ordered sequence of the gaps between them paired with the input value within the bounds of k. TODO: check all cases at the bounds (hi = 0xFFF...) *)
  let gaps (v : 'a) (k : t) (s : (t * 'a) seq) : (t * 'a) seq =
    (* compute what (and whether) the next lower point is *)
    let next_pt pt =
      let next = succ pt in
      Option.some_if (not (is_zero next)) next in
    (* given a low point to start from, generate the next element in the sequence. *)
    let running_step' pt (k',_) =
      let hi = min k.hi k'.lo in
      if gt pt k.hi then Seq.Step.Done
      else if le pt hi then Seq.Step.Yield
          {value = ({lo=pt; hi}, v); state = next_pt hi}
      else Seq.Step.Skip {state = next_pt (max hi pt)} in
    (* computes the last gap after the input sequence ends *)
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
    else if lt k1.hi k2.hi then (* k1.lo = k2.lo *)
      let newK2 = {lo=succ k1.hi;hi=k2.hi} in
      Both_sides, k1, Some (Seq_ME.Right newK2)
    else if lt k2.hi k1.hi then
      let newK1 = {lo=succ k2.hi;hi=k1.hi} in
      Both_sides, k2, Some (Seq_ME.Left newK1)
    else (* k1.hi = k2.hi *)
      Both_sides, k1, None

  (* takes two ordered sequences of non-overlapping keys and returns an ordered sequence of non-overlapping keys with the side they came from. *)
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


end

(* Represents the values stored at each key in an internal interval tree. Contains a WordSet and ancillary data. *)
module Val : sig

  type t [@@deriving bin_io, sexp, compare]

  module Idx : Lattice.S_semi with type t = WordSet.idx * endian

  include Lattice.S_indexed with type t := t and type idx = Idx.t

  val create : WordSet.t -> endian -> t

  val data : t -> WordSet.t

  val idx_equal : idx -> idx -> bool

  val is_top : t -> bool
  val is_bottom : t -> bool

  val join_at : idx -> t -> t -> t
  val meet_at : idx -> t -> t -> t


  val join_poly : t -> t -> t
  val meet_poly : t -> t -> t

  val pp : Format.formatter -> t -> unit

end = struct

  type idx = WordSet.idx * endian

  module Idx : Lattice.S_semi with type t = idx = struct

    type t = idx

    let top = 1, BigEndian

    let join (w1, e1 : t) (w2, e2 : t) : t =
      if Bitvector.compare_endian e1 e2 = 0
      then min w1 w2, e1
      else min addressable_width (min w1 w2), e1

    let widen_join = join

    let precedes (w1, e1 : t) (w2, e2 : t) : bool =
      w1 >= w2 && (w2 <= addressable_width || Bitvector.compare_endian e1 e2 = 0)

    let equal i1 i2 : bool = precedes i1 i2 && precedes i2 i1

    let sexp_of_t (w, e : t) : Sexp.t =
      let edstr = Word_ops.endian_string e in
      Sexp.List [Sexp.Atom (string_of_int w); Sexp.Atom edstr]

  end

  type t = {data : WordSet.t; endian : endian} [@@deriving bin_io, sexp, compare]

  let create data endian = {data; endian}

  let data (v : t) : WordSet.t = v.data

  let get_idx (v : t) : idx = WordSet.bitwidth v.data, v.endian

  let idx_equal (w1, e1 : idx) (w2, e2 : idx) : bool =
    w1 = w2 && (w1 <= addressable_width || Bitvector.compare_endian e1 e2 = 0)

  let lift_in (f : WordSet.t -> 'a) (v : t) : 'a = f v.data

  let lift (f : WordSet.t -> WordSet.t) (v : t) : t = {data = lift_in f v; endian = v.endian}

  let top (w, e : idx) : t = {data = WordSet.top w; endian = e}
  let bottom (w, e : idx) : t = {data = WordSet.bottom w; endian = e}

  (* Ported from the prior-art cbat_value_set fork. *)
  let equal v1 v2 =
    if idx_equal (get_idx v1) (get_idx v2)
    then WordSet.equal v1.data v2.data
    else false

  let precedes v1 v2 =
    if idx_equal (get_idx v1) (get_idx v2)
    then WordSet.precedes v1.data v2.data
    else false

  (* Joining/meeting two memory cells whose indices (width, endian) differ is unsound to perform directly: cells of the same width but different endianness (or different widths above the addressable unit) represent incompatible abstractions. *)
  let join (v1 : t) (v2 : t) : t =
    if idx_equal (get_idx v1) (get_idx v2)
    then {data = WordSet.join v1.data v2.data; endian = v1.endian}
    else {data = WordSet.top (max (WordSet.bitwidth v1.data) (WordSet.bitwidth v2.data));
          endian = v1.endian}

  let meet (v1 : t) (v2 : t) : t =
    if idx_equal (get_idx v1) (get_idx v2)
    then {data = WordSet.meet v1.data v2.data; endian = v1.endian}
    else {data = WordSet.bottom (max (WordSet.bitwidth v1.data) (WordSet.bitwidth v2.data));
          endian = v1.endian}

  let widen_join (v1 : t) (v2 : t) : t =
    if idx_equal (get_idx v1) (get_idx v2)
    then {data = WordSet.widen_join v1.data v2.data; endian = v1.endian}
    else {data = WordSet.top (max (WordSet.bitwidth v1.data) (WordSet.bitwidth v2.data));
          endian = v1.endian}


  let is_top = lift_in WordSet.is_top
  let is_bottom = lift_in WordSet.is_bottom

  let pp ppf (v : t) =
    Format.fprintf ppf "@[%s %a@]" (Word_ops.endian_string v.endian) WordSet.pp v.data

  (* Helper function; splits a WordSet into a sequence of WordSets of length w. w should be a factor of p's width. *)
  let segment_wordset (p : WordSet.t) (w : int) : WordSet.t seq =
    let p_sz = WordSet.bitwidth p in
    assert(w mod addressable_width = 0);
    assert(p_sz mod addressable_width = 0);
    Seq.unfold ~init:0 ~f:begin fun lo ->
      let hi = lo + (w - 1) in
      if lo >= p_sz then None
      else if hi >= p_sz then
        (* E2e-A, ora-7 — provably unreachable: the only call site (:365, [cast_seq]) is guarded by [p_sz mod sz = 0], and [replicate_wordset] guarantees [p_sz mod sz = 0] — so the loop always lands exactly on p_sz. *)
        Utils.not_implemented ~top:None
          "Wordset segmented by non-factor size"
      else Option.return (WordSet.extract ~hi ~lo p, hi + 1)
    end

  let reverse_seq : 'a seq -> 'a seq = Fn.compose Seq.of_list Seq.to_list_rev

(* Returns a sequence of values ordered from lowest address to highest *)
(* TODO: fold into cast_seq? *)
let cast_seq (sz, e : idx) (v : t) : WordSet.t seq =
    let sz = if Bitvector.compare_endian e v.endian = 0 then sz else addressable_width in
    let w, e = get_idx v in
    let top = Seq.singleton @@ WordSet.top sz in
    if w = sz then
      (* The same-width fast path — the common case (a cell read at its stored width) skips the segment/sequence machinery entirely; the profiled hot path is ZArith/GC in the bitvector ops, and the Seq/segment wrapper multiplied it. *)
      Seq.singleton v.data
    else if w < sz then
      (* A value of width [w] read at the WIDER width [sz] — the unknown high (LE) / low (BE) bytes are NOT the value's own bytes. *)
      top
    else if WordSet.bitwidth v.data mod sz > 0 then
      (* Lane C — non-divisor geometry has NO sound precise form: zero-padding the value to the next multiple would claim zero for the pad bits on a wider read (the memory there is unknown — unsound); padding with unknowns is. *)
      Utils.not_implemented ~top
        (Printf.sprintf "%i-val cast to incompatible size %i" w sz)
    else let wordset_seq = segment_wordset v.data sz in
      match e with
      | BigEndian -> reverse_seq wordset_seq
      | LittleEndian -> wordset_seq

  let op_at_seq op (sz, e : idx) (v1 : t) (v2 : t) : WordSet.t seq =
    let sz1, _ = get_idx v1 in
    let sz2, _ = get_idx v2 in
    if
      sz1 = sz && sz2 = sz
      && Bitvector.compare_endian e v1.endian = 0
      && Bitvector.compare_endian e v2.endian = 0
    then
      (* The same-width fast path — the common same-width cell join/meet skips the cast/zip/sequence machinery (precision-identical: the generic path's single segment pair is the direct op). *)
      Seq.singleton (op v1.data v2.data)
    else
    let seq1 = cast_seq (sz, e) v1 in
    let seq2 = cast_seq (sz, e) v2 in
    let seq_len = Utils.cdiv (max sz1 sz2) sz in
    let seq1 = Seq.concat @@ Seq.repeat seq1 in
    let seq2 = Seq.concat @@ Seq.repeat seq2 in
    let res_inf_seq = Seq.zip seq1 seq2 |>
                      Seq.map ~f:(fun (x,y) -> op x y) in
    Seq.take res_inf_seq seq_len


  let op_at (op : WordSet.t -> WordSet.t -> WordSet.t) (sz, e : idx) (v1 : t) (v2 : t) : t =
    let w1, _ = get_idx v1 in
    let w2, _ = get_idx v2 in
    if
      w1 = sz && w2 = sz
      && Bitvector.compare_endian e v1.endian = 0
      && Bitvector.compare_endian e v2.endian = 0
    then
      (* The same-width direct op — the profiled hot path (the find'/join_at cell reads) skips the segment placement + join machinery entirely. *)
      create (op v1.data v2.data) e
    else
    let wordset_seq  = op_at_seq op (sz, e) v1 v2 in
    let wordset_of_int i = WordSet.singleton (Word.of_int ~width:sz i) in
    let place_in_result = match e with
      | LittleEndian -> fun i p ->
        let sized_p = WordSet.cast Bil.UNSIGNED sz p in
        WordSet.lshift sized_p @@ wordset_of_int @@ i * (WordSet.bitwidth p)
      | BigEndian -> fun i p ->
        let sized_p = WordSet.cast Bil.UNSIGNED sz p in
        WordSet.lshift sized_p @@ wordset_of_int @@
        (sz - (i + 1) * (WordSet.bitwidth p)) in
    wordset_seq |> Seq.mapi ~f:place_in_result
    |> Seq.reduce_exn ~f:WordSet.join
    |> fun p -> create p e

  (* Computes the op of two tree values with possibly differring indices. The result has the maximum of the two values' sizes. Note that this operation is not commutative since it has the endianness of the right argument. *)
  let op_poly (op : WordSet.t -> WordSet.t -> WordSet.t) (v1 : t) (v2 : t) : t =
    let w1, _ = get_idx v1 in
    let w2, _ = get_idx v2 in
    let sz = max w1 w2 in
    op_at op (sz, v2.endian) v1 v2

  let join_at = op_at WordSet.join
  let meet_at = op_at WordSet.meet

  let join_poly = op_poly WordSet.join
  let meet_poly = op_poly WordSet.meet

end

module IT = Cbat_interval_tree.Make_binable(Key)

type idx = {addr_width:int; addressable_width:int} [@@deriving bin_io, sexp, compare]

type itree = Val.t IT.t

type t = {itree : Val.t IT.t option; width : int}
[@@deriving bin_io, sexp, compare]

let get_idx (m : t) : idx = {addr_width = m.width; addressable_width}
let top (i : idx) : t =
  assert(i.addressable_width = addressable_width);
  {itree=Some IT.empty; width=i.addr_width}
let bottom (i : idx) : t =
  assert(i.addressable_width = addressable_width);
  {itree=None; width=i.addr_width}

(* A note on complexity: A number of the operations used internally are linear in the number of overlaps in the tree. *)

(* dynamic keys implementation *)
(* TODO: issues: endianness, width. Current implementation does not handle variable endianness or width properly. These must be addressed. TODO: performance: the add functions all sometimes split existing intervals. This might usually work, but could cause pathological blowup *)

(* TODO: Currently, some memory entries are repeated. This should not affect the results, but is an unnecessary use of memory. Fix this. *)
let op_add' op (m : itree) (width : int) ~key:(k : Key.t) ~data:(d : Val.t) : t =
  (* Single-pass: collect the intersecting cells AND remove them in ONE pruned descent (the O2 rewrite — the old code made two separate [intersections] + [remove_intersections] traversals of the same spine). *)
  let ints, rest = IT.collect_remove_intersections m k in
  let gaps = Key.gaps (Val.top (Val.get_idx d)) k ints in
  let overlaps = Seq.append gaps ints in
  let itree =
    Seq.fold overlaps ~init:rest ~f:begin fun rest (k',d') ->
      let newD = op d d' in
      let k_int = Key.intersection k k' in
      (* Update the range of the key that overlaps the add *)
      let rest = IT.add rest k_int newD in
      (* Replace the range(s) of the key that do not overlap *)
      match Key.interval_diff k' k with
      | `none -> rest
      | `one k1 -> IT.add rest k1 d'
      | `two (k1, k2) -> IT.add (IT.add rest k1 d') k2 d'
    end in
  {itree = Some itree; width}

let op_add op (m : t) : key:Key.t -> data:Val.t -> t = match m.itree with
  | None -> fun ~key:_ ~data:_ -> {itree=None; width=m.width}
  | Some t -> op_add' op t m.width

(* Adds the new value by joining it with prior overlapping values *)
let join_add : t -> key:Key.t -> data:Val.t -> t = op_add Val.join_poly

(* Adds the new value by meeting it with prior overlapping values *)
let meet_add : t -> key:Key.t -> data:Val.t -> t = op_add Val.meet_poly

(* [meet_range m ~key ~data]: The RANGED meet (the trace-partitioning subtraction substrate, docs/trace-partitioning-plan.md §3) — meet [data] into every cell of [m] whose key intersects [key]: the overlapping cells' values meet [data] (the. *)
let meet_range (m : t) ~key ~data : t = meet_add m ~key ~data

(* [call_keep m ~keep_lo ~escape]: The caller-frame-preserving call abstraction (the fix for the precision gap where every call topped the WHOLE memory — docs/trace-partitioning-plan.md §10, the "call abstraction" lane). *)
let call_keep (m : t) ~(keep_lo : word) ~(escape : (word * word) list) : t =
  match m.itree with
  | None -> m
  | Some it ->
    (* the caller-side words convert to native points ONCE; a word wider than the native 64 bits is un-keyable -> no refinement (the sound over-approximation). *)
    let escape_pts = Option.all (List.map escape ~f:(fun (lo, hi) ->
        match Key.of_word lo, Key.of_word hi with
        | Some lo, Some hi -> Some (lo, hi)
        | _ -> None)) in
    (match Key.of_word keep_lo, escape_pts with
     | Some keep_lo_pt, Some escape_pts ->
       let in_escape (k : Key.t) : bool =
         List.exists escape_pts ~f:(fun (lo, hi) ->
             Key.ge (Key.lower k) lo && Key.le (Key.upper k) hi) in
       let kept =
         IT.to_sequence it
         |> Seq.fold ~init:IT.empty ~f:(fun acc (k, v) ->
             if Key.lt (Key.lower k) keep_lo_pt || in_escape k then acc
             else IT.add acc k v) in
       {itree = Some kept; width = m.width}
     | _ -> m)

(* [store_merge d d']: The width-aware point-store merge (the fix for the heritage "op is unsound in the case that d' is longer than d" TODO). *)
let store_merge (d : Val.t) (d' : Val.t) : Val.t =
  let w = WordSet.bitwidth (Val.data d) in
  let w' = WordSet.bitwidth (Val.data d') in
  if w < w' then
    let _, e = Val.get_idx d in
    let _, e' = Val.get_idx d' in
    if Bitvector.compare_endian e e' = 0 then
      (* (d' & mask_hi) | zext(d) — the low [w] bits replaced, the high bits kept. The mask: bits [0, w) cleared. *)
      let mask =
        WordSet.lnot
          (WordSet.cast Bil.UNSIGNED w'
             (WordSet.singleton (Word.ones w))) in
      Val.create
        (WordSet.logor
           (WordSet.logand (Val.data d') mask)
           (WordSet.cast Bil.UNSIGNED w' (Val.data d)))
        e'
    else d
  else d

(* Adds the new value by overwriting the prior value if it can only be written to one location and joining it with the prior overlapping values otherwise. *)
let add (m : t) ~key : data:Val.t -> t =
  if Key.equal (Key.lower key) (Key.upper key) then op_add store_merge m ~key
  else join_add m ~key

(* [fold_intersections ~default m k ~f]: fold over the key's intersecting cells, seeded with the first — the [find']/ [find_idx'] scaffold ([f] receives the first cell, the full intersection sequence, and its tail). *)
let fold_intersections ~(default : 'a) (m : itree) (k : Key.t)
    ~(f : Val.t -> (Key.t * Val.t) seq -> (Key.t * Val.t) seq -> 'a) : 'a =
  let ints = IT.intersections m k in
  Option.value_map ~default (Seq.next ints) ~f:(fun ((_, hd), tl) ->
      f hd ints tl)

(* Retrieves a WORDSET representing the set of possible values stored at the given key and with the given index. *)
let find' (i : Val.idx) (m : itree) (k : Key.t) : Val.t =
  assert(fst i > 0);
  fold_intersections ~default:(Val.top i) m k ~f:(fun hd ints _ ->
    (* Mapping back over ints will cause join_at i to be called every time. This ensures that the result has the correct width even when there is only one intersection. *)
    Seq.fold ints ~init:hd ~f:(fun v (k',v') ->
        let lo_key_start = Key.min (Key.lower k) (Key.lower k') in
        let hi_key_start = Key.max (Key.lower k) (Key.lower k') in
        let keys_aligned = Key.aligned_mod lo_key_start hi_key_start (fst i) in
        if keys_aligned then Val.join_at i v v' else Val.top i))

let find (i : Val.idx) (m : t) (k : Key.t) = match m.itree with
  | None -> Val.bottom i
  | Some t -> find' i t k

(* Retrieves the index of values referenced at the given key. *)
let find_idx' (m : itree) (k : Key.t) : Val.idx =
  fold_intersections ~default:Val.Idx.top m k ~f:(fun hd _ tl ->
    Seq.map ~f:(Fn.compose Val.get_idx snd) tl
    |> Seq.fold ~init:(Val.get_idx hd) ~f:Val.Idx.join)

let find_idx (m : t) (k : Key.t) : Val.idx = match m.itree with
  | None -> Val.Idx.top
  | Some t -> find_idx' t k

(* Note that the behavior of precedes is non-intuitive due to the definition of Wordset union. *)
let precedes' (m1 : itree) (m2 : itree) : bool =
  let m1_seq = IT.to_sequence m1 in
  let m2_seq = IT.to_sequence m2 in
  Seq.for_all m1_seq ~f: begin fun (k, v) ->
    (* If the key overlaps a space, v must precede m2's default *)
    (IT.dominates m2 k ||
     Val.precedes v (Val.top (Val.get_idx v))) &&
    Seq.for_all (IT.intersections m2 k) ~f:begin fun (_,v') ->
      Val.precedes v v'
    end
  end &&
  Seq.for_all m2_seq ~f: begin fun (k, v) ->
    (* If the key overlaps a space, m2's default must precede v *)
    (IT.dominates m2 k ||
     Val.precedes (Val.top (Val.get_idx v)) v) &&
    Seq.for_all (IT.intersections m2 k) ~f:begin fun (_,v') ->
      Val.precedes v' v
    end
  end

let precedes (m1 : t) (m2 : t) : bool =
  assert(m1.width = m2.width);
  match m1.itree, m2.itree with
  | None, _ -> true
  | Some _, None -> false
  | Some t1, Some t2 -> precedes' t1 t2

(* TODO: check *)
let equal' (m1 : itree) (m2 : itree) : bool =
  Seq.for_all (IT.to_sequence m1) ~f: begin fun (key, d1) ->
    let d2 = find' (Val.get_idx d1) m2 key in
    (* d1 = find ... m1 key since all keys are disjoint *)
    Val.equal d1 d2
  end && Seq.for_all (IT.to_sequence m2) ~f: begin fun (key, d2) ->
    let d1 = find' (Val.get_idx d2) m1 key in
    Val.equal d1 d2
  end

let equal (m1 : t) (m2 : t) : bool =
  assert(m1.width = m2.width);
  Option.equal equal' m1.itree m2.itree

(* Note that this definition of join, while sound, can greatly increase the size of memory. *)
(* A7e, loop attempt 11 (user-approved; the A7d deep-profile root cause) — drop TOP-VALUED cells from join'/widen_join' results. *)
(* One-pass per-merge canonize (the merged strip_tops + coalesce; user directive, ora-1): (1) drop top-valued cells inline (the A7e strip — absent=top, so a dropped cell is read-equivalent; dropping never creates. *)
let coalesce (it : itree) : itree =
  IT.to_sequence it
  |> Seq.fold ~init:(IT.empty, None) ~f:(fun (acc, pending) (k, v) ->
      if Val.equal v (Val.top (Val.get_idx v))
      then (acc, pending) (* inline top drop *)
      else match pending with
        | None -> (acc, Some (k, v))
        | Some (pk, pv) when Key.equal (Key.lower k) (Key.lower pk) ->
            (acc, Some ({Key.lo = Key.lower pk;
                         Key.hi = Key.max (Key.upper pk) (Key.upper k)},
                        Val.join_poly pv v)) (* equal-lower merge *)
        | Some (pk, pv) when Val.equal pv v &&
            (let nxt = Key.succ (Key.upper pk) in
             not (Key.is_zero nxt) && Key.equal (Key.lower k) nxt) ->
            (acc, Some ({Key.lo = Key.lower pk; Key.hi = Key.upper k}, v))
        | Some (pk, pv) -> (IT.add acc pk pv, Some (k, v)))
  |> fun (acc, pending) ->
  Option.fold ~init:acc pending ~f:(fun acc (k, v) -> IT.add acc k v)

(* [fold_keys op m1 m2]: the seq_product key walk shared by the join and the meet — per section of the merged key sequence, compute the best index compatible with all of the data at the key and combine the two sides' values with [op]. *)
let fold_keys (op : Val.t -> Val.t -> Val.t) (m1 : itree) (m2 : itree) : itree =
  let m1_seq = Seq.map ~f:fst (IT.to_sequence m1) in
  let m2_seq = Seq.map ~f:fst (IT.to_sequence m2) in
  let keys = Key.seq_product m1_seq m2_seq in
  Seq.fold keys ~init:IT.empty ~f: begin fun it (s, key) ->
    (* Get the best index compatible with all of the data stored at this key *)
    let idx = match s with
      | Key.Left -> find_idx' m1 key
      | Key.Right -> find_idx' m2 key
      | Key.Both_sides ->
        let idx1 = find_idx' m1 key in
        let idx2 = find_idx' m2 key in
        Val.Idx.join idx1 idx2 in
    let d1 = find' idx m1 key in
    let d2 = find' idx m2 key in
    IT.add it key @@ op d1 d2
  end

let join' (m1 : itree) (m2 : itree) : itree =
  coalesce (fold_keys Val.join m1 m2)

let lift_join f (m1 : t) (m2 : t) : t =
  assert(m1.width = m2.width);
  match m1.itree, m2.itree with
  | Some t1, Some t2 -> {itree=Some (f t1 t2); width=m1.width}
  | Some _, None -> m1
  | None, Some _ -> m2
  | None, None -> m1 (* m1 = m2 = bottom *)

let join : t -> t -> t = lift_join join'

let widen_join_op (w : Val.t -> Val.t -> Val.t) : t -> t -> t =
  lift_join (fun t1 t2 ->
    if precedes' t1 t2
    then begin
      let m2_seq = Seq.map ~f:fst (IT.to_sequence t2) in
      coalesce begin
        Seq.fold m2_seq ~init:IT.empty ~f:begin fun it key ->
          let idx = find_idx' t2 key in
          let d1 = find' idx t1 key in
          let d2 = find' idx t2 key in
          IT.add it key @@ w d1 d2
        end
      end
    end
    else join' t1 t2)

let widen_join = widen_join_op Val.widen_join


(* Note that this definition of meet, while sound, can greatly increase the size of memory. *)
let meet' (m1 : itree) (m2 : itree) : itree =
  fold_keys Val.meet m1 m2

let meet (m1 : t) (m2 : t) : t =
  assert(m1.width = m2.width);
  match m1.itree, m2.itree with
  | Some t1, Some t2 -> {itree=Some (meet' t1 t2); width=m1.width}
  | None, _ -> {itree=None; width=m1.width}
  | _, None -> {itree=None; width=m1.width}

(* TODO: the pp filter does not produce a unique form (byte-endianness, maybe more). *)
let pp ppf (m : t) : unit =
  let itree = Option.map m.itree ~f:(IT.filter ~f:(fun d ->
      not (Val.equal d (Val.top (Val.get_idx d))))) in
  match itree with
  | None -> Format.fprintf ppf "unreachable"
  | Some t ->
    Format.fprintf ppf "@[<2>----------------------------------------@ ";
    t
    |> IT.to_sequence
    |> Seq.iter ~f:(fun (k, v) -> Format.fprintf ppf "@[<hov 1>[%a@ -> %a]@]@ " Key.pp k Val.pp v);
    Format.fprintf ppf "----------------------------------------@]"
