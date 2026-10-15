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
include Bap.Std

module Fn = Core.Fn
module Sexp = Core.Sexp
module Option = Core.Option
module Or_error = Core.Or_error
module Result = Core.Result
module Binable = Core.Binable

module Lattice = Cbat_lattice_intf
module WordSet = Cbat_clp_set_composite
module Utils = Cbat_vsa_utils
module Map_lattice = Cbat_map_lattice
module Word_ops = Cbat_word

(* Memories are byte-addressable. *)
let addressable_width = 8

module Key = struct
  include Cbat_mem_key

  (* The hull ends as the unsigned words the queries speak; a point's
     [pwidth]/[pvalue] pair is exactly a [pwidth]-bit word. *)
  let hull (k : t) : Cbat_word.t * Cbat_word.t =
    let word (p : point) : Cbat_word.t =
      Cbat_word.of_word (Word.of_int64 ~width:p.pwidth p.pvalue) in
    word (lower k), word (upper k)
end

(* Value stored at each key. *)
module Val : sig

  type t [@@deriving bin_io, sexp, compare]

  module Idx : Lattice.S_semi with type t = WordSet.idx * endian

  include Lattice.S_indexed with type t := t and type idx = Idx.t

  val create : WordSet.t -> endian -> t

  val data : t -> WordSet.t

  val idx_equal : idx -> idx -> bool

  val is_top : t -> bool
  val is_bottom : t -> bool

  (* [equal v (top (get_idx v))]: the lattice top, not a symbolic one. *)
  val equal_top : t -> bool

  val join_at : idx -> t -> t -> t
  val meet_at : idx -> t -> t -> t


  val join_poly : t -> t -> t
  val meet_poly : t -> t -> t

  val pp : Format.formatter -> t -> unit

end = struct

  type idx = WordSet.idx * endian

  module Idx : Lattice.S_semi with type t = idx = struct

    type t = idx

    let top = 64, BigEndian

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

  (* Shared per width and endianness: every gap and coalesce builds one. *)
  let top_tbl (endian : endian) : t array =
    Array.init 257 ~f:(fun w -> {data = WordSet.top (max w 1); endian})
  let top_le = top_tbl LittleEndian
  let top_be = top_tbl BigEndian

  let top (w, e : idx) : t =
    if w > 0 && w < Array.length top_le then
      (match e with LittleEndian -> top_le.(w) | BigEndian -> top_be.(w))
    else {data = WordSet.top w; endian = e}
  let bottom (w, e : idx) : t = {data = WordSet.bottom w; endian = e}

  
  let equal v1 v2 =
    if idx_equal (get_idx v1) (get_idx v2)
    then WordSet.equal v1.data v2.data
    else false

  let precedes v1 v2 =
    if idx_equal (get_idx v1) (get_idx v2)
    then WordSet.precedes v1.data v2.data
    else false

  (* One lift at equal indices; mismatched indices meet/join to
     bottom/top at the max width. *)
  let lift_idx ~(mismatch : int -> WordSet.t)
      (op : WordSet.t -> WordSet.t -> WordSet.t) (v1 : t) (v2 : t) : t =
    if idx_equal (get_idx v1) (get_idx v2)
    then {data = op v1.data v2.data; endian = v1.endian}
    else {data = mismatch (max (WordSet.bitwidth v1.data) (WordSet.bitwidth v2.data));
          endian = v1.endian}

  let join (v1 : t) (v2 : t) : t =
    lift_idx ~mismatch:WordSet.top WordSet.join v1 v2

  let meet (v1 : t) (v2 : t) : t =
    lift_idx ~mismatch:WordSet.bottom WordSet.meet v1 v2

  let widen_join (v1 : t) (v2 : t) : t =
    lift_idx ~mismatch:WordSet.top WordSet.widen_join v1 v2


  let is_top = lift_in WordSet.is_top

  let equal_top (v : t) : bool =
    WordSet.equal v.data (WordSet.top (WordSet.bitwidth v.data))
  let is_bottom = lift_in WordSet.is_bottom

  let pp ppf (v : t) =
    Format.fprintf ppf "@[%s %a@]" (Word_ops.endian_string v.endian) WordSet.pp v.data

  (* Split a set into width-[w] pieces. *)
  let segment_wordset (p : WordSet.t) (w : int) : WordSet.t seq =
    let p_sz = WordSet.bitwidth p in
    assert(w mod addressable_width = 0);
    assert(p_sz mod addressable_width = 0);
    Seq.unfold ~init:0 ~f:begin fun lo ->
      let hi = lo + (w - 1) in
      if lo >= p_sz then None
      else if hi >= p_sz then
        (* Sizes divide evenly; a non-factor size degrades to top. *)
        Utils.not_implemented
          ~top:(Some (WordSet.top ((hi + 1) - lo), hi + 1))
          "Wordset segmented by non-factor size"
      else Option.return (WordSet.extract ~hi ~lo p, hi + 1)
    end

  let reverse_seq : 'a seq -> 'a seq = Fn.compose Seq.of_list Seq.to_list_rev

(* Values lowest address first. *)

let cast_seq (sz, e : idx) (v : t) : WordSet.t seq =
    let sz = if Bitvector.compare_endian e v.endian = 0 then sz else addressable_width in
    let w, e = get_idx v in
    let top = Seq.singleton @@ WordSet.top sz in
    if w = sz then
      (* Same width: direct. *)
      Seq.singleton v.data
    else if w < sz then
      (* Wider read: unknown bytes. *)
      top
    else if WordSet.bitwidth v.data mod sz > 0 then
      (* Non-divisor width: top. *)
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
      (* Same width: direct. *)
      Seq.singleton (op v1.data v2.data)
    else
    let seq1 = cast_seq (sz, e) v1 in
    let seq2 = cast_seq (sz, e) v2 in
    let seq_len = Hike_stack_bounds.cdiv (max sz1 sz2) sz in
    let seq1 = Seq.concat @@ Seq.repeat seq1 in
    let seq2 = Seq.concat @@ Seq.repeat seq2 in
    let res_inf_seq = Seq.zip seq1 seq2 |>
                      Seq.map ~f:(fun (x,y) -> op x y) in
    Seq.take res_inf_seq seq_len


  let op_at (op : WordSet.t -> WordSet.t -> WordSet.t) (sz, e : idx) (v1 : t) (v2 : t) : t =
    (* The cell world is byte-granular: a sub-byte composition is
       unrepresentable — the read identity (top at the read's width). *)
    if sz mod addressable_width <> 0 then create (WordSet.top sz) e
    else
    let w1, _ = get_idx v1 in
    let w2, _ = get_idx v2 in
    if
      w1 = sz && w2 = sz
      && Bitvector.compare_endian e v1.endian = 0
      && Bitvector.compare_endian e v2.endian = 0
    then
      (* Same width: direct — the composed path's cast/lshift would
         collapse the CLP direction metadata the widening reads. *)
      create (op v1.data v2.data) e
    else
    let wordset_seq  = op_at_seq op (sz, e) v1 v2 in
    let wordset_of_int i = WordSet.singleton (Cbat_word.of_int ~width:sz i) in
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

  (* Op at the max width with the right endianness. *)
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

module IT = Interval_tree.Make_binable(Key)

(* The interval tree's [intersections] is point-only, so a cell of
   another coordinate line would match a query at the same point.  Every
   query filters by line; every removal removes only same-line cells. *)
let same_line (a : Key.t) (b : Key.t) : bool =
  Hike_origin.equal (Key.origin a) (Key.origin b)

let it_intersections (m : 'a IT.t) (k : Key.t) : (Key.t * 'a) Sequence.t =
  IT.intersections m k |> Sequence.filter ~f:(fun (k', _) -> same_line k k')

let it_remove_intersections (m : 'a IT.t) (k : Key.t) : 'a IT.t =
  Sequence.fold (it_intersections m k) ~init:m ~f:(fun m (k', _) ->
      IT.remove m k')

let it_dominates (m : 'a IT.t) (k : Key.t) : bool =
  IT.dominators m k
  |> Sequence.exists ~f:(fun (k', _) -> same_line k k')

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

(* Drop top cells; merge adjacent ones. *)
let coalesce (it : itree) : itree =
  IT.to_sequence it
  |> Seq.fold ~init:(IT.empty, None) ~f:(fun (acc, pending) (k, v) ->
      if Val.equal_top v
      then (acc, pending) (* drop top *)
      else match pending with
        | None -> (acc, Some (k, v))
        | Some (pk, pv)
          when Hike_origin.equal (Key.origin k) (Key.origin pk)
               && Key.equal (Key.lower k) (Key.lower pk) ->
            (acc, Some (Key.union pk k, Val.join_poly pv v)) (* merge *)
        | Some (pk, pv)
          when Hike_origin.equal (Key.origin k) (Key.origin pk)
               && Val.equal pv v
               (* Only a dense or congruently-strided union claims exactly
                  the two cells' bytes; a mixed-step union would demote to
                  a hull and claim the stride gaps. *)
               && ((Key.step pk = 1 && Key.step k = 1)
                   || Key.combined_step pk k > 1)
            && (let nxt = Key.succ (Key.upper pk) in
                not (Key.is_zero nxt) && Key.equal (Key.lower k) nxt) ->
            (acc, Some (Key.union pk k, v))
        | Some (pk, pv) -> (IT.add acc pk pv, Some (k, v)))
  |> fun (acc, pending) ->
  Option.fold ~init:acc pending ~f:(fun acc (k, v) -> IT.add acc k v)

(* [op_demoted] combines data at an intersection piece not fully
   covered by both keys' claims (mixed grids): the incoming fact
   covers only its own stride points there. *)
let op_add' ~(op : Val.t -> Val.t -> Val.t)
    ~(op_demoted : Val.t -> Val.t -> Val.t)
    (m : itree) (width : int) ~key:(k : Key.t) ~data:(d : Val.t) : t =
  let ints = it_intersections m k in
  let rest = it_remove_intersections m k in
  let gaps = Key.gaps (Val.top (Val.get_idx d)) k ints in
  let overlaps = Seq.append gaps ints in
  let itree =
    Seq.fold overlaps ~init:rest ~f:begin fun rest (k',d') ->
      let k_int = Key.intersection k k' in
      let combine =
        if Key.covers k k_int && Key.covers k' k_int
        then op else op_demoted in
      let new_data = combine d d' in
      (* Overlapping range; a top-data overlap carries no fact —
         absence reads top, so adding it only bloats the tree. *)
      let rest =
        if Val.is_top new_data then rest
        else IT.add rest k_int new_data
      in
      (* Non-overlapping ranges. *)
      List.fold (Key.interval_diff k' k) ~init:rest
        ~f:(fun rest k1 -> IT.add rest k1 d')
    end in
  (* One coalesce per store: top pieces drop, adjacent equal-data
     pieces merge — the tree stays tight between joins. *)
  {itree = Some (coalesce itree); width}

(* A write wider than the word (the address width) is one write per
   word, each at its own address: a word access is then an exact cell
   hit, and a word's origin stays with it.  A width the word does not
   divide, or a key a lane cannot move to, writes whole. *)
let word_writes (word : int) (key : Key.t) (d : Val.t) : (Key.t * Val.t) list =
  let w, e = Val.get_idx d in
  if w <= word || w mod word <> 0 then [ (key, d) ]
  else
    let n = w / word in
    List.init n ~f:(fun i ->
        let pos = match e with LittleEndian -> i | BigEndian -> n - 1 - i in
        Option.map (Key.shift key ~bytes:(pos * word / addressable_width))
          ~f:(fun k ->
              ( k,
                Val.create
                  (WordSet.extract ~hi:(((i + 1) * word) - 1) ~lo:(i * word)
                     (Val.data d))
                  e )))
    |> Option.all
    |> Option.value ~default:[ (key, d) ]

let op_add ~(op : Val.t -> Val.t -> Val.t) ~(op_demoted : Val.t -> Val.t -> Val.t)
    (m : t) : key:Key.t -> data:Val.t -> t = match m.itree with
  | None -> fun ~key:_ ~data:_ -> {itree=None; width=m.width}
  | Some _ -> fun ~key ~data ->
    List.fold (word_writes m.width key data) ~init:m ~f:(fun m (key, data) ->
        match m.itree with
        | Some t -> op_add' ~op ~op_demoted t m.width ~key ~data
        | None -> m)

(* Join-add: a store's fact widens both sides everywhere. *)
let join_add : t -> key:Key.t -> data:Val.t -> t =
  op_add ~op:Val.join_poly ~op_demoted:Val.join_poly

(* Meet-add: the constraint narrows same-grid cells; on a demoted
   piece the cell keeps its data (the constraint does not cover the
   interleaved bytes). *)
let meet_add : t -> key:Key.t -> data:Val.t -> t =
  op_add ~op:Val.meet_poly ~op_demoted:(fun _ d' -> d')

(* Meet [data] into intersecting cells; an empty piece meet keeps the
   cell — a constraint that empties a contributing cell bounds the
   read, not that cell, and the dead-path bottom is never written. *)
let meet_range_keep (m : t) ~key ~data : t =
  op_add
    ~op:(fun d d' ->
      let m = Val.meet_poly d d' in
      if Val.is_bottom m then d' else m)
    ~op_demoted:(fun _ d' -> d') m ~key ~data

(* Keep the caller's frame across a call: all inputs are OFFSET-space
   (the segment-relative line the Stack cells key by).  A called
   function writes only its own frame below its entry SP and the
   escape ranges — so Stack cells keep at/above [keep_lo]
   outside [escape]; a VLA cell belongs to the caller's own allocation,
   which the callee cannot reach (it keeps); a plain (absolute) or rip
   cell names no stack line and the callee may clobber any non-stack
   memory (it drops). *)
let call_keep (m : t) ~(keep_lo : word) ~(escape : (word * word) list) : t =
  match m.itree with
  | None -> m
  | Some it ->
    let escape_pts = Option.all (List.map escape ~f:(fun (lo, hi) ->
        Option.map2 (Key.of_word (Cbat_word.of_word lo))
          (Key.of_word (Cbat_word.of_word hi)) ~f:(fun lo hi -> (lo, hi)))) in
    let keep_lo_pt = Key.of_word (Cbat_word.of_word keep_lo) in
    match keep_lo_pt, escape_pts with
    | Some keep_lo_pt, Some escape_pts ->
      let in_escape (k : Key.t) : bool =
        List.exists escape_pts ~f:(fun (lo, hi) ->
            Key.ge (Key.lower k) lo && Key.le (Key.upper k) hi) in
      let keeps (k : Key.t) : bool =
        let o = Key.origin k in
        Hike_origin.names_stack_line o
        && (match o with
            | Hike_origin.Vla _ -> true
            | _ ->
              (not (in_escape k)) && not (Key.lt (Key.lower k) keep_lo_pt))
      in
      let kept =
        IT.to_sequence it
        |> Seq.fold ~init:IT.empty ~f:(fun acc (k, v) ->
            if keeps k then IT.add acc k v else acc) in
      {itree = Some kept; width = m.width}
    | _ ->
      (* An unkeyable bound keeps the whole line (the sound identity). *)
      m

(* Whether the map is the bottom map: no tree, no reads (the
   unreached state's memory). *)
let is_bottom (m : t) : bool =
  match m.itree with None -> true | Some _ -> false

(* Whether a stored cell's key intersects the byte range [lo, hi]
   (inclusive addresses).  Unkeyable bounds answer "yes" — the caller
   keeps its abstract read. *)
let has_cell_in (m : t) ~(origin : Hike_origin.t) ~(lo : Cbat_word.t)
    ~(hi : Cbat_word.t) : bool =
  match m.itree with
  | None -> false
  | Some it -> (
      match Key.of_word lo, Key.of_word hi with
      | Some plo, Some phi when Key.le plo phi ->
        let k = { Key.origin; lo = plo; hi = phi; step = 1 } in
        (* The intersections index answers; no full-tree scan.  The
           tree is point-only, so the query filters by line. *)
        not (Seq.is_empty (it_intersections it k))
      | _ -> true)

(* A store [d] merged into the cell [d'] that starts where it does: a
   narrower store replaces the bytes it covers — the low bits
   (little-endian) or the high bits (big-endian) — and keeps the rest. *)
let store_merge (d : Val.t) (d' : Val.t) : Val.t =
  let w = WordSet.bitwidth (Val.data d) in
  let w' = WordSet.bitwidth (Val.data d') in
  let _, e = Val.get_idx d in
  let _, e' = Val.get_idx d' in
  if w < w' && Bitvector.compare_endian e e' = 0 then
    let at = match e with LittleEndian -> 0 | BigEndian -> w' - w in
    let place v =
      let v = WordSet.cast Bil.UNSIGNED w' v in
      if at = 0 then v
      else WordSet.lshift v (WordSet.singleton (Cbat_word.of_int ~width:w' at))
    in
    let mask = WordSet.lnot (place (WordSet.singleton (Cbat_word.ones w))) in
    Val.create
      (WordSet.logor (WordSet.logand (Val.data d') mask) (place (Val.data d)))
      e'
  else d

(* The bytes a cell's value covers from each of its starts. *)
let val_bytes (v : Val.t) : int =
  Int.max 1 (WordSet.bitwidth (Val.data v) / addressable_width)

(* The widest cell a store records: [word_writes] splits a wider write
   per word, so only an access that splits unevenly can exceed it. *)
let max_cell_bytes = 64

(* The last point of a [w]-bit line. *)
let line_max (w : int) : int64 =
  if w >= 64 then -1L else Stdlib.Int64.pred (Stdlib.Int64.shift_left 1L w)

(* [p] moved [n] along its line, wrapping. *)
let pt_add (p : Key.point) (n : int64) : Key.point =
  let v = Stdlib.Int64.add p.pvalue n in
  { p with pvalue = (if p.pwidth >= 64 then v else Stdlib.Int64.logand v (line_max p.pwidth)) }

(* [b - a] on [a]'s line, signed. *)
let sdist (a : Key.point) (b : Key.point) : int64 =
  let d = Stdlib.Int64.sub b.pvalue a.pvalue in
  if a.pwidth >= 64 then d
  else
    let sh = 64 - a.pwidth in
    Stdlib.Int64.shift_right (Stdlib.Int64.shift_left d sh) sh

(* The starts a store writes: [w_lo + i*wstep] for [0 <= i*wstep <=
   span], each writing [n] bytes; a negative [span] (a hull too wide to
   measure) writes anywhere on the line. *)
type write = { w_lo : Key.point; span : int64; wstep : int64; n : int64 }

(* Whether some write's bytes meet [x, x+cb-1], [x] relative to [w_lo]. *)
let touches (w : write) (x : int64) (cb : int64) : bool =
  let module I = Stdlib.Int64 in
  let ( <. ) a b = I.compare a b < 0 and ( <=. ) a b = I.compare a b <= 0 in
  w.span <. 0L
  || 0L <=. I.add x (I.pred cb)
     && x <=. I.add w.span (I.pred w.n)
     && (I.equal w.span 0L || x <. 0L || w.span <. x
         || (let r = I.rem x w.wstep in
             not (w.n <=. r && I.add r cb <=. w.wstep)))

(* Floor and ceiling division by a positive [b]. *)
let fdiv (a : int64) (b : int64) : int64 =
  let q = Stdlib.Int64.div a b in
  if Stdlib.Int64.compare (Stdlib.Int64.rem a b) 0L < 0 then Stdlib.Int64.pred q else q

let cdiv (a : int64) (b : int64) : int64 = Stdlib.Int64.neg (fdiv (Stdlib.Int64.neg a) b)

(* Distances past this bound are not measured: such a cell drops whole. *)
let far = Stdlib.Int64.shift_left 1L 61

(* What a store does to one cell [k'] (value [v']): the parts of its
   grid no write touches keep [v'], and the touched starts are either
   one start [x] (relative to the store, for the caller to decide) or a
   run that lies exactly on the store's own grid at the store's width
   (the weak-update join), or dropped. *)
type cell_fate =
  { kept : Key.t list; one : int64 option; same_grid : Key.t option }

let cell_fate (w : write) ((k', v') : Key.t * Val.t) : cell_fate =
  let module I = Stdlib.Int64 in
  let ( <. ) a b = I.compare a b < 0 and ( <=. ) a b = I.compare a b <= 0 in
  let none = { kept = []; one = None; same_grid = None } in
  let cb = I.of_int (val_bytes v') in
  let x0 = sdist w.w_lo k'.lo in
  let cspan = sdist k'.lo k'.hi in
  let g =
    if I.equal cspan 0L then cb
    else if k'.step > 1 then I.of_int k'.step else cb
  in
  if w.span <. 0L || cspan <. 0L || far <. I.abs x0 || far <. cspan then none
  else
    let count = I.succ (I.div cspan g) in
    let i0 = I.max 0L (cdiv (I.sub (I.sub 1L cb) x0) g) in
    let i1 = I.min (I.pred count) (fdiv (I.sub (I.add w.span (I.pred w.n)) x0) g) in
    let start i = pt_add k'.lo (I.mul i g) in
    let piece lo hi = { k' with Key.lo; hi } in
    if i1 <. i0 then { none with kept = [ k' ] }
    else
      let lower = if 0L <. i0 then [ piece k'.lo (start (I.pred i0)) ] else [] in
      let upper =
        if i1 <. I.pred count then [ piece (start (I.succ i1)) k'.hi ] else []
      in
      let x_at i = I.add x0 (I.mul i g) in
      if I.equal i0 i1 then
        let x = x_at i0 in
        if touches w x cb then { none with kept = lower @ upper; one = Some x }
        else { none with kept = [ k' ] }
      else
        let on_grid =
          I.equal cb w.n && I.equal g w.wstep && w.n <=. w.wstep
          && I.equal (I.rem (x_at i0) w.wstep) 0L
          && 0L <=. x_at i0 && x_at i1 <=. w.span
        in
        { kept = lower @ upper; one = None;
          same_grid = (if on_grid then Some (piece (start i0) (start i1)) else None) }

(* The cells on [k]'s line whose bytes can meet [k]'s writes of [n]
   bytes: a cell starts at most [max_cell_bytes - 1] bytes before its
   last byte, and the window may wrap the line's end. *)
let candidates (m : itree) (k : Key.t) (w : write) : (Key.t * Val.t) list =
  let q lo hi = Seq.to_list (it_intersections m { k with Key.lo; hi; step = 1 }) in
  let top_pt = { k.lo with pvalue = line_max k.lo.pwidth } in
  let zero_pt = { k.lo with pvalue = 0L } in
  if Stdlib.Int64.compare w.span 0L < 0 then q zero_pt top_pt
  else
    let wlo = pt_add k.lo (Stdlib.Int64.of_int (1 - max_cell_bytes)) in
    let whi = pt_add k.hi (Stdlib.Int64.pred w.n) in
    if Key.le wlo k.lo && Key.le k.hi whi then q wlo whi
    else
      List.dedup_and_sort ~compare:(fun (a, _) (b, _) -> Key.compare a b)
        (q wlo top_pt @ q zero_pt whi)

(* One store at one key.  Every cell whose bytes the store may write is
   resolved: a strong store (one point, the access's only address)
   merges into the cell at its start and drops every other touched
   cell; a weak store keeps a touched cell only where it lies on the
   store's grid at the store's width (each slot is either the store's
   value or what it held: the join); every other touched byte reads top.
   No touched cell keeps its old value. *)
let store_one ~(strong : bool) (m : itree) (width : int) ~(key : Key.t)
    ~(data : Val.t) : t =
  let n = val_bytes data in
  let point = Key.equal key.lo key.hi in
  let w =
    { w_lo = key.lo;
      span = (if point then 0L else sdist key.lo key.hi);
      wstep = Stdlib.Int64.of_int (Int.max 1 key.step);
      n = Stdlib.Int64.of_int n }
  in
  let strong = strong && point in
  let cands = candidates m key w in
  let rest = List.fold cands ~init:m ~f:(fun m (k', _) -> IT.remove m k') in
  let add_val it k v = if Val.is_top v then it else IT.add it k v in
  let at x = { key with Key.lo = pt_add key.lo x; hi = pt_add key.lo x; step = 1 } in
  let it, merged =
    List.fold cands ~init:(rest, None) ~f:(fun (it, merged) (k', v') ->
        let f = cell_fate w (k', v') in
        let it = List.fold f.kept ~init:it ~f:(fun it k -> IT.add it k v') in
        let it =
          match f.same_grid with
          | Some kg when not strong -> add_val it kg (Val.join_poly data v')
          | _ -> it
        in
        match f.one with
        | Some x when strong && Stdlib.Int64.equal x 0L -> (it, Some (store_merge data v'))
        | Some x
          when (not strong) && Stdlib.Int64.compare x 0L >= 0
               && Stdlib.Int64.compare x w.span <= 0
               && Int.equal (val_bytes v') n
               && (point || Stdlib.Int64.(equal (rem x w.wstep) 0L))
               && (point || Stdlib.Int64.compare w.wstep w.n >= 0) ->
          (add_val it (at x) (Val.join_poly data v'), merged)
        | _ -> (it, merged))
  in
  let it =
    if strong && n <= max_cell_bytes then
      add_val it key (Option.value merged ~default:data)
    else it
  in
  {itree = Some (coalesce it); width}

(* A store of [data] at [key]: [strong] when the key is the access's
   only address (the caller's fan-out decides), weak otherwise. *)
let store (m : t) ~(strong : bool) ~(key : Key.t) ~(data : Val.t) : t =
  match m.itree with
  | None -> m
  | Some _ ->
    List.fold (word_writes m.width key data) ~init:m ~f:(fun m (key, data) ->
        match m.itree with
        | Some t -> store_one ~strong t m.width ~key ~data
        | None -> m)

(* A store at a single key: a point key overwrites, a wider key is a
   weak update. *)
let add (m : t) ~key ~data : t = store m ~strong:true ~key ~data

(* Fold intersecting cells. *)
let fold_intersections ~(default : 'a) (m : itree) (k : Key.t)
    ~(f : Val.t -> (Key.t * Val.t) seq -> (Key.t * Val.t) seq -> 'a) : 'a =
  let ints = it_intersections m k in
  Option.value_map ~default (Seq.next ints) ~f:(fun ((_, hd), tl) ->
      f hd ints tl)

let try_assemble_cells ((_, endian) : Val.idx) (k : Key.t)
    (ints : (Key.t * Val.t) list) : Val.t option =
  if List.length ints < 2 then None
  else
    let sorted = List.sort ints ~compare:(fun (k1, _) (k2, _) ->
        Key.compare_point (Key.lower k1) (Key.lower k2)) in
    match sorted with
    | [] -> None
    | (first_k, first_v) :: _ ->
      if not (Key.equal (Key.lower first_k) (Key.lower k)) then None
      else
        let first_w = WordSet.bitwidth (Val.data first_v) in
        let first_end =
          Stdlib.Int64.add (Key.lower first_k).pvalue
            (Stdlib.Int64.of_int (first_w / addressable_width - 1)) in
        let rec check_contiguous prev_end rest =
          match rest with
          | [] -> Some prev_end
          | (next_k, next_v) :: rest' ->
            let expected_start = Stdlib.Int64.succ prev_end in
            if Stdlib.Int64.equal expected_start (Key.lower next_k).pvalue
            then
              let next_w = WordSet.bitwidth (Val.data next_v) in
              let next_end =
                Stdlib.Int64.add (Key.lower next_k).pvalue
                  (Stdlib.Int64.of_int (next_w / addressable_width - 1)) in
              check_contiguous next_end rest'
            else None
        in
        match check_contiguous first_end (List.tl_exn sorted) with
        | Some last_end when Stdlib.Int64.equal last_end (Key.upper k).pvalue ->
          (* The cells concatenate in address order (little-endian: a
             higher address is higher bits), so each keeps its lanes. *)
          let datas = List.map sorted ~f:(fun (_, v) -> Val.data v) in
          let assembled =
            match endian with
            | LittleEndian -> List.reduce datas ~f:(fun lo hi -> WordSet.concat hi lo)
            | BigEndian -> List.reduce datas ~f:WordSet.concat
          in
          Option.map assembled ~f:(fun data -> Val.create data endian)
        | _ -> None

(* The starts a key claims, as a grid step (0: the one start [lo]): a
   strided key its grid, a hull key the width grid of its [bytes]-wide
   values from its low end. *)
let grid_step (k : Key.t) ~(bytes : int) : int64 =
  if Key.equal (Key.lower k) (Key.upper k) then 0L
  else if Key.step k > 1 then Stdlib.Int64.of_int (Key.step k)
  else Stdlib.Int64.of_int (Int.max 1 bytes)

(* A read of [i] at [k] over the cells intersecting it: the join of the
   cells' values when every cell's starts lie on the read's grid and
   every read start is a cell's start; top otherwise.  A cell wider than
   the read gives the bytes at its start (cells are keyed by start). *)
let read_cells ((bits, endian) as i : Val.idx) (k : Key.t)
    (cells : (Key.t * Val.t) list) : Val.t =
  let open Stdlib.Int64 in
  let qlo = (Key.lower k).pvalue and qhi = (Key.upper k).pvalue in
  let qs = grid_step k ~bytes:(bits / addressable_width) in
  let divides s d = equal s 0L || equal (rem d s) 0L in
  (* The cell's value at its starts and how many read starts it claims;
     None when it is not on the read's grid. *)
  let claim ((c, v) : Key.t * Val.t) : (Val.t * int64) option =
    let cbits, cendian = Val.get_idx v in
    let value =
      if Int.equal cbits bits && Val.idx_equal (cbits, cendian) i then Some v
      else if cbits > bits && Bitvector.compare_endian cendian endian = 0 then
        let lo = match endian with LittleEndian -> 0 | BigEndian -> cbits - bits in
        Some (Val.create (WordSet.extract ~hi:(lo + bits - 1) ~lo (Val.data v)) endian)
      else None
    in
    let clo = (Key.lower c).pvalue and chi = (Key.upper c).pvalue in
    let cs = grid_step c ~bytes:(cbits / addressable_width) in
    Option.bind value ~f:(fun v ->
        if equal qs 0L then
          (* A point read: the cell must claim the read's start. *)
          Option.some_if (if equal cs 0L then equal clo qlo else divides cs (sub qlo clo)) (v, 1L)
        else if divides qs cs && divides qs (sub clo qlo) then
          let first =
            if unsigned_compare clo qlo >= 0 || equal cs 0L then clo
            else add clo (mul cs (unsigned_div (add (sub qlo clo) (pred cs)) cs))
          in
          let last = if unsigned_compare chi qhi <= 0 then chi else qhi in
          let n =
            if unsigned_compare first qlo < 0 || unsigned_compare first last > 0 then 0L
            else if equal cs 0L then 1L
            else succ (unsigned_div (sub last first) cs)
          in
          Some (v, n)
        else None)
  in
  let total = if equal qs 0L then 1L else succ (unsigned_div (sub qhi qlo) qs) in
  match Option.all (List.map cells ~f:claim) with
  | Some claims
    when equal total (List.fold claims ~init:0L ~f:(fun a (_, n) -> add a n)) ->
    List.filter_map claims ~f:(fun (v, n) -> Option.some_if (compare n 0L > 0) v)
    |> List.reduce ~f:Val.join
    |> (function Some v -> v | None -> Val.top i)
  | _ -> Val.top i

(* A point read whose bytes lie inside one wider point cell that starts
   before it: the high dword of a stored qword, byte 1 of a qword (the
   same-start narrower read already extracts).  The containing cell's
   bytes at the read's offset are the answer, but only when it is the
   sole cell overlapping the read — any other overlap must join, which
   this rule cannot do, so it answers top. *)
let containing_cell ((bits, endian) : Val.idx) (m : itree) (k : Key.t) :
    Val.t option =
  if not (Key.equal (Key.lower k) (Key.upper k)) then None
  else
    let req_bytes = bits / addressable_width in
    let klo = Key.lower k in
    let qlo = klo.pvalue in
    let khi =
      { klo with
        pvalue =
          Stdlib.Int64.add qlo (Stdlib.Int64.of_int (req_bytes - 1)) } in
    let back_lo = pt_add klo (Stdlib.Int64.of_int (1 - max_cell_bytes)) in
    let q lo hi =
      Seq.to_list (it_intersections m { k with Key.lo = lo; hi; step = 1 }) in
    let cands =
      if Key.le back_lo klo then q back_lo khi
      else
        let top_pt = { klo with pvalue = line_max klo.pwidth } in
        let zero_pt = { klo with pvalue = 0L } in
        List.dedup_and_sort ~compare:(fun (a, _) (b, _) -> Key.compare a b)
          (q back_lo top_pt @ q zero_pt khi) in
    (* Only a point cell has a determined byte extent; its bytes overlap
       the read when the spans meet. *)
    let overlaps ((c, v) : Key.t * Val.t) : bool =
      if not (Key.equal (Key.lower c) (Key.upper c)) then true
      else
        let cbits, _ = Val.get_idx v in
        let clo = (Key.lower c).pvalue in
        let cbytes = Stdlib.Int64.of_int (cbits / addressable_width) in
        Stdlib.Int64.compare clo khi.pvalue <= 0
        && Stdlib.Int64.compare
             (Stdlib.Int64.add clo (Stdlib.Int64.pred cbytes))
             qlo >= 0 in
    let contains ((c, v) : Key.t * Val.t) : Val.t option =
      if not (Key.equal (Key.lower c) (Key.upper c)) then None
      else
        let cbits, cendian = Val.get_idx v in
        if cbits < bits || not (Bitvector.compare_endian cendian endian = 0)
        then None
        else
          let d_bytes =
            Stdlib.Int64.to_int (Stdlib.Int64.sub qlo (Key.lower c).pvalue) in
          if d_bytes < 0 || d_bytes + req_bytes > cbits / addressable_width
          then None
          else if d_bytes = 0 && Int.equal cbits bits then
            (* The whole cell at its start: keep the value, origin and all. *)
            Some v
          else
            let lo =
              match endian with
              | LittleEndian -> d_bytes * addressable_width
              | BigEndian -> cbits - bits - (d_bytes * addressable_width) in
            Some
              (Val.create
                 (WordSet.extract ~hi:(lo + bits - 1) ~lo (Val.data v))
                 endian) in
    (match List.filter cands ~f:overlaps with
     | [ one ] -> contains one
     | _ -> None)

(* Values stored at a key: an assembly of narrower cells covering a
   point read exactly, a single containing wider cell it starts inside,
   else the cells read on the key's grid. *)
let find' (i : Val.idx) (m : itree) (k : Key.t) : Val.t =
  assert(fst i > 0);
  let req_bytes = fst i / addressable_width in
  let query_k, expanded =
    if req_bytes > 1 && Key.equal (Key.lower k) (Key.upper k) then
      let hi =
        { (Key.lower k) with
          pvalue =
            Stdlib.Int64.add (Key.lower k).pvalue
              (Stdlib.Int64.of_int (req_bytes - 1)) } in
      ( { Key.origin = Key.origin k; lo = Key.lower k; hi; step = Key.step k },
        true )
    else (k, false) in
  let ints_list = Seq.to_list (it_intersections m query_k) in
  match try_assemble_cells i query_k ints_list with
  | Some v -> v
  | None -> (
    match containing_cell i m k with
    | Some v -> v
    | None ->
      (* [ints_list] is the read's own query, or a superset widened by the
         read size: the cells containing the read's start are [m k]'s. *)
      let cell_ints =
        if expanded then
          List.filter ints_list ~f:(fun (c, _) -> Key.contains c (Key.lower k))
        else ints_list in
      read_cells i k cell_ints)

let find (i : Val.idx) (m : t) (k : Key.t) =
  match m.itree with None -> Val.bottom i | Some t -> find' i t k

(* Index of values at a key. *)
let find_idx' (m : itree) (k : Key.t) : Val.idx =
  fold_intersections ~default:Val.Idx.top m k ~f:(fun hd _ tl ->
    Seq.map ~f:(Fn.compose Val.get_idx snd) tl
    |> Seq.fold ~init:(Val.get_idx hd) ~f:Val.Idx.join)

let find_idx (m : t) (k : Key.t) : Val.idx =
  Option.value_map m.itree ~default:Val.Idx.top ~f:(fun t -> find_idx' t k)

(* Order via cellwise precedes. *)
let precedes' (m1 : itree) (m2 : itree) : bool =
  let m1_seq = IT.to_sequence m1 in
  let m2_seq = IT.to_sequence m2 in
  Seq.for_all m1_seq ~f: begin fun (k, v) ->
    (* Gaps precede the default. *)
    (it_dominates m2 k ||
     Val.precedes v (Val.top (Val.get_idx v))) &&
    Seq.for_all (it_intersections m2 k) ~f:begin fun (_,v') ->
      Val.precedes v v'
    end
  end &&
  Seq.for_all m2_seq ~f: begin fun (k, v) ->
    (* Default precedes gaps. *)
    (it_dominates m2 k ||
     Val.precedes (Val.top (Val.get_idx v)) v) &&
    Seq.for_all (it_intersections m2 k) ~f:begin fun (_,v') ->
      Val.precedes v' v
    end
  end

let precedes (m1 : t) (m2 : t) : bool =
  assert(m1.width = m2.width);
  match m1.itree, m2.itree with
  | None, _ -> true
  | Some _, None -> false
  | Some t1, Some t2 -> precedes' t1 t2


let equal' (m1 : itree) (m2 : itree) : bool =
  (* The stabilization check re-compares mostly-identical trees: the
     physical-equality fast path skips the per-cell semantic walk. *)
  if phys_equal m1 m2 then true
  else
  Seq.for_all (IT.to_sequence m1) ~f: begin fun (key, d1) ->
    let d2 = find' (Val.get_idx d1) m2 key in
    (* Keys are disjoint. *)
    Val.equal d1 d2
  end && Seq.for_all (IT.to_sequence m2) ~f: begin fun (key, d2) ->
    let d1 = find' (Val.get_idx d2) m1 key in
    Val.equal d1 d2
  end

let equal (m1 : t) (m2 : t) : bool =
  assert(m1.width = m2.width);
  Option.equal equal' m1.itree m2.itree

(* Join may grow the tree. *)


(* Shared key walk for join, meet, and widen: the op takes the pair's
   key (the cell-landmark rows are keyed by it). *)
let fold_keys (op : Key.t -> Val.t -> Val.t -> Val.t) (m1 : itree)
    (m2 : itree) : itree =
  let m1_seq = Seq.map ~f:fst (IT.to_sequence m1) in
  let m2_seq = Seq.map ~f:fst (IT.to_sequence m2) in
  let keys = Key.seq_product m1_seq m2_seq in
  Seq.fold keys ~init:IT.empty ~f: begin fun it (s, key) ->
    (* Best index for this key. *)
    let idx = match s with
      | Key.Left -> find_idx' m1 key
      | Key.Right -> find_idx' m2 key
      | Key.Both_sides ->
        let idx1 = find_idx' m1 key in
        let idx2 = find_idx' m2 key in
        Val.Idx.join idx1 idx2 in
    let d1 = find' idx m1 key in
    let d2 = find' idx m2 key in
    IT.add it key @@ op key d1 d2
  end

let join' (m1 : itree) (m2 : itree) : itree =
  coalesce (fold_keys (fun _ d1 d2 -> Val.join d1 d2) m1 m2)

let lift_join f (m1 : t) (m2 : t) : t =
  assert(m1.width = m2.width);
  match m1.itree, m2.itree with
  | Some t1, Some t2 -> {itree=Some (f t1 t2); width=m1.width}
  | Some _, None -> m1
  | None, Some _ -> m2
  | None, None -> m1 (* both bottom *)

let join : t -> t -> t = lift_join join'

(* The trees widen cell by cell over the key-aligned product: every
   overlapping pair takes the caller's per-cell widen, and a cell only
   one side holds widens against the other side's default. *)
let widen_join_op (w : Key.t -> Val.t -> Val.t -> Val.t) : t -> t -> t =
  lift_join (fun t1 t2 -> coalesce (fold_keys w t1 t2))

let widen_join = widen_join_op (fun _ d1 d2 -> Val.widen_join d1 d2)

(* The stored cells, key and value.  A full treap walk: the backward
   address filter's element-level coverage test is the per-cell caller;
   the read path never uses it. *)
let cells (m : t) : (Key.t * Val.t) list =
  match m.itree with
  | None -> []
  | Some it -> IT.to_sequence it |> Sequence.to_list


(* Meet may grow the tree. *)
let meet' (m1 : itree) (m2 : itree) : itree =
  fold_keys (fun _ d1 d2 -> Val.meet d1 d2) m1 m2

let meet (m1 : t) (m2 : t) : t =
  assert(m1.width = m2.width);
  match m1.itree, m2.itree with
  | Some t1, Some t2 -> {itree=Some (meet' t1 t2); width=m1.width}
  | None, _ -> {itree=None; width=m1.width}
  | _, None -> {itree=None; width=m1.width}


let pp ppf (m : t) : unit =
  let itree = Option.map m.itree ~f:(IT.filter ~f:(fun d ->
      not (Val.equal_top d))) in
  match itree with
  | None -> Format.fprintf ppf "unreachable"
  | Some t ->
    Format.fprintf ppf "@[<2>----------------------------------------@ ";
    t
    |> IT.to_sequence
    |> Seq.iter ~f:(fun (k, v) -> Format.fprintf ppf "@[<hov 1>[%a@ -> %a]@]@ " Key.pp k Val.pp v);
    Format.fprintf ppf "----------------------------------------@]"
