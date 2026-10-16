(* The analysis's word sets: a scalar value, or a value wider than a
   word whose words carry origins.  An origin rides a pointer-sized
   word, so such a value keeps its words as lanes (low lane first, at
   least one carrying an origin).  Concat, extract, the widening cast
   and the lattice ops at shared lane boundaries keep the lanes; every
   other op computes on the plain value, the scalar concat of the
   lanes. *)

open !Core
open Bap.Std

module S = Cbat_clp_set_scalar
module Clp = S.Clp
module Origin = S.Origin

type t = Scalar of S.t | Lanes of S.t list [@@deriving bin_io, sexp, compare]
type word = Cbat_word.t
type idx = int
type address_verdict = S.address_verdict

type kind = S.kind =
  | Range of int64 * int64
  | Infinite of int64 * int64
  | Caller of int64 * int64
  | Mixed of int64 * int64

(* ---------------- lanes ---------------- *)

let lanes_of (t : t) : S.t list = match t with Scalar s -> [ s ] | Lanes ls -> ls

(* A word worth a lane of its own: it carries an origin other than Abs. *)
let carries (s : S.t) : bool =
  match S.origin s with Some o -> not (Origin.equal o Origin.Abs) | None -> false

let has_lanes (t : t) : bool =
  match t with Lanes _ -> true | Scalar s -> carries s

let bitwidth (t : t) : int =
  match t with
  | Scalar s -> S.bitwidth s
  | Lanes ls -> List.fold ls ~init:0 ~f:(fun a s -> a + S.bitwidth s)

(* The plain value: the lanes concatenated, each above the lower ones. *)
let[@inline] plain (t : t) : S.t =
  match t with
  | Scalar s -> s
  | Lanes ls -> List.reduce_exn ls ~f:(fun lo hi -> S.concat hi lo)

(* The canonical value of [ts] (low first, non-empty): nested lanes
   splice, adjacent lanes without an origin merge into their concat,
   and a sequence with no origin lane is one scalar. *)
let make_lanes (ts : t list) : t =
  let ls = List.concat_map ts ~f:lanes_of in
  if List.exists ls ~f:S.is_bottom then
    Scalar (S.bottom (List.fold ls ~init:0 ~f:(fun a s -> a + S.bitwidth s)))
  else
    let merged =
      List.fold ls ~init:[] ~f:(fun acc s ->
          match acc with
          | prev :: rest when not (carries prev || carries s) -> S.concat s prev :: rest
          | _ -> s :: acc)
    in
    match List.rev merged with [ s ] -> Scalar s | ls -> Lanes ls

let is_bottom (t : t) : bool =
  match t with Scalar s -> S.is_bottom s | Lanes ls -> List.exists ls ~f:S.is_bottom

let is_top (t : t) : bool =
  match t with Scalar s -> S.is_top s | Lanes ls -> List.for_all ls ~f:S.is_top

(* The bit offsets ending [t]'s lanes, ascending. *)
let lane_ends (t : t) : int list =
  List.folding_map (lanes_of t) ~init:0 ~f:(fun off s ->
      let e = off + S.bitwidth s in
      (e, e))

(* ---------------- the two dispatches ---------------- *)

(* THE unary dispatch above the scalar's: bits [lo..hi] of a lane value
   are the lanes they cover (a wholly covered lane keeps its origin, a
   partly covered one extracts); an unsigned widening of a lane value
   appends a zero lane; a narrowing cast is the low (or [HIGH]: high)
   extract.  Every other row computes on the plain value. *)
let rec lift1 (op : S.unop) (t : t) : t =
  let w = bitwidth t in
  match op, t with
  | S.Cast (Bil.UNSIGNED, sz), _ when sz > w && has_lanes t ->
    make_lanes [ t; Scalar (S.singleton (Cbat_word.zero (sz - w))) ]
  | S.Cast (Bil.HIGH, sz), Lanes _ when sz > 0 && sz <= w ->
    lift1 (S.Extract (Some (w - 1), w - sz)) t
  | S.Cast (_, sz), Lanes _ when sz > 0 && sz <= w -> lift1 (S.Extract (Some (sz - 1), 0)) t
  | S.Extract (hi, lo), Lanes ls
    when lo >= 0 && lo <= Option.value hi ~default:(w - 1)
         && Option.value hi ~default:(w - 1) < w ->
    let hi = Option.value hi ~default:(w - 1) in
    List.fold ls ~init:(0, []) ~f:(fun (off, acc) s ->
        let sw = S.bitwidth s in
        let a = Int.max lo off and b = Int.min hi (off + sw - 1) in
        let acc =
          if a > b then acc
          else if a = off && b = off + sw - 1 then Scalar s :: acc
          else Scalar (S.lift1 (S.Extract (Some (b - off), a - off)) s) :: acc
        in
        (off + sw, acc))
    |> snd |> List.rev |> make_lanes
  | _ -> Scalar (S.lift1 op (plain t))

(* [t] cut at [ends]: each segment lies within one lane of [t] when
   [ends] contains [t]'s own lane ends. *)
let segments (t : t) (ends : int list) : S.t list =
  List.folding_map ends ~init:0 ~f:(fun lo e ->
      (e, plain (lift1 (S.Extract (Some (e - 1), lo)) t)))

(* [op] lane by lane at both sides' lane boundaries.  A side's segments
   over-approximate it (their product contains it). *)
let lanewise (op : S.t -> S.t -> S.t) (a : t) (b : t) : t =
  match a, b with
  | Scalar a, Scalar b -> Scalar (op a b)
  | _ when bitwidth a <> bitwidth b -> Scalar (op (plain a) (plain b))
  | _ ->
    let ends =
      Cbat_vsa_utils.merge_dedup ~compare:Int.compare (lane_ends a) (lane_ends b) in
    make_lanes
      (List.map2_exn (segments a ends) (segments b ends) ~f:(fun x y -> Scalar (op x y)))

(* A join-like op on lanes: a bottom side is the identity. *)
let join_like (op : S.t -> S.t -> S.t) (a : t) (b : t) : t =
  match a, b with
  | Scalar a, Scalar b -> Scalar (op a b)
  | _ when is_bottom a -> b
  | _ when is_bottom b -> a
  | _ -> lanewise op a b

(* THE binary dispatch above the scalar's: a concat with a lane operand
   keeps both operands' lanes; the join and meet of lane values go lane
   by lane.  Every other row computes on the plain values. *)
let lift2 (op : S.binop) (a : t) (b : t) : t =
  match op, a, b with
  | S.Concat, _, _ when has_lanes a || has_lanes b -> make_lanes [ b; a ]
  | _, Scalar a, Scalar b -> Scalar (S.lift2 op a b)
  | S.Union, _, _ -> join_like (S.lift2 op) a b
  | S.Meet, _, _ -> lanewise (S.lift2 op) a b
  | _ -> Scalar (S.lift2 op (plain a) (plain b))

let union a b = lift2 S.Union a b
let intersection a b = lift2 S.Meet a b
let join = union
let meet = intersection
let add a b = lift2 S.Add a b
let sub a b = lift2 S.Sub a b
let mul a b = lift2 S.Mul a b
let div a b = lift2 S.Div a b
let sdiv a b = lift2 S.Sdiv a b
let modulo a b = lift2 S.Modulo a b
let smodulo a b = lift2 S.Smodulo a b
let lshift a b = lift2 S.Lshift a b
let rshift a b = lift2 S.Rshift a b
let arshift a b = lift2 S.Arshift a b
let logand a b = lift2 S.Logand a b
let logor a b = lift2 S.Logor a b
let logxor a b = lift2 S.Logxor a b
let concat a b = lift2 S.Concat a b
let lnot t = lift1 S.Lnot t
let neg t = lift1 S.Neg t
let extract ?hi ?lo t = lift1 (S.Extract (hi, Option.value lo ~default:0)) t
let cast c sz t = lift1 (S.Cast (c, sz)) t

let widen_join = join_like S.widen_join
let extrapolate_steps ~steps = join_like (S.extrapolate_steps ~steps)
let diff a b = Scalar (S.diff (plain a) (plain b))

(* Against a lane value, [a] compares through its segments at [b]'s
   boundaries (their product contains [a]). *)
let precedes (a : t) (b : t) : bool =
  match a, b with
  | Scalar a, Scalar b -> S.precedes a b
  | _, Lanes ls when bitwidth a = bitwidth b ->
    List.for_all2_exn (segments a (lane_ends b)) ls ~f:S.precedes
  | _ -> S.precedes (plain a) (plain b)

let equal (a : t) (b : t) : bool =
  phys_equal a b ||
  match a, b with
  | Scalar a, Scalar b -> S.equal a b
  | Lanes a, Lanes b -> List.equal S.equal a b
  | _ -> false

let get_idx (t : t) : idx = match t with Scalar s -> S.get_idx s | Lanes _ -> bitwidth t
let top_cache : t array = Array.init 257 ~f:(fun i -> Scalar (S.top (Int.max i 1)))
let top (i : idx) : t =
  if i > 0 && i < Array.length top_cache then top_cache.(i) else Scalar (S.top i)
let bottom (i : idx) : t = Scalar (S.bottom i)

(* A lane value prints high lane first, as BIL writes a concat. *)
let pp ppf (t : t) =
  match t with
  | Scalar s -> S.pp ppf s
  | Lanes ls ->
    Format.fprintf ppf "@[<1>[%a]@]"
      (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf ".@,") S.pp)
      (List.rev ls)

(* ---------------- the scalar queries ---------------- *)

(* A lane value names no address and keeps its lanes under re-tagging. *)
let on_scalar f t = match t with Scalar s -> Scalar (f s) | Lanes _ -> t

let origin t = match t with Scalar s -> S.origin s | Lanes _ -> None
let set_origin o = on_scalar (S.set_origin o)
let keep_section ~old ~new_ = on_scalar (S.keep_section ~old:(plain old) ~new_:(plain new_))
let filter_addresses t ~decide = on_scalar (S.filter_addresses ~decide) t

let of_list ~width l = Scalar (S.of_list ~width l)
let of_exact s = Scalar (S.of_exact s)
let singleton w = Scalar (S.singleton w)
let of_clp p = Scalar (S.of_clp p)
let module_address a = Scalar (S.module_address a)
let stack_word p = Scalar (S.stack_word p)
let stack_word_i64 k = Scalar (S.stack_word_i64 k)

let cardinality t = S.cardinality (plain t)
let min_elem t = S.min_elem (plain t)
let max_elem t = S.max_elem (plain t)
let min_elem_signed t = S.min_elem_signed (plain t)
let max_elem_signed t = S.max_elem_signed (plain t)
let splits_by t w = S.splits_by (plain t) w
let elem w t = S.elem w (plain t)
let iter t = S.iter (plain t)
let overlap a b = S.overlap (plain a) (plain b)
let is_infinite t = S.is_infinite (plain t)
let is_ascending t = S.is_ascending (plain t)
let is_descending t = S.is_descending (plain t)
let is_circular t = S.is_circular (plain t)
let stack_offsets t = S.stack_offsets (plain t)
let stack_leaves t = List.map (S.stack_leaves (plain t)) ~f:(fun s -> Scalar s)
let address_groups t = S.address_groups (plain t)
let stride t = S.stride (plain t)
let in_stack_segment t = S.in_stack_segment (plain t)
let offset_extrema t = S.offset_extrema (plain t)
let singleton_of t = S.singleton_of (plain t)
let stack_bounds t = S.stack_bounds (plain t)
let offset_runs t = S.offset_runs (plain t)
let classify t = S.classify (plain t)
let enumerate ~cap t = S.enumerate ~cap (plain t)

let stack_base = S.stack_base
let key_line = S.key_line
let equal_kind = S.equal_kind
let unbounded_span = S.unbounded_span
let is_unbounded_span = S.is_unbounded_span
let position_of_offset = S.position_of_offset
let caller_split = S.caller_split

#ifdef VSA_DEBUG
let tag t =
  match t with Scalar s -> S.tag s | Lanes ls -> sprintf "Lanes%d" (List.length ls)
#endif

let backward1 op ~arg ~result =
  let answer = S.backward1 op ~arg:(plain arg) ~result:(plain result) in
  if S.is_bottom answer then Scalar (S.bottom (bitwidth arg))
  else intersection arg (Scalar answer)

let backward2 op ~left ~right ~result =
  let a,b = S.backward2 op ~left:(plain left) ~right:(plain right) ~result:(plain result) in
  let keep original answer =
    if S.is_bottom answer then Scalar (S.bottom (bitwidth original))
    else intersection original (Scalar answer) in
  keep left a,keep right b
