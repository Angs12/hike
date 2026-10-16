(* CLP core: types, creation, order, meet/join, widening, printing. *)

open Bap.Std
open Bin_prot.Std
include Cbat_vsa_utils

module W = Cbat_word
module Option = Core.Option
module Sexp = Core.Sexp
module List = Core.List

open !Cbat_word
open Core
let min = Stdlib.min
let max = Stdlib.max
let ( = ) = Stdlib.( = )
let ( <> ) = Stdlib.( <> )
let ( < ) = Stdlib.( < )
let ( > ) = Stdlib.( > )
let ( <= ) = Stdlib.( <= )
let ( >= ) = Stdlib.( >= )

type direction =
  | Finite
  | Ascending
  | Descending
  | Circular
[@@deriving bin_io, sexp, compare]

type word = W.t

(* {base +/- n*step | 0 <= n < cardn}; only Descending subtracts. *)
type t = {
  base : W.t;
  step : W.t;
  cardn : W.t;
  dir : direction;
}
[@@deriving bin_io, sexp, compare]

let base_of (p : t) : W.t = p.base
let step_of (p : t) : W.t = p.step
let cardn_of (p : t) : W.t = p.cardn

let is_ascending (p : t) : bool =
  match p.dir with Ascending -> true | _ -> false

let is_descending (p : t) : bool =
  match p.dir with Descending -> true | _ -> false

let is_circular (p : t) : bool =
  match p.dir with Circular -> true | _ -> false

let is_infinite (p : t) : bool =
  match p.dir with Finite -> false | _ -> true

let fit_to (width : int) (w : W.t) : W.t =
  if W.bitwidth w = width then W.unsigned w else W.extract_exn ~hi:(width - 1) w

let create ?(width : int option) ?(step = W.b1) ?(cardn = W.b1) base : t =
  let width = Option.value ~default:(W.bitwidth base) width in
  let cardn_w = W.cap_at_width ~width:(width + 1) (W.unsigned cardn) in
  let base' = fit_to width base in
  let step' = fit_to width step in
  
  if W.is_zero cardn_w then
    {base = W.zero width; step = W.zero width; cardn = W.zero (width + 1); dir = Finite}
  else if W.is_zero step' || is_one cardn_w then
    {base = base'; step = W.zero width; cardn = W.one (width + 1); dir = Finite}
  else if W.(=) cardn_w (W.of_int ~width:(width + 1) 2) then
    let e = W.add base' step' in
    if W.(>=) e base' then {base = base'; step = step'; cardn = cardn_w; dir = Finite}
    else {base = e; step = W.neg step'; cardn = cardn_w; dir = Finite}
  else
    (* [cardn_w] has [width+1] bits, [step'] [width]; the exact product
       reaches [2^width] exactly when the operands' bit lengths sum past
       [width].  A sum of exactly [width+1] is the one undecided case:
       the product's own top bit decides it. *)
    let bits (x : W.t) = match lead_1_bit x with None -> 0 | Some k -> k + 1 in
    let is_wrap =
      let sum = bits cardn_w + bits step' in
      if sum >= width + 2 then true
      else if sum <= width then false
      else msb (W.mul cardn_w step')
    in
    if is_wrap then
      let div, twos = factor_2s step' in
      let step'' = W.div step' div in
      let base'' = W.modulo base' step'' in
      let cardn'' = dom_size ~width:(width + 1) (width - twos) in
      {base = base''; step = step''; cardn = cardn''; dir = Circular}
    else
      {base = base'; step = step'; cardn = cardn_w; dir = Finite}

let singleton w = create w

let bitwidth (p : t) : int = W.bitwidth p.base

let bottom (width : int) : t =
  assert(width > 0);
  create ~width W.b0 ~cardn:W.b0

let is_bottom (p : t) : bool = W.is_zero (cardn_of p)

let infinite (b, s) : t =
  let width = W.bitwidth b in
  assert (width = W.bitwidth s);
  if W.is_zero s then create b
  else let div, twos = factor_2s s in
    let step = W.div s div in
    let base = W.modulo b step in
    let cardn = dom_size ~width:(width + 1) (width - twos) in
    {base; step; cardn; dir = Circular}

(* Cached per width.  Widths are small and bounded, so an array beats a
   hash table (the profile's hot [caml_hash]). *)
let top_cache : t option array = Stdlib.Array.make 2049 None

let top (i : int) : t =
  assert(i > 0);
  if i < Array.length top_cache then
    match top_cache.(i) with
    | Some t -> t
    | None ->
      let t = infinite (W.zero i, W.one i) in
      top_cache.(i) <- Some t;
      t
  else infinite (W.zero i, W.one i)

(* A ray from [base] by [step]; [num_steps] counts the steps to the
   domain edge in the ray's direction. *)
let ray ~dir ~width ~base ~step (num_steps : W.t -> W.t -> W.t) : t =
  assert (width > 0);
  let base' = fit_to width base in
  let step' = fit_to width step in
  if W.is_zero step' then create ~width base'
  else
    let cardn = W.succ (W.extract_exn ~hi:width (num_steps base' step')) in
    if is_one cardn then create ~width base'
    else if W.is_zero cardn then bottom width
    else if W.equal cardn (dom_size ~width:(width + 1) width) then top width
    else { base = base'; step = step'; cardn; dir }

let create_ascending ~width ~base ~step : t =
  ray ~dir:Ascending ~width ~base ~step (fun base' step' ->
      W.div (W.sub (W.ones width) base') step')

let create_descending ~width ~base ~step : t =
  ray ~dir:Descending ~width ~base ~step W.div

let cardn_from_bounds base step e : W.t =
  let width = W.bitwidth base in
  assert(W.bitwidth step = width);

    if W.is_zero step then W.one (width + 1) else
    (* Step 1 (every interval) needs no division. *)
    let diff = W.sub e base in
    let div_by_step =
      if W.is_one step then diff else W.div diff step in
    (* Extra bit so succ never wraps. *)
    W.succ (W.extract_exn ~hi:width div_by_step)

(* Step-1 CLP [lo, hi]; wrapped pair is circular. *)
let interval ~(width : int) (lo : W.t) (hi : W.t) : t =
  create ~width ~step:(W.one width)
    ~cardn:(cardn_from_bounds lo (W.one width) hi) lo

(* Sound hull of an ascending, deduped list (a precondition — no sort). *)
let of_list ~width l : t =
  assert (width > 0);
  let open Monads.Std.Monad.Option.Syntax in
  (match begin
    let l = List.map l ~f:(W.extract_exn ~hi:(width - 1) ~lo:0) in
#ifdef VSA_DEBUG
    let () = assert (List.is_sorted l ~compare:W.compare) in
#endif
    let diff_list = List.map2_exn l (rotate_list l) ~f:W.sub in
    let idx, _, step = List.foldi diff_list ~init:(0, W.zero width, W.zero width)
        ~f:(fun i (idx, diff, step) d ->
            assert(W.bitwidth diff = W.bitwidth step);
            assert(W.bitwidth diff = W.bitwidth d);
            if W.(>) d diff
             then i, d, bounded_gcd diff step
             else idx, diff, bounded_gcd d step) in
    let l = idx
            (* Rotate to the first element. *)
            |> List.split_n l
            |> (fun (end_l, start_l) -> List.append start_l end_l) in
    List.hd l >>= fun base ->
    List.last l >>= fun e ->
    let cardn = cardn_from_bounds base step e in
    assert(W.bitwidth base = width);
    !!(create base ~step ~cardn)
  end with
  | None -> bottom width
  | Some x -> x)

(* Cardinality as a (width+1)-bit W.t; exact for a finite CLP. *)
let cardinality (p : t) : W.t = cardn_of p

(* The same denotation traversed with a positive step. *)
let forward (p : t) : t =
  match p.dir with
  | Descending -> {p with base = W.modulo p.base p.step; dir = Finite}
  | Ascending -> {p with dir = Finite}
  | Finite | Circular -> p

(* Last point of the forward traversal. *)
let finite_end (p : t) : W.t option =
  let p = forward p in
  let width = bitwidth p in
  let n = W.extract_exn ~hi:(width - 1) (cardn_of p) in
  if W.is_zero (cardn_of p) then None
  else Some (W.add (base_of p) (W.mul (step_of p) (W.pred n)))

let lnot (p : t) : t =
  match finite_end p with
  | None -> bottom (bitwidth p)
  | Some e ->
    match p.dir with
    | Ascending -> {p with base = W.lnot p.base; dir = Descending}
    | Descending -> {p with base = W.lnot p.base; dir = Ascending}
    | Finite | Circular -> {p with base = W.lnot e}

let iter (p : t) : W.t list =
  let p = forward p in
  let rec iter_acc b s n acc =
    if W.is_zero n then acc
    else let n' = W.pred n in
      iter_acc (W.add b s) s n' (b :: acc) in
  List.rev (iter_acc (base_of p) (step_of p) (cardn_of p) [])

(* Closest element at or below i. *)
let nearest_pred (i : W.t) (p : t) : W.t option =
  let p = forward p in
  assert(bitwidth p = W.bitwidth i);
  let open Monads.Std.Monad.Option.Syntax in
  finite_end p >>= fun e ->
  if W.is_zero (step_of p) then !!((base_of p))
  else
    let diff = W.sub i (base_of p) in
    let rm = W.modulo diff (step_of p) in
    let end' = W.sub e (base_of p) in
    if is_infinite p then !!(W.sub i rm)
    else if W.(>=) diff end' then !!(W.add end' (base_of p)) else
      !!(W.sub i rm)

let nearest_inf_pred (w : W.t) (base : W.t) (step : W.t) : W.t =
  if W.is_zero step then base else
    let diff = W.sub w base in
    let rm = W.modulo diff step in
    W.sub w rm

let nearest_succ (i : W.t) (p : t) : W.t option =
  Option.map ~f:W.lnot (nearest_pred (W.lnot i) (lnot p))

let nearest_inf_succ (w : W.t) (base : W.t) (step : W.t) : W.t =
  W.lnot (nearest_inf_pred (W.lnot w) (W.lnot base) step)

let max_elem (p : t) : W.t option =
  if is_bottom p then None
  else match p.dir with
  | Finite | Circular ->
    let max_wd = W.ones (bitwidth p) in
    nearest_pred max_wd p
  | Ascending ->
    let max_wd = W.ones (bitwidth p) in
    let diff = W.sub max_wd p.base in
    let rem = if W.is_zero p.step then W.zero (bitwidth p) else W.modulo diff p.step in
    Some (W.sub max_wd rem)
  | Descending -> Some p.base

let min_elem (p : t) : W.t option =
  if is_bottom p then None
  else match p.dir with
  | Finite | Circular ->
    let min_wd = W.zero (bitwidth p) in
    nearest_succ min_wd p
  | Ascending -> Some p.base
  | Descending ->
    if W.is_zero p.step then Some p.base else Some (W.modulo p.base p.step)

let is_wrapped (p : t) : bool =
  if is_infinite p || is_bottom p then false
  else
    match finite_end p with
    | Some e -> W.(<) e (base_of p)
    | None -> false

(* The elements at or below [bound], then the rest; each part is a
   non-wrapping arc when the input's span crosses [bound] once.  The
   input must start at or below [bound]. *)
let split_above (bound : W.t) (p : t) : t list =
  let width = bitwidth p in
  let b = base_of p and s = step_of p in
  if W.is_zero s then [ p ]
  else
    let n = W.extract_exn ~hi:(width - 1) (cardn_of p) in
    if W.is_zero n then [ infinite (b, s) ]
    else
      (* First index whose element exceeds [bound]. *)
      let k = W.succ (W.div (W.sub bound b) s) in
      let below = create ~width ~step:s ~cardn:k b in
      let above_count = W.sub n k in
      if W.is_zero above_count then [ below ]
      else
        let above_base = W.add b (W.mul k s) in
        let above = create ~width ~step:s ~cardn:above_count above_base in
        [ below; above ]

(* A wrapped Finite piece is two non-wrapping arcs (the high arc before
   the modulus and the low arc after the wrap); the meet of each arc is
   joined. *)
let split_wrapped (p : t) : t list =
  if not (is_wrapped p) then [ p ]
  else split_above (W.ones (bitwidth p)) p

(* The elements in ascending unsigned order.  [iter] follows the
   traversal, so a wrapped progression runs its high arc before its low
   one; this emits the arcs by base. *)
let iter_ascending (p : t) : W.t list =
  match split_wrapped p with
  | [ a; b ] when W.(>) (base_of a) (base_of b) -> iter b @ iter a
  | arcs -> List.concat_map arcs ~f:iter

(* The runs of one sign half: the non-negative elements first, the
   negative ones after.  Each run maps element-wise under a signed
   cast. *)
let split_sign (p : t) : t list =
  List.concat_map (split_wrapped p) ~f:(fun q ->
      match finite_end q with
      | None -> [ q ]
      | Some e ->
        if Bool.equal (W.msb (base_of q)) (W.msb e) then [ q ]
        else split_above (W.pred (half (bitwidth q))) q)

(* Signed order: at/above the half the word is negative. *)
let signed_le (width : int) (x : W.t) (y : W.t) : bool =
  let h = half width in
  match W.(>=) x h, W.(>=) y h with
  | true, false -> true
  | false, true -> false
  | _ -> W.(<=) x y

(* The signed extrema of one NON-wrapped finite arc [a, a+s, ..., l]
   (l >= a unsigned).  Elements at/above the half are negative: the
   signed max is the largest element below the half (the whole arc
   when every element is at/above it), the signed min the smallest
   element at/above the half (the whole arc when every element is
   below it). *)
let arc_max_signed (p : t) : W.t =
  let width = bitwidth p in
  let h = half width in
  let a = base_of p and s = step_of p in
  let l = Option.value (finite_end p) ~default:a in
  if W.(>=) a h then l
  else if W.(<) l h then l
  else
    let n = W.extract_exn ~hi:width (cardn_of p) in
    let k = W.div (W.sub (W.pred h) a) s in
    let k = if W.(>=) k (W.pred n) then W.pred n else k in
    W.add a (W.mul k s)

let arc_min_signed (p : t) : W.t =
  let width = bitwidth p in
  let h = half width in
  let a = base_of p and s = step_of p in
  let l = Option.value (finite_end p) ~default:a in
  if W.(<) l h then a
  else if W.(>=) a h then a
  else
    let n = W.extract_exn ~hi:width (cardn_of p) in
    let gap = W.sub h a in
    let k = W.div gap s in
    let rem = W.modulo gap s in
    let k = if W.is_zero rem then k else W.succ k in
    let k = if W.(>=) k (W.pred n) then W.pred n else k in
    W.add a (W.mul k s)

(* The signed extrema of a finite piece: its (possibly two) arcs
   answer separately and the signed order folds them — a wrapped
   traversal measures exactly instead of answering None. *)
let max_elem_signed (p : t) : W.t option =
  if is_bottom p then None
  else match p.dir with
  | Descending -> Some p.base
  | Ascending | Circular -> nearest_pred (W.pred (half (bitwidth p))) p
  | Finite ->
    let width = bitwidth p in
    List.fold (split_wrapped p) ~init:None ~f:(fun acc arc ->
        let c = arc_max_signed arc in
        match acc with
        | None -> Some c
        | Some b -> Some (if signed_le width c b then b else c))

(* Min signed element. *)
let min_elem_signed (p : t) : W.t option =
  if is_bottom p then None
  else match p.dir with
  | Ascending -> Some p.base
  | Descending | Circular -> nearest_succ (half (bitwidth p)) p
  | Finite ->
    let width = bitwidth p in
    List.fold (split_wrapped p) ~init:None ~f:(fun acc arc ->
        let c = arc_min_signed arc in
        match acc with
        | None -> Some c
        | Some b -> Some (if signed_le width c b then c else b))

let splits_by (p : t) (w : W.t) : bool =
  let divides a b = W.is_zero (W.modulo b a) in
  let open Monads.Std.Monad.Option.Syntax in
  Option.value ~default:true begin
    min_elem p >>= fun min_p ->
    finite_end p >>= fun e ->
    if W.is_zero (step_of p) then !!true else
      (* Multi-element case. *)
      !!(divides w (step_of p) &&
         (* Wrapping case. *)
         (W.(=) (base_of p) min_p ||
          divides w (W.sub e (base_of p))))
  end

(* Membership. *)
let elem (i : W.t) (p : t) : bool =
  assert (W.bitwidth i = bitwidth p);
  Option.value_map (nearest_pred i p) ~default:false ~f:(W.( = ) i)

(* Equivalence; faster than subset.  The structural comparison over
   the record's fields (all comparable words/directions), not the
   polymorphic hook. *)
let equal (p1 : t) (p2 : t) : bool =
  if phys_equal p1 p2 then true
  else if bitwidth p1 <> bitwidth p2 then false
  else
    Int.equal (compare_direction p1.dir p2.dir) 0
    && W.equal p1.base p2.base
    && W.equal p1.step p2.step
    && W.equal p1.cardn p2.cardn

(* Top test via the canonical top value. *)
let is_top (p : t) : bool = equal p (top (bitwidth p))

(* Rebase onto an extrema interval; [default] when the extrema give
   out (bottom). *)
let unwrap_with ~default min max (p : t) : t =
  let open Monads.Std.Monad.Option.Syntax in
  match begin
    min p >>= fun base ->
    max p >>= fun e ->
    let step = (step_of p) in
    let cardn = cardn_from_bounds base step e in
    !!(create base ~step ~cardn)
  end with
  | None -> default (bitwidth p)
  | Some x -> x

let unwrap (p : t) : t = unwrap_with ~default:bottom min_elem max_elem p

let unwrap_signed (p : t) : t =
  unwrap_with ~default:top min_elem_signed max_elem_signed p

(* Smallest circular hull of two intervals.  The offsets are rebased
   to a1 (the *_rel suffix); all comparisons run in the rebased line,
   which never wraps when the intervals overlap. *)
let interval_union (a1,b1) (a2,b2) : (W.t * W.t) =
  let sz_int = W.bitwidth a1 in
  let b1_rel = W.sub b1 a1 in
  let a2_rel = W.sub a2 a1 in
  let b2_rel = W.sub b2 a1 in
  let zero = W.zero sz_int in
  (* Interleaved across the wrap: the hull is the full circle,
     spelled as the degenerate interval [b, b-1]. *)
  if W.(>=) b1_rel a2_rel && W.(<) b2_rel a2_rel then (b1, W.pred b1)
  (* [a1,b1] contains [a2,b2]. *)
  else if W.(>=) b1_rel a2_rel && W.(>=) b1_rel b2_rel then (a1, b1)
  (* [a1,b1] reaches into [a2,b2]: the hull spans to the farther end. *)
  else if W.(>=) b1_rel a2_rel then (a1, b2)
  (* Disjoint by a gap: take the spanning pair around the gap. *)
  else if W.(<) b2_rel b1_rel then (a2, b1)
  (* [a2,b2] contains [a1,b1]. *)
  else if W.(<) b2_rel a2_rel then (a2, b2)
  (* [a2,b2] wraps the rebase and covers [a1,b1]. *)
  else if W.(>) (W.sub a2_rel b1_rel) (W.sub zero b2_rel) then (a2,b1)
  else (a1, b2)

(* Rotate without changing step/cardinality. *)
let translate (p : t) i : t =
  let width = bitwidth p in
  assert (W.bitwidth i = width);
  if is_bottom p then p
  else
    let new_base = W.add (base_of p) i in
    match p.dir with
    | Finite -> create ~width new_base ~step:(step_of p) ~cardn:(cardn_of p)
    | Ascending | Descending -> (
      (* A ray's image keeps its order unless the shift carries elements
         across the word boundary.  An ordered image keeps the ray to the
         same edge (a superset); a wrapped image is the exact progression. *)
      let lo = W.add (base_of (forward p)) i in
      match finite_end p with
      | None -> p
      | Some e ->
        let hi = W.add e i in
        if W.(<) hi lo then
          create ~width lo ~step:(step_of p) ~cardn:(cardn_of p)
        else if is_ascending p then
          create_ascending ~width ~base:lo ~step:(step_of p)
        else create_descending ~width ~base:hi ~step:(step_of p))
    | Circular ->
      infinite (new_base, step_of p)

(* Largest step covering both progressions. *)
let common_step (b1,s1) (b2,s2) : W.t =
  let b_diff = if W.(>) b1 b2 then W.sub b1 b2 else W.sub b2 b1 in
  if W.is_zero s1 then bounded_gcd s2 b_diff
  else if W.is_zero s2 then bounded_gcd s1 b_diff
  else let gcd_s = (bounded_gcd s1 s2) in
    bounded_gcd gcd_s b_diff

let subset_finite (p1 : t) (p2 : t) : bool =
  let width = bitwidth p1 in
  let nb2 = W.neg (base_of p2) in
  let p1 = translate p1 nb2 in
  let p2 = translate p2 nb2 in
  (* Rotation can split the source grid into differently aligned arcs. *)
  List.for_all (split_wrapped p1) ~f:(fun p1 ->
      match finite_end p1, finite_end p2 with
      | None, _ -> true
      | Some _, None -> false
      | Some e1, Some e2 ->
        let in_bounds = W.(<=) e1 e2 && W.(<=) (base_of p1) e2 in
        let step_and_overlap = W.(=) (common_step ((base_of p1),(step_of p1)) (W.zero width, (step_of p2))) (step_of p2) in
        let singleton_elem = is_one (cardn_of p1) && elem (base_of p1) p2 in
        singleton_elem || (in_bounds && step_and_overlap))

(* Subset order. *)
let rec subset (p1 : t) (p2 : t) : bool =
  if bitwidth p1 <> bitwidth p2 then false
  else if is_bottom p1 then true
  else if is_bottom p2 then false
  else if phys_equal p1 p2 || equal p1 p2 then true
  else if is_wrapped p1 then
    List.for_all (split_wrapped p1) ~f:(fun arc -> subset arc p2)
  else
    let divides a b =
      if W.is_zero a then W.is_zero b
      else if W.is_zero b then true
      else W.is_zero (W.modulo b a)
    in
    match p1.dir, p2.dir with
    | Finite, Finite -> subset_finite p1 p2
    (* A non-bottom Finite set's extrema are Some; the [false] arms
       answer the bottom contour. *)
    | Finite, Ascending ->
      (match min_elem p1, max_elem p1 with
       | Some lo1, _ ->
         W.(>=) lo1 p2.base &&
         divides p2.step (step_of p1) &&
         W.is_zero (W.modulo (W.sub lo1 p2.base) p2.step)
       | _ -> false)
    | Finite, Descending ->
      (match min_elem p1, max_elem p1 with
       | _, Some hi1 ->
         W.(<=) hi1 p2.base &&
         divides p2.step (step_of p1) &&
         W.is_zero (W.modulo (W.sub p2.base hi1) p2.step)
       | _ -> false)
    | Ascending, Ascending ->
      W.(>=) p1.base p2.base &&
      divides p2.step p1.step &&
      W.is_zero (W.modulo (W.sub p1.base p2.base) p2.step)
    | Descending, Descending ->
      W.(<=) p1.base p2.base &&
      divides p2.step p1.step &&
      W.is_zero (W.modulo (W.sub p2.base p1.base) p2.step)
    | _, Circular ->
      divides p2.step (step_of p1) &&
      W.is_zero (W.modulo (W.sub (base_of p1) p2.base) p2.step)
    | Circular, _ -> false
    | (Ascending | Descending), Finite -> false
    | Ascending, Descending | Descending, Ascending -> false
(* Congruences are integer equations. Reducing Bezout coefficients or the
   period at word width changes the grid unless its step divides 2^width. *)
let intersect_grids ~lo1 ~s1 ~lo2 ~s2 =
  let lo1 = W.to_z lo1 and lo2 = W.to_z lo2 in
  let s1 = W.to_z s1 and s2 = W.to_z s2 in
  let g, u, _ = Z.gcdext s1 s2 in
  let delta = Z.sub lo2 lo1 in
  if Z.equal g Z.zero then
    if Z.equal delta Z.zero then Some (lo1, Z.zero) else None
  else if not (Z.equal (Z.erem delta g) Z.zero) then None
  else
    let step = Z.mul s1 (Z.div s2 g) in
    let base =
      if Z.equal step Z.zero then (if Z.equal s1 Z.zero then lo1 else lo2)
      else Z.erem (Z.add lo1 (Z.mul s1 (Z.mul u (Z.div delta g)))) step in
    Some (base, step)

let solve_point ~lower ~lo1 ~s1 ~lo2 ~s2 ~bound =
  Option.bind (intersect_grids ~lo1 ~s1 ~lo2 ~s2) ~f:(fun (base, step) ->
      let width = W.bitwidth bound in
      let bound = W.to_z bound in
      let x =
        if Z.equal step Z.zero then base
        else
          let round = if lower then Z.cdiv else Z.fdiv in
          Z.add base (Z.mul (round (Z.sub bound base) step) step) in
      let limit = Z.shift_left Z.one width in
      if Z.sign x < 0 || Z.compare x limit >= 0
         || (if lower then Z.compare x bound < 0 else Z.compare x bound > 0)
      then None
      else
        (* A period outside the target domain leaves only this singleton. *)
        let step = if Z.compare step limit >= 0 then Z.zero else step in
        Some (W.of_z x width, W.of_z step width))

let solve_grid_interval ~width ~lo1 ~s1 ~lo2 ~s2 ~min_bound ~max_bound : t =
  if W.(>) min_bound max_bound then bottom width
  else
    match solve_point ~lower:true ~lo1 ~s1 ~lo2 ~s2 ~bound:min_bound with
    | Some (base, step) when W.(<=) base max_bound ->
      create ~width base ~step ~cardn:(cardn_from_bounds base step max_bound)
    | _ -> bottom width

let solve_ascending_ascending ~width (p1 : t) (p2 : t) ~min_bound : t =
  match solve_point ~lower:true ~lo1:p1.base ~s1:p1.step ~lo2:p2.base ~s2:p2.step ~bound:min_bound with
  | None -> bottom width
  | Some (base, step) -> create_ascending ~width ~base ~step

let solve_descending_descending ~width (p1 : t) (p2 : t) ~max_bound : t =
  match solve_point ~lower:false ~lo1:p1.base ~s1:p1.step ~lo2:p2.base ~s2:p2.step ~bound:max_bound with
  | None -> bottom width
  | Some (base, step) -> create_descending ~width ~base ~step

(* A ray with a finite piece: the ray extends to the finite piece's
   near end, on the grid both share. *)
let union_ray_finite ~width ~ascending (ray : t) (fin : t) : t =
  let step = common_step (ray.base, ray.step) (fin.base, step_of fin) in
  if ascending then
    let lo = Option.value (min_elem fin) ~default:fin.base in
    create_ascending ~width ~base:(W.min ray.base lo) ~step
  else
    let hi = Option.value (max_elem fin) ~default:fin.base in
    create_descending ~width ~base:(W.max ray.base hi) ~step

(* Union; same width expected.  The finite arm's hull is MODULAR: the
   grid step divides both steps and every endpoint's modular distance
   from the hull base, so a wrap-traversing hull keeps its far end (an
   absolute-difference step can leave the wrapped end unreachable).
   Wrapped finite operands ride the same path: their traversal is the
   forward arc [base, finite_end]. *)
let rec union (p1 : t) (p2 : t) : t =
  if bitwidth p1 <> bitwidth p2 then top (Stdlib.max (bitwidth p1) (bitwidth p2))
  else
    let width = bitwidth p1 in
    if is_bottom p1 then p2
    else if is_bottom p2 then p1
    else if is_top p1 || is_top p2 then top width
    else if equal p1 p2 then p1
    else match p1.dir, p2.dir with
    | (Ascending | Descending | Circular), Finite when is_wrapped p2 ->
      List.fold (split_wrapped p2) ~init:(bottom width)
        ~f:(fun acc q -> union acc (union p1 q))
    | Finite, (Ascending | Descending | Circular) when is_wrapped p1 ->
      List.fold (split_wrapped p1) ~init:(bottom width)
        ~f:(fun acc q -> union acc (union q p2))
    | Finite, Finite ->
      Option.value_map ~default:p2 (finite_end p1) ~f:begin fun e1 ->
        Option.value_map ~default:p1 (finite_end p2) ~f:begin fun e2 ->
          let b1 = base_of p1 and b2 = base_of p2 in
          let base, newE = interval_union (b1, e1) (b2, e2) in
          let g x acc = bounded_gcd acc (W.sub x base) in
          let step =
            bounded_gcd (step_of p1) (step_of p2)
            |> g b1 |> g e1 |> g b2 |> g e2 in
          let cardn = cardn_from_bounds base step newE in
          create base ~step ~cardn
        end
      end
    | Ascending, Ascending ->
      let base = W.min p1.base p2.base in
      let step = common_step (p1.base, p1.step) (p2.base, p2.step) in
      create_ascending ~width ~base ~step
    | Descending, Descending ->
      let base = W.max p1.base p2.base in
      let step = common_step (p1.base, p1.step) (p2.base, p2.step) in
      create_descending ~width ~base ~step
    | Ascending, Finite -> union_ray_finite ~width ~ascending:true p1 p2
    | Finite, Ascending -> union_ray_finite ~width ~ascending:true p2 p1
    | Descending, Finite -> union_ray_finite ~width ~ascending:false p1 p2
    | Finite, Descending -> union_ray_finite ~width ~ascending:false p2 p1
    | _ ->
      let step = common_step (base_of p1, step_of p1) (base_of p2, step_of p2) in
      infinite (base_of p1, step)

let intersection_finite_or_circular (p1 : t) (p2 : t) : t =
  let width = bitwidth p1 in
  match min_elem p1, max_elem p1, min_elem p2, max_elem p2 with
  | Some lo1, Some hi1, Some lo2, Some hi2 ->
    solve_grid_interval ~width ~lo1 ~s1:(step_of p1) ~lo2 ~s2:(step_of p2)
      ~min_bound:(W.max lo1 lo2) ~max_bound:(W.min hi1 hi2)
  | _ -> bottom width

(* Circular step-1 arc (start, length) of a finite CLP; None otherwise.
   [create] keeps step-1 shapes verbatim, so the arc is (base, cardn)
   directly. Normalized edge shapes recover too: a singleton is a length-1
   arc; the wrapped two-point pair is stored descending (base = the second
   element, step = -1), which is the arc (base-1, 2). *)
let step1_arc (p : t) : (word * word) option =
  let width = bitwidth p in
  if is_bottom p || is_infinite p then None
  else if W.is_one (step_of p) then Some (base_of p, cardn_of p)
  else if W.is_zero (step_of p) && is_one (cardn_of p) then
    Some (base_of p, W.one (width + 1))
  else if W.is_zero (W.succ (step_of p)) && W.(=) (cardn_of p) (W.of_int ~width:(width + 1) 2) then
    Some (W.pred (base_of p), W.of_int ~width:(width + 1) 2)
  else None

(* Exact meet of two circular step-1 arcs; None when the true intersection
   is two separate pieces (not representable as one CLP). All arithmetic at
   width+1 bits so the wrap never overflows. *)
let step1_intersection (width : int) (p1 : t) (p2 : t) : t option =
  match step1_arc p1, step1_arc p2 with
  | Some (s1, l1), Some (s2, l2) ->
    let n = dom_size ~width:(width + 1) width in
    if W.(>=) l1 n then Some p2
    else if W.(>=) l2 n then Some p1
    else if W.is_zero l1 || W.is_zero l2 then Some (bottom width)
    else
      let d = W.extract_exn ~hi:width (W.sub s2 s1) in
      let e = W.add d l2 in
      if W.(>=) d l1 then begin
        (* B starts at/after A's end; only B's wrapped tail reaches into A. *)
        if W.(<) e n then Some (bottom width)
        else begin
          let tail = W.sub e n in
          let m = if W.(<=) tail l1 then tail else l1 in
          if W.is_zero m then Some (bottom width)
          else Some (create ~width s1 ~step:(W.one width) ~cardn:m)
        end
      end
      else begin
        (* B starts inside A. *)
        if W.(<=) e n then begin
          let m = if W.(<=) e l1 then e else l1 in
          if W.(=) m d then Some (bottom width)
          else Some (create ~width (W.add s1 d) ~step:(W.one width) ~cardn:(W.sub m d))
        end
        else begin
          (* B wraps: pieces [d, l1) and [0, min(e-n, l1)). *)
          let en = W.sub e n in
          let piece = if W.(<=) en l1 then en else l1 in
          if W.(>=) piece d then Some p1
          else Some (if W.(<=) l1 l2 then p1 else p2)
        end
      end
  | _ -> None

let rec intersection (p1 : t) (p2 : t) : t =
  (* Width mismatch returns the wider operand. *)
  if bitwidth p1 <> bitwidth p2 then
    (if bitwidth p1 > bitwidth p2 then p1 else p2)
  else
    let width = bitwidth p1 in
    if is_bottom p1 || is_bottom p2 then bottom width
    else if is_top p1 then p2
    else if is_top p2 then p1
    else if equal p1 p2 then p1
    else (match step1_intersection width p1 p2 with
    | Some p -> p
    | None ->
          (* A wrapped Finite operand must meet arc-by-arc: its
             finite_end is the wrap edge, not its upper bound. *)
          if is_wrapped p1 || is_wrapped p2 then
            List.fold
              (List.concat_map (split_wrapped p1) ~f:(fun q1 ->
                   List.map (split_wrapped p2) ~f:(fun q2 ->
                       intersection q1 q2)))
              ~init:(bottom width) ~f:union
          else
          (match p1.dir, p2.dir with
          | Finite, Finite -> intersection_finite_or_circular p1 p2
          | Circular, Circular -> intersection_finite_or_circular p1 p2
          | Ascending, Finite ->
            (match min_elem p2, max_elem p2 with
             | Some lo2, Some hi2 ->
               let min_bound = W.max p1.base lo2 in
               solve_grid_interval ~width ~lo1:p1.base ~s1:p1.step ~lo2:p2.base ~s2:(step_of p2) ~min_bound ~max_bound:hi2
             | _ -> bottom width)
          | Finite, Ascending -> intersection p2 p1
          | Descending, Finite ->
            (match min_elem p2, max_elem p2 with
             | Some lo2, Some hi2 ->
               let max_bound = W.min p1.base hi2 in
               solve_grid_interval ~width ~lo1:p1.base ~s1:p1.step ~lo2:p2.base ~s2:(step_of p2) ~min_bound:lo2 ~max_bound
             | _ -> bottom width)
          | Finite, Descending -> intersection p2 p1
          | Ascending, Ascending ->
            let min_bound = W.max p1.base p2.base in
            solve_ascending_ascending ~width p1 p2 ~min_bound
          | Descending, Descending ->
            let max_bound = W.min p1.base p2.base in
            solve_descending_descending ~width p1 p2 ~max_bound
          | Ascending, Descending ->
            if W.(>) p1.base p2.base then bottom width
            else
              solve_grid_interval ~width ~lo1:p1.base ~s1:p1.step ~lo2:p2.base ~s2:p2.step ~min_bound:p1.base ~max_bound:p2.base
          | Descending, Ascending -> intersection p2 p1
          | Ascending, Circular ->
            solve_ascending_ascending ~width p1 p2 ~min_bound:p1.base
          | Circular, Ascending -> intersection p2 p1
          | Descending, Circular ->
            solve_descending_descending ~width p1 p2 ~max_bound:p1.base
          | Circular, Descending -> intersection p2 p1
          | Finite, Circular ->
            (match min_elem p1, max_elem p1 with
             | Some lo1, Some hi1 ->
               solve_grid_interval ~width ~lo1:p1.base ~s1:(step_of p1) ~lo2:p2.base ~s2:p2.step ~min_bound:lo1 ~max_bound:hi1
             | _ -> bottom width)
          | Circular, Finite -> intersection p2 p1
      ))

let overlap (p1 : t) (p2 : t) : bool = not (is_bottom (intersection p1 p2))

(* The remainder past a removed run [i] ending at [i_end], per the
   minuend's direction; [cardn] is the removed run's cardinality and
   [fallback] the survivor hull when no closed form applies. *)
let diff_ascending (p1 : t) (i : t) (i_end : W.t) : t =
  match min_elem i with
  | Some i_lo when W.(=) i_lo p1.base ->
    let new_base = W.add i_end (step_of p1) in
    if W.(<) new_base i_end then bottom (bitwidth p1)
    else create_ascending ~width:(bitwidth p1) ~base:new_base ~step:(step_of p1)
  | _ -> p1

let diff_descending (p1 : t) (i : t) (i_end : W.t) : t =
  match min_elem i with
  | Some i_lo when W.(=) i_end p1.base ->
    let new_base = W.sub i_lo (step_of p1) in
    if W.(>) new_base i_lo then bottom (bitwidth p1)
    else create_descending ~width:(bitwidth p1) ~base:new_base ~step:(step_of p1)
  | _ -> p1

let diff_circular (p1 : t) (i_end : W.t) (cardn : W.t) : t =
  (* Wrapping remainder. *)
  create (W.add i_end (step_of p1)) ~step:(step_of p1) ~cardn

let diff_finite (p1 : t) (i : t) (i_end : W.t) (cardn : W.t)
    ~(fallback : unit -> t) : t =
  (* The edges are one interval only on a non-wrapping traversal,
     where the unsigned minimum is the start; a wrapped Finite set
     decides by its survivors. *)
  match finite_end p1 with
  | Some p_end when W.(<) p_end (base_of p1) -> fallback ()
  | _ ->
    (match min_elem i, min_elem p1 with
     | Some i_lo, Some p_lo ->
       if W.(=) i_lo p_lo then
         create (W.add i_end (step_of p1)) ~step:(step_of p1) ~cardn
       else
         (match finite_end p1 with
          | Some p_end when W.(=) i_end p_end ->
            create p_lo ~step:(step_of p1) ~cardn
          | _ -> p1)
     | _ -> p1)

(* Difference; exact when one CLP, else identity. *)
let diff (p1 : t) (p2 : t) : t =
  if bitwidth p1 <> bitwidth p2 then p1
  else if is_bottom p1 then p1
  else if is_bottom p2 then p1
  else
    let i = intersection p1 p2 in
    if is_bottom i then p1
    else
      let run =
        (is_one (cardn_of i) || W.(=) (step_of i) (step_of p1))
        && subset i p2 in
      (* Within the budget the survivors decide: an exact hull when they
         form one, the identity otherwise; past the budget the identity
         is the sound over-approximation. *)
      let enumerate_or_identity () =
        if W.gt_int (cardn_of p1) fin_set_size then p1
        else
          let survivors =
            List.filter ~f:(fun x -> not (elem x p2)) (iter_ascending p1)
          in
          let hull = of_list ~width:(bitwidth p1) survivors in
          if W.equal (cardn_of hull)
             (W.of_int ~width:(bitwidth p1 + 1) (List.length survivors))
          then hull
          else p1
      in
      if not run then enumerate_or_identity ()
      else
        match finite_end i with
        | None -> p1
        | Some i_end ->
          let cardn = W.sub (cardn_of p1) (cardn_of i) in
          if W.is_zero cardn then bottom (bitwidth p1)
          else if is_ascending p1 then diff_ascending p1 i i_end
          else if is_descending p1 then diff_descending p1 i i_end
          else if is_circular p1 then diff_circular p1 i_end cardn
          else diff_finite p1 i i_end cardn ~fallback:enumerate_or_identity

type idx = int
let get_idx = bitwidth
let precedes = subset
let join = union
let meet = intersection

let widen_join (p1 : t) (p2 : t) : t =
  (* From bottom the new iterate is itself the widening step; the later
     iterates carry the extrapolation.  Answering top would drop a real
     bound the first widening is meant to keep. *)
  if is_bottom p1 then p2
  else if subset p1 p2 then
    if equal p1 p2 then p1 else
    let width = bitwidth p2 in
    let step = step_of p2 in
    if W.is_zero step then top width
    else
      match min_elem p1, max_elem p1, min_elem p2, max_elem p2 with
      | Some lo1, Some hi1, Some lo2, Some hi2 ->
        let lo_stable = W.(=) lo1 lo2 in
        let hi_stable = W.(=) hi1 hi2 in
        let hi_grew = W.(>) hi2 hi1 in
        let lo_grew = W.(<) lo2 lo1 in
        if lo_stable && hi_grew then
          create_ascending ~width ~base:lo1 ~step
        else if hi_stable && lo_grew then
          create_descending ~width ~base:hi1 ~step
        else
          infinite ((base_of p2), step)
      | _ -> infinite ((base_of p2), step)
  else join p1 p2

let extrapolate_steps ~steps:(steps:int) (p1 : t) (p2 : t) : t =
  if is_bottom p1 then p2
  else if subset p1 p2 then
    if equal p1 p2 then p1
    else if steps < 0 then widen_join p1 p2
    else
      match min_elem p1, max_elem p1, min_elem p2, max_elem p2 with
      | Some lo1, Some hi1, Some lo2, Some hi2 ->
        let width = bitwidth p2 in
        let step = step_of p2 in
        if W.is_zero step then top width
        else
          let lo_unstable = W.compare lo2 lo1 < 0 in
          let hi_unstable = W.compare hi2 hi1 > 0 in
          let lo_growth = if lo_unstable then Some (W.sub lo1 lo2) else None in
          let hi_growth = if hi_unstable then Some (W.sub hi2 hi1) else None in
          let extrap_lo = match lo_growth with
            | None -> lo2
            | Some g ->
              let steps_w = W.of_int ~width steps in
              let delta = W.mul g steps_w in
              let v = W.sub lo2 delta in
              let c = nearest_inf_succ v (base_of p2) step in
              if W.compare c lo2 > 0 then lo2 else c
          in
          let extrap_hi = match hi_growth with
            | None -> hi2
            | Some g ->
              let steps_w = W.of_int ~width steps in
              let delta = W.mul g steps_w in
              let v = W.add hi2 delta in
              if W.compare v hi2 < 0 then (* Overflow wraps. *)
                (* Escaping translation goes infinite. *)
                W.ones width
              else
                let f = nearest_inf_pred v (base_of p2) step in
                if W.compare f hi2 < 0 then hi2 else f
          in
          if W.compare extrap_lo lo2 > 0 || W.compare extrap_hi hi2 < 0 then
            widen_join p1 p2
          else
            let try_create lo hi =
              try create lo ~step ~cardn:(cardn_from_bounds lo step hi)
              with _ -> widen_join p1 p2
            in
            (* Stable bounds kept. *)
            if not lo_unstable && not hi_unstable then p2
            else if lo_unstable && hi_unstable then try_create extrap_lo extrap_hi
            else if hi_unstable then try_create lo2 extrap_hi
            else try_create extrap_lo hi2
      | _ -> widen_join p1 p2
  else join p1 p2

let pp ppf (p : t) =
  let p = forward p in
  let width = bitwidth p in
  match finite_end p with
  | None -> Format.fprintf ppf "{}:%i" width
  | Some _ when W.is_one (cardn_of p) ->
    Format.fprintf ppf "@[{%a}:%i@]" W.pp (base_of p) width
  | Some e when W.is_one @@ W.pred (cardn_of p) ->
    Format.fprintf ppf "@[{%a,@ %a}:%i@]"
      W.pp (base_of p)
      W.pp e
      width
  | Some e ->
    Format.fprintf ppf "@[{%a,@ %a,@ ...,@ %a}:%i@]"
      W.pp (base_of p)
      W.pp (W.add (base_of p) (step_of p))
      W.pp e
      width
