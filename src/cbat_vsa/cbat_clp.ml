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

open Bap.Std
open Bin_prot.Std
include Cbat_vsa_utils

module W = Word
module Option = Core_kernel.Option
module Sexp = Core_kernel.Sexp
module List = Core_kernel.List

open !Cbat_word_ops
open Core_kernel
module Hashtbl = Stdlib.Hashtbl
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

(* {base + n*step | 0 <= n < cardn}. *)
type t = {
  base : word;
  step : word;
  cardn : word;
  dir : direction;
}
[@@deriving bin_io, sexp, compare]


let base_of (p : t) : word = p.base
let step_of (p : t) : word = p.step
let cardn_of (p : t) : word = p.cardn
let dir_of (p : t) : direction = p.dir

let is_ascending (p : t) : bool =
  match p.dir with Ascending -> true | _ -> false

let is_descending (p : t) : bool =
  match p.dir with Descending -> true | _ -> false

let is_circular (p : t) : bool =
  match p.dir with Circular -> true | _ -> false

let is_infinite (p : t) : bool =
  match p.dir with Finite -> false | _ -> true

(* CLP from base stepping by step. *)

let fit_to (width : int) (w : word) : word =
  if W.bitwidth w = width then w else W.extract_exn ~hi:(width - 1) w

let create ?(width : int option) ?(step = W.b1) ?(cardn = W.b1) base : t =
  let width = Option.value ~default:(W.bitwidth base) width in
  let cardn_w = Cbat_word_ops.cap_at_width ~width:(width + 1) cardn in
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
    let is_wrap =
      let ds = dom_size ~width:(2*width + 1) width in
      let mul = mul_exact cardn_w step' in
      W.(>=) mul ds
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

let create_ascending ~width ~base ~step : t =
  assert (width > 0);
  let base' = fit_to width base in
  let step' = fit_to width step in
  if W.is_zero step' then create ~width base'
  else
    let max_wd = W.ones width in
    let diff = W.sub max_wd base' in
    let num_steps = W.div diff step' in
    let cardn = W.succ (W.extract_exn ~hi:width num_steps) in
    if is_one cardn then create ~width base'
    else if W.is_zero cardn then bottom width
    else { base = base'; step = step'; cardn; dir = Ascending }

let create_descending ~width ~base ~step : t =
  assert (width > 0);
  let base' = fit_to width base in
  let step' = fit_to width step in
  if W.is_zero step' then create ~width base'
  else
    let num_steps = W.div base' step' in
    let cardn = W.succ (W.extract_exn ~hi:width num_steps) in
    if is_one cardn then create ~width base'
    else if W.is_zero cardn then bottom width
    else { base = base'; step = step'; cardn; dir = Descending }

let cardn_from_bounds base step e : word =
  let width = W.bitwidth base in
  assert(W.bitwidth step = width);
  
    if W.is_zero step then W.one (width + 1) else
    let div_by_step = W.div (W.sub e base) step in
    (* Extra bit so succ never wraps. *)
    W.succ (W.extract_exn ~hi:width div_by_step)

(* Step-1 CLP [lo, hi]; wrapped pair is circular. *)
let interval ~(width : int) (lo : word) (hi : word) : t =
  create ~width ~step:(W.one width)
    ~cardn:(cardn_from_bounds lo (W.one width) hi) lo

let infinite (b, s) : t =
  let width = W.bitwidth b in
  assert (width = W.bitwidth s);
  if W.is_zero s then create b
  else let div, twos = factor_2s s in
    let step = W.div s div in
    let base = W.modulo b step in
    let cardn = dom_size ~width:(width + 1) (width - twos) in
    {base; step; cardn; dir = Circular}

(* Cached per width. *)
let top_cache : (int, t) Hashtbl.t = Hashtbl.create 16

let top (i : int) : t =
  assert(i > 0);
  match Hashtbl.find_opt top_cache i with
  | Some t -> t
  | None ->
    let t = infinite (W.zero i, W.one i) in
    Hashtbl.add top_cache i t;
    t




(* Cardinality as a (width+1)-bit word. *)
let cardinality (p : t) : word = cardn_of p

(* Last point; meaningless for infinite CLPs. *)
let finite_end (p : t) : word option =
  let width = bitwidth p in
  let n = W.extract_exn ~hi:(width - 1) (cardn_of p) in
  if W.is_zero (cardn_of p) then None
  else Some (W.add (base_of p) (W.mul (step_of p) (W.pred n)))


let lnot (p : t) : t =
  (* Any point works as the infinite base. *)
  match finite_end p with
  | None -> bottom (bitwidth p)
  | Some e -> create (W.lnot e) ~step:(step_of p) ~cardn:(cardn_of p)


let iter (p : t) : word list =
  let rec iter_acc b s n acc =
    if W.is_zero n then acc
    else let n' = W.pred n in
      iter_acc (W.add b s) s n' (b :: acc) in
  iter_acc (base_of p) (step_of p) (cardn_of p) []

(* Closest element at or below i. *)
let nearest_pred (i : word) (p : t) : word option =
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


let nearest_inf_pred (w : word) (base : word) (step : word) : word =
  if W.is_zero step then base else
    let diff = W.sub w base in
    let rm = W.modulo diff step in
    W.sub w rm

let nearest_succ (i : word) (p : t) : word option =
  Option.map ~f:W.lnot (nearest_pred (W.lnot i) (lnot p))


let nearest_inf_succ (w : word) (base : word) (step : word) : word =
  W.lnot (nearest_inf_pred (W.lnot w) (W.lnot base) step)

let max_elem (p : t) : word option =
  if is_bottom p then None
  else match p.dir with
  | Finite ->
    let max_wd = W.ones (bitwidth p) in
    nearest_pred max_wd p
  | Ascending ->
    let max_wd = W.ones (bitwidth p) in
    let diff = W.sub max_wd p.base in
    let rem = if W.is_zero p.step then W.zero (bitwidth p) else W.modulo diff p.step in
    Some (W.sub max_wd rem)
  | Descending -> Some p.base
  | Circular ->
    let max_wd = W.ones (bitwidth p) in
    nearest_pred max_wd p

let min_elem (p : t) : word option =
  if is_bottom p then None
  else match p.dir with
  | Finite ->
    let min_wd = W.zero (bitwidth p) in
    nearest_succ min_wd p
  | Ascending -> Some p.base
  | Descending ->
    if W.is_zero p.step then Some p.base else Some (W.modulo p.base p.step)
  | Circular ->
    let min_wd = W.zero (bitwidth p) in
    nearest_succ min_wd p

(* Max signed element. *)
let max_elem_signed (p : t) : word option =
  if is_bottom p then None
  else match p.dir with
  | Descending -> Some p.base
  | _ -> nearest_pred (W.pred (half (bitwidth p))) p

(* Min signed element. *)
let min_elem_signed (p : t) : word option =
  if is_bottom p then None
  else match p.dir with
  | Ascending -> Some p.base
  | _ -> nearest_succ (half (bitwidth p)) p

let splits_by (p : t) (w : word) : bool =
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
let elem (i : word) (p : t) : bool =
  assert (W.bitwidth i = bitwidth p);
  match nearest_pred i p with
  | None -> false
  | Some j -> W.(=) i j

(* Top test via coprime step. *)
let is_top (p : t) : bool = p = top (bitwidth p)


(* Equivalence; faster than subset. *)
let equal (p1 : t) (p2 : t) : bool =
  if p1 == p2 then true
  else if bitwidth p1 <> bitwidth p2 then false
  else p1 = p2

(* Rebase onto extrema interval. *)
let unwrap_with ~(default : unit -> t) ~(min : t -> word option)
    ~(max : t -> word option) (p : t) : t =
  let open Monads.Std.Monad.Option.Syntax in
  match begin
    min p >>= fun base ->
    max p >>= fun e ->
    let step = (step_of p) in
    let cardn = cardn_from_bounds base step e in
    !!(create base ~step ~cardn)
  end with
  | None -> default ()
  | Some x -> x

let unwrap (p : t) : t =
  unwrap_with ~default:(fun () -> bottom (bitwidth p)) ~min:min_elem ~max:max_elem p

let unwrap_signed (p : t) : t =
  unwrap_with ~default:(fun () -> top (bitwidth p))
    ~min:min_elem_signed ~max:max_elem_signed p

(* Smallest circular hull of two intervals. *)
let interval_union (a1,b1) (a2,b2) : (word * word) =
  let szInt = W.bitwidth a1 in
  
  let b1' = W.sub b1 a1 in
  let a2' = W.sub a2 a1 in
  let b2' = W.sub b2 a1 in
  let zero = W.zero szInt in
  
  if W.(>=) b1' a2' && W.(<) b2' a2' then (b1, W.pred b1)
  
  else if W.(>=) b1' a2' && W.(>=) b1' b2' then (a1, b1)
  
  else if W.(>=) b1' a2' then (a1, b2)
  
  else if W.(<) b2' b1' then (a2, b1)
  
  else if W.(<) b2' a2' then (a2, b2)
  
  else if W.(>) (W.sub a2' b1') (W.sub zero b2') then (a2,b1)
  else (a1, b2)


(* Rotate without changing step/cardinality. *)
let translate (p : t) i : t =
  create (W.add (base_of p) i) ~step:(step_of p) ~cardn:(cardn_of p)

(* Largest step covering both progressions. *)
let common_step (b1,s1) (b2,s2) : word =
  let bDiff = if W.(>) b1 b2 then W.sub b1 b2 else W.sub b2 b1 in
  if W.is_zero s1 then bounded_gcd s2 bDiff
  else if W.is_zero s2 then bounded_gcd s1 bDiff
  else let gcdS = (bounded_gcd s1 s2) in
    bounded_gcd gcdS bDiff

(* Subset order. *)
let subset (p1 : t) (p2 : t) : bool =
  (* Width mismatch compares false. *)
  if bitwidth p1 <> bitwidth p2 then false
  else
    let width = bitwidth p1 in
    let nb2 = W.neg (base_of p2) in
      let p1 = translate p1 nb2 in
      let p2 = translate p2 nb2 in
      let end1 = finite_end p1 and end2 = finite_end p2 in
      begin match end1, end2 with
      | None, _ -> true
      | Some _, None -> false
      | Some e1, Some e2 ->
        let in_bounds = W.(<=) e1 e2 && W.(<=) (base_of p1) e2 in
        let step_and_overlap = W.(=) (common_step ((base_of p1),(step_of p1)) (W.zero width, (step_of p2))) (step_of p2) in
        let singleton_elem = is_one (cardn_of p1) && elem (base_of p1) p2 in
        singleton_elem || (in_bounds && step_and_overlap)
      end

(* First common point of both progressions. *)
let intersection (p1 : t) (p2 : t) : t =
  (* Width mismatch returns the wider operand. *)
  if bitwidth p1 <> bitwidth p2 then
    (if bitwidth p1 > bitwidth p2 then p1 else p2)
  else
    let width = bitwidth p1 in
    let p1, p2 = if W.(>=) (base_of p1) (base_of p2) then p1, p2 else p2, p1 in
    
    let translation = (base_of p1) in
    let translated_p1 = translate p1 (W.neg (base_of p1)) in
    let translated_p2 = translate p2 (W.neg (base_of p1)) in
    let p1, p2 = translated_p1, translated_p2 in
    let p1_infinite = is_infinite p1 in
    let p2_infinite = is_infinite p2 in
    let open Monads.Std.Monad.Option.Syntax in
    (match begin
      finite_end p1 >>= fun e1 ->
      finite_end p2 >>= fun e2 ->
        let step = W.lcm_exn (step_of p1) (step_of p2) in
        if W.is_zero step then begin
          (* Singleton case: exact or empty. *)
          if W.is_zero (step_of p2) then
            Option.some_if (elem (base_of p2) p1) () >>= fun _ ->
            !!(create (base_of p2))
          else
            Option.some_if (elem (base_of p1) p2) () >>= fun _ ->
            !! (create (base_of p1))
        end else begin
          bounded_diophantine (step_of p1) (step_of p2) (base_of p2) >>= fun (x,_) ->
          let base = W.mul x (step_of p1) in
          let base =
            if p2_infinite then base
            else match min_elem p2 with
              | None -> base
              | Some m when W.(<) base m ->
                let w1 = width + 1 in
                let d = W.extract_exn ~hi:width (W.sub m base) in
                let s = W.extract_exn ~hi:width step in
                let q = W.div d s in
                let r = W.modulo d s in
                let k = if W.is_zero r then q else W.succ q in
                let up = W.add (W.extract_exn ~hi:width base) (W.mul k s) in
                if W.(>=) up (dom_size ~width:w1 width) then W.ones width else W.extract_exn ~hi:(width - 1) up
              | Some _ -> base in
          let minE = if p1_infinite then e2 else if p2_infinite then e1 else min e1 e2 in
          if W.(<=) base minE then begin
            let cardn = cardn_from_bounds base step minE in
            !!(create base ~step ~cardn)
          end else begin
            let safe_operand = if subset p1 p2 then p2 else if subset p2 p1 then p1 else if W.(>=) (cardinality p1) (cardinality p2) then p1 else p2 in
            !!safe_operand
          end
        end
    end with
    | None -> bottom width
    | Some x -> x) |> (fun p -> translate p translation)

let overlap (p1 : t) (p2 : t) : bool = not (is_bottom (intersection p1 p2))

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
      if not run then p1
      else
        match finite_end i with
        | None -> p1
        | Some i_end ->
          let cardn = W.sub (cardn_of p1) (cardn_of i) in
          if W.is_zero cardn then bottom (bitwidth p1)
          else if is_infinite p1 then
            (* Wrapping remainder. *)
            create (W.add i_end (step_of p1)) ~step:(step_of p1) ~cardn
          else
            (* Remainder is one interval only at the edges. *)
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


(* Union; same width expected. *)
let union (p1 : t) ( p2 : t) : t =
  if bitwidth p1 <> bitwidth p2 then top (Stdlib.max (bitwidth p1) (bitwidth p2))
  else
  Option.value_map ~default:p2 (finite_end p1) ~f:begin fun e1 ->
      Option.value_map ~default:p1 (finite_end p2) ~f:begin fun e2 ->
        let base, newE = interval_union ((base_of p1), e1) ((base_of p2), e2) in
        let step = common_step ((base_of p1), (step_of p1)) ((base_of p2), (step_of p2)) in
        let cardn = cardn_from_bounds base step newE in
        create base ~step ~cardn
      end
    end

let add (p1 : t) (p2 : t) : t =
  (* Mixed widths coerce to max. *)
  if bitwidth p1 <> bitwidth p2 then top (Stdlib.max (bitwidth p1) (bitwidth p2)) else let sz = bitwidth p1 in
  match finite_end p1 with
  | None -> bottom sz
  | Some e1 ->
    match finite_end p2 with
    | None -> bottom sz
    | Some e2 ->
      if W.is_zero (step_of p1) || is_one (cardn_of p1) then translate p2 (base_of p1)
      else if W.is_zero (step_of p2) || is_one (cardn_of p2) then translate p1 (base_of p2)
      else if is_infinite p1 || is_infinite p2 then
        infinite (W.add (base_of p1) (base_of p2), bounded_gcd (step_of p1) (step_of p2))
      else
        let e1' = W.sub e1 (base_of p1) in
        let e2' = W.sub e2 (base_of p2) in
        let e' = W.add e1' e2' in
        let base = W.add (base_of p1) (base_of p2) in
        let step = bounded_gcd (step_of p1) (step_of p2) in
        if W.(<) e' e1' then infinite (base, step)
        else let cardn = cardn_from_bounds (W.zero sz) step e' in create base ~step ~cardn



let neg (p : t) : t =
  (* Any point works as the infinite base. *)
  match finite_end p with
  | None -> bottom (bitwidth p)
  | Some e -> create (W.neg e) ~step:(step_of p) ~cardn:(cardn_of p)

let sub (p1: t) (p2 : t) : t = add p1 (neg p2)

let mul (p1 : t) (p2 : t) : t =
  (* Mixed widths coerce to max. *)
  if bitwidth p1 <> bitwidth p2 then top (Stdlib.max (bitwidth p1) (bitwidth p2)) else let sz = bitwidth p1 in
  (* Empty operand gives bottom. *)
  match finite_end p1 with
  | None -> bottom sz
  | Some e1 ->
    match finite_end p2 with
    | None -> bottom sz
    | Some e2 ->
      (* Singleton case is exact. *)
      if W.is_zero (step_of p1) || is_one (cardn_of p1) then
        let base = W.mul (base_of p2) (base_of p1) in
        let step = W.mul (step_of p2) (base_of p1) in
        create base ~step ~cardn:(cardn_of p2)
      else if W.is_zero (step_of p2) || is_one (cardn_of p2) then
        let base = W.mul (base_of p1) (base_of p2) in
        let step = W.mul (step_of p1) (base_of p2) in
        create base ~step ~cardn:(cardn_of p1)
      else
        let base = mul_exact (base_of p1) (base_of p2) in
        let e'_exact = mul_exact e1 e2 in
        let step = bounded_gcd (mul_exact (base_of p1) (step_of p2))
            (bounded_gcd (mul_exact (base_of p2) (step_of p1))
               (mul_exact (step_of p1) (step_of p2))) in
        let end_diff = W.sub e'_exact base in
        let div_res = W.div end_diff step in
        let cardn = W.succ @@ add_bit div_res in
        if is_infinite p1 ||is_infinite p2 then
          let fit = W.extract_exn ~hi:(sz - 1) in
          infinite (fit base, fit step)
        else create ~width:sz base ~step ~cardn



let lead_1_bit_run (w : word) ~hi ~lo : int =
  let rec lead_help (hi : int) (lo : int) : int =
    if hi = lo then hi else
    let mid = (hi + lo) / 2 in
    let hi_part = W.extract_exn ~hi ~lo:(mid + 1) w in
    if W.is_zero (W.lnot hi_part) then lead_help mid lo
    else lead_help hi (mid + 1)
  in
  assert(lo >= 0);
  assert(hi >= lo);
  (lead_help hi lo)  + 1



let compute_l_s_b lsb1 lsb2 b1 b2 : int = if lsb1 < lsb2 then
    let interval = W.extract_exn ~hi:(lsb2 - 1) ~lo:lsb1 b2 in
    let w, bit = factor_2s interval in
    if W.is_zero w then lsb2 else bit + lsb1
  else if lsb1 > lsb2 then
    let interval =  W.extract_exn ~hi:(lsb1 - 1) ~lo:lsb2 b1 in
    let w, bit = factor_2s interval in
    if W.is_zero w then lsb1 else bit + lsb2
  else lsb1  (* Equal low bits. *)



let compute_m_s_b msb1 msb2 b1 b2 : int = if msb1 > msb2 then
    let interval = W.extract_exn ~hi:msb1 ~lo:(msb2 + 1) b2 in
    Option.value_map ~default:msb2
      (lead_1_bit interval)
      ~f:(fun b -> b + msb2 + 1)
  else if msb1 < msb2 then
    let interval =  W.extract_exn ~hi:msb2 ~lo:(msb1 + 1) b1 in
    Option.value_map ~default:msb1
      (lead_1_bit interval)
      ~f:(fun b -> b + msb1 + 1)
  else msb1  (* Equal high bits. *)


let compute_range_sep msb msb1 msb2 b1 b2 : int = if msb1 > msb2
  then if msb = msb1 then lead_1_bit_run b2 ~hi:msb1 ~lo:(msb2 + 1) else msb + 1
  else if msb1 < msb2 then
    if msb = msb2 then lead_1_bit_run b1 ~hi:msb2 ~lo:(msb1 + 1) else msb + 1
    (* TODO: verify this branch. *)
  else -1


(* Bitwise op via non-wrapping superset. *)
let logand (p1 : t) (p2 : t) : t =
  (* Mixed widths coerce to max. *)
  if bitwidth p1 <> bitwidth p2 then top (Stdlib.max (bitwidth p1) (bitwidth p2)) else let sz = bitwidth p1 in
  let cardn_two = W.of_int ~width:(sz + 1) 2 in
  
  let cp1 = p1 in
  let cp2 = p2 in
  
  let p1, p2 = if W.(<=) (cardinality cp1) (cardinality cp2)
    then (cp1, cp2) else (cp2, cp1) in
  let open Monads.Std.Monad.Option.Syntax in
  (match begin
    if W.is_zero (cardn_of p1) || W.is_zero (cardn_of p2) then !!(bottom sz)
    else if W.is_one (cardn_of p1) && W.is_one (cardn_of p2) then
      !!(create (W.logand (base_of p1) (base_of p2)))
    else if W.is_one (cardn_of p1) && W.(=) (cardn_of p2) cardn_two then
      (* Two-element case is exact. *)
      finite_end p2 >>= fun e2 ->
      let base = W.logand (base_of p1) (base_of p2) in
      let newE = W.logand (base_of p1) e2 in
      let step = W.sub newE base in
      let cardn = cardn_two in
      !!(create base ~step ~cardn)
    else
      min_elem p1 >>= fun min_elem_p1 ->
      max_elem p1 >>= fun max_elem_p1 ->
      min_elem p2 >>= fun min_elem_p2 ->
      max_elem p2 >>= fun max_elem_p2 ->
      let _, twos_in_s1 = factor_2s (step_of p1) in
      let _, twos_in_s2 = factor_2s (step_of p2) in
      let least_significant_bit_p1 = if W.is_one (cardn_of p1) then sz
      
        else twos_in_s1 in
      let least_significant_bit_p2 = if W.is_one (cardn_of p2) then sz
      
        else twos_in_s2 in
      
      let most_significant_bit_p1 = Option.value ~default:(-1)
          (lead_1_bit (W.logxor min_elem_p1 max_elem_p1)) in
      let most_significant_bit_p2 = Option.value ~default:(-1)
          (lead_1_bit (W.logxor min_elem_p2 max_elem_p2)) in
      let l_s_b = compute_l_s_b
          least_significant_bit_p1
          least_significant_bit_p2
          min_elem_p1 min_elem_p2 in
      let m_s_b = compute_m_s_b
          most_significant_bit_p1
          most_significant_bit_p2
          min_elem_p1 min_elem_p2 in
      if l_s_b > m_s_b then
        (* Singleton result. *)
        let base = W.logand min_elem_p1 min_elem_p2 in
        !!(create base)
      else
        let range_sep = compute_range_sep m_s_b
            most_significant_bit_p1
            most_significant_bit_p2
            min_elem_p1 min_elem_p2
        in
        let mask = if l_s_b >= range_sep then W.zero sz
              else let ones = W.ones (range_sep - l_s_b) in
                let sized_ones = W.extract_exn ~hi:(sz - 1) ones in
                Word.lshift sized_ones (W.of_int ~width:sz l_s_b) in
        let safe_lower_bound =
          W.logand min_elem_p1 min_elem_p2 |> W.logand (W.lnot mask) in
        let safe_upper_bound = W.logand max_elem_p1 max_elem_p2 |>
                               W.logor mask |>
                               W.min max_elem_p1 |>
                               W.min max_elem_p2 in
        let twos_step = W.lshift (W.of_int 1 ~width:sz)
            (W.of_int l_s_b ~width:sz) in
        let step = if most_significant_bit_p1 > most_significant_bit_p2 &&
                      m_s_b = most_significant_bit_p1 &&
                      range_sep = l_s_b then
            W.max (step_of p1) twos_step
          else if most_significant_bit_p2 > most_significant_bit_p1 &&
                      m_s_b = most_significant_bit_p2 &&
                      range_sep = l_s_b then
            W.max (step_of p2) twos_step
          else twos_step in
        let b1_and_b2 = W.logand min_elem_p1 min_elem_p2 in
        let frac = cdiv (W.sub safe_lower_bound b1_and_b2) step in
        let base = W.add b1_and_b2 (W.mul step frac) in
        (* TODO: use cardn_from_bounds. *)
        let cardn = W.div (W.sub safe_upper_bound base) step |> succ_exact in
        !!(create base ~step ~cardn)
  end with
  | None -> bottom sz
  | Some x -> x)

let logor (p1 : t) (p2 : t) : t = lnot (logand (lnot p1) (lnot p2))

let logxor (p1 : t) (p2 : t) : t =
  (* Mixed widths coerce to max. *)
  if bitwidth p1 <> bitwidth p2 then top (Stdlib.max (bitwidth p1) (bitwidth p2)) else let width = bitwidth p1 in
  let two = create (W.of_int 2 ~width) in
  let approx1 = logor (logand p1 (lnot p2)) (logand (lnot p1) p2) in
  (* Bitwise equality. *)
  let approx2 = sub (add p1 p2) (mul (logand p1 p2) two) in
  (* Meet of two sound approximations. *)
  intersection approx1 approx2

(* Overshift: exact, overshifted, straddling. *)

(* Overshift image is sign extension. *)
let overshift_sign_extend (sz : int) : t =
  create ~width:sz ~step:(W.ones sz)
    ~cardn:(W.of_int ~width:(sz + 1) 2) (W.zero sz)

(* Overshift result per sign. *)
let overshift_value (p : t) : t =
  let sz = bitwidth p in
  let half = dom_size ~width:sz (sz - 1) in
  let has_low = Option.value_map (min_elem p) ~default:false
      ~f:(fun w -> W.(<) w half) in
  let has_high = Option.value_map (max_elem p) ~default:false
      ~f:(fun w -> W.(>=) w half) in
  match has_low, has_high with
  | true, false -> create (W.zero sz)
  | false, true -> create (W.ones sz)
  | _ -> overshift_sign_extend sz

(* Straddling amounts cap below the width. *)
let cap_amount (p2 : t) (cap : word) (min_p2 : word) (e2 : word) : t list =
  let sz2 = bitwidth p2 in
  let part ~step lo hi =
    if W.(>) lo hi then []
    else
      let cardn = W.succ
          (W.extract_exn ~hi:sz2 (W.div (W.sub hi lo) step)) in
      [ create ~width:sz2 ~step ~cardn lo ] in
  if W.(<) e2 (base_of p2) then
    part ~step:(step_of p2) (base_of p2) cap
    @ part ~step:(step_of p2) min_p2 (if W.(>) cap e2 then e2 else cap)
  else if is_infinite p2 then
    let twos = snd (factor_2s (step_of p2)) in
    let step = W.lshift (W.one sz2) (W.of_int ~width:sz2 twos) in
    part ~step min_p2 cap
  else
    part ~step:(step_of p2) min_p2 cap


(* Overshift: exact, overshifted, straddling. *)
let split_shift ~(sz1 : int) ~(overshift : t)
    ~(exact : t -> word -> word -> t) (p2 : t) : t option =
  let open Monads.Std.Monad.Option.Syntax in
  min_elem p2 >>= fun min_p2 ->
  max_elem p2 >>= fun max_p2 ->
  let amount_w = Stdlib.max 64 (W.bitwidth max_p2) in
  let width_i = W.of_int sz1 ~width:amount_w in
  let max_p2_i = W.extract_exn ~hi:(amount_w - 1) max_p2 in
  let min_p2_i = W.extract_exn ~hi:(amount_w - 1) min_p2 in
  if W.(<) max_p2_i width_i then
    (* All amounts exact. *)
    !!(exact p2 min_p2 max_p2)
  else if W.(>=) min_p2_i width_i then
    (* All amounts overshifted. *)
    !!overshift
  else
    (* Mixed amounts: capped exact plus overshift. *)
    let cap = W.of_int (sz1 - 1) ~width:(W.bitwidth min_p2) in
    let e2 = Option.value (finite_end p2) ~default:min_p2 in
    let parts = cap_amount p2 cap min_p2 e2 in
    !!(List.fold parts ~init:overshift ~f:(fun acc p2' ->
        union acc (exact p2' (base_of p2')
                     (Option.value (finite_end p2') ~default:(base_of p2')))))

let lshift (p1 : t) (p2 : t) : t =
  let sz1 = bitwidth p1 in
    let open Monads.Std.Monad.Option.Syntax in
  (match begin
    finite_end p1 >>= fun e1 ->
    (* Exact path per amount part. *)
    let exact_path (p2 : t) (min_p2 : word) (max_p2 : word) : t =
      let max_p2_int = W.to_int_exn max_p2 in
      let base = W.lshift (base_of p1) min_p2 in
      let step = if is_one (cardn_of p2)
        then W.lshift (step_of p1) min_p2
        else W.lshift (bounded_gcd (base_of p1) (step_of p1)) min_p2 in
      let e_no_wrap = lshift_exact e1 max_p2_int in
      let e_width = W.bitwidth e_no_wrap in
      (* Cardinality at the wider width. *)
      let cardn = if W.is_zero step then W.one 1 else
          let base_ext = W.extract_exn ~hi:(e_width - 1) base in
          let step_ext = W.extract_exn ~hi:(e_width - 1) step in
          let div_by_step = W.div (W.sub e_no_wrap base_ext) step_ext in
          (* Extra bit so succ never wraps. *)
          W.succ (W.extract_exn ~hi:e_width div_by_step) in
      create base ~step ~cardn in
    split_shift ~sz1 ~overshift:(create (W.zero sz1))
      ~exact:exact_path p2
  end with
  | None -> bottom sz1
  | Some x -> x)

let rshift_step rshift ~p1 ~p2 ~e2 ~sz1 ~sz2 =
  (* Widths match after coercion. *)
  let _, b1twos = factor_2s (base_of p1) in
  let _, s1twos = factor_2s (step_of p1) in
  let s1_divisible = W.(>=) (W.of_int s1twos ~width:sz1) e2 in
  let b1_divisible = W.(>=) (W.of_int b1twos ~width:sz1) e2 in
  let b1_initial_ones = count_initial_1s (base_of p1) in
  if (s1_divisible && W.is_one (cardn_of p2)) ||
     (s1_divisible && b1_divisible) ||
     (s1_divisible && W.(>=) (W.of_int ~width:sz2 b1_initial_ones) e2)
  then bounded_gcd (rshift (step_of p1) e2) @@ W.sub (rshift (base_of p1) @@ W.sub e2 (step_of p2))
      (rshift (base_of p1) @@ e2)
  else W.one sz1

(* Equal widths required. *)
let rec rshift (p1 : t) (p2 : t) : t =
  let sz1 = bitwidth p1 in
  let sz2 = bitwidth p2 in
  if sz1 <> sz2 then
    (* Mixed widths coerce to max. *)
    let w = Stdlib.max sz1 sz2 in
    let ext_zero (p : t) : t =
      create ~width:w (base_of p) ~step:(step_of p) ~cardn:(cardn_of p) in
    let shifted = rshift (ext_zero p1) (ext_zero p2) in
    create ~width:sz1 (base_of shifted) ~step:(step_of shifted) ~cardn:(cardn_of shifted)
  else
  let p1 = unwrap p1 in
  let p2 = unwrap p2 in
  let open Monads.Std.Monad.Option.Syntax in
  (match begin
    finite_end p1 >>= fun e1 ->
    (* Exact path per capped part. *)
    let exact_path (p2 : t) (e2 : word) : t =
      let base = W.rshift (base_of p1) e2 in
      if W.is_one (cardn_of p1) && W.is_one (cardn_of p2)
      then create base
      else
        let step = rshift_step W.rshift ~p1 ~p2 ~e2 ~sz1 ~sz2 in
        let cardn = cardn_from_bounds base step (W.rshift e1 (base_of p2)) in
        create base ~step ~cardn in
    split_shift ~sz1 ~overshift:(create (W.zero sz1))
      ~exact:(fun p2 min_p2 _ ->
        exact_path p2 (Option.value ~default:min_p2 (finite_end p2)))
      p2
  end with
  | None -> bottom sz1
  | Some x -> x)

let rec arshift (p1 : t) (p2 : t) : t =
  let sz1 = bitwidth p1 in
  let sz2 = bitwidth p2 in
  if sz1 <> sz2 then
    (* Mixed widths coerce to max. *)
    let w = Stdlib.max sz1 sz2 in
    let halfw = half sz1 in
    let d = W.sub (W.ones w) (W.ones sz1) in
    let p1' =
      match min_elem p1, max_elem p1 with
      | Some mn, Some mx ->
        if W.(<) mx halfw then
          (* Non-negative: identity. *)
          create ~width:w (base_of p1) ~step:(step_of p1) ~cardn:(cardn_of p1)
        else if W.(>=) mn halfw then
          (* Negative: shift base. *)
          create ~width:w (W.add (W.extract_exn ~hi:(w - 1) (base_of p1)) d)
            ~step:(W.extract_exn ~hi:(w - 1) (step_of p1)) ~cardn:(cardn_of p1)
        else
          (* Mixed sign: top. *)
          top sz1
      | _ -> top sz1 in
    if is_top p1' then top sz1
    else
      let p2' =
        create ~width:w (base_of p2) ~step:(step_of p2) ~cardn:(cardn_of p2) in
      let shifted = arshift p1' p2' in
      create ~width:sz1 (base_of shifted) ~step:(step_of shifted) ~cardn:(cardn_of shifted)
  else
  let zero = W.zero sz1 in
  (* True set drives sign classification. *)
  let p1c = p1 in
  let p1 = unwrap_signed p1c in
  let p2 = unwrap p2 in
  let open Monads.Std.Monad.Option.Syntax in
  (match begin
    finite_end p1 >>= fun e1 ->
    (* Exact path per capped part. *)
    let exact_path (p2 : t) (e2 : word) : t =
      if W.is_one (cardn_of p1) && W.is_one (cardn_of p2)
      then
        let base = W.arshift (W.signed (base_of p1)) (base_of p2) in
        create base ~width:sz1
      else
        let base =
          if W.(>=) (W.signed (base_of p1)) zero
          then W.arshift (W.signed (base_of p1)) e2
          else W.arshift (W.signed (base_of p1)) (base_of p2)
          in
        let step = rshift_step W.arshift ~p1 ~p2 ~e2 ~sz1 ~sz2 in
        let new_end =
          if W.(>=) (W.signed e1) zero
          then W.arshift (W.signed e1) (base_of p2)
          else W.arshift (W.signed e1) e2
          in
        let cardn = cardn_from_bounds base step new_end in
        create base ~step ~cardn in
    split_shift ~sz1 ~overshift:(overshift_value p1c)
      ~exact:(fun p2 min_p2 _ ->
        exact_path p2 (Option.value ~default:min_p2 (finite_end p2)))
      p2
  end with
  | None -> bottom sz1
  | Some x -> x)

(* Split at n. *)
let split_at_n (p : t) n : t * t =
  
  
  let cardn1 = min (cardn_from_bounds (base_of p) (step_of p) n) (cardn_of p) in
  
  let cardn2 = W.sub (cardn_of p) cardn1 in
  let p2_base = nearest_inf_succ (W.succ n) (base_of p) (step_of p) in
  create (base_of p) ~step:(step_of p) ~cardn:cardn1,
  create p2_base ~step:(step_of p) ~cardn:cardn2

(* Widen to the given width. *)
let extract_exact ~width:(width : int) (p : t) : t * t =
  let p_width = bitwidth p in
  assert (width >= p_width);
  
  let lastn = W.ones p_width in
  let p1, p2 = split_at_n p lastn in
  create ~width (base_of p1) ~step:(step_of p1) ~cardn:(cardn_of p1),
  create ~width (base_of p2) ~step:(step_of p2) ~cardn:(cardn_of p2)

let extract_lo ?(lo = 0) (p : t) : t =
  let width = bitwidth p in
  (* Degenerate cast keeps top. *)
  if lo >= width then top width
  else begin
    let res_width = width - lo in
    if lo = 0 then p else
      match finite_end p with
      | None -> bottom res_width
      | Some e ->
      let base = W.extract_exn ~lo (base_of p) in
      let ext_lo w = W.extract_exn ~hi:(lo - 1) w in
      let base_mod_2lo = ext_lo (base_of p) in
      let step_mod_2lo = ext_lo (step_of p) in
      (* No-carry case ignores low bits. *)
      let max_step_effect = add_exact base_mod_2lo @@
        mul_exact step_mod_2lo (W.pred (cardn_of p)) in
      let carry_bound = dom_size ~width:(W.bitwidth max_step_effect) lo in
      if W.(<) max_step_effect carry_bound then
        create base ~step:(W.extract_exn ~lo (step_of p)) ~cardn:(cardn_of p)
      else
        let e = W.extract_exn ~lo e in
        let step = W.one res_width in
        let cardn = cardn_from_bounds base step e in
        create base ~step ~cardn
  end

let extract_hi ?(hi = None) ?(signed = false) (p : t) : t =
  let sz = bitwidth p in
  let hiv = Option.value ~default:(bitwidth p - 1) hi in
  (* Degenerate cast keeps top. *)
  if hiv < 0 then top sz
  else if not signed && hiv + 1 >= sz then
    let res1, res2 = extract_exact ~width:(hiv + 1) p in
    union res1 res2
  else if not signed then
    create ~width:(hiv+1) (base_of p) ~step:(step_of p) ~cardn:(cardn_of p)
  else if hiv >= sz then top sz
  else
    (* TODO: check the signed case. *)
    let ext =  W.extract_exn ~hi:hiv in
    let ext_signed w = W.extract_exn ~hi:hiv (W.signed w) in
    match finite_end p with
    | None -> bottom (hiv + 1)
    | Some e ->
        (* TODO: check the infinite case. *)
        if is_infinite p then infinite (ext (base_of p), ext (step_of p))
        else
          (* negmin precedes maxint. *)
          let negmin = half sz in
          let posmax = W.pred negmin in
          if elem negmin p && elem posmax p &&
             ((base_of p) <> negmin || e <> posmax) then
            
            not_implemented ~top:(top (hiv + 1))
              "extract signed crossing max signed int"
          else
            let e' = W.sub e (base_of p) in
            let newE' = ext e' in
            let base = if signed then ext_signed (base_of p) else ext (base_of p) in
            let step = ext (step_of p) in
            (* Wrap covers the full circle. *)
            if W.(<) newE' e' then infinite(base, step)
            else
              let cardn = cardn_from_bounds (W.zero (hiv + 1)) step newE' in
              create base ~step ~cardn

let extract_internal ?hi ?(lo = 0) ?(signed = false) (p : t) : t =
  let hi = Option.map hi ~f:(fun hi -> hi - lo) in
  extract_lo ~lo p |> extract_hi ~hi ~signed

(* Degenerate cast keeps top. *)
let cast ct (sz : int) (p : t) : t =
  let width = bitwidth p in
  if sz <= 0 then
    not_implemented ~top:(top width)
      (Printf.sprintf "cast to degenerate size %d" sz)
  else match ct with
  | Bil.HIGH when sz > width ->
    not_implemented ~top:(top width)
      (Printf.sprintf "HIGH cast to size %d wider than operand %d" sz width)
  | Bil.UNSIGNED -> extract_internal ~hi:(sz - 1) p
  | Bil.SIGNED -> extract_internal ~hi:(sz - 1) ~signed:true p
  | Bil.LOW -> extract_internal ~hi:(sz - 1) p
  | Bil.HIGH -> extract_internal ~lo:(width - sz) p

let extract ?hi:hi ?lo:lo (p : t) : t = extract_internal ?hi ?lo p

let concat (p1 : t) (p2 : t) : t =
  let width1 = bitwidth p1 in
  let width2 = bitwidth p2 in
  let width = width1 + width2 in
  let p1'base = lshift_exact (base_of p1) width2 in
  let p1'step = lshift_exact (step_of p1) width2 in
  let p1' = create p1'base ~step:p1'step ~cardn:(cardn_of p1) in
  let p2' = cast Bil.UNSIGNED width p2 in
  
  (add p1' p2')

(* Sound hull of a list. *)
let of_list ~width l : t =
  assert (width > 0);
  let open Monads.Std.Monad.Option.Syntax in
  (match begin
    let l = List.map l ~f:(W.extract_exn ~hi:(width - 1) ~lo:0) in
    let l = List.sort ~compare:W.compare l in
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

(* BAP div truncates; ediv is Euclidean. *)
let div (p1 : t) (p2 : t) : t =
  (* Mixed widths coerce to max. *)
  if bitwidth p1 <> bitwidth p2 then top (Stdlib.max (bitwidth p1) (bitwidth p2)) else let width = bitwidth p1 in
  let open Monads.Std.Monad.Option.Syntax in
  (match begin
    min_elem p1 >>= fun min_e1 ->
    min_elem p2 >>= fun min_e2 ->
    max_elem p1 >>= fun max_e1 ->
    max_elem p2 >>= fun max_e2 ->
    (* Zero divisor gives top. *)
    if elem (W.zero width) p2
    then !!(if W.is_one (cardinality p2) then bottom width else top width)
    else
      let base = W.div min_e1 max_e2 in
      let e = W.div max_e1 min_e2 in
      let step = if W.is_one (cardinality p2) &&
                    W.is_zero (W.modulo (step_of p1) (base_of p2))
          then bounded_gcd (W.div (step_of p1) (base_of p2))
              (W.sub (W.div (base_of p1) (base_of p2)) base)
              (* TODO: improve step precision. *)
          else W.one width in
      let cardn = cardn_from_bounds base step e in
      !!(create base ~step ~cardn)
  end with
  | None -> bottom width
  | Some x -> x)

let sdiv (p1 : t) (p2 : t) : t =
  let wsdiv a b = W.div (W.signed a) (W.signed b) in
  (* Mixed widths coerce to max. *)
  if bitwidth p1 <> bitwidth p2 then top (Stdlib.max (bitwidth p1) (bitwidth p2)) else let width = bitwidth p1 in
  (* Infinite operand gives unbounded quotient. *)
  if is_infinite p1 || is_infinite p2 then top width
  else
  let open Monads.Std.Monad.Option.Syntax in
  (match begin
    min_elem p1 >>= fun min_e1 ->
    min_elem p2 >>= fun min_e2 ->
    max_elem p1 >>= fun max_e1 ->
    max_elem p2 >>= fun max_e2 ->
    (* Zero divisor gives top; exact {0} is bottom. *)
    if elem (W.zero width) p2
    then !!(if W.is_one (cardinality p2) then bottom width else top width)
    else if W.is_one (cardinality p1) &&
            W.is_one (cardinality p2)
    then !!(singleton (wsdiv (base_of p1) (base_of p2)))
    else
      let minmax = wsdiv min_e1 max_e2 in
      let minmin = wsdiv min_e1 min_e2 in
      let maxmax = wsdiv max_e1 max_e2 in
      let maxmin = wsdiv max_e1 min_e2 in
      let base =
        min minmax @@
        min minmin @@
        min maxmax maxmin in
      let e =
        max minmax @@
        max minmin @@
        max maxmax maxmin in
      (* TODO: improve step accuracy. *)
      let step = W.one width in
      let cardn = cardn_from_bounds base step e in
      !!(create base ~step ~cardn)
  end with
  | None -> bottom width
  | Some x -> x)


let modulo (p1 : t) (p2 : t) : t =
  sub p1 (mul (div p1 p2) p2)


let smodulo (p1 : t) (p2 : t) : t =
  sub p1 (mul (sdiv p1 p2) p2)

(* Lattice. *)
type idx = int
let get_idx = bitwidth
let precedes = subset
let join = union
let meet = intersection


let widen_join (p1 : t) (p2 : t) =
  (* Widening needs an ascending chain. *)
  (* Bottom-to-singleton widens to top. *)
  if is_bottom p1 then top (bitwidth p2)
  else if subset p1 p2 then
    if equal p1 p2 then p1 else
    let step = step_of p2 in
    if W.is_zero step then top (bitwidth p2)
    else infinite ((base_of p2), step)
  else join p1 p2

let extrapolate_steps ~steps:(steps:int) (p1 : t) (p2 : t) : t =
  if is_bottom p1 then top (bitwidth p2)
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
              let steps_w = Word.of_int ~width steps in
              let delta = W.mul g steps_w in
              let v = W.sub lo2 delta in
              let c = nearest_inf_succ v (base_of p2) step in
              if W.compare c lo2 > 0 then lo2 else c
          in
          let extrap_hi = match hi_growth with
            | None -> hi2
            | Some g ->
              let steps_w = Word.of_int ~width steps in
              let delta = W.mul g steps_w in
              let v = W.add hi2 delta in
              if W.compare v hi2 < 0 then (* Overflow wraps. *)
                (* Escaping translation goes infinite. *)
                Word.ones width
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





let compare (p1 : t) (p2 : t) : int =
  let base_comp = W.compare (base_of p1) (base_of p2) in
  let step_comp = W.compare (step_of p1) (step_of p2) in
  let cardn_comp = W.compare (cardn_of p1) (cardn_of p2) in
  let dir_comp = compare_direction p1.dir p2.dir in
  let if_nzero_else a b = if a = 0 then b else a in
  if_nzero_else base_comp @@
  if_nzero_else step_comp @@
  if_nzero_else cardn_comp @@
  dir_comp


let sexp_of_t (p : t) : Sexp.t =
  Sexp.List begin match finite_end p with
    | Some e ->
      if W.is_one (cardn_of p) then [W.sexp_of_t (base_of p)]
      else if W.is_one @@ W.pred @@ (cardn_of p) then
        [W.sexp_of_t (base_of p); W.sexp_of_t e]
      else [W.sexp_of_t (base_of p);
            W.sexp_of_t (W.add (base_of p) (step_of p));
            Sexp.Atom "...";
            W.sexp_of_t e]
    | None -> [Sexp.Atom "{}"; Sexp.Atom (string_of_int (bitwidth p))]
  end

let t_of_sexp : Sexp.t -> t = function
  | Sexp.List [Sexp.Atom "{}"; Sexp.Atom s] ->
    let width = int_of_string s in
    bottom width
  | Sexp.List [be] ->
    let base = Word.t_of_sexp be in
    create base
  | Sexp.List [be; ne as ee]
  | Sexp.List [be; ne; Sexp.Atom "..."; ee] ->
    let base = Word.t_of_sexp be in
    let next = Word.t_of_sexp ne in
    let e = Word.t_of_sexp ee in
    let step = Word.sub next base in
    let cardn = cardn_from_bounds base step e in
    create base ~step ~cardn
  | Sexp.List _
  | Sexp.Atom _ -> failwith "Sexp not a CLP"



let pp ppf (p : t) =
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
