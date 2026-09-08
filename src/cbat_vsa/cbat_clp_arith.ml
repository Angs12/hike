(* CLP arithmetic: binops, shifts, casts, division. Pure over the core
   (one-directional dep: arith -> core; the seam shims live in
   cbat_clp.ml). *)

open Bap.Std
open Bin_prot.Std
include Cbat_vsa_utils

module W = Cbat_word
module Option = Core_kernel.Option
module Sexp = Core_kernel.Sexp
module List = Core_kernel.List

open !Cbat_word
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

open Cbat_clp_core

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



(* Fixed bit positions of [p]: below the step's 2-power (the residue class)
   and above the highest bit where [min_p] and [max_p] differ. *)
let fixed_bits (p : t) (min_p : word) (max_p : word) : word =
  let sz = bitwidth p in
  let low_twos = if is_one (cardn_of p) then sz
    else snd (factor_2s (step_of p)) in
  let low = if low_twos = 0 then W.zero sz else
    W.extract_exn ~hi:(sz - 1) (W.ones low_twos) in
  let msb = Option.value ~default:(-1)
      (lead_1_bit (W.logxor min_p max_p)) in
  let high = if msb < 0 || msb >= sz - 1 then W.zero sz else
    let sized = W.extract_exn ~hi:(sz - 1)
        (W.ones (sz - msb - 1)) in
    W.lshift sized (W.of_int ~width:sz (msb + 1)) in
  W.logor low high



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
      (* Bits fixed in both operands keep their AND value; a bit fixed to 0
         in either operand is 0 in the result. On every such bit the result
         agrees with [min_elem_p1 & min_elem_p2]. *)
      let fixed1 = fixed_bits p1 min_elem_p1 max_elem_p1 in
      let fixed2 = fixed_bits p2 min_elem_p2 max_elem_p2 in
      let forced = W.logand fixed1 fixed2
        |> W.logor (W.logand fixed1 (W.lnot min_elem_p1))
        |> W.logor (W.logand fixed2 (W.lnot min_elem_p2)) in
      let mask = W.lnot forced in
      if W.is_zero mask then
        (* No free bits: the result is the singleton AND of the minima. *)
        !!(create (W.logand min_elem_p1 min_elem_p2))
      else

        let safe_lower_bound =
          W.logand min_elem_p1 min_elem_p2 |> W.logand forced in
        let safe_upper_bound = W.logand max_elem_p1 max_elem_p2 |>
                               W.logor mask |>
                               W.min max_elem_p1 |>
                               W.min max_elem_p2 in
        let _, l_s_b = factor_2s mask in
        let step = W.lshift (W.one sz) (W.of_int ~width:sz l_s_b) in
        let base = safe_lower_bound in
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
let cap_amount (p2 : t) (cap : W.t) (min_p2 : W.t) (e2 : W.t) : t list =
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
    ~(exact : t -> W.t -> W.t -> t) (p2 : t) : t option =
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
    let exact_path (p2 : t) (min_p2 : W.t) (max_p2 : W.t) : t =
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
    let exact_path (p2 : t) (e2 : W.t) : t =
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
    let exact_path (p2 : t) (e2 : W.t) : t =
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
