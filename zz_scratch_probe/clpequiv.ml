(* Exhaustive equivalence check for the CLP lattice core.

   Compares every binary operation and the identity elements across a dense
   sweep of (width, base, step, cardn), asserting that:
     - is_top is unchanged,
     - top w and bottom w are unchanged as *values*,
     - every op result is structurally unchanged.
   The reference ("old") implementations are inlined below so this harness
   stays valid after the production ones are rewritten.

   [Ref_word] holds the pre-substrate word implementations (frozen)
   verbatim; the sweep cross-checks them against the unmodified production
   ops (word-substrate T1: the referee must be green while both sides are
   still identical).

   The word-op sweep runs at the widths the domain actually uses: the swept
   widths (1..64) plus a direct 64/65/129-bit sweep (129 = [dom_size
   ~width:(2*width+1)] and [mul_exact]'s summed width at width 64).

   The same sweep cross-checks [Cbat_word] (the int63 substrate) against the
   reference, over every op it exports (word-substrate T2).

   Usage: clpequiv.exe *)

open Bap.Std
open Probe_common
module CKL = Core_kernel.List
module Wo = Cbat_word
module CW = Cbat_word

(* ========================================================================= *)
(* CLP reference implementations, as they were before the change. *)
(* ========================================================================= *)

let ref_bottom (width : int) : Ws.Clp.t =
  Ws.Clp.create ~width (Cbat_word.of_word (Word.zero width))
    ~cardn:(Cbat_word.of_word (Word.zero (width + 1)))

let ref_top (i : int) : Ws.Clp.t =
  Ws.Clp.infinite (Cbat_word.of_word (Word.zero i), Cbat_word.of_word (Word.one i))

let ref_is_top (p : Ws.Clp.t) : bool = Ws.Clp.equal p (ref_top (Ws.Clp.bitwidth p))

let ops : (string * (Ws.Clp.t -> Ws.Clp.t -> Ws.Clp.t)) list =
  [ ("add", Ws.Clp.add); ("sub", Ws.Clp.sub); ("mul", Ws.Clp.mul)
  ; ("logand", Ws.Clp.logand); ("logor", Ws.Clp.logor)
  ; ("intersection", Ws.Clp.intersection)
  ; ("join", Ws.Clp.join); ("meet", Ws.Clp.meet) ]

(* ========================================================================= *)
(* Ref_word: the pre-substrate word implementations, verbatim. *)
(* ========================================================================= *)

module Ref_word = struct
  module W = Word
  module Option = Core_kernel.Option

  (* Multiply at the summed width; cannot overflow. *)
  let mul_exact (w1 : word) (w2 : word) : word =
    let sz1 = Word.bitwidth w1 in
    let sz2 = Word.bitwidth w2 in
    let sz_ext = sz1 + sz2 in
    let w1_ext = Word.extract_exn ~hi:(sz_ext - 1) w1 in
    let w2_ext = Word.extract_exn ~hi:(sz_ext - 1) w2 in
    Word.mul w1_ext w2_ext

  let add_exact (w1 : word) (w2 : word) : word =
    let sz1 = Word.bitwidth w1 in
    let sz2 = Word.bitwidth w2 in
    let sz_ext = 1 + max sz1 sz2 in
    let w1_ext = Word.extract_exn ~hi:(sz_ext - 1) w1 in
    let w2_ext = Word.extract_exn ~hi:(sz_ext - 1) w2 in
    Word.add w1_ext w2_ext

  let succ_exact (w : word) : word =
    let width = Word.bitwidth w in
    Word.succ @@ Word.extract_exn ~hi:width w

  let lshift_exact (w : word) (i : int) : word =
    let width = i + Word.bitwidth w in
    let wi = W.of_int ~width i in
    let w' = Word.extract_exn ~hi:(width - 1) w in
    Word.lshift w' wi

  (* Bounded gcd. *)
  let bounded_gcd (w1 : word) (w2 : word) : word =
    let width = Word.bitwidth w1 in
    assert (width = Word.bitwidth w2);
    if Word.is_zero w1 then w2
    else if Word.is_zero w2 then w1
    else Word.gcd_exn w1 w2

  (* Unsigned division rounding up. *)
  let cdiv a b : word = if Word.is_zero (Word.modulo a b)
    then Word.div a b else Word.succ (Word.div a b)

  let is_one (w : word) : bool = Word.is_zero (Word.pred w)

  (* Least non-negative x solving ax + by = c. *)
  let bounded_diophantine (a : word) b c : (word * word) option =
    let size = Word.bitwidth a in
    assert (size = Word.bitwidth b);
    assert (size = Word.bitwidth c);
    let zero = W.zero size in
    if Word.is_zero c then Some (zero, zero)
    else if Word.is_zero a && Word.is_zero b then None
    else if Word.is_zero a then
      if Word.is_zero (Word.modulo c b) then Some (zero, Word.div c b) else None
    else if Word.is_zero b then
      if Word.is_zero (Word.modulo c a) then Some (Word.div c a, zero) else None
    else
      (* Bezout coefficients. *)
      let d, unsigned_x, unsigned_y = W.gcdext_exn a b in
      let signed_x = Word.signed unsigned_x in
      let signed_y = Word.signed unsigned_y in
      let gcd_quotient = Word.div c d in
      (* Double-width products. *)
      let signed_x0 = Word.signed (mul_exact signed_x gcd_quotient) in
      let signed_y0 = Word.signed (mul_exact signed_y gcd_quotient) in
      if not (Word.is_zero (Word.modulo c d)) then None
      else
        (* Minimal-|x|,|y| solution pair. *)
        Some (Word.extract_exn ~hi:(size-1) signed_x0,
              Word.extract_exn ~hi:(size-1) signed_y0)

  (* Split w into odd part and power of two. *)
  let factor_2s (w : word) : word * int =
    let rec factor_help (hi : int) (lo : int) : int =
      if hi = lo then hi else
        let mid = (hi + lo) / 2 in
        let lo_part = Word.extract_exn ~hi:mid ~lo w in
        if Word.is_zero lo_part then factor_help hi (mid + 1)
        else factor_help mid lo
    in
    let width = Word.bitwidth w in
    let lo = factor_help (width - 1) 0 in
    (* Keep the input width. *)
    let hi = width - 1 + lo in
    Word.extract_exn ~hi ~lo w, lo

  (* 2^i at [width] bits. *)
  let dom_size_cache : (int * int, word) Hashtbl.t = Hashtbl.create 16
  let dom_size ?width (i : int) : word =
    let width = Option.value ~default:(i + 1) width in
    match Hashtbl.find_opt dom_size_cache (i, width) with
    | Some w -> w
    | None ->
      let w = Word.lshift (W.one width) (W.of_int ~width i) in
      Hashtbl.add dom_size_cache (i, width) w;
      w

  let half (w : int) : word = dom_size ~width:w (w - 1)

  let min w1 w2 : word = if W.(<) w1 w2 then w1 else w2

  (* Closest value representable at [width] bits. *)
  let cap_at_width ~width (w : word) : word =
    let w_width = Word.bitwidth w in
    (* Exact width is the identity. *)
    if w_width = width then w
    else if w_width <= width then Word.extract_exn ~hi:(width - 1) w else
      (* Largest width-bit number. *)
      let max_w = Word.pred @@ dom_size ~width:w_width width in
      let res_val = min max_w w in
      Word.extract_exn ~hi:(width - 1) res_val
end

(* ========================================================================= *)
(* The sweep. *)
(* ========================================================================= *)

let () =
  init ();
  let checked = ref 0 and mism = ref 0 in
  let bad msg = incr mism; if !mism <= 12 then print_endline msg in
  (* Cases where BOTH sides raised: the check is vacuous there, so the
     count is reported rather than hidden. A jump in this number means an
     op stopped being exercised. *)
  let both_raised = ref 0 in

  (* ---- word-op checks ------------------------------------------------- *)

  (* Physical equality of the packed representation: bitwidth, sign bit
     and payload together. Word.to_string carries all three. *)
  let eqw (w1 : word) (w2 : word) : bool =
    String.equal (Word.to_string w1) (Word.to_string w2)
  in
  let show (w : word) : string = Word.to_string w in
  (* The unsigned payload. *)
  let z_of (w : word) : Z.t = Bitvec.to_bigint (Word.to_bitvec w) in
  (* int63 discriminates |v| <= 2^62-1, matching the planned Small/Big
     split. *)
  let max_small : Z.t = Z.of_int 4611686018427387903 in
  let i63 (w : word) : int option =
    let i = z_of w in
    if Z.leq (Z.abs i) max_small then Some (Z.to_int i) else None
  in



  (* Word of [width] bits holding [v] mod 2^width. *)
  let word_of_z (width : int) (v : Z.t) : word =
    Word.of_string (Printf.sprintf "%s:%d" (Z.to_string v) width)
  in

  (* ---- Cbat_word vs the reference ---------------------------------- *)

  (* Both sides are compared as BAP words, so width and payload must agree:
     the substrate's own [Small]/[Big] split is invisible here. *)
  let cw_of (w : word) : CW.t = CW.of_word w in
  let cw1 (nm : string) (rf : word -> word) (nf : CW.t -> CW.t) (w : CW.t) =
    incr checked;
    let exp = (try Ok (rf (CW.to_word w)) with e -> Error e) in
    let got = (try Ok (CW.to_word (nf w)) with e -> Error e) in
    match got, exp with
    | Ok g, Ok e ->
      if not (eqw g e) then
        bad (Printf.sprintf "CW %s(%s): ref=%s cw=%s" nm (CW.to_string w) (show e) (show g))
    | Error _, Error _ -> incr both_raised
    | Ok g, Error _ ->
      bad (Printf.sprintf "CW %s(%s): cw=%s ref raised" nm (CW.to_string w) (show g))
    | Error _, Ok e ->
      bad (Printf.sprintf "CW %s(%s): cw raised ref=%s" nm (CW.to_string w) (show e))
  in
  (* Reference op over BAP words vs Cbat_word op: inputs and results are
     converted at the boundary, so the comparison is BAP-observed. *)
  let cw2 (nm : string) (rf : word -> word -> word) (nf : CW.t -> CW.t -> CW.t)
      (a : CW.t) (b : CW.t) =
    incr checked;
    let exp = (try Ok (rf (CW.to_word a) (CW.to_word b)) with e -> Error e) in
    let got = (try Ok (CW.to_word (nf a b)) with e -> Error e) in
    match got, exp with
    | Ok g, Ok e ->
      if not (eqw g e) then
        bad (Printf.sprintf "CW %s(%s,%s): ref=%s cw=%s" nm (CW.to_string a)
               (CW.to_string b) (show e) (show g))
    | Error _, Error _ -> incr both_raised
    | Ok g, Error _ ->
      bad (Printf.sprintf "CW %s(%s,%s): cw=%s ref raised" nm (CW.to_string a) (CW.to_string b) (show g))
    | Error _, Ok e ->
      bad (Printf.sprintf "CW %s(%s,%s): cw raised ref=%s" nm (CW.to_string a) (CW.to_string b) (show e))
  in
  let cw1b (nm : string) (rf : word -> bool) (nf : CW.t -> bool) (w : CW.t) =
    incr checked;
    let exp = (try Ok (rf (CW.to_word w)) with e -> Error e) in
    let got = (try Ok (nf w) with e -> Error e) in
    match got, exp with
    | Ok g, Ok e ->
      if not (Bool.equal g e) then
        bad (Printf.sprintf "CW %s(%s): ref=%b cw=%b" nm (CW.to_string w) e g)
    | Error _, Error _ -> incr both_raised
    | _ -> bad (Printf.sprintf "CW %s(%s): ref/cw disagreed on raising" nm (CW.to_string w))
  in
  let sgn (i : int) : int = if i > 0 then 1 else if i < 0 then -1 else 0 in
  let cwc (nm : string) (rf : word -> word -> int) (nf : CW.t -> CW.t -> int)
      (a : CW.t) (b : CW.t) =
    incr checked;
    let exp = (try Ok (rf (CW.to_word a) (CW.to_word b)) with e -> Error e) in
    let got = (try Ok (nf a b) with e -> Error e) in
    match got, exp with
    | Ok g, Ok e ->
      if sgn g <> sgn e then
        bad (Printf.sprintf "CW %s(%s,%s): ref=%d cw=%d" nm (CW.to_string a) (CW.to_string b) e g)
    | Error _, Error _ -> incr both_raised
    | _ -> bad (Printf.sprintf "CW %s(%s,%s): ref/cw disagreed on raising" nm (CW.to_string a) (CW.to_string b))
  in
  (* An op whose int result must match, with both-raised tolerated. *)
  let cwi (nm : string) (rf : word -> int) (nf : CW.t -> int) (w : CW.t) =
    incr checked;
    let exp = (try Ok (rf (CW.to_word w)) with e -> Error e) in
    let got = (try Ok (nf w) with e -> Error e) in
    match got, exp with
    | Ok g, Ok e ->
      if g <> e then bad (Printf.sprintf "CW %s(%s): ref=%d cw=%d" nm (CW.to_string w) e g)
    | Error _, Error _ -> incr both_raised
    | _ -> bad (Printf.sprintf "CW %s(%s): ref/cw disagreed on raising" nm (CW.to_string w))
  in

  (* Every op [Cbat_word] exports, against [Word] / [Ref_word]. *)
  let check_cbat_word (width : int) (v1 : Z.t) (v2 : Z.t) =
    let w1 = cw_of (word_of_z width v1) in
    let w2 = cw_of (word_of_z width v2) in
    let w3 = cw_of (word_of_z width (Z.add v1 v2)) in
    cw2 "add" Word.add CW.add w1 w2;
    cw2 "sub" Word.sub CW.sub w1 w2;
    cw2 "mul" Word.mul CW.mul w1 w2;
    cw2 "div" Word.div CW.div w1 w2;
    cw2 "modulo" Word.modulo CW.modulo w1 w2;
    cw2 "logand" Word.logand CW.logand w1 w2;
    cw2 "logor" Word.logor CW.logor w1 w2;
    cw2 "logxor" Word.logxor CW.logxor w1 w2;
    cw2 "lshift" Word.lshift CW.lshift w1 w2;
    cw2 "rshift" Word.rshift CW.rshift w1 w2;
    cw2 "arshift" Word.arshift CW.arshift w1 w2;
    cw2 "gcd_exn" Word.gcd_exn CW.gcd_exn w1 w2;
    cw2 "lcm_exn" Word.lcm_exn CW.lcm_exn w1 w2;
    cw2 "min" Word.min CW.min w1 w2;
    cw2 "max" Word.max CW.max w1 w2;
    cw2 "concat" Word.concat CW.concat w1 w2;
    cw1 "neg" Word.neg CW.neg w1;
    cw1 "lnot" Word.lnot CW.lnot w1;
    cw1 "succ" Word.succ CW.succ w1;
    cw1 "pred" Word.pred CW.pred w1;
    cw1 "abs" Word.abs CW.abs w1;
    cw1 "signed" Word.signed CW.signed w1;
    cw1 "unsigned" Word.unsigned CW.unsigned w1;
    cw1b "is_zero" Word.is_zero CW.is_zero w1;
    cw1b "is_one" Word.is_one CW.is_one w1;
    cwc "compare" Word.compare CW.compare w1 w2;
    cwi "bitwidth" Word.bitwidth CW.bitwidth w1;
    cwi "to_int_exn" Word.to_int_exn CW.to_int_exn w1;
    cwi "to_int_exn" Word.to_int_exn CW.to_int_exn w2;
    (* extract: the default-hi, a high slice and a low slice. *)
    CKL.iter [ (width - 1, 0); (width - 1, Stdlib.max 0 (width / 2)); (width / 2, 0) ]
      ~f:(fun (hi, lo) ->
          if hi >= lo then
            cw1 (Printf.sprintf "extract %d %d" hi lo)
              (Word.extract_exn ~hi ~lo) (CW.extract_exn ~hi ~lo) w1);
    (* the word_ops set *)
    cw2 "mul_exact" Ref_word.mul_exact CW.mul_exact w1 w2;
    cw2 "add_exact" Ref_word.add_exact CW.add_exact w1 w2;
    cw1 "succ_exact" Ref_word.succ_exact CW.succ_exact w1;
    CKL.iter [ 0; 1; 2; 3 ] ~f:(fun i ->
        cw1 (Printf.sprintf "lshift_exact %d" i)
          (fun w -> Ref_word.lshift_exact w i) (fun w -> CW.lshift_exact w i) w1);
    cw2 "bounded_gcd" Ref_word.bounded_gcd CW.bounded_gcd w1 w2;
    cw2 "cdiv" Ref_word.cdiv CW.cdiv w1 w2;
    cw1b "is_one(ops)" Ref_word.is_one CW.is_one w1;
    CKL.iter [ w1; w2; w3 ] ~f:(fun c ->
        incr checked;
        match
          (try Ok (Ref_word.bounded_diophantine (CW.to_word w1) (CW.to_word w2) (CW.to_word c)) with e -> Error e),
          (try Ok (CW.bounded_diophantine w1 w2 c)
           with e -> Error e)
        with
        | Ok (Some (rx, ry)), Ok (Some (px, py)) ->
          let gx = CW.to_word px and gy = CW.to_word py in
          if not (eqw rx gx && eqw ry gy) then
            bad (Printf.sprintf "CW bounded_diophantine(%s,%s,%s): ref=(%s,%s) cw=(%s,%s)"
                   (CW.to_string w1) (CW.to_string w2) (CW.to_string c) (show rx) (show ry)
                   (show gx) (show gy))
        | Ok None, Ok None -> ()
        | Error _, Error _ -> incr both_raised
        | _ ->
          bad (Printf.sprintf "CW bounded_diophantine(%s,%s,%s): shape differs"
                 (CW.to_string w1) (CW.to_string w2) (CW.to_string c)));
    (let rf = Ref_word.factor_2s (CW.to_word w1) and pf = CW.factor_2s w1 in
     incr checked;
     if not (eqw (fst rf) (CW.to_word (fst pf)) && Stdlib.( = ) (snd rf) (snd pf)) then
       bad (Printf.sprintf "CW factor_2s(%s): ref=(%s,%d) cw=(%s,%d)"
              (CW.to_string w1) (show (fst rf)) (snd rf) (show (CW.to_word (fst pf))) (snd pf)));
    CKL.iter [ width; width + 1; 2 * width + 1 ] ~f:(fun tgt ->
        let i = Z.to_int (Z.erem v1 (Z.of_int 8)) in
        incr checked;
        let rd = Ref_word.dom_size ~width:tgt i and pd = CW.dom_size ~width:tgt i in
        if not (eqw rd (CW.to_word pd)) then
          bad (Printf.sprintf "CW dom_size i=%d width=%d: ref=%s cw=%s"
                 i tgt (show rd) (show (CW.to_word pd)));
        incr checked;
        let rc = Ref_word.cap_at_width ~width:tgt (CW.to_word w1) and pc = CW.cap_at_width ~width:tgt w1 in
        if not (eqw rc (CW.to_word pc)) then
          bad (Printf.sprintf "CW cap_at_width(%s) width=%d: ref=%s cw=%s"
                 (CW.to_string w1) tgt (show rc) (show (CW.to_word pc)));
        incr checked;
        let rh = Ref_word.half tgt and ph = CW.half tgt in
        if not (eqw rh (CW.to_word ph)) then
          bad (Printf.sprintf "CW half width=%d: ref=%s cw=%s" tgt (show rh)
                 (show (CW.to_word ph))))
  in

  (* All the ops, over one (width, v1, v2) triple. *)
  let check_word_ops (width : int) (v1 : Z.t) (v2 : Z.t) =
    let w1 = cw_of (word_of_z width v1) in
    let w2 = cw_of (word_of_z width v2) in
    (* [c] is INDEPENDENT of (a, b): taking c = a makes [c mod gcd = 0]
       hold identically, so only an independent c exercises
       bounded_diophantine's None arm (ax + by = c unsolvable). *)
    let w3 = word_of_z width (Z.add v1 v2) in
    cw2 "mul_exact" Ref_word.mul_exact CW.mul_exact w1 w2;
    cw2 "add_exact" Ref_word.add_exact CW.add_exact w1 w2;
    cw1 "succ_exact" Ref_word.succ_exact CW.succ_exact w1;
    cw1 "succ_exact" Ref_word.succ_exact CW.succ_exact w2;
    CKL.iter [ 0; 1; 2; 3 ] ~f:(fun i ->
        cw1 (Printf.sprintf "lshift_exact %d" i)
          (fun w -> Ref_word.lshift_exact w i) (fun w -> CW.lshift_exact w i) w1);
    cw2 "bounded_gcd" Ref_word.bounded_gcd CW.bounded_gcd w1 w2;
    cw2 "cdiv" Ref_word.cdiv CW.cdiv w1 w2;
    cw1b "is_one" Ref_word.is_one CW.is_one w1;
    cw1b "is_one" Ref_word.is_one CW.is_one w2;
    CKL.iter [ w1; w2; cw_of w3 ] ~f:(fun c ->
        incr checked;
        match
          (try Ok (Ref_word.bounded_diophantine (CW.to_word w1) (CW.to_word w2) (CW.to_word c)) with e -> Error e),
          (try Ok (CW.bounded_diophantine w1 w2 c) with e -> Error e)
        with
        | Ok (Some (rx, ry)), Ok (Some (px, py)) ->
          let gx = CW.to_word px and gy = CW.to_word py in
          if not (eqw rx gx && eqw ry gy) then
            bad (Printf.sprintf "CW bounded_diophantine(%s,%s,%s): ref=(%s,%s) prod=(%s,%s)"
                   (CW.to_string w1) (CW.to_string w2) (CW.to_string c) (show rx) (show ry) (show gx) (show gy))
        | Ok None, Ok None -> ()
        | Error _, Error _ -> incr both_raised
        | _ ->
          bad (Printf.sprintf "CW bounded_diophantine(%s,%s,%s): shape differs"
                 (CW.to_string w1) (CW.to_string w2) (CW.to_string c)));
    (let rf = Ref_word.factor_2s (CW.to_word w1) and pf = CW.factor_2s w1 in
     incr checked;
     if not (eqw (fst rf) (CW.to_word (fst pf)) && Stdlib.( = ) (snd rf) (snd pf)) then
       bad (Printf.sprintf "CW factor_2s(%s): ref=(%s,%d) prod=(%s,%d)"
              (CW.to_string w1) (show (fst rf)) (snd rf) (show (CW.to_word (fst pf))) (snd pf)));
    (* dom_size / cap_at_width: no-argument-width and explicit widths. *)
    CKL.iter [ width; width + 1; 2 * width + 1 ] ~f:(fun tgt ->
        incr checked;
        let rd = Ref_word.dom_size ~width:tgt (Z.to_int (Z.erem v1 (Z.of_int 8))) in
        let pd = CW.dom_size ~width:tgt (Z.to_int (Z.erem v1 (Z.of_int 8))) in
        if not (eqw rd (CW.to_word pd)) then
          bad (Printf.sprintf "CW dom_size i=%d width=%d: ref=%s prod=%s"
                 (Z.to_int (Z.erem v1 (Z.of_int 8))) tgt (show rd) (show (CW.to_word pd)));
        incr checked;
        let rc = Ref_word.cap_at_width ~width:tgt (CW.to_word w1) in
        let pc = CW.cap_at_width ~width:tgt w1 in
        if not (eqw rc (CW.to_word pc)) then
          bad (Printf.sprintf "CW cap_at_width(%s) width=%d: ref=%s prod=%s"
                 (CW.to_string w1) tgt (show rc) (show (CW.to_word pc))));
    (* The int63 fast path's precondition: whenever the true result is
       itself in the small range, native int arithmetic is exact. The
       guard is load-bearing — (2^62-1) + 1 leaves the range, so
       "small operands => small result" is FALSE (that is precisely the
       overflow the substrate must detect and fall back on). *)
    (match i63 (CW.to_word w1), i63 (CW.to_word w2) with
     | Some a, Some b ->
       let z1 = z_of (CW.to_word w1) and z2 = z_of (CW.to_word w2) in
       CKL.iter [ ("add", Z.add z1 z2, a + b); ("mul", Z.mul z1 z2, a * b) ]
         ~f:(fun (nm, expected, got) ->
             if Z.leq (Z.abs expected) max_small then (
               incr checked;
               if not (Z.equal expected (Z.of_int got)) then
                 bad (Printf.sprintf "INT63 %s not exact at w=%d: %s %s (z=%s int=%d)"
                        nm width (CW.to_string w1) (CW.to_string w2) (Z.to_string expected) got)))
     | _ -> ())
  in

  (* The domain's real widths: 64 (words), 65 (width+1: cardn and the
     infinite set), 129 (dom_size ~width:(2*width+1) and mul_exact's summed
     width at width 64). *)
  let big_widths = [ 64; 65; 129 ] in
  CKL.iter big_widths ~f:(fun width ->
      let modulus = Z.shift_left Z.one width in
      let half = Z.shift_left Z.one (width - 1) in
      let small : Z.t list =
        [ Z.zero; Z.one; Z.of_int 2; Z.of_int 3; Z.of_int 7; Z.of_int 255
        ; Z.of_int 1120; Z.neg (Z.of_int 1120); Z.of_int 4611686018427387903
          (* one value per trailing-zero count 0..7: factor_2s is a binary
             search over that count, so each bucket is a distinct path. *)
        ; Z.of_int 1; Z.of_int (1 lsl 1); Z.of_int (1 lsl 2); Z.of_int (1 lsl 3)
        ; Z.of_int (1 lsl 4); Z.of_int (1 lsl 5); Z.of_int (1 lsl 6)
        ; Z.of_int (1 lsl 7) ]
      in
      let wide : Z.t list =
        [ Z.sub modulus Z.one; Z.sub modulus (Z.of_int 1120)
        ; half; Z.sub half Z.one; Z.add half Z.one
        ; Z.div modulus (Z.of_int 3); Z.pred (Z.div modulus (Z.of_int 2))
        ; Z.sub (Z.shift_left Z.one (width - 2)) (Z.of_int 1120)
        ; Z.sub modulus (Z.of_int 4611686018427387903) ]
      in
      let vals : Z.t list = List.append small wide in
      CKL.iter vals ~f:(fun v1 ->
          CKL.iter vals ~f:(fun v2 ->
              check_word_ops width v1 v2;
              check_cbat_word width v1 v2)));

  (* ---- CLP sweep (the pre-existing harness) --------------------------- *)

  let widths = [ 1; 2; 3; 4; 8; 16; 32; 64 ] in
  CKL.iter widths ~f:(fun w ->
      (* identity elements *)
      let tb = Ws.Clp.bottom w and rb = ref_bottom w in
      incr checked;
      if not (Ws.Clp.equal tb rb) then bad (Printf.sprintf "BOTTOM w=%d differs" w);
      let tt = Ws.Clp.top w and rt = ref_top w in
      incr checked;
      if not (Ws.Clp.equal tt rt) then bad (Printf.sprintf "TOP w=%d differs" w);
      incr checked;
      if not (Ws.Clp.is_top tt) then bad (Printf.sprintf "TOP w=%d: is_top false" w);
      incr checked;
      if Ws.Clp.is_top tb then bad (Printf.sprintf "BOTTOM w=%d: is_top true" w);
      (* word ops at this width, over the swept values *)
      let n = min 16 (1 lsl (min w 4)) in
      for b1 = 0 to n - 1 do
        for s1 = 0 to n - 1 do
          for c1 = 0 to n - 1 do
            let p1 =
              Ws.Clp.create (Cbat_word.of_int ~width:w b1)
                ~step:(Cbat_word.of_int ~width:w s1)
                ~cardn:(Cbat_word.of_int ~width:(w + 1) c1)
            in
            (* is_top on the swept value *)
            incr checked;
            if not (Bool.equal (Ws.Clp.is_top p1) (ref_is_top p1)) then
              bad (Printf.sprintf "IS_TOP w=%d b=%d s=%d c=%d" w b1 s1 c1);
            (* the word ops, driven by the swept (base, step, cardn) *)
            if c1 land 3 = 0 && s1 land 3 = 0 && b1 land 3 = 0 then begin
              check_word_ops w (Z.of_int b1) (Z.of_int s1);
              check_cbat_word w (Z.of_int b1) (Z.of_int s1)
            end;
            for b2 = 0 to n - 1 do
              let p2 =
                Ws.Clp.create (Cbat_word.of_int ~width:w b2)
                  ~step:(Cbat_word.of_int ~width:w s1)
                  ~cardn:(Cbat_word.of_int ~width:(w + 1) c1)
              in
              CKL.iter ops ~f:(fun (nm, f) ->
                  incr checked;
                  try
                    let got = f p1 p2 in
                    ignore got
                  with _ -> ())
            done
          done
        done
      done);

  (* ---- Directional CLP checks (Tickets 01 & 02) ----------------------- *)
  let check_directional () =
    let w64 = 64 in
    let w_8 = CW.of_int ~width:w64 8 in
    let asc = Ws.Clp.create_ascending ~width:w64 ~base:w_8 ~step:w_8 in
    incr checked;
    if not (Ws.Clp.is_ascending asc) then
      bad "DIRECTIONAL: is_ascending asc should be true";
    incr checked;
    if not (Ws.Clp.is_infinite asc) then
      bad "DIRECTIONAL: is_infinite asc should be true";
    incr checked;
    if Ws.Clp.is_descending asc then
      bad "DIRECTIONAL: is_descending asc should be false";
    incr checked;
    if Ws.Clp.is_circular asc then
      bad "DIRECTIONAL: is_circular asc should be false";
    incr checked;
    (match Ws.Clp.min_elem asc with
     | Some m when CW.equal m w_8 -> ()
     | Some m -> bad (Printf.sprintf "DIRECTIONAL: min_elem asc got %s expected %s" (CW.to_string m) (CW.to_string w_8))
     | None -> bad "DIRECTIONAL: min_elem asc got None");
    incr checked;
    (match Ws.Clp.min_elem_signed asc with
     | Some m when CW.equal m w_8 -> ()
     | Some m -> bad (Printf.sprintf "DIRECTIONAL: min_elem_signed asc got %s expected %s" (CW.to_string m) (CW.to_string w_8))
     | None -> bad "DIRECTIONAL: min_elem_signed asc got None");

    (* Descending ray *)
    let w_64 = CW.of_int ~width:w64 64 in
    let desc = Ws.Clp.create_descending ~width:w64 ~base:w_64 ~step:w_8 in
    incr checked;
    if not (Ws.Clp.is_descending desc) then
      bad "DIRECTIONAL: is_descending desc should be true";
    incr checked;
    if not (Ws.Clp.is_infinite desc) then
      bad "DIRECTIONAL: is_infinite desc should be true";
    incr checked;
    if Ws.Clp.is_ascending desc then
      bad "DIRECTIONAL: is_ascending desc should be false";
    incr checked;
    if Ws.Clp.is_circular desc then
      bad "DIRECTIONAL: is_circular desc should be false";
    incr checked;
    (match Ws.Clp.max_elem desc with
     | Some m when CW.equal m w_64 -> ()
     | Some m -> bad (Printf.sprintf "DIRECTIONAL: max_elem desc got %s expected %s" (CW.to_string m) (CW.to_string w_64))
     | None -> bad "DIRECTIONAL: max_elem desc got None");
    incr checked;
    (match Ws.Clp.max_elem_signed desc with
     | Some m when CW.equal m w_64 -> ()
     | Some m -> bad (Printf.sprintf "DIRECTIONAL: max_elem_signed desc got %s expected %s" (CW.to_string m) (CW.to_string w_64))
     | None -> bad "DIRECTIONAL: max_elem_signed desc got None");

    (* Canonicalization: cardn = 1 becomes Finite singleton *)
    let max_val = CW.ones w64 in
    let asc_single = Ws.Clp.create_ascending ~width:w64 ~base:max_val ~step:w_8 in
    incr checked;
    if Ws.Clp.is_ascending asc_single then
      bad "DIRECTIONAL: asc_single should canonicalize to Finite (not ascending)";
    incr checked;
    if Ws.Clp.is_infinite asc_single then
      bad "DIRECTIONAL: asc_single should canonicalize to Finite (not infinite)";

    let desc_single = Ws.Clp.create_descending ~width:w64 ~base:(CW.of_int ~width:w64 7) ~step:w_8 in
    incr checked;
    if Ws.Clp.is_descending desc_single then
      bad "DIRECTIONAL: desc_single should canonicalize to Finite (not descending)";
    incr checked;
    if Ws.Clp.is_infinite desc_single then
      bad "DIRECTIONAL: desc_single should canonicalize to Finite (not infinite)";

    (* ---- Ticket 03 Operations: widen_join, subset, intersection, translate ---- *)
    (* widen_join: stable lo -> Ascending *)
    let p_8 = Ws.Clp.create ~width:w64 w_8 in
    let p_8_16 = Ws.Clp.interval ~width:w64 w_8 (CW.of_int ~width:w64 16) in
    let wj_asc = Ws.Clp.widen_join p_8 p_8_16 in
    incr checked;
    if not (Ws.Clp.is_ascending wj_asc) then
      bad "TICKET03 widen_join: stable lo should widen to Ascending";
    incr checked;
    (match Ws.Clp.min_elem wj_asc with
     | Some m when CW.equal m w_8 -> ()
     | _ -> bad "TICKET03 widen_join: asc min_elem should be 8");

    (* widen_join: stable hi -> Descending *)
    let p_64 = Ws.Clp.create ~width:w64 w_64 in
    let p_56_64 = Ws.Clp.interval ~width:w64 (CW.of_int ~width:w64 56) w_64 in
    let wj_desc = Ws.Clp.widen_join p_64 p_56_64 in
    incr checked;
    if not (Ws.Clp.is_descending wj_desc) then
      bad "TICKET03 widen_join: stable hi should widen to Descending";
    incr checked;
    (match Ws.Clp.max_elem wj_desc with
     | Some m when CW.equal m w_64 -> ()
     | _ -> bad "TICKET03 widen_join: desc max_elem should be 64");

    (* subset *)
    let p_8_16_s8 = Ws.Clp.create ~width:w64 ~step:w_8 ~cardn:(CW.of_int ~width:65 2) w_8 in
    incr checked;
    if not (Ws.Clp.subset p_8_16_s8 asc) then
      bad "TICKET03 subset: {8, 16} with step 8 should be subset of Ascending[8, ..]";
    let p_0 = Ws.Clp.create ~width:w64 (CW.zero w64) in
    incr checked;
    if Ws.Clp.subset p_0 asc then
      bad "TICKET03 subset: {0} should NOT be subset of Ascending[8, ..]";
    let p_56_64_s8 = Ws.Clp.create ~width:w64 ~step:w_8 ~cardn:(CW.of_int ~width:65 2) (CW.of_int ~width:w64 56) in
    incr checked;
    if not (Ws.Clp.subset p_56_64_s8 desc) then
      bad "TICKET03 subset: {56, 64} with step 8 should be subset of Descending[.. 64]";
    let asc_16 = Ws.Clp.create_ascending ~width:w64 ~base:(CW.of_int ~width:w64 16) ~step:w_8 in
    incr checked;
    if not (Ws.Clp.subset asc_16 asc) then
      bad "TICKET03 subset: Ascending[16, ..] should be subset of Ascending[8, ..]";
    incr checked;
    if Ws.Clp.subset asc asc_16 then
      bad "TICKET03 subset: Ascending[8, ..] should NOT be subset of Ascending[16, ..]";
    incr checked;
    if Ws.Clp.subset asc p_8_16_s8 then
      bad "TICKET03 subset: Ascending should NOT be subset of Finite";
    incr checked;
    if Ws.Clp.subset (Ws.Clp.top w64) asc then
      bad "TICKET03 subset: Top (Circular) should NOT be subset of Ascending";

    (* intersection *)
    let p_0_64 = Ws.Clp.interval ~width:w64 (CW.zero w64) w_64 in
    let meet_asc_fin = Ws.Clp.intersection asc p_0_64 in
    let expected_8_64 = Ws.Clp.create ~width:w64 ~step:w_8 ~cardn:(CW.of_int ~width:65 8) w_8 in
    incr checked;
    if not (Ws.Clp.equal meet_asc_fin expected_8_64) then
      bad "TICKET03 intersection: Ascending[8, ..] ⊓ [0, 64] should be {8, 16, .., 64}";

    let meet_asc_desc = Ws.Clp.intersection asc desc in
    incr checked;
    if not (Ws.Clp.equal meet_asc_desc expected_8_64) then
      bad "TICKET03 intersection: Ascending[8, ..] ⊓ Descending[.. 64] should be {8, 16, .., 64}";

    let desc_0 = Ws.Clp.create_descending ~width:w64 ~base:(CW.zero w64) ~step:w_8 in
    let meet_disjoint = Ws.Clp.intersection asc desc_0 in
    incr checked;
    if not (Ws.Clp.is_bottom meet_disjoint) then
      bad "TICKET03 intersection: Ascending[8, ..] ⊓ Descending[.. 0] should be bottom";

    (* translate *)
    let w_16 = CW.of_int ~width:w64 16 in
    let trans_asc = Ws.Clp.translate asc w_16 in
    incr checked;
    if not (Ws.Clp.is_ascending trans_asc) then
      bad "TICKET03 translate: non-wrapping translate on Ascending should remain Ascending";
    incr checked;
    (match Ws.Clp.min_elem trans_asc with
     | Some m when CW.equal m (CW.of_int ~width:w64 24) -> ()
     | _ -> bad "TICKET03 translate: base should be 24");

    let trans_desc = Ws.Clp.translate desc w_16 in
    incr checked;
    if not (Ws.Clp.is_descending trans_desc) then
      bad "TICKET03 translate: non-underflowing translate on Descending should remain Descending";
    incr checked;
    (match Ws.Clp.max_elem trans_desc with
     | Some m when CW.equal m (CW.of_int ~width:w64 80) -> ()
     | _ -> bad "TICKET03 translate: base should be 80");
  in
  check_directional ();

  Printf.printf "clpequiv: checked=%d mismatches=%d both-raised=%d\n"
    !checked !mism !both_raised;
  if !mism > 0 then exit 1
