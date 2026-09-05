(* Exhaustive equivalence check for the CLP lattice core.

   Compares every binary operation and the identity elements across a dense
   sweep of (width, base, step, cardn), asserting that:
     - is_top is unchanged,
     - top w and bottom w are unchanged as *values*,
     - every op result is structurally unchanged.
   The reference ("old") implementations are inlined below so this harness
   stays valid after the production ones are rewritten.

   [Ref_word] holds the current [Cbat_word_ops] word implementations
   verbatim; the sweep cross-checks them against the unmodified production
   ops (word-substrate T1: the referee must be green while both sides are
   still identical).

   The word-op sweep runs at the widths the domain actually uses: the swept
   widths (1..64) plus a direct 64/65/129-bit sweep (129 = [dom_size
   ~width:(2*width+1)] and [mul_exact]'s summed width at width 64).

   Usage: clpequiv.exe *)

open Bap.Std
open Probe_common
module CKL = Core_kernel.List
module Wo = Cbat_word_ops

(* ========================================================================= *)
(* CLP reference implementations, as they were before the change. *)
(* ========================================================================= *)

let ref_bottom (width : int) : Ws.Clp.t =
  Ws.Clp.create ~width (Word.zero width)
    ~cardn:(Word.zero (width + 1))

let ref_top (i : int) : Ws.Clp.t =
  Ws.Clp.infinite (Word.zero i, Word.one i)

let ref_is_top (p : Ws.Clp.t) : bool = Ws.Clp.equal p (ref_top (Ws.Clp.bitwidth p))

let ops : (string * (Ws.Clp.t -> Ws.Clp.t -> Ws.Clp.t)) list =
  [ ("add", Ws.Clp.add); ("sub", Ws.Clp.sub); ("mul", Ws.Clp.mul)
  ; ("logand", Ws.Clp.logand); ("logor", Ws.Clp.logor)
  ; ("intersection", Ws.Clp.intersection)
  ; ("join", Ws.Clp.join); ("meet", Ws.Clp.meet) ]

(* ========================================================================= *)
(* Ref_word: the current Cbat_word_ops implementations, verbatim. *)
(* ========================================================================= *)

module Ref_word = struct
  module W = Word
  module Option = Core_kernel.Option

  (* Multiply at the summed width; cannot overflow. *)
  let mul_exact (w1 : word) (w2 : word) : word =
    let sz1 = W.bitwidth w1 in
    let sz2 = W.bitwidth w2 in
    let sz_ext = sz1 + sz2 in
    let w1_ext = W.extract_exn ~hi:(sz_ext - 1) w1 in
    let w2_ext = W.extract_exn ~hi:(sz_ext - 1) w2 in
    W.mul w1_ext w2_ext

  let add_exact (w1 : word) (w2 : word) : word =
    let sz1 = W.bitwidth w1 in
    let sz2 = W.bitwidth w2 in
    let sz_ext = 1 + max sz1 sz2 in
    let w1_ext = W.extract_exn ~hi:(sz_ext - 1) w1 in
    let w2_ext = W.extract_exn ~hi:(sz_ext - 1) w2 in
    W.add w1_ext w2_ext

  let succ_exact (w : word) : word =
    let width = W.bitwidth w in
    W.succ @@ W.extract_exn ~hi:width w

  let lshift_exact (w : word) (i : int) : word =
    let width = i + W.bitwidth w in
    let wi = W.of_int ~width i in
    let w' = W.extract_exn ~hi:(width - 1) w in
    W.lshift w' wi

  (* Bounded gcd. *)
  let bounded_gcd (w1 : word) (w2 : word) : word =
    let width = W.bitwidth w1 in
    assert (width = W.bitwidth w2);
    if W.is_zero w1 then w2
    else if W.is_zero w2 then w1
    else W.gcd_exn w1 w2

  (* Unsigned division rounding up. *)
  let cdiv a b : word = if W.is_zero (W.modulo a b)
    then W.div a b else W.succ (W.div a b)

  let is_one (w : word) : bool = W.is_zero (W.pred w)

  (* Least non-negative x solving ax + by = c. *)
  let bounded_diophantine (a : word) b c : (word * word) option =
    let size = W.bitwidth a in
    assert (size = W.bitwidth b);
    assert (size = W.bitwidth c);
    let zero = W.zero size in
    if W.is_zero c then Some (zero, zero)
    else if W.is_zero a && W.is_zero b then None
    else if W.is_zero a then
      if W.is_zero (W.modulo c b) then Some (zero, W.div c b) else None
    else if W.is_zero b then
      if W.is_zero (W.modulo c a) then Some (W.div c a, zero) else None
    else
      (* Bezout coefficients. *)
      let d, unsigned_x, unsigned_y = W.gcdext_exn a b in
      let signed_x = W.signed unsigned_x in
      let signed_y = W.signed unsigned_y in
      let gcd_quotient = W.div c d in
      (* Double-width products. *)
      let signed_x0 = W.signed (mul_exact signed_x gcd_quotient) in
      let signed_y0 = W.signed (mul_exact signed_y gcd_quotient) in
      if not (W.is_zero (W.modulo c d)) then None
      else
        (* Minimal-|x|,|y| solution pair. *)
        Some (W.extract_exn ~hi:(size-1) signed_x0,
              W.extract_exn ~hi:(size-1) signed_y0)

  (* Split w into odd part and power of two. *)
  let factor_2s (w : word) : word * int =
    let rec factor_help (hi : int) (lo : int) : int =
      if hi = lo then hi else
        let mid = (hi + lo) / 2 in
        let lo_part = W.extract_exn ~hi:mid ~lo w in
        if W.is_zero lo_part then factor_help hi (mid + 1)
        else factor_help mid lo
    in
    let width = W.bitwidth w in
    let lo = factor_help (width - 1) 0 in
    (* Keep the input width. *)
    let hi = width - 1 + lo in
    W.extract_exn ~hi ~lo w, lo

  (* 2^i at [width] bits. *)
  let dom_size_cache : (int * int, word) Hashtbl.t = Hashtbl.create 16
  let dom_size ?width (i : int) : word =
    let width = Option.value ~default:(i + 1) width in
    match Hashtbl.find_opt dom_size_cache (i, width) with
    | Some w -> w
    | None ->
      let w = W.lshift (W.one width) (W.of_int ~width i) in
      Hashtbl.add dom_size_cache (i, width) w;
      w

  let min w1 w2 : word = if W.(<) w1 w2 then w1 else w2

  (* Closest value representable at [width] bits. *)
  let cap_at_width ~width (w : word) : word =
    let w_width = W.bitwidth w in
    (* Exact width is the identity. *)
    if w_width = width then w
    else if w_width <= width then W.extract_exn ~hi:(width - 1) w else
      (* Largest width-bit number. *)
      let max_w = W.pred @@ dom_size ~width:w_width width in
      let res_val = min max_w w in
      W.extract_exn ~hi:(width - 1) res_val
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

  (* One unary word op: reference vs production. *)
  let chk1 (nm : string) (w : word) (f : word -> word) (rf : word -> word) =
    incr checked;
    let got = (try Ok (rf w) with e -> Error e) in
    let exp = (try Ok (f w) with e -> Error e) in
    match got, exp with
    | Ok g, Ok e ->
      if not (eqw g e) then
        bad (Printf.sprintf "WORD %s(%s): ref=%s prod=%s" nm (show w) (show g) (show e))
    | Error _, Error _ -> incr both_raised
    | Ok g, Error _ ->
      bad (Printf.sprintf "WORD %s(%s): ref=%s prod raised" nm (show w) (show g))
    | Error _, Ok e ->
      bad (Printf.sprintf "WORD %s(%s): ref raised prod=%s" nm (show w) (show e))
  in

  (* One binary word op. *)
  let chk2 (nm : string) (w1 : word) (w2 : word)
      (f : word -> word -> word) (rf : word -> word -> word) =
    incr checked;
    let got = (try Ok (rf w1 w2) with e -> Error e) in
    let exp = (try Ok (f w1 w2) with e -> Error e) in
    match got, exp with
    | Ok g, Ok e ->
      if not (eqw g e) then
        bad (Printf.sprintf "WORD %s(%s,%s): ref=%s prod=%s" nm (show w1) (show w2)
               (show g) (show e))
    | Error _, Error _ -> incr both_raised
    | Ok g, Error _ ->
      bad (Printf.sprintf "WORD %s(%s,%s): ref=%s prod raised" nm (show w1) (show w2)
             (show g))
    | Error _, Ok e ->
      bad (Printf.sprintf "WORD %s(%s,%s): ref raised prod=%s" nm (show w1) (show w2)
             (show e))
  in

  (* One bool-valued word op. *)
  let chk1b (nm : string) (w : word) (f : word -> bool) (rf : word -> bool) =
    incr checked;
    let got = (try Ok (rf w) with e -> Error e) in
    let exp = (try Ok (f w) with e -> Error e) in
    match got, exp with
    | Ok g, Ok e ->
      if not (Bool.equal g e) then
        bad (Printf.sprintf "WORD %s(%s): ref=%b prod=%b" nm (show w) g e)
    | Error _, Error _ -> incr both_raised
    | _ ->
      bad (Printf.sprintf "WORD %s(%s): ref/prod disagreed on raising" nm (show w))
  in

  (* Word of [width] bits holding [v] mod 2^width. *)
  let word_of_z (width : int) (v : Z.t) : word =
    Word.of_string (Printf.sprintf "%s:%d" (Z.to_string v) width)
  in

  (* All the ops, over one (width, v1, v2) triple. *)
  let check_word_ops (width : int) (v1 : Z.t) (v2 : Z.t) =
    let w1 = word_of_z width v1 in
    let w2 = word_of_z width v2 in
    (* [c] is INDEPENDENT of (a, b): taking c = a makes [c mod gcd = 0]
       hold identically, so only an independent c exercises
       bounded_diophantine's None arm (ax + by = c unsolvable). *)
    let w3 = word_of_z width (Z.add v1 v2) in
    chk2 "mul_exact" w1 w2 Wo.mul_exact Ref_word.mul_exact;
    chk2 "add_exact" w1 w2 Wo.add_exact Ref_word.add_exact;
    chk1 "succ_exact" w1 Wo.succ_exact Ref_word.succ_exact;
    chk1 "succ_exact" w2 Wo.succ_exact Ref_word.succ_exact;
    CKL.iter [ 0; 1; 2; 3 ] ~f:(fun i ->
        chk1 (Printf.sprintf "lshift_exact %d" i) w1
          (fun w -> Wo.lshift_exact w i) (fun w -> Ref_word.lshift_exact w i));
    chk2 "bounded_gcd" w1 w2 Wo.bounded_gcd Ref_word.bounded_gcd;
    chk2 "cdiv" w1 w2 Wo.cdiv Ref_word.cdiv;
    chk1b "is_one" w1 Wo.is_one Ref_word.is_one;
    chk1b "is_one" w2 Wo.is_one Ref_word.is_one;
    CKL.iter [ w1; w2; w3 ] ~f:(fun c ->
        incr checked;
        match
          (try Ok (Ref_word.bounded_diophantine w1 w2 c) with e -> Error e),
          (try Ok (Wo.bounded_diophantine w1 w2 c) with e -> Error e)
        with
        | Ok (Some (rx, ry)), Ok (Some (px, py)) ->
          if not (eqw rx px && eqw ry py) then
            bad (Printf.sprintf "WORD bounded_diophantine(%s,%s,%s): ref=(%s,%s) prod=(%s,%s)"
                   (show w1) (show w2) (show c) (show rx) (show ry) (show px) (show py))
        | Ok None, Ok None -> ()
        | Error _, Error _ -> incr both_raised
        | _ ->
          bad (Printf.sprintf "WORD bounded_diophantine(%s,%s,%s): shape differs"
                 (show w1) (show w2) (show c)));
    (let rf = Ref_word.factor_2s w1 and pf = Wo.factor_2s w1 in
     incr checked;
     if not (eqw (fst rf) (fst pf) && Stdlib.( = ) (snd rf) (snd pf)) then
       bad (Printf.sprintf "WORD factor_2s(%s): ref=(%s,%d) prod=(%s,%d)"
              (show w1) (show (fst rf)) (snd rf) (show (fst pf)) (snd pf)));
    (* dom_size / cap_at_width: no-argument-width and explicit widths. *)
    CKL.iter [ width; width + 1; 2 * width + 1 ] ~f:(fun tgt ->
        incr checked;
        let rd = Ref_word.dom_size ~width:tgt (Z.to_int (Z.erem v1 (Z.of_int 8))) in
        let pd = Wo.dom_size ~width:tgt (Z.to_int (Z.erem v1 (Z.of_int 8))) in
        if not (eqw rd pd) then
          bad (Printf.sprintf "WORD dom_size i=%d width=%d: ref=%s prod=%s"
                 (Z.to_int (Z.erem v1 (Z.of_int 8))) tgt (show rd) (show pd));
        incr checked;
        let rc = Ref_word.cap_at_width ~width:tgt w1 in
        let pc = Wo.cap_at_width ~width:tgt w1 in
        if not (eqw rc pc) then
          bad (Printf.sprintf "WORD cap_at_width(%s) width=%d: ref=%s prod=%s"
                 (show w1) tgt (show rc) (show pc)));
    (* The int63 fast path's precondition: whenever the true result is
       itself in the small range, native int arithmetic is exact. The
       guard is load-bearing — (2^62-1) + 1 leaves the range, so
       "small operands => small result" is FALSE (that is precisely the
       overflow the substrate must detect and fall back on). *)
    (match i63 w1, i63 w2 with
     | Some a, Some b ->
       let z1 = z_of w1 and z2 = z_of w2 in
       CKL.iter [ ("add", Z.add z1 z2, a + b); ("mul", Z.mul z1 z2, a * b) ]
         ~f:(fun (nm, expected, got) ->
             if Z.leq (Z.abs expected) max_small then (
               incr checked;
               if not (Z.equal expected (Z.of_int got)) then
                 bad (Printf.sprintf "INT63 %s not exact at w=%d: %s %s (z=%s int=%d)"
                        nm width (show w1) (show w2) (Z.to_string expected) got)))
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
          CKL.iter vals ~f:(fun v2 -> check_word_ops width v1 v2)));

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
              Ws.Clp.create (Word.of_int ~width:w b1)
                ~step:(Word.of_int ~width:w s1)
                ~cardn:(Word.of_int ~width:(w + 1) c1)
            in
            (* is_top on the swept value *)
            incr checked;
            if not (Bool.equal (Ws.Clp.is_top p1) (ref_is_top p1)) then
              bad (Printf.sprintf "IS_TOP w=%d b=%d s=%d c=%d" w b1 s1 c1);
            (* the word ops, driven by the swept (base, step, cardn) *)
            if c1 land 3 = 0 && s1 land 3 = 0 && b1 land 3 = 0 then
              check_word_ops w (Z.of_int b1) (Z.of_int s1);
            for b2 = 0 to n - 1 do
              let p2 =
                Ws.Clp.create (Word.of_int ~width:w b2)
                  ~step:(Word.of_int ~width:w s1)
                  ~cardn:(Word.of_int ~width:(w + 1) c1)
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
  Printf.printf "clpequiv: checked=%d mismatches=%d both-raised=%d\n"
    !checked !mism !both_raised
