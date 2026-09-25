(* Cbat_clp pins.  One Alcotest group per pin; each pin builds its own
   fixture, so no state crosses pins. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

(* Interval builder: [lo, hi] step 1. *)
let int32 ~lo ~hi =
  Clp.create ~width:32 ~step:(w32 1) ~cardn:(Cbat_word.of_int ~width:33 (hi - lo + 1)) (w32 lo)

(* Two CLPs agree: equal, same cardn, same elems, same extrema. *)
let clp_agree a b =
  let elems p = List.sort compare (Clp.iter p) in
  Clp.equal a b
  && Clp.cardinality a = Clp.cardinality b
  && elems a = elems b
  && Clp.min_elem a = Clp.min_elem b && Clp.max_elem a = Clp.max_elem b

(* An all-overshifted image is exactly {zero}: min/max/cardn agree, non-top. *)
let is_zero_clp (zero : Cbat_word.t) (r : Clp.t) : bool =
  Clp.min_elem r = Some zero
  && Clp.max_elem r = Some zero
  && Cbat_word.to_int_exn (Clp.cardinality r) = 1
  && (not (Clp.is_top r))
  && not (Clp.is_bottom r)

let w64i (v : int64) = Cbat_word.of_int64 ~width:64 v
let w63i (v : int64) = Cbat_word.of_int64 ~width:63 v

(* Shift operand fixtures + the wrapped-guard component strings. *)
let lshift_comp = "During lshift, maximum element of CLP2 is >= CLP1's width"
let rshift_comp = "During rshift, maximum element of CLP2 is >= CLP1's width"
let arshift_comp = "During arshift, maximum element of CLP2 is >= CLP1's width"
let sh16 = Clp.create (w64 16)
let amt2 = Clp.of_list ~width:2 [ Cbat_word.of_int ~width:2 2 ]
let amt64 = Clp.of_list ~width:64 [ w64 64 ]
let straddle = Clp.create ~width:64 ~step:(w64 2) ~cardn:(Cbat_word.of_int ~width:65 32) (w64 8)
let antipodal64 = Clp.of_list ~width:64 [ w64 1; Cbat_word.lshift (w64 1) (w64 63) ]

(* PBH divisor-row fixtures. *)
let pbh_iv (w : int) (lo : int) (hi : int) =
  Clp.interval ~width:w (Wo.of_int ~width:w lo) (Wo.of_int ~width:w hi)

let pbh_one (w : int) (v : int) = Clp.singleton (Wo.of_int ~width:w v)

(* Soundness/exactness counters for the mod/smod sweep, per pin. *)
let pbh_mod_sweep () : int * int =
  let unsound = ref 0 in
  let inexact = ref 0 in
  for w = 4 to 8 do
    for lo = -12 to 12 do
      for hi = lo to 12 do
        for k = 1 to 5 do
          let p1 = pbh_iv w lo hi in
          let p2 = pbh_one w k in
          let r = Clp.modulo p1 p2 in
          let gt = List.map (fun x -> Cbat_word.modulo x (Wo.of_int ~width:w k)) (Clp.iter p1) in
          if not (List.for_all (fun x -> Clp.elem x r) gt) then incr unsound;
          let r' = Clp.smodulo p1 p2 in
          let gt' =
            List.map
              (fun x ->
                 Cbat_word.modulo (Cbat_word.signed x) (Cbat_word.signed (Wo.of_int ~width:w k)))
              (Clp.iter p1)
          in
          if not (List.for_all (fun x -> Clp.elem x r') gt') then incr unsound;
          let slo = if lo < 0 then 0 else lo in
          let shi = max hi slo in
          if slo / k = shi / k && hi >= 0 && lo >= 0 then
            let want = Clp.of_list ~width:w gt in
            if not (Clp.equal r want) then incr inexact
        done
      done
    done
  done;
  (!unsound, !inexact)

let tests : unit Alcotest.test list =
  [
    pin "CLP-01" "CLP1: create n is a 32-bit singleton (bitwidth/min/max/cardn)"
      (fun () ->
        let c = Clp.create (w32 10) in
        check "CLP-01"
          (Clp.bitwidth c = 32
          && Clp.min_elem c = Some (w32 10)
          && Clp.max_elem c = Some (w32 10)
          && Cbat_word.to_int_exn (Clp.cardinality c) = 1));

    pin "CLP-02" "CLP1: elem of the singleton {10}"
      (fun () ->
        let c = Clp.create (w32 10) in
        check "CLP-02" (Clp.elem (w32 10) c && not (Clp.elem (w32 11) c)));

    pin "CLP-03" "CLP2: interval {10,12,14,16,18}: bounds sane"
      (fun () ->
        let clp2 = Clp.create ~width:32 ~step:(w32 2) ~cardn:(w33 5) (w32 10) in
        check "CLP-03"
          (Clp.bitwidth clp2 = 32
          && Clp.min_elem clp2 = Some (w32 10)
          && Clp.max_elem clp2 = Some (w32 18)
          && Cbat_word.to_int_exn (Clp.cardinality clp2) = 5));

    pin "CLP-04" "CLP2: interval membership (14 in, 15 not in)"
      (fun () ->
        let clp2 = Clp.create ~width:32 ~step:(w32 2) ~cardn:(w33 5) (w32 10) in
        check "CLP-04" (Clp.elem (w32 14) clp2 && not (Clp.elem (w32 15) clp2)));

    pin "CLP-05" "CLP2: iter enumerates the interval (descending; sorted = the set)"
      (fun () ->
        let clp2 = Clp.create ~width:32 ~step:(w32 2) ~cardn:(w33 5) (w32 10) in
        check "CLP-05"
          (List.sort compare (List.map Cbat_word.to_int_exn (Clp.iter clp2)) = [ 10; 12; 14; 16; 18 ]));

    pin "CLP-06" "CLP2: cardinality equals the iter length (bounds sanity)"
      (fun () ->
        let clp2 = Clp.create ~width:32 ~step:(w32 2) ~cardn:(w33 5) (w32 10) in
        check "CLP-06"
          (Cbat_word.to_int_exn (Clp.cardinality clp2) = List.length (Clp.iter clp2)));

    pin "CLP-07" "CLP3: of_list ~width:16 [3;1;2] -> {1,2,3} (sorted, deduped)"
      (fun () ->
        check "CLP-07"
          (let c = Clp.of_list ~width:16 [ w32 3; w32 1; w32 2 ] in
           Clp.bitwidth c = 16
           && Cbat_word.to_int_exn (Clp.cardinality c) = 3
           && Clp.min_elem c = Some (Cbat_word.of_int ~width:16 1)
           && Clp.max_elem c = Some (Cbat_word.of_int ~width:16 3)
           && Clp.elem (Cbat_word.of_int ~width:16 2) c));

    pin "CLP-08" "CLP4: of_list [] is bottom"
      (fun () -> check "CLP-08" (Clp.is_bottom (Clp.of_list ~width:32 [])));

    pin "CLP-09" "CLP5: bottom: cardn 0, empty iter, no min elem"
      (fun () ->
        check "CLP-09"
          (let b = Clp.bottom 32 in
           Clp.is_bottom b
           && Cbat_word.to_int_exn (Clp.cardinality b) = 0
           && Clp.iter b = []
           && Clp.min_elem b = None));

    pin "CLP-10" "CLP6: top: is_top, not bottom, absorbs by subset"
      (fun () ->
        let clp1 = Clp.create (w32 10) in
        let t = Clp.top 32 in
        check "CLP-10" (Clp.is_top t && (not (Clp.is_bottom t)) && Clp.subset clp1 t && Clp.subset t t));

    pin "CLP-11" "CLP7a: create_ascending basic properties and bounds"
      (fun () ->
        check "CLP-11"
          (let asc =
             Clp.create_ascending ~width:64 ~base:(Cbat_word.of_int ~width:64 8)
               ~step:(Cbat_word.of_int ~width:64 8)
           in
           Clp.is_ascending asc
           && Clp.is_infinite asc
           && not (Clp.is_descending asc)
           && not (Clp.is_circular asc)
           && Clp.min_elem asc = Some (Cbat_word.of_int ~width:64 8)
           && Clp.min_elem_signed asc = Some (Cbat_word.of_int ~width:64 8)));

    pin "CLP-12" "CLP7b: create_descending basic properties and bounds"
      (fun () ->
        check "CLP-12"
          (let desc =
             Clp.create_descending ~width:64 ~base:(Cbat_word.of_int ~width:64 64)
               ~step:(Cbat_word.of_int ~width:64 8)
           in
           Clp.is_descending desc
           && Clp.is_infinite desc
           && not (Clp.is_ascending desc)
           && not (Clp.is_circular desc)
           && Clp.max_elem desc = Some (Cbat_word.of_int ~width:64 64)
           && Clp.max_elem_signed desc = Some (Cbat_word.of_int ~width:64 64)));

    pin "CLP-13" "CLP7c: directional rays canonicalize singletons to Finite"
      (fun () ->
        check "CLP-13"
          (let asc1 =
             Clp.create_ascending ~width:64 ~base:(Cbat_word.ones 64) ~step:(Cbat_word.of_int ~width:64 8)
           in
           let desc1 =
             Clp.create_descending ~width:64 ~base:(Cbat_word.of_int ~width:64 7)
               ~step:(Cbat_word.of_int ~width:64 8)
           in
           not (Clp.is_ascending asc1)
           && not (Clp.is_infinite asc1)
           && not (Clp.is_descending desc1)
           && not (Clp.is_infinite desc1)));

    pin "CLP-14" "CLP8: join of disjoint singletons contains both operands"
      (fun () ->
        let s5 = Clp.create (w32 5) in
        let s9 = Clp.create (w32 9) in
        let u = Clp.join s5 s9 in
        check "CLP-14" (Clp.elem (w32 5) u && Clp.elem (w32 9) u));

    pin "CLP-15" "CLP8: join is above its operands (precedes = subset)"
      (fun () ->
        let s5 = Clp.create (w32 5) in
        let s9 = Clp.create (w32 9) in
        let u = Clp.join s5 s9 in
        check "CLP-15" (Clp.precedes s5 u && Clp.precedes s9 u));

    pin "CLP-16" "CLP9: join is commutative"
      (fun () ->
        let s5 = Clp.create (w32 5) in
        let s9 = Clp.create (w32 9) in
        check "CLP-16" (Clp.equal (Clp.join s5 s9) (Clp.join s9 s5)));

    pin "CLP-17" "CLP10: bottom is the join identity (both orders)"
      (fun () ->
        let s5 = Clp.create (w32 5) in
        check "CLP-17"
          (Clp.equal (Clp.join s5 (Clp.bottom 32)) s5 && Clp.equal (Clp.join (Clp.bottom 32) s5) s5));

    pin "CLP-18" "CLP11: top absorbs in join"
      (fun () ->
        let s5 = Clp.create (w32 5) in
        check "CLP-18" (Clp.is_top (Clp.join s5 (Clp.top 32))));

    pin "CLP-19" "CLP19: join of equal single points is the point"
      (fun () ->
        let s5 = Clp.create (w32 5) in
        check "CLP-19" (Clp.equal (Clp.join s5 s5) s5));

    pin "CLP-20" "CLP12: meet of overlapping intervals: intersection members only"
      (fun () ->
        let clp2 = Clp.create ~width:32 ~step:(w32 2) ~cardn:(w33 5) (w32 10) in
        let q = Clp.of_list ~width:32 [ w32 14; w32 16; w32 18 ] in
        let m = Clp.meet clp2 q in
        check "CLP-20"
          (Clp.elem (w32 14) m
          && Clp.elem (w32 16) m
          && Clp.elem (w32 18) m
          && (not (Clp.elem (w32 10) m))
          && not (Clp.elem (w32 17) m)));

    pin "CLP-21" "CLP13: top is the meet identity; bottom is the meet zero"
      (fun () ->
        let clp2 = Clp.create ~width:32 ~step:(w32 2) ~cardn:(w33 5) (w32 10) in
        check "CLP-21"
          (Clp.equal (Clp.meet clp2 (Clp.top 32)) clp2 && Clp.is_bottom (Clp.meet clp2 (Clp.bottom 32))));

    pin "CLP-22" "CLP14: meet absorption: (p U q) n p = p"
      (fun () ->
        let clp2 = Clp.create ~width:32 ~step:(w32 2) ~cardn:(w33 5) (w32 10) in
        check "CLP-22"
          (let p = clp2 and q2 = Clp.create (w32 20) in
           let un = Clp.join p q2 in
           Clp.equal (Clp.meet un p) p && Clp.equal (Clp.meet p un) p));

    pin "CLP-23" "CLP15: meet of disjoint single points is bottom"
      (fun () ->
        check "CLP-23" (Clp.is_bottom (Clp.meet (Clp.create (w32 10)) (Clp.create (w32 11)))));

    pin "CLP-24" "CLP16: single-point meet: {10} n {10,12,14,16,18} = {10}"
      (fun () ->
        let clp2 = Clp.create ~width:32 ~step:(w32 2) ~cardn:(w33 5) (w32 10) in
        check "CLP-24"
          (Clp.equal (Clp.meet (Clp.create (w32 10)) clp2) (Clp.create (w32 10))));

    pin "CLP-25" "CLP17: meet is below join"
      (fun () ->
        let clp2 = Clp.create ~width:32 ~step:(w32 2) ~cardn:(w33 5) (w32 10) in
        let q = Clp.of_list ~width:32 [ w32 14; w32 16; w32 18 ] in
        check "CLP-25" (Clp.precedes (Clp.meet clp2 q) (Clp.join clp2 q)));

    pin "CLP-26" "CLP18: widen_join p p = p; widen_join bottom {5} = top"
      (fun () ->
        let s5 = Clp.create (w32 5) in
        check "CLP-26"
          (Clp.equal (Clp.widen_join s5 s5) s5 && Clp.is_top (Clp.widen_join (Clp.bottom 32) s5)));

    pin "CLP-27"
      "W1: [0,9] \\ [3,5] — the interior run is two pieces, not one CLP: the identity (the sound \
       over-approximation)"
      (fun () ->
        let a = int32 ~lo:0 ~hi:9 in
        let b = int32 ~lo:3 ~hi:5 in
        check "CLP-27" (Clp.equal (Clp.diff a b) a && Clp.subset (Clp.diff a b) a));

    pin "CLP-28"
      "W1b: the boundary-touch runs are exact — [0,9] \\ [0,2] = {3..9}; [0,9] \\ [7,9] = {0..6}"
      (fun () ->
        let a = int32 ~lo:0 ~hi:9 in
        let d_s = Clp.diff a (int32 ~lo:0 ~hi:2) in
        let d_e = Clp.diff a (int32 ~lo:7 ~hi:9) in
        check "CLP-28"
          (Clp.cardinality d_s = w33 7
          && Clp.elem (w32 3) d_s
          && Clp.elem (w32 9) d_s
          && (not (Clp.elem (w32 2) d_s))
          && Clp.cardinality d_e = w33 7
          && Clp.elem (w32 0) d_e
          && Clp.elem (w32 6) d_e
          && not (Clp.elem (w32 7) d_e)));

    pin "CLP-29" "W2: full64 \\ {0x2a} = the wrapped complement (cardn 2^64 − 1, exact)"
      (fun () ->
        let c = w64 0x2a in
        let d2 = Clp.diff (Clp.top 64) (Clp.create c) in
        check "CLP-29"
          (Clp.cardinality d2
           = Cbat_word.sub
               (Cbat_word.lshift (Cbat_word.of_int ~width:65 1) (Cbat_word.of_int ~width:65 64))
               (Cbat_word.of_int ~width:65 1)
          && Clp.elem (w64 0x2b) d2
          && Clp.elem (w64 0x29) d2
          && not (Clp.elem c d2)));

    pin "CLP-30"
      "W3: the bottom/absorption — diff bottom a = bottom; diff a bottom = a; diff a a = bottom; the \
       singleton cases"
      (fun () ->
        let a = int32 ~lo:0 ~hi:9 in
        check "CLP-30"
          (Clp.is_bottom (Clp.diff (Clp.bottom 32) a)
          && Clp.equal (Clp.diff a (Clp.bottom 32)) a
          && Clp.is_bottom (Clp.diff a a)
          && Clp.is_bottom (Clp.diff (Clp.create (w32 5)) (Clp.create (w32 5)))
          && Clp.equal (Clp.diff (Clp.create (w32 5)) (Clp.create (w32 7))) (Clp.create (w32 5))));

    pin "CLP-31" "W4: the diff contract — (diff a b) ∩ b = ∅ element-wise; diff ⊆ a; a\\b ⊆ diff"
      (fun () ->
        let a = int32 ~lo:0 ~hi:9 in
        let d_s = Clp.diff a (int32 ~lo:0 ~hi:2) in
        let d_e = Clp.diff a (int32 ~lo:7 ~hi:9) in
        let c = w64 0x2a in
        check "CLP-31"
          (List.for_all (fun w -> not (Clp.elem w (int32 ~lo:0 ~hi:2))) (Clp.iter d_s)
          && Clp.subset d_s a
          && List.for_all
               (fun w -> (Clp.elem w a && not (Clp.elem w (int32 ~lo:0 ~hi:2))) = Clp.elem w d_s)
               (Clp.iter a)
          && List.for_all (fun w -> not (Clp.elem w (int32 ~lo:7 ~hi:9))) (Clp.iter d_e)
          && Clp.subset d_e a
          && not (Clp.elem c (Clp.diff (Clp.top 64) (Clp.create c)))));

    pin "CLP-32"
      "W5: the small-card gapped subtraction is exact — {0,2,4,6,8} \\ {0,4,8} = {2,6}"
      (fun () ->
        let a5 = Clp.create ~width:32 ~step:(w32 2) ~cardn:(w33 5) (w32 0) in
        let b5 = Clp.create ~width:32 ~step:(w32 4) ~cardn:(w33 3) (w32 0) in
        check "CLP-32"
          (Clp.equal (Clp.diff a5 b5)
             (Clp.create ~width:32 ~step:(w32 4) ~cardn:(w33 2) (w32 2))));

    pin "CLP-33"
      "W6: the singleton removal — the boundary singletons exact ([0,10] \\ {0} = {1..10}; \\ {10} = \
       {0..9}); the interior singleton is the identity"
      (fun () ->
        let a6 = int32 ~lo:0 ~hi:10 in
        let d6b = Clp.diff a6 (Clp.create (w32 0)) in
        let d6e = Clp.diff a6 (Clp.create (w32 10)) in
        let d6i = Clp.diff a6 (Clp.create (w32 4)) in
        check "CLP-33"
          (Clp.cardinality d6b = w33 10
          && Clp.elem (w32 1) d6b
          && (not (Clp.elem (w32 0) d6b))
          && Clp.cardinality d6e = w33 10
          && Clp.elem (w32 0) d6e
          && (not (Clp.elem (w32 10) d6e))
          && Clp.equal d6i a6));

    pin "CLP-34"
      "W9: lnot/neg — the exact mirror rows: lnot {0,2,4} = {7,5,3}; neg {0,2,4} = {0,6,4}; the top \
       fixed; the singleton mirrors"
      (fun () ->
        let w3 = Cbat_word.of_int ~width:3 in
        let l9 = Clp.create ~width:3 ~step:(w3 2) ~cardn:(Cbat_word.of_int ~width:4 3) (w3 0) in
        check "CLP-34"
          (Clp.elem (w3 7) (Clp.lnot l9)
          && Clp.elem (w3 5) (Clp.lnot l9)
          && Clp.elem (w3 3) (Clp.lnot l9)
          && (not (Clp.elem (w3 0) (Clp.lnot l9)))
          && Clp.elem (w3 0) (Clp.neg l9)
          && Clp.elem (w3 6) (Clp.neg l9)
          && Clp.elem (w3 4) (Clp.neg l9)
          && (not (Clp.elem (w3 2) (Clp.neg l9)))
          && Ws.is_top (Ws.lnot (Ws.top 32))
          && Ws.is_top (Ws.neg (Ws.top 32))
          && Ws.equal (Ws.lnot (Ws.of_list ~width:3 [ w3 5 ])) (Ws.of_list ~width:3 [ w3 2 ])
          && Ws.equal (Ws.neg (Ws.of_list ~width:3 [ w3 5 ])) (Ws.of_list ~width:3 [ w3 3 ])));

    pin "CLP-35" "P5: not_implemented ~top degrades to top without raising"
      (fun () ->
        check "CLP-35" (Cbat_vsa_utils.not_implemented ~top:42 "policy5-probe" = 42));

    pin "CLP-36" "P5: not_implemented without a top still raises NotImplemented"
      (fun () ->
        let raised f =
          try
            f ();
            false
          with Cbat_vsa_utils.NotImplemented _ -> true
        in
        check "CLP-36" (raised (fun () -> Cbat_vsa_utils.not_implemented "no-top-probe")));

    pin "CLP-37" "P5: the top-path hit emits a warning log line (section cbat_vsa)"
      (fun () ->
        let hits = ref [] in
        Bap_future.Std.Stream.observe Bap.Std.Event.stream (fun ev ->
            match ev with
            | Event.Log.Message info -> hits := (info.section, info.message) :: !hits
            | _ -> ());
        ignore (Cbat_vsa_utils.not_implemented ~top:7 "policy5-log-probe");
        check "CLP-37"
          (List.exists
             (fun (sec, msg) -> sec = "cbat_vsa" && contains_substring msg "policy5-log-probe")
             !hits));

    pin "CLP-38" "A1: meet wrap {10..18} n {16..19} is NOT bottom (live path)"
      (fun () ->
        let a = Clp.of_list ~width:32 [ w32 10; w32 12; w32 14; w32 16; w32 18 ] in
        let b = Clp.of_list ~width:32 [ w32 16; w32 17; w32 18; w32 19 ] in
        let m = Clp.meet a b in
        check "CLP-38" (not (Clp.is_bottom m)));

    pin "CLP-39" "A1: ... and still contains the true intersection {16,18}"
      (fun () ->
        let a = Clp.of_list ~width:32 [ w32 10; w32 12; w32 14; w32 16; w32 18 ] in
        let b = Clp.of_list ~width:32 [ w32 16; w32 17; w32 18; w32 19 ] in
        let m = Clp.meet a b in
        check "CLP-39" (Clp.elem (w32 16) m && Clp.elem (w32 18) m));

    pin "CLP-40"
      "A1: ... the wrapped-finite meet is the exact intersection {16,18}"
      (fun () ->
        let a = Clp.of_list ~width:32 [ w32 10; w32 12; w32 14; w32 16; w32 18 ] in
        let b = Clp.of_list ~width:32 [ w32 16; w32 17; w32 18; w32 19 ] in
        let m = Clp.meet a b in
        check "CLP-40"
          (Clp.elem (w32 16) m && Clp.elem (w32 18) m
          && (not (Clp.elem (w32 10) m)) && (not (Clp.elem (w32 12) m))
          && (not (Clp.elem (w32 14) m)) && (not (Clp.elem (w32 17) m))
          && not (Clp.elem (w32 19) m)));

    pin "CLP-41" "A2: wrap {3,4,5} n {0,2,4} not bottom, contains 4"
      (fun () ->
        let m2 =
          Clp.meet
            (Clp.of_list ~width:32 [ w32 3; w32 4; w32 5 ])
            (Clp.of_list ~width:32 [ w32 0; w32 2; w32 4 ])
        in
        check "CLP-41" ((not (Clp.is_bottom m2)) && Clp.elem (w32 4) m2));

    pin "CLP-42" "A3: genuinely disjoint meets are still bottom (unchanged)"
      (fun () ->
        check "CLP-42" (Clp.is_bottom (Clp.meet (Clp.create (w32 10)) (Clp.create (w32 11)))));

    pin "CLP-43" "A3: bottom is still the meet zero; top the meet identity"
      (fun () ->
        let clp2 = Clp.create ~width:32 ~step:(w32 2) ~cardn:(w33 5) (w32 10) in
        check "CLP-43"
          (Clp.is_bottom (Clp.meet clp2 (Clp.bottom 32)) && Clp.equal (Clp.meet clp2 (Clp.top 32)) clp2));

    pin "CLP-44" "D3-1: div by a set containing 0 -> top, no raise"
      (fun () ->
        let d1 = Clp.of_list ~width:32 [ w32 1; w32 2 ] in
        let d0 = Clp.of_list ~width:32 [ w32 0; w32 1 ] in
        check "CLP-44" (Clp.is_top (Clp.div d1 d0)));

    pin "CLP-45" "D3-2: sdiv by a set containing 0 -> top, no raise"
      (fun () ->
        let d1 = Clp.of_list ~width:32 [ w32 1; w32 2 ] in
        let d0 = Clp.of_list ~width:32 [ w32 0; w32 1 ] in
        check "CLP-45" (Clp.is_top (Clp.sdiv d1 d0)));

    pin "CLP-46" "D3-3: div by exactly {0} -> the word semantics (x/0 = ones)"
      (fun () ->
        let d1 = Clp.of_list ~width:32 [ w32 1; w32 2 ] in
        check "CLP-46"
          (let r = Clp.div d1 (Clp.create (Cbat_word.zero 32)) in
           Clp.min_elem r = Some (Cbat_word.ones 32)
           && Clp.max_elem r = Some (Cbat_word.ones 32)));

    pin "CLP-47" "D3-4: sdiv by exactly {0} -> the word semantics (x/0 = ones)"
      (fun () ->
        let d1 = Clp.of_list ~width:32 [ w32 1; w32 2 ] in
        check "CLP-47"
          (let r = Clp.sdiv d1 (Clp.create (Cbat_word.zero 32)) in
           Clp.min_elem r = Some (Cbat_word.ones 32)
           && Clp.max_elem r = Some (Cbat_word.ones 32)));

    pin "CLP-48" "D3-5: div by a nonzero singleton still computes (no regression)"
      (fun () ->
        check "CLP-48"
          (let r = Clp.div (Clp.create (w32 10)) (Clp.create (w32 2)) in
           Clp.min_elem r = Some (w32 5) && Clp.max_elem r = Some (w32 5)));

    pin "CLP-49" "D2-1: CLP widen_join of non-subset singletons -> join, no assert"
      (fun () ->
        let s5 = Clp.create (w32 5) in
        let s9 = Clp.create (w32 9) in
        let w = Clp.widen_join s5 s9 in
        check "CLP-49" (Clp.elem (w32 5) w && Clp.elem (w32 9) w));

    pin "CLP-50" "D2-2: CLP widen_join of equal inputs is still the input"
      (fun () ->
        let s5 = Clp.create (w32 5) in
        check "CLP-50" (Clp.equal (Clp.widen_join s5 s5) s5));

    pin "CLP-51" "D2-3: CLP widen_join of a subset pair still widens (bottom {5} -> top)"
      (fun () ->
        let s5 = Clp.create (w32 5) in
        check "CLP-51" (Clp.is_top (Clp.widen_join (Clp.bottom 32) s5)));

    pin "CLP-52" "EX1b: the extrapolation contains the join (soundness)"
      (fun () ->
        let q9 = Clp.interval ~width:32 (w32 0) (w32 1) in
        let g9 = Clp.interval ~width:32 (w32 0) (w32 2) in
        let r1 = Clp.widen_join q9 g9 in
        check "CLP-52" (Clp.subset g9 r1));

    pin "CLP-53" "EX3: widen_join sound"
      (fun () ->
        let d1 = Clp.create (Cbat_word.neg (w32 16)) ~step:(w32 8) ~cardn:(w32 1) in
        let d2 = Clp.create (Cbat_word.neg (w32 24)) ~step:(w32 8) ~cardn:(w32 2) in
        let r3 = Clp.widen_join d1 d2 in
        check "CLP-53" (Clp.subset d2 r3));

    pin "CLP-54" "EX4: widen_join idempotent"
      (fun () ->
        let g9 = Clp.interval ~width:32 (w32 0) (w32 2) in
        check "CLP-54" (Clp.equal (Clp.widen_join g9 g9) g9));

    pin "CLP-55" "EX5: widen_join sound"
      (fun () ->
        let big1 = Clp.interval ~width:64 (w64 0) (Cbat_word.of_int ~width:64 0x100000000) in
        let big2 = Clp.interval ~width:64 (w64 0) (Cbat_word.of_int ~width:64 0x10000000000) in
        let r5 = Clp.widen_join big1 big2 in
        check "CLP-55" (Clp.subset big2 r5));

    pin "CLP-56" "EX6: widen_join sound"
      (fun () ->
        let s1 = Clp.interval ~width:32 (w32 0) (w32 0) in
        let s2 = Clp.create (w32 0) ~step:(w32 3) ~cardn:(w32 2) in
        let r6 = Clp.widen_join s1 s2 in
        check "CLP-56" (Clp.subset s2 r6));

    pin "CLP-57"
      "O4c-1: width-64 singleton 0xFFFF_FFFF_FFFF_FFFF is unsigned — min = max = itself, elem holds, 0 \
       not in"
      (fun () ->
        let ones64 = w64i (-1L) in
        let c1 = Clp.create ones64 in
        check "CLP-57"
          (Clp.min_elem c1 = Some ones64
          && Clp.max_elem c1 = Some ones64
          && Clp.elem ones64 c1
          && (not (Clp.elem (w64 0) c1))
          && (not (Clp.is_top c1))
          && not (Clp.is_bottom c1)));

    pin "CLP-58"
      "O4c-2: top 64 is the 2^64-cardinality class — is_top/is_infinite, absorbs a singleton (the Big \
       fallback, not I64-truncated)"
      (fun () ->
        let ones64 = w64i (-1L) in
        let t64 = Clp.top 64 in
        check "CLP-58"
          (Clp.is_top t64 && Clp.is_infinite t64
          && (not (Clp.is_bottom t64))
          && Clp.subset (Clp.create (w64 0)) t64
          && Clp.elem ones64 t64
          && Clp.elem (w64 0) t64));

    pin "CLP-59"
      "O4c-3: top 63 is the 2^63-cardinality class (fits Int64 — the I64 boundary) — is_top/is_infinite"
      (fun () ->
        let t63 = Clp.top 63 in
        check "CLP-59" (Clp.is_top t63 && Clp.is_infinite t63 && not (Clp.is_bottom t63)));

    pin "CLP-60"
      "O4c-4: width-63 singleton 2^63−1 is unsigned and exact (top bit of a 63-bit word; min = max = \
       itself)"
      (fun () ->
        let w63 = Cbat_word.of_int ~width:63 in
        let max63 = w63i Int64.max_int in
        let c4 = Clp.create max63 in
        check "CLP-60"
          (Clp.min_elem c4 = Some max63
          && Clp.max_elem c4 = Some max63
          && Clp.elem max63 c4
          && (not (Clp.elem (w63 0) c4))
          && Cbat_word.to_int64_exn max63 = Int64.max_int));

    pin "CLP-61" "O4c-5: 64-bit wrap add — {0xFFFF_FFFF_FFFF_FFFF} + {1} = {0}"
      (fun () ->
        let ones64 = w64i (-1L) in
        let a5 = Clp.add (Clp.create ones64) (Clp.create (w64 1)) in
        check "CLP-61"
          (Clp.equal a5 (Clp.create (w64 0)) && Clp.elem (w64 0) a5 && not (Clp.elem (w64 1) a5)));

    pin "CLP-62" "O4c-6: 63-bit wrap sub — {0} − {1} = {2^63 − 1}"
      (fun () ->
        let w63 = Cbat_word.of_int ~width:63 in
        let max63 = w63i Int64.max_int in
        let a6 = Clp.sub (Clp.create (w63 0)) (Clp.create (w63 1)) in
        check "CLP-62"
          (Clp.equal a6 (Clp.create max63) && Clp.elem max63 a6 && not (Clp.elem (w63 0) a6)));

    pin "CLP-63" "O4c-7a: add commutative"
      (fun () ->
        let p = Clp.create ~width:64 ~step:(w64 2) ~cardn:(Cbat_word.of_int ~width:65 5) (w64 10) in
        let q = Clp.create ~width:64 ~step:(w64 4) ~cardn:(Cbat_word.of_int ~width:65 3) (w64 6) in
        check "CLP-63" (clp_agree (Clp.add p q) (Clp.add q p)));

    pin "CLP-64" "O4c-7b: meet commutative"
      (fun () ->
        let p = Clp.create ~width:64 ~step:(w64 2) ~cardn:(Cbat_word.of_int ~width:65 5) (w64 10) in
        let q = Clp.create ~width:64 ~step:(w64 4) ~cardn:(Cbat_word.of_int ~width:65 3) (w64 6) in
        check "CLP-64" (clp_agree (Clp.meet p q) (Clp.meet q p)));

    pin "CLP-65" "O4c-7c: join commutative"
      (fun () ->
        let p = Clp.create ~width:64 ~step:(w64 2) ~cardn:(Cbat_word.of_int ~width:65 5) (w64 10) in
        let q = Clp.create ~width:64 ~step:(w64 4) ~cardn:(Cbat_word.of_int ~width:65 3) (w64 6) in
        check "CLP-65" (clp_agree (Clp.join p q) (Clp.join q p)));

    pin "CLP-66" "O4c-7d: meet idempotent"
      (fun () ->
        let p = Clp.create ~width:64 ~step:(w64 2) ~cardn:(Cbat_word.of_int ~width:65 5) (w64 10) in
        check "CLP-66" (clp_agree (Clp.meet p p) p));

    pin "CLP-67" "O4c-8: step 0 with cardn 1 canonizes to the singleton {10}"
      (fun () ->
        let s8 = Clp.create ~width:32 ~step:(w32 0) ~cardn:(w33 1) (w32 10) in
        check "CLP-67"
          (Clp.equal s8 (Clp.create (w32 10))
          && Clp.iter s8 = [ w32 10 ]
          && Clp.elem (w32 10) s8
          && not (Clp.elem (w32 11) s8)));

    pin "CLP-68" "O4c-9: cardn 0 is bottom (empty iter, no min)"
      (fun () ->
        let s9 = Clp.create ~width:32 ~step:(w32 1) ~cardn:(w33 0) (w32 10) in
        check "CLP-68" (Clp.is_bottom s9 && Clp.iter s9 = [] && Clp.min_elem s9 = None));

    pin "CLP-69"
      "O4c-10: cardn-2 wrap flips the pair to ascending order (min 0xFFFFFFEE, max 0xFFFFFFF0)"
      (fun () ->
        let s10 = Clp.create ~width:32 ~step:(w32 0xFFFFFFFE) ~cardn:(w33 2) (w32 0xFFFFFFF0) in
        check "CLP-69"
          (Clp.min_elem s10 = Some (w32 0xFFFFFFEE)
          && Clp.max_elem s10 = Some (w32 0xFFFFFFF0)
          && Clp.elem (w32 0xFFFFFFEE) s10
          && Clp.elem (w32 0xFFFFFFF0) s10
          && not (Clp.elem (w32 0xFFFFFFEF) s10)));

    pin "CLP-70"
      "O4c-11: step·cardn = 2^w (2·4 = 8 = 2^3) is infinite — {0,2,4,6}, cardn 4, 7 not in"
      (fun () ->
        let w3 = Cbat_word.of_int ~width:3 in
        let w4 = Cbat_word.of_int ~width:4 in
        let s11 = Clp.create ~width:3 ~step:(w3 2) ~cardn:(w4 4) (w3 0) in
        check "CLP-70"
          (Clp.is_infinite s11
          && (not (Clp.is_top s11))
          && Clp.cardinality s11 = w4 4
          && Clp.elem (w3 6) s11
          && not (Clp.elem (w3 7) s11)));

    pin "CLP-71"
      "O4c-12: R2-1 — meet {0..8} with the circular hull {0xFFFFFFFF,0..8} = {0..8} exactly (no \
       spurious 0xFFFFFFFF)"
      (fun () ->
        let lo12 = Clp.create ~width:32 ~step:(w32 1) ~cardn:(w33 9) (w32 0) in
        let circ12 = Clp.create ~width:32 ~step:(w32 1) ~cardn:(w33 10) (w32 0xFFFFFFFF) in
        let m12 = Clp.meet lo12 circ12 in
        check "CLP-71"
          (Clp.equal m12 lo12
          && Clp.cardinality m12 = w33 9
          && (not (Clp.elem (w32 0xFFFFFFFF) m12))
          && Clp.elem (w32 0) m12
          && Clp.elem (w32 8) m12));

    pin "CLP-72"
      "A-1: mixed-width rshift (32-bit {0xFF} >> 64-bit {2}) is EXACTLY {0x3F} at 32 bits (no guard \
       fire)"
      (fun () ->
        let r1 = Clp.rshift (Clp.create (w32 0xFF)) (Clp.create (w64 2)) in
        check "CLP-72" (Clp.equal r1 (Clp.create (w32 0x3F))));

    pin "CLP-73"
      "A-2: the 32-bit shift over a 64-bit interval [0,40) yields a non-top, \
       non-bottom result"
      (fun () ->
        let amt40 = Clp.create ~width:64 ~step:(w64 1) ~cardn:(Cbat_word.of_int ~width:65 40) (w64 0) in
        let r2 = Clp.rshift (Clp.create (w32 1)) amt40 in
        check "CLP-73" ((not (Clp.is_top r2)) && (not (Clp.is_bottom r2)) && Clp.bitwidth r2 = 32));

    pin "CLP-74" "A-3: mixed-width rshift overshift (32-bit >> 64-bit {40}) is EXACTLY {0} at 32 bits"
      (fun () ->
        let r3 = Clp.rshift (Clp.create (w32 8)) (Clp.create (w64 40)) in
        check "CLP-74" (Clp.equal r3 (Clp.create (w32 0))));

    pin "CLP-75"
      "A-4: mixed-width arshift sign-fill (32-bit {all-ones} arshift 64-bit {40}) is EXACTLY \
       {all-ones} at 32 bits (the SIGN-extension)"
      (fun () ->
        let r4 = Clp.arshift (Clp.create (w32 0xFFFFFFFF)) (Clp.create (w64 40)) in
        check "CLP-75" (Clp.equal r4 (Clp.create (w32 0xFFFFFFFF))));

    pin "CLP-76"
      "A-5: the antipodal overshift image (64-bit {1, 2^63} arshift {70}) is {0, all-ones} \
       (equal-width path, no coercion)"
      (fun () ->
        let r5 = Clp.arshift antipodal64 (Clp.create (w64 70)) in
        check "CLP-76"
          (Cbat_word.to_int_exn (Clp.cardinality r5) = 2
          && Clp.elem (w64 0) r5
          && Clp.elem (Cbat_word.ones 64) r5
          && (not (Clp.elem (w64 1) r5))
          && not (Clp.is_top r5)));

    pin "CLP-77" "D5-1: CLP rshift on mixed-width operands COMPUTES (lane A) — {0} exactly, no assert, no top"
      (fun () ->
        let c32 = Clp.create (w32 16) in
        let c64 = sh16 in
        check "CLP-77" (Clp.equal (Clp.rshift c32 c64) (Clp.create (w32 0))));

    pin "CLP-78" "D5-2: CLP arshift on mixed-width operands COMPUTES (lane A) — {0} exactly, no assert, no top"
      (fun () ->
        let c32 = Clp.create (w32 16) in
        let c64 = sh16 in
        check "CLP-78" (Clp.equal (Clp.arshift c32 c64) (Clp.create (w32 0))));

    pin "CLP-79" "D5-3: CLP rshift/arshift on same-width singletons still exact"
      (fun () ->
        check "CLP-79"
          (let r = Clp.rshift (Clp.create (w32 16)) (Clp.create (w32 2)) in
           Clp.min_elem r = Some (w32 4)
           && Clp.max_elem r = Some (w32 4)
           &&
           let a = Clp.arshift (Clp.create (w32 16)) (Clp.create (w32 2)) in
           Clp.min_elem a = Some (w32 4) && Clp.max_elem a = Some (w32 4)));

    pin "CLP-80" "D5-4: rshift by an amount >= the operand width -> {0} exactly (overshift=zero, no raise)"
      (fun () ->
        check "CLP-80"
          (let r = Clp.rshift (Clp.create (w32 1)) (Clp.create (w32 32)) in
           Clp.min_elem r = Some (w32 0)
           && Clp.max_elem r = Some (w32 0)
           && Cbat_word.to_int_exn (Clp.cardinality r) = 1
           && (not (Clp.is_top r))
           && not (Clp.is_bottom r)));

    pin "CLP-81" "D5-5: rshift by an amount < the operand width still computes"
      (fun () ->
        check "CLP-81"
          (let r = Clp.rshift (Clp.create (w32 8)) (Clp.create (w32 3)) in
           Clp.min_elem r = Some (w32 1) && Clp.max_elem r = Some (w32 1)));

    pin "CLP-82" "D7-10: lshift 2-bit {2} amount vs 64-bit operand -> computes {64}, no spurious fire"
      (fun () ->
        let fire_l = fired lshift_comp (fun () -> ignore (Clp.lshift sh16 amt2)) in
        let r = Clp.lshift sh16 amt2 in
        check "CLP-82"
          (Clp.bitwidth r = 64 && Clp.min_elem r = Some (w64 64) && (not (Clp.is_top r)) && not fire_l));

    pin "CLP-83" "D7-11: lshift overshift (6-bit {40} amount vs 32-bit operand) -> {0} exactly, no fire"
      (fun () ->
        let fire_l = fired lshift_comp (fun () -> ignore (Clp.lshift sh16 amt2)) in
        check "CLP-83"
          (let r =
             Clp.lshift (Clp.create (w32 8)) (Clp.of_list ~width:6 [ Cbat_word.of_int ~width:6 40 ])
           in
           is_zero_clp (w32 0) r && not fire_l));

    pin "CLP-84"
      "D7-12: rshift 2-bit {2} amount vs 64-bit operand COMPUTES {4} (lane A), wrapped guard never fires"
      (fun () ->
        let fire_r = fired rshift_comp (fun () -> ignore (Clp.rshift sh16 amt2)) in
        check "CLP-84" (Clp.equal (Clp.rshift sh16 amt2) (Clp.create (w64 4)) && not fire_r));

    pin "CLP-85"
      "D7-13: arshift 2-bit {2} amount vs 64-bit operand COMPUTES {4} (lane A), wrapped guard never fires"
      (fun () ->
        let fire_a = fired arshift_comp (fun () -> ignore (Clp.arshift sh16 amt2)) in
        check "CLP-85" (Clp.equal (Clp.arshift sh16 amt2) (Clp.create (w64 4)) && not fire_a));

    pin "CLP-86" "D7-14: rshift/arshift overshift ({40} vs 32-bit) -> {0} exactly, no fire"
      (fun () ->
        let r8 = Clp.create (w32 8) in
        let a40 = Clp.of_list ~width:32 [ w32 40 ] in
        let fire_r = fired rshift_comp (fun () -> ignore (Clp.rshift r8 a40)) in
        let fire_a = fired arshift_comp (fun () -> ignore (Clp.arshift r8 a40)) in
        check "CLP-86"
          (let r = Clp.rshift r8 a40 in
           let a = Clp.arshift r8 a40 in
           is_zero_clp (w32 0) r && is_zero_clp (w32 0) a && (not fire_r) && not fire_a));

    pin "CLP-87" "E2eC-1: lshift {16} by {64} (min >= width) -> EXACTLY {0}, no fire"
      (fun () ->
        let fire_l = fired lshift_comp (fun () -> ignore (Clp.lshift sh16 amt64)) in
        check "CLP-87" (is_zero_clp (w64 0) (Clp.lshift sh16 amt64) && not fire_l));

    pin "CLP-88" "E2eC-2: lshift {16} by multi-card overshift {64,68,72} stride 4 -> {0}, no fire"
      (fun () ->
        let fire_l = fired lshift_comp (fun () -> ignore (Clp.lshift sh16 amt64)) in
        check "CLP-88"
          (let amt =
             Clp.create ~width:64 ~step:(w64 4) ~cardn:(Cbat_word.of_int ~width:65 3) (w64 64)
           in
           is_zero_clp (w64 0) (Clp.lshift sh16 amt) && not fire_l));

    pin "CLP-89" "E2eC-3: rshift {16} by {64} (min >= width) -> EXACTLY {0}, no fire"
      (fun () ->
        let fire_r = fired rshift_comp (fun () -> ignore (Clp.rshift sh16 amt64)) in
        check "CLP-89" (is_zero_clp (w64 0) (Clp.rshift sh16 amt64) && not fire_r));

    pin "CLP-90" "E2eC-4: arshift overshift of a mixed-sign operand -> {0, all-ones}, no fire"
      (fun () ->
        let fire_a = fired arshift_comp (fun () -> ignore (Clp.arshift antipodal64 amt64)) in
        check "CLP-90"
          (let r = Clp.arshift antipodal64 amt64 in
           Cbat_word.to_int_exn (Clp.cardinality r) = 2
           && Clp.elem (w64 0) r
           && Clp.elem (Cbat_word.ones 64) r
           && (not (Clp.elem (w64 1) r))
           && (not (Clp.is_top r))
           && not fire_a));

    pin "CLP-91" "E2eC-5: arshift overshift of a nonneg operand -> {0} exactly (sign-extension)"
      (fun () ->
        let fire_a = fired arshift_comp (fun () -> ignore (Clp.arshift sh16 amt64)) in
        check "CLP-91" (is_zero_clp (w64 0) (Clp.arshift sh16 amt64) && not fire_a));

    pin "CLP-92" "E2eC-6: arshift overshift of a negative operand -> {all-ones} exactly"
      (fun () ->
        let fire_a = fired arshift_comp (fun () -> ignore (Clp.arshift sh16 amt64)) in
        check "CLP-92"
          (let r = Clp.arshift (Clp.create (Cbat_word.lshift (w64 1) (w64 63))) amt64 in
           Clp.min_elem r = Some (Cbat_word.ones 64)
           && Clp.max_elem r = Some (Cbat_word.ones 64)
           && Cbat_word.to_int_exn (Clp.cardinality r) = 1
           && (not (Clp.is_top r))
           && not fire_a));

    pin "CLP-93" "E2eC-7: lshift {16} by straddling [8,70] step 2 -> non-top, contains capped image ∪ {0}"
      (fun () ->
        let fire_l = fired lshift_comp (fun () -> ignore (Clp.lshift sh16 straddle)) in
        check "CLP-93"
          (let r = Clp.lshift sh16 straddle in
           (not (Clp.is_top r))
           && (not (Clp.is_bottom r))
           && Clp.elem (w64 0) r (* overshift (and 16<<62 mod 2^64) *)
           && Clp.elem (w64 0x1000) r (* 16<<8 = capped min *)
           && Clp.elem (w64 0x4000) r (* 16<<10 *)
           && Clp.elem (w64 0x40000000) r (* 16<<30 *)
           && not fire_l));

    pin "CLP-94" "E2eC-8: rshift {2^40} by straddling [8,70] step 2 -> non-top, contains capped image ∪ {0}"
      (fun () ->
        let fire_r =
          fired rshift_comp (fun () -> ignore (Clp.rshift (Clp.create (Cbat_word.lshift (w64 1) (w64 40))) straddle))
        in
        check "CLP-94"
          (let r = Clp.rshift (Clp.create (Cbat_word.lshift (w64 1) (w64 40))) straddle in
           (not (Clp.is_top r))
           && (not (Clp.is_bottom r))
           && Clp.elem (w64 0) r (* 2^40>>a = 0 for a >= 41 *)
           && Clp.elem (w64 1) r (* 2^40>>40 *)
           && Clp.elem (w64 4) r (* 2^40>>38 *)
           && Clp.elem (w64 0x100000000) r (* 2^40>>8 = capped min *)
           && not fire_r));

    pin "CLP-95"
      "E2eC-9: arshift {2^63} by straddling [8,70] step 2 -> non-top, contains capped base ∪ {all-ones}"
      (fun () ->
        let fire_a =
          fired arshift_comp
            (fun () -> ignore (Clp.arshift (Clp.create (Cbat_word.lshift (w64 1) (w64 63))) straddle))
        in
        check "CLP-95"
          (let r = Clp.arshift (Clp.create (Cbat_word.lshift (w64 1) (w64 63))) straddle in
           (not (Clp.is_top r))
           && (not (Clp.is_bottom r))
           && Clp.elem (Cbat_word.ones 64) r (* overshift: amount 70 *)
           && Clp.elem (Cbat_word.neg (Cbat_word.lshift (w64 1) (w64 55))) r
           (* amount 8: sign-ext of 2^63>>8 = -2^55 *)
           && not fire_a));

    pin "CLP-96"
      "E2eC-10: lshift {16} by top(64) amount -> stride-class result (non-bottom, contains 0 and 16), no \
       fire"
      (fun () ->
        let fire_l = fired lshift_comp (fun () -> ignore (Clp.lshift sh16 (Clp.top 64))) in
        check "CLP-96"
          (let r = Clp.lshift sh16 (Clp.top 64) in
           (not (Clp.is_bottom r)) && Clp.elem (w64 0) r && Clp.elem (w64 16) r && not fire_l));

    pin "CLP-97" "E2eC-11: array_local pattern — 32-bit operand shifted by {32} -> {0} exactly, no fire"
      (fun () ->
        let fire_l =
          fired lshift_comp (fun () -> ignore (Clp.lshift (Clp.create (w32 1)) (Clp.of_list ~width:32 [ w32 32 ])))
        in
        check "CLP-97"
          (let r = Clp.lshift (Clp.create (w32 1)) (Clp.of_list ~width:32 [ w32 32 ]) in
           is_zero_clp (w32 0) r && not fire_l));

    pin "CLP-98" "E2eC-12: array_local pattern — 8-bit operand shifted by {8} -> {0} exactly, no fire"
      (fun () ->
        let a8 = Clp.of_list ~width:8 [ Cbat_word.of_int ~width:8 8 ] in
        let base = Clp.create (Cbat_word.of_int ~width:8 1) in
        let fire_l = fired lshift_comp (fun () -> ignore (Clp.lshift base a8)) in
        check "CLP-98"
          (let r = Clp.lshift base a8 in
           is_zero_clp (Cbat_word.of_int ~width:8 0) r && not fire_l));

    pin "CLP-100"
      "property m6 FinSet↔Clp round-trips enumerated (200 random progression trials: soundness always, \
       exactness on wrap-free arcs)"
      (fun () ->
        Random.init 20260822;
        let failures = ref 0 in
        for _i = 1 to 200 do
          let w = [| 4; 8; 12; 32 |].(Random.int 4) in
          let dom = 1 lsl w in
          (* Random.int's bound stays under 2^31: a 32-bit domain draws
             its base in two halves. *)
          let base =
            if dom <= 1 lsl 29 then Random.int dom
            else (Random.int (dom lsr 16) lsl 16) + Random.int (1 lsl 16)
          in
          let step = 1 + Random.int 5 in
          let n = 1 + Random.int 10 in
          let rec els acc k =
            if k = n then acc
            else els (Cbat_word.of_int ~width:w ((base + (k * step)) mod dom) :: acc) (k + 1)
          in
          (* Exact-round-trip shape: no wrap AND seam gap step-multiple. *)
          let wrap_free = base + ((n - 1) * step) < dom in
          let seam_ok = (dom - (base + ((n - 1) * step) - base)) mod step = 0 in
          let exact_shape = wrap_free && seam_ok in
          let subset s1 s2 = List.for_all (fun x -> Fs.elem x s2) s1 in
          let expect b msg = if not b then begin
              Printf.printf "FAIL: property m6 %s (trial %d)\n" msg _i;
              incr failures
            end
          in
          (* FinSet -> Clp -> FinSet *)
          let s = Fs.of_list ~width:w (els [] 0) in
          let p = Clp.of_list ~width:(Fs.bitwidth s) (Fs.iter s) in
          let s2 = Fs.of_list ~width:(Clp.bitwidth p) (Clp.iter p) in
          expect (subset (Fs.iter s) s2) "FinSet->Clp->FinSet SOUND (s ⊆ s2)";
          expect
            (Cbat_word.compare (Fs.cardinality s) (Fs.cardinality s2) <= 0)
            "FinSet->Clp->FinSet cardn non-decreasing";
          if exact_shape then expect (Fs.equal s s2) "FinSet->Clp->FinSet EXACT (wrap-free arc)";
          (* Clp -> FinSet -> Clp *)
          let p3 =
            Clp.create (Cbat_word.of_int ~width:w base) ~step:(Cbat_word.of_int ~width:w step)
              ~cardn:(Cbat_word.of_int ~width:(w + 1) n)
          in
          let s3 = Fs.of_list ~width:(Clp.bitwidth p3) (Clp.iter p3) in
          let p4 = Clp.of_list ~width:(Fs.bitwidth s3) (Fs.iter s3) in
          expect
            (List.for_all (fun x -> Clp.elem x p4) (Clp.iter p3))
            "Clp->FinSet->Clp SOUND (p3 ⊆ p4)";
          expect
            (Cbat_word.compare (Clp.cardinality p3) (Clp.cardinality p4) <= 0)
            "Clp->FinSet->Clp cardn non-decreasing";
          if exact_shape then expect (Clp.equal p3 p4) "Clp->FinSet->Clp EXACT (wrap-free arc)"
        done;
        check "CLP-100" (!failures = 0));

    pin "CLP-101" "PBH-M1: mod of a wide interval by a constant is the residue hull"
      (fun () ->
        check "CLP-101"
          (let r = Clp.modulo (pbh_iv 64 0x17 0xfb6) (pbh_one 64 16) in
           Clp.min_elem r = Some (Wo.of_int ~width:64 0)
           && Clp.max_elem r = Some (Wo.of_int ~width:64 15)));

    pin "CLP-102" "PBH-M2: mod inside one quotient block is the exact sub-interval"
      (fun () ->
        check "CLP-102"
          (let r = Clp.modulo (pbh_iv 64 0x23 0x29) (pbh_one 64 16) in
           Clp.min_elem r = Some (Wo.of_int ~width:64 3)
           && Clp.max_elem r = Some (Wo.of_int ~width:64 9)));

    pin "CLP-103" "PBH-M3: mod at width 128 (the idiv concat) keeps the residue bound"
      (fun () ->
        check "CLP-103"
          (let r = Clp.modulo (pbh_iv 128 0x17 0xfb6) (pbh_one 128 16) in
           Clp.min_elem r = Some (Wo.of_int ~width:128 0)
           && Clp.max_elem r = Some (Wo.of_int ~width:128 15)));

    pin "CLP-104" "PBH-M4: mod by exactly {0} is the identity (word semantics)"
      (fun () -> check "CLP-104" (Clp.equal (Clp.modulo (pbh_iv 64 5 9) (pbh_one 64 0)) (pbh_iv 64 5 9)));

    pin "CLP-105" "PBH-M5: mod by a bounded divisor range caps at its max"
      (fun () ->
        check "CLP-105"
          (let kmax = Wo.of_int64 ~width:128 0xffffffffffffffffL in
           let r =
             Clp.modulo (pbh_one 128 0x80)
               (Clp.interval ~width:128 (Wo.of_int ~width:128 1) kmax)
           in
           Clp.min_elem r = Some (Wo.of_int ~width:128 0)
           && Clp.max_elem r = Some (Wo.pred kmax)));

    pin "CLP-106" "PBH-M6: mod by strictly larger divisors keeps the dividend"
      (fun () -> check "CLP-106" (Clp.equal (Clp.modulo (pbh_iv 64 3 7) (pbh_iv 64 9 20)) (pbh_iv 64 3 7)));

    pin "CLP-107" "PBH-M7: smod of a nonnegative interval is the residue hull"
      (fun () ->
        check "CLP-107"
          (let r = Clp.smodulo (pbh_iv 64 3 0x33) (pbh_one 64 16) in
           Clp.min_elem r = Some (Wo.of_int ~width:64 0)
           && Clp.max_elem r = Some (Wo.of_int ~width:64 15)));

    pin "CLP-108" "PBH-M8: smod of a mixed-sign interval stays within +-(k-1)"
      (fun () ->
        check "CLP-108"
          (let p1 = pbh_iv 64 (-4) 7 in
           let r = Clp.smodulo p1 (pbh_one 64 16) in
           let gt =
             List.map
               (fun x ->
                  Cbat_word.modulo (Cbat_word.signed x) (Cbat_word.signed (Wo.of_int ~width:64 16)))
               (Clp.iter p1)
           in
           gt <> [] && List.for_all (fun x -> Clp.elem x r) gt));

    pin "CLP-109" "PBH-M11: sdiv corner hull soundness sweep (signed dividends, k<=5)"
      (fun () ->
        let qunsound = ref 0 in
        for w = 4 to 8 do
          for lo = -12 to 12 do
            for hi = lo to 12 do
              for k = 1 to 5 do
                let p1 = pbh_iv w lo hi in
                let p2 = pbh_one w k in
                let q = Clp.sdiv p1 p2 in
                let gt =
                  List.map
                    (fun x ->
                       Cbat_word.div (Cbat_word.signed x)
                         (Cbat_word.signed (Wo.of_int ~width:w k)))
                    (Clp.iter p1)
                in
                if not (List.for_all (fun x -> Clp.elem x q) gt) then incr qunsound
              done
            done
          done
        done;
        check "CLP-109" (!qunsound = 0));

    (* One sweep, two facts: the sound rows and the exact hull. *)
    pin "CLP-110" "PBH-M9/M10: mod/smod sweep — row soundness and the same-quotient exact residue hull (widths 4..8, all intervals, k<=5)"
      (fun () ->
        let unsound, inexact = pbh_mod_sweep () in
        check "CLP-110" (unsound = 0);
        check "CLP-111" (inexact = 0));

    pin "CLP-112" "PBH-M11: mod by a zero-straddling divisor keeps the dividend's hull (never top)"
      (fun () ->
        check "CLP-112"
          (let r =
             Clp.modulo (pbh_iv 64 10 20)
               (Clp.interval ~width:64 (Wo.of_int ~width:64 0)
                  (Wo.of_int ~width:64 4))
           in
           (not (Clp.is_top r))
           && Clp.min_elem r = Some (Wo.of_int ~width:64 0)
           && Clp.max_elem r = Some (Wo.of_int ~width:64 20)));

    pin "CLP-114"
      "WF-2: the wrapped-finite meet is sound — logxor {0x75..0x7B step 2} \
       {0x88} contains all four concrete xors"
      (fun () ->
        let w8 = Cbat_word.of_int ~width:8 in
        let q1 =
          Clp.create ~width:8 ~step:(w8 2) ~cardn:(Cbat_word.of_int ~width:9 4)
            (w8 0x75) in
        let q2 = Clp.singleton (w8 0x88) in
        let lx = Clp.logxor q1 q2 in
        check "CLP-114"
          (List.for_all (fun v -> Clp.elem (w8 v) lx)
             [ 0xFD; 0xFF; 0xF1; 0xF3 ]));

    pin "CLP-115"
      "WF-3: the wrapped-finite meet is sound — logxor {0xCF} {0xE9,0xEC} \
       contains both concrete xors"
      (fun () ->
        let w8 = Cbat_word.of_int ~width:8 in
        let s1 = Clp.singleton (w8 0xCF) in
        let s2 =
          Clp.create ~width:8 ~step:(w8 3) ~cardn:(Cbat_word.of_int ~width:9 2)
            (w8 0xE9) in
        let lx = Clp.logxor s1 s2 in
        check "CLP-115"
          (List.for_all (fun v -> Clp.elem (w8 v) lx) [ 0x26; 0x23 ]));
  ]

let () = run "clp" tests
