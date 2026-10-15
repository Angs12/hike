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
let w64i (v : int64) = Cbat_word.of_int64 ~width:64 v
let lshift_comp = "During lshift, maximum element of CLP2 is >= CLP1's width"
let sh16 = Clp.create (w64 16)
let amt2 = Clp.of_list ~width:2 [ Cbat_word.of_int ~width:2 2 ]
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















    pin "CLP-09" "CLP5: bottom: cardn 0, empty iter, no min elem"
      (fun () ->
        check "CLP-09"
          (let b = Clp.bottom 32 in
           Clp.is_bottom b
           && Cbat_word.to_int_exn (Clp.cardinality b) = 0
           && Clp.iter b = []
           && Clp.min_elem b = None));









    pin "CLP-14" "CLP8: join of disjoint singletons contains both operands"
      (fun () ->
        let s5 = Clp.create (w32 5) in
        let s9 = Clp.create (w32 9) in
        let u = Clp.join s5 s9 in
        check "CLP-14" (Clp.elem (w32 5) u && Clp.elem (w32 9) u));











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











    pin "CLP-44" "D3-1: div by a set containing 0 -> top, no raise"
      (fun () ->
        let d1 = Clp.of_list ~width:32 [ w32 1; w32 2 ] in
        let d0 = Clp.of_list ~width:32 [ w32 0; w32 1 ] in
        check "CLP-44" (Clp.is_top (Clp.div d1 d0)));









    pin "CLP-49" "D2-1: CLP widen_join of non-subset singletons -> join, no assert"
      (fun () ->
        let s5 = Clp.create (w32 5) in
        let s9 = Clp.create (w32 9) in
        let w = Clp.widen_join s5 s9 in
        check "CLP-49" (Clp.elem (w32 5) w && Clp.elem (w32 9) w));















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











    pin "CLP-63" "O4c-7a: add commutative"
      (fun () ->
        let p = Clp.create ~width:64 ~step:(w64 2) ~cardn:(Cbat_word.of_int ~width:65 5) (w64 10) in
        let q = Clp.create ~width:64 ~step:(w64 4) ~cardn:(Cbat_word.of_int ~width:65 3) (w64 6) in
        check "CLP-63" (clp_agree (Clp.add p q) (Clp.add q p)));







    pin "CLP-67" "O4c-8: step 0 with cardn 1 canonizes to the singleton {10}"
      (fun () ->
        let s8 = Clp.create ~width:32 ~step:(w32 0) ~cardn:(w33 1) (w32 10) in
        check "CLP-67"
          (Clp.equal s8 (Clp.create (w32 10))
          && Clp.iter s8 = [ w32 10 ]
          && Clp.elem (w32 10) s8
          && not (Clp.elem (w32 11) s8)));









    pin "CLP-72"
      "A-1: mixed-width rshift (32-bit {0xFF} >> 64-bit {2}) is EXACTLY {0x3F} at 32 bits (no guard \
       fire)"
      (fun () ->
        let r1 = Clp.rshift (Clp.create (w32 0xFF)) (Clp.create (w64 2)) in
        check "CLP-72" (Clp.equal r1 (Clp.create (w32 0x3F))));



















    pin "CLP-82" "D7-10: lshift 2-bit {2} amount vs 64-bit operand -> computes {64}, no spurious fire"
      (fun () ->
        let fire_l = fired lshift_comp (fun () -> ignore (Clp.lshift sh16 amt2)) in
        let r = Clp.lshift sh16 amt2 in
        check "CLP-82"
          (Clp.bitwidth r = 64 && Clp.min_elem r = Some (w64 64) && (not (Clp.is_top r)) && not fire_l));

































    pin "CLP-100"
      "property m6 Exact↔Clp round-trips enumerated (200 random progression trials: soundness always, \
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
          let subset s1 s2 = List.for_all (fun x -> Ex.elem x s2) s1 in
          let expect b msg = if not b then begin
              Printf.printf "FAIL: property m6 %s (trial %d)\n" msg _i;
              incr failures
            end
          in
          (* Exact -> Clp -> Exact *)
          let s = Ex.of_list ~width:w (els [] 0) in
          let p = Clp.of_list ~width:(Ex.bitwidth s) (Ex.iter s) in
          let s2 = Ex.of_list ~width:(Clp.bitwidth p) (Clp.iter p) in
          expect (subset (Ex.iter s) s2) "Exact->Clp->Exact SOUND (s ⊆ s2)";
          expect
            (Cbat_word.compare (Ex.cardinality s) (Ex.cardinality s2) <= 0)
            "Exact->Clp->Exact cardn non-decreasing";
          if exact_shape then expect (Ex.equal s s2) "Exact->Clp->Exact EXACT (wrap-free arc)";
          (* Clp -> Exact -> Clp *)
          let p3 =
            Clp.create (Cbat_word.of_int ~width:w base) ~step:(Cbat_word.of_int ~width:w step)
              ~cardn:(Cbat_word.of_int ~width:(w + 1) n)
          in
          let s3 = Ex.of_list ~width:(Clp.bitwidth p3) (Clp.iter p3) in
          let p4 = Clp.of_list ~width:(Ex.bitwidth s3) (Ex.iter s3) in
          expect
            (List.for_all (fun x -> Clp.elem x p4) (Clp.iter p3))
            "Clp->Exact->Clp SOUND (p3 ⊆ p4)";
          expect
            (Cbat_word.compare (Clp.cardinality p3) (Clp.cardinality p4) <= 0)
            "Clp->Exact->Clp cardn non-decreasing";
          if exact_shape then expect (Clp.equal p3 p4) "Clp->Exact->Clp EXACT (wrap-free arc)"
        done;
        check "CLP-100" (!failures = 0));

    pin "CLP-101" "PBH-M1: mod of a wide interval by a constant is the residue hull"
      (fun () ->
        check "CLP-101"
          (let r = Clp.modulo (pbh_iv 64 0x17 0xfb6) (pbh_one 64 16) in
           Clp.min_elem r = Some (Wo.of_int ~width:64 0)
           && Clp.max_elem r = Some (Wo.of_int ~width:64 15)));

















    (* One sweep, two facts: the sound rows and the exact hull. *)
    pin "CLP-110" "PBH-M9/M10: mod/smod sweep — row soundness and the same-quotient exact residue hull (widths 4..8, all intervals, k<=5)"
      (fun () ->
        let unsound, inexact = pbh_mod_sweep () in
        check "CLP-110" (unsound = 0);
        check "CLP-111" (inexact = 0));

    pin "CLP-112"
      "CAST-S1: a SIGNED extension of a set crossing the sign boundary is the element-wise image of both \
       runs — exact, never top"
      (fun () ->
        (* {126, 128} at 8 bits: 126 keeps its value, 128 sign-extends to
           -128, so the 64-bit image is exactly {126, 2^64 - 128}. *)
        let p =
          Clp.create ~width:8 ~step:(Cbat_word.of_int ~width:8 2)
            ~cardn:(Cbat_word.of_int ~width:9 2) (Cbat_word.of_int ~width:8 126)
        in
        let r = Clp.cast Bil.SIGNED 64 p in
        check "CLP-112"
          (not (Clp.is_top r)
          && Clp.bitwidth r = 64
          && Clp.elem (w64 126) r
          && Clp.elem (w64i (-128L)) r
          && Cbat_word.to_int_exn (Clp.cardinality r) = 2);
        (* A wrapped progression {200, 44, 144} at 8 bits: the low arc
           straddles the boundary, so 44 images to itself and 144 to
           -112 — not to 144. *)
        let q =
          Clp.create ~width:8 ~step:(Cbat_word.of_int ~width:8 100)
            ~cardn:(Cbat_word.of_int ~width:9 3) (Cbat_word.of_int ~width:8 200)
        in
        let s = Clp.cast Bil.SIGNED 64 q in
        check "CLP-112w"
          (not (Clp.is_top s)
          && Clp.elem (w64i (-56L)) s
          && Clp.elem (w64 44) s
          && Clp.elem (w64i (-112L)) s));

    pin "CLP-113"
      "CAST-S2: the composite's SIGNED extension of the full 32-bit domain is the two half-domains, never top"
      (fun () ->
        let r = Ws.cast Bil.SIGNED 64 (Ws.top 32) in
        check "CLP-113"
          (not (Ws.is_top r)
          && Ws.min_elem r = Some (w64 0)
          && Ws.max_elem r = Some (w64i (-1L))
          && Cbat_word.to_int (Ws.cardinality r) = Ok 4294967296));

    pin "CLP-114"
      "DIV-Z: sdiv by an exact {0} contains every elementwise image — a negative dividend gives 1, a \
       non-negative one gives ones"
      (fun () ->
        let w8 = Cbat_word.of_int ~width:8 in
        let zero = Clp.singleton (w8 0) in
        let machine x = Wo.div (Wo.signed x) (Wo.signed (w8 0)) in
        let covers p =
          List.for_all
            (fun x -> Clp.elem (machine x) (Clp.sdiv p zero))
            (Clp.iter p)
        in
        (* {0xFF} is -1: x/0 = 1, not ones. *)
        check "CLP-114"
          (covers (Clp.singleton (w8 0xFF))
          && Clp.elem (w8 1) (Clp.sdiv (Clp.singleton (w8 0xFF)) zero)
          && covers (Clp.singleton (w8 0x05))
          && covers (Clp.of_list ~width:8 [ w8 0; w8 0xFF ])));

    pin "CLP-115"
      "AND/OR with a constant respect the operand's bounds and stride: [0..10] & 0xff stays \
       [0..10], {0,8,…,800} & 0xf is the exact {0,8}, and [0..100] | 1 stays bounded"
      (fun () ->
        let bounded = int32 ~lo:0 ~hi:10 in
        let r = Clp.logand bounded (Clp.singleton (w32 0xff)) in
        check "CLP-115.and-bounds"
          (Clp.min_elem r = Some (w32 0) && Clp.max_elem r = Some (w32 10));
        let grid =
          Clp.create ~width:32 ~step:(w32 8)
            ~cardn:(Cbat_word.of_int ~width:33 101) (w32 0) in
        let r2 = Clp.logand grid (Clp.singleton (w32 0xf)) in
        check "CLP-115.and-stride" (Clp.equal r2 (Clp.of_list ~width:32 [ w32 0; w32 8 ]));
        let ray = int32 ~lo:0 ~hi:100 in
        let r3 = Clp.logor ray (Clp.singleton (w32 1)) in
        let odd_image =
          Clp.create ~width:32 ~step:(w32 2) ~cardn:(Cbat_word.of_int ~width:33 64) (w32 1)
        in
        check "CLP-115.or-bounds"
          (not (Clp.is_top r3)
          && Clp.subset (Clp.of_list ~width:32 [ w32 1; w32 3; w32 101 ]) r3
          && Clp.max_elem r3 = Some (w32 0x7F)
          && Clp.equal r3 odd_image));












  ]

let () = run "clp" tests
