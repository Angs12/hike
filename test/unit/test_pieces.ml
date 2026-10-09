(* Cbat_clp.Pieces pins: the canonical progression union.  One Alcotest
   group per pin; each pin builds its own fixture, so no state crosses
   pins. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common

module P = Clp.Pieces

(* Interval builder: [lo, hi] step 1 at width 32. *)
let int32 ~lo ~hi = Clp.interval ~width:32 (w32 lo) (w32 hi)

let prog32 ~lo ~hi = P.of_progression (int32 ~lo ~hi)
let p32 l = P.of_list ~width:32 (List.map w32 l)
let mem_all ps v = List.for_all (fun w -> P.elem w ps) v
let not_mem_all ps v = List.for_all (fun w -> not (P.elem w ps)) v

let tests : unit Alcotest.test list =
  [
    pin "PCS-01"
      "the canonical form: sorted, disjoint, constant-difference runs, \
       contained pieces dropped, adjacent same-step runs merged"
      (fun () ->
        let p = p32 [ 0; 1; 2; 6; 7; 8 ] in
        check "PCS-01"
          (List.length (P.to_list p) = 2
          && mem_all p (List.map w32 [ 0; 1; 2; 6; 7; 8 ])
          && not_mem_all p (List.map w32 [ 3; 4; 5; 9 ])
          && P.equal p (P.union (prog32 ~lo:0 ~hi:2) (prog32 ~lo:6 ~hi:8))
          && P.equal (p32 [ 0; 2; 4 ])
               (P.of_progression
                  (Clp.create ~width:32 ~step:(w32 2)
                     ~cardn:(Cbat_word.of_int ~width:33 3) (w32 0)))
          && List.length
               (P.to_list (P.union (p32 [ 0; 1; 2; 3; 4 ]) (P.singleton (w32 2))))
             = 1
          && List.length
               (P.to_list (P.union (p32 [ 0; 1; 2 ]) (p32 [ 3; 4; 5 ])))
             = 1
          && P.elem (w32 5) (P.union (p32 [ 0; 1; 2 ]) (p32 [ 3; 4; 5 ]))));





    pin "PCS-04"
      "the cap: five pieces hull to four by the smallest growth, sound"
      (fun () ->
        let a = P.singleton (w32 0) in
        let b = P.of_progression (int32 ~lo:10 ~hi:20) in
        let c = P.of_progression (int32 ~lo:100 ~hi:110) in
        let d = P.of_progression (int32 ~lo:1000 ~hi:1010) in
        let e = P.of_progression (int32 ~lo:10000 ~hi:10100) in
        let u = P.union (P.union (P.union (P.union a b) c) d) e in
        check "PCS-04"
          (List.length (P.to_list u) = 4
          && mem_all u (List.map w32 [ 0; 10; 20; 100; 110; 1000; 1010; 10000; 10100 ])
          && P.elem (w32 5) u
          && not_mem_all u (List.map w32 [ 50; 500; 5000 ])));

    pin "PCS-05"
      "the positional widen: stable pairs widen, excess hulls into the last, \
       a top pair collapses"
      (fun () ->
        let a = p32 [ 0; 2; 4 ] in
        let b = p32 [ 0; 2; 4; 6; 8 ] in
        let w = P.widen_join a b in
        let l =
          P.widen_join (p32 [ 0; 1; 2; 10; 11; 12 ]) (p32 [ 0; 1; 2 ]) in
        let t = P.widen_join (P.top 32) (p32 [ 0; 1; 2 ]) in
        check "PCS-05"
          (P.elem (w32 6) w && P.elem (w32 100) w && P.is_ascending w
          && List.length (P.to_list l) = 1
          && P.elem (w32 5) l && P.elem (w32 12) l
          && P.is_top t));

    pin "PCS-06"
      "the union-order precedes: one covering piece or element-wise coverage"
      (fun () ->
        let gappy = p32 [ 0; 1; 2; 6; 7; 8 ] in
        let whole = prog32 ~lo:0 ~hi:8 in
        check "PCS-06"
          (P.precedes gappy whole
          && (not (P.precedes whole gappy))
          && P.precedes (prog32 ~lo:0 ~hi:2) whole
          && P.precedes (P.bottom 32) whole
          && not (P.precedes whole (P.bottom 32))));

    pin "PCS-09"
      "excess pieces join the last pair before widening or landmark extrapolation"
      (fun () ->
        let old = prog32 ~lo:10 ~hi:100 in
        let incoming = P.union (prog32 ~lo:10 ~hi:20) (prog32 ~lo:40 ~hi:110) in
        let widened = P.widen_join old incoming in
        check "PCS-09.widen" (P.max_elem widened = Some (Cbat_word.ones 32));
        let extrapolated = P.extrapolate_steps ~steps:2 old incoming in
        check "PCS-09.extrapolate" (P.max_elem extrapolated = Some (w32 130)));

    pin "PCS-10" "large strided meets retain their shared grid"
      (fun () ->
        List.iter (fun width ->
          let w = Cbat_word.of_int ~width in
          let prog base step count = P.of_progression
            (Clp.create ~width ~step:(w step)
               ~cardn:(Cbat_word.of_int ~width:(width + 1) count) (w base)) in
          let r = P.intersection (prog 23 11 20) (prog 66 8 14) in
          check "PCS-10" (P.equal r (P.singleton (w 122)))) [8;16;32;64];
        let w = Cbat_word.of_int ~width:5 in
        let a = Clp.create_ascending ~width:5 ~base:(w 1) ~step:(w 7) in
        let b = Clp.create_ascending ~width:5 ~base:(w 4) ~step:(w 9) in
        check "PCS-10.period" (Clp.equal (Clp.intersection a b) (Clp.singleton (w 22))));

    pin "PCS-11" "disjoint grids stay separate through order and extrapolation"
      (fun () ->
        List.iter (fun width ->
          let w = Cbat_word.of_int ~width in
          let scaled n = Cbat_word.lshift (w n) (w (width - 8)) in
          let prog base step count = P.of_progression
            (Clp.create ~width ~step:(scaled step)
               ~cardn:(Cbat_word.of_int ~width:(width + 1) count) (scaled base)) in
          let a = P.union (prog 59 10 20) (prog 7 1 11) in
          let b = P.of_progression (Clp.interval ~width (w 0) (scaled 59)) in
          check "PCS-11.disjoint" (List.length (P.to_list a) = 2);
          check "PCS-11.canonical" (List.for_all (fun p -> not (Clp.is_wrapped p)) (P.to_list a));
          check "PCS-11.order" (not (P.precedes a b));
          check "PCS-11.extrapolate"
            (P.elem (scaled 69) (P.extrapolate_steps ~steps:2 a b))) [8;16;32;64]);

    pin "PCS-12" "subset checks each arc after rebasing"
      (fun () ->
        let w = Cbat_word.of_int ~width:8 in
        let a = Clp.interval ~width:8 (w 200) (w 100) in
        let b = Clp.interval ~width:8 (w 50) (w 220) in
        check "PCS-12" (not (Clp.subset a b));
        let sparse = Clp.create ~width:8 ~step:(w 80)
            ~cardn:(Cbat_word.of_int ~width:9 3) (w 200) in
        check "PCS-12.sparse" (Clp.subset sparse (Clp.interval ~width:8 (w 0) (w 220)));
        let misaligned = Clp.create ~width:8 ~step:(w 6)
            ~cardn:(Cbat_word.of_int ~width:9 3) (w 252) in
        let grid = Clp.create ~width:8 ~step:(w 3)
            ~cardn:(Cbat_word.of_int ~width:9 85) (w 0) in
        check "PCS-12.alignment" (not (Clp.subset misaligned grid));
        let ray = Clp.create_descending ~width:8 ~base:(w 252) ~step:(w 3) in
        check "PCS-12.ray" (not (Clp.subset misaligned ray)));

    pin "PCS-13" "directional membership, enumeration and complement agree"
      (fun () ->
        List.iter (fun width ->
          let w = Cbat_word.of_int ~width in
          let d = Clp.create_descending ~width ~base:(w 9) ~step:(w 5) in
          let a = Clp.create_ascending ~width ~base:(w 9) ~step:(w 5) in
          check "PCS-13.desc" (Clp.elem (w 4) d && not (Clp.elem (w 14) d));
          check "PCS-13.asc" (Clp.elem (w 14) a && not (Clp.elem (w 4) a));
          check "PCS-13.iter" (List.sort Cbat_word.compare (Clp.iter d) = [w 4;w 9]);
          let flipped = Clp.lnot d in
          check "PCS-13.lnot" (Clp.elem (Cbat_word.lnot (w 4)) flipped);
          check "PCS-13.meet"
            (P.equal (P.intersection (P.of_progression d) (P.singleton (w 4))) (P.singleton (w 4))))
          [8;16;32;64]);



    pin "PCS-08"
      "the parts exactness: a straddling lshift keeps the overshift and the \
       capped exact pieces apart"
      (fun () ->
        let a = P.singleton (w64 16) in
        let amt =
          P.of_progression (Clp.interval ~width:64 (w64 8) (w64 70)) in
        let r = P.lshift a amt in
        check "PCS-08"
          (P.elem (w64 0) r && P.elem (w64 4096) r && P.elem (w64 8192) r
          && (not (P.is_top r)) && not (P.is_bottom r)));

    pin "PCS-14"
      "a directional translate contains every shifted element, including \
       those carried across the word boundary"
      (fun () ->
        let w8 = Cbat_word.of_int ~width:8 in
        let covers p i =
          let t = Clp.translate p i in
          List.for_all (fun x -> Clp.elem (Cbat_word.add x i) t) (Clp.iter p)
        in
        for base = 0 to 255 do
          List.iter (fun step ->
            let rays =
              [ Clp.create_ascending ~width:8 ~base:(w8 base) ~step:(w8 step);
                Clp.create_descending ~width:8 ~base:(w8 base) ~step:(w8 step) ]
            in
            List.iter (fun p ->
              for k = 0 to 36 do
                let i = w8 (k * 7) in
                if not (covers p i) then
                  Alcotest.failf "PCS-14.exhaustive: %s + %d"
                    (Sexplib.Sexp.to_string (Clp.sexp_of_t p)) (k * 7)
              done) rays)
            [ 1; 2; 3; 5; 8; 16; 48 ]
        done;
        let full = Clp.create_descending ~width:64 ~base:(w64 (-8)) ~step:(w64 8) in
        let shifted = Clp.add full (Clp.singleton (w64 8)) in
        check "PCS-14.full"
          (List.for_all (fun x -> Clp.elem (w64 x) shifted) [ 0; 8; -8; -16 ]);
        let ray = Clp.create_ascending ~width:64 ~base:(w64 (-0x58)) ~step:(w64 8) in
        let up = Clp.translate ray (w64 8) in
        check "PCS-14.ray" (Clp.elem (w64 0) up && Clp.elem (w64 (-0x50)) up));




  ]

let () = run "pieces" tests
