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




  ]

let () = run "pieces" tests
