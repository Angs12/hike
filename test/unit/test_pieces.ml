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
let card32 n = Cbat_word.of_int ~width:33 n

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

    pin "PCS-02"
      "the exact interior diff: [0,10] \\ [3,5] = [0,2] ∪ [6,10]"
      (fun () ->
        let d = P.diff (prog32 ~lo:0 ~hi:10) (prog32 ~lo:3 ~hi:5) in
        check "PCS-02"
          (P.equal d (P.union (prog32 ~lo:0 ~hi:2) (prog32 ~lo:6 ~hi:10))
          && P.cardinality d = card32 8
          && mem_all d (List.map w32 [ 0; 1; 2; 6; 7; 8; 9; 10 ])
          && not_mem_all d (List.map w32 [ 3; 4; 5 ])
          && P.equal
               (P.diff (prog32 ~lo:0 ~hi:10) (p32 [ 3; 4; 5 ]))
               (P.union (prog32 ~lo:0 ~hi:2) (prog32 ~lo:6 ~hi:10))
          && P.equal
               (P.diff (p32 [ 0; 2; 4; 6; 8 ]) (p32 [ 0; 4; 8 ]))
               (p32 [ 2; 6 ])));

    pin "PCS-03" "the exact disjoint union: two case targets stay two pieces"
      (fun () ->
        let a = prog32 ~lo:0 ~hi:2 and b = prog32 ~lo:6 ~hi:10 in
        let u = P.union a b in
        check "PCS-03"
          (List.length (P.to_list u) = 2
          && P.equal u (P.join a b)
          && P.equal (p32 [ 0; 1; 2; 6; 7; 8; 9; 10 ]) u
          && P.cardinality u = card32 8));

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

    pin "PCS-07"
      "the exact mixed-step meet: {10,12,14,16,18} ∩ {16..19} = {16,18}"
      (fun () ->
        let a =
          P.of_progression
            (Clp.of_list ~width:32 (List.map w32 [ 10; 12; 14; 16; 18 ])) in
        let b =
          P.of_progression
            (Clp.of_list ~width:32 (List.map w32 [ 16; 17; 18; 19 ])) in
        let m = P.meet a b in
        check "PCS-07"
          (P.cardinality m = card32 2
          && P.elem (w32 16) m && P.elem (w32 18) m
          && not_mem_all m (List.map w32 [ 10; 12; 14; 17; 19 ])
          && P.equal m (p32 [ 16; 18 ])));

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

    pin "PCS-09"
      "the piece differential: binops sound and meet/diff exact on small \
       operands (200 random trials)"
      (fun () ->
        Random.init 20260925;
        let failures = ref 0 in
        let fail msg =
          incr failures;
          if !failures <= 10 then Printf.eprintf "PCS-09 FAIL: %s\n%!" msg
        in
        let show_clp p = Format.asprintf "%a" Clp.pp p in
        let rand_clp w =
          let step = Cbat_word.of_int ~width:w (1 + Random.int 3) in
          let c = 1 + Random.int 6 in
          let cardn = Cbat_word.of_int ~width:(w + 1) c in
          let base =
            Cbat_word.of_int ~width:w
              (Random.bits () land ((1 lsl Stdlib.(min w 20)) - 1)) in
          Clp.create base ~step ~cardn in
        for _ = 1 to 200 do
          let w = [| 4; 8 |].(Random.int 2) in
          let p1 = rand_clp w and p2 = rand_clp w in
          let a = P.of_progression p1 and b = P.of_progression p2 in
          let xa = Clp.iter p1 and xb = Clp.iter p2 in
          let ops =
            [ ("add", P.add, Cbat_word.add); ("sub", P.sub, Cbat_word.sub);
              ("mul", P.mul, Cbat_word.mul); ("logand", P.logand, Cbat_word.logand);
              ("logor", P.logor, Cbat_word.logor); ("logxor", P.logxor, Cbat_word.logxor) ]
          in
          List.iter
            (fun (nm, f, wop) ->
              let got = f a b in
              List.iter
                (fun x ->
                  List.iter
                    (fun y ->
                      if not (P.elem (wop x y) got) then
                        fail
                          (Printf.sprintf "%s w=%d p1=%s p2=%s x=%s y=%s got=[%s]"
                             nm w (show_clp p1) (show_clp p2)
                             (Cbat_word.to_string x) (Cbat_word.to_string y)
                             (String.concat "; "
                                (List.map (fun q -> Format.asprintf "%a" Clp.pp q)
                                   (P.to_list got)))))
                    xb)
                xa)
            ops;
          let m = P.meet a b in
          List.iter
            (fun x ->
              if not (P.elem x m) then
                fail
                  (Printf.sprintf "meet w=%d p1=%s p2=%s x=%s" w
                     (show_clp p1) (show_clp p2) (Cbat_word.to_string x)))
            (List.filter (fun x -> P.elem x b) xa);
          let d = P.diff a b in
          let exact_a =
            (not (Clp.is_circular p1)) && (not (Clp.is_infinite p1))
            && not (Clp.is_wrapped p1) in
          List.iter
            (fun x ->
              if P.elem x b then (
                if exact_a && P.elem x d then
                  fail
                    (Printf.sprintf "diff-extra w=%d p1=%s p2=%s x=%s" w
                       (show_clp p1) (show_clp p2) (Cbat_word.to_string x)))
              else if not (P.elem x d) then
                fail
                  (Printf.sprintf "diff-missing w=%d p1=%s p2=%s x=%s" w
                     (show_clp p1) (show_clp p2) (Cbat_word.to_string x)))
            xa
        done;
        check "PCS-09" (!failures = 0));

    pin "PCS-10"
      "the wrapped class: distributed add keeps every sum, the interleaved \
       union stays two pieces, and no canonical piece wraps"
      (fun () ->
        let w4 = Cbat_word.of_int ~width:4 in
        let p2 =
          Clp.create (w4 12) ~step:(w4 3) ~cardn:(Cbat_word.of_int ~width:5 5) in
        let a = P.union (P.of_progression (Clp.create (w4 0))) (P.of_progression p2) in
        let got = P.add a (P.of_progression p2) in
        let sums_ok =
          List.for_all (fun x ->
              List.for_all (fun y -> P.elem (Cbat_word.add x y) got)
                (P.elements (P.of_progression p2)))
            (P.elements a) in
        let w8 = Cbat_word.of_int ~width:8 in
        let far =
          P.union (P.singleton (w8 0xF8)) (P.singleton (w8 0)) in
        check "PCS-10"
          (sums_ok
          && P.elem (w4 0) got
          (* 8 + 8 wraps the modulus *)
          && P.elem (Cbat_word.add (w4 8) (w4 8)) got
          && List.length (P.to_list far) = 2
          && P.elem (w8 0) far && P.elem (w8 0xF8) far
          && List.for_all
               (fun ps ->
                 List.for_all (fun q -> not (Clp.is_wrapped q)) (P.to_list ps))
               [ got; far; a ]));
  ]

let () = run "pieces" tests
