(* Cbat_clp.Pieces pins: the canonical progression union.  One Alcotest
   group per pin; each pin builds its own fixture, so no state crosses
   pins. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common

module P = Clp.Pieces
module Ex = Clp.Exact

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
      "the widening pairing: the overlapping couple widens, an unmatched \
       piece stays its own atom, a top couple collapses"
      (fun () ->
        let a = p32 [ 0; 2; 4 ] in
        let b = p32 [ 0; 2; 4; 6; 8 ] in
        let w = P.widen_join a b in
        let l =
          P.widen_join (p32 [ 0; 1; 2; 10; 11; 12 ]) (p32 [ 0; 1; 2 ]) in
        let t = P.widen_join (P.top 32) (p32 [ 0; 1; 2 ]) in
        check "PCS-05"
          (P.elem (w32 6) w && P.elem (w32 100) w && P.is_ascending w
          && List.length (P.to_list l) = 2
          && (not (P.elem (w32 5) l)) && P.elem (w32 12) l
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
      "the overlap pairing: the old grid pairs with the first overlapping \
       incoming piece and the disjoint excess is its own atom (no hull \
       into the pair)"
      (fun () ->
        let old = prog32 ~lo:10 ~hi:100 in
        let incoming = P.union (prog32 ~lo:10 ~hi:20) (prog32 ~lo:40 ~hi:110) in
        let widened = P.widen_join old incoming in
        check "PCS-09.widen"
          (P.max_elem widened = Some (w32 110)
          && not (P.elem (w32 1000) widened));
        let extrapolated = P.extrapolate_steps ~steps:2 old incoming in
        check "PCS-09.extrapolate" (P.max_elem extrapolated = Some (w32 110)));

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




    pin "PCS-15"
      "the canonical merge: union/intersection/diff stay sound and canonical \
       over random progressions (the merge paths, no re-sort)"
      (fun () ->
        let st = Random.State.make [| 20261013 |] in
        let width = 8 in
        let size = 1 lsl width in
        let w = Cbat_word.of_int ~width in
        let rand_piece () =
          let base = w (Random.State.int st size) in
          let step = w (Random.State.int st 4) in
          let cardn =
            Cbat_word.of_int ~width:(width + 1) (1 + Random.State.int st 6)
          in
          P.of_progression (Clp.create ~width ~step ~cardn base) in
        let make () =
          List.fold_left
            (fun acc _ -> P.union acc (rand_piece ()))
            (P.bottom width)
            (List.init (1 + Random.State.int st 4) Fun.id) in
        let render p =
          String.concat " | "
            (List.map (Format.asprintf "%a" Clp.pp) (P.to_list p)) in
        let why_canonical p =
          let ls = P.to_list p in
          let rec mono = function
            | x :: (y :: _ as rest) -> (
              match Clp.min_elem x, Clp.min_elem y with
              | Some mx, Some my -> Cbat_word.compare mx my <= 0 && mono rest
              | _ -> false)
            | _ -> true in
          if not (mono ls) then Some "min-order"
          else if
            not
              (List.for_all
                 (fun q -> (not (Clp.is_bottom q)) && not (Clp.is_wrapped q))
                 ls)
          then Some "shape"
          else None in
        let sound p req =
          List.for_all
            (fun x -> not (req x) || P.elem (w x) p)
            (List.init size Fun.id) in
        let fail = ref None in
        let note what op a b r =
          if !fail = None then
            fail :=
              Some
                (Printf.sprintf "%s %s: a=%s b=%s r=%s" what op (render a)
                   (render b) (render r)) in
        for _ = 1 to 200 do
          let a = make () and b = make () in
          let va = Array.init size (fun x -> P.elem (w x) a) in
          let vb = Array.init size (fun x -> P.elem (w x) b) in
          let u = P.union a b
          and i = P.intersection a b
          and d = P.diff a b in
          (match why_canonical u with
          | Some w -> note ("canonical:" ^ w) "union" a b u
          | None -> ());
          (match why_canonical i with
          | Some w -> note ("canonical:" ^ w) "intersection" a b i
          | None -> ());
          (match why_canonical d with
          | Some w -> note ("canonical:" ^ w) "diff" a b d
          | None -> ());
          if not (sound u (fun x -> va.(x) || vb.(x))) then
            note "sound" "union" a b u;
          if not (sound i (fun x -> va.(x) && vb.(x))) then
            note "sound" "intersection" a b i;
          if not (sound d (fun x -> va.(x) && not vb.(x))) then
            note "sound" "diff" a b d
        done;
        match !fail with
        | None -> check "PCS-15" true
        | Some m -> Alcotest.failf "PCS-15: %s" m);

    pin "PCS-16"
      "the union merge is a linear merge: disjoint spans keep every piece, \
       operand order does not matter, and re-union is idempotent"
      (fun () ->
        let a = P.union (prog32 ~lo:0 ~hi:2) (prog32 ~lo:6 ~hi:8) in
        let b = P.union (prog32 ~lo:10 ~hi:12) (prog32 ~lo:16 ~hi:18) in
        let u = P.union a b in
        check "PCS-16"
          (P.equal u (P.union b a)
          && List.length (P.to_list u) = 4
          && P.equal u (P.union u a)
          && P.equal u (P.union u b)));

    pin "PCS-17"
      "exactness survives: a nine-element five-run set stays exactly its \
       elements through union, intersection, diff and to_pieces (no hull, \
       no cap)"
      (fun () ->
        let w8 = Cbat_word.of_int ~width:8 in
        let nums v = List.map Cbat_word.to_int_exn (Ex.elements v) in
        let sorted = List.sort Stdlib.compare in
        let bshow l = String.concat ";" (List.map string_of_int l) in
        let card v = Cbat_word.to_int_exn (Ex.cardinality v) in
        let runs v =
          List.concat_map (fun p -> Clp.iter p) (Ex.to_pieces v)
          |> List.map Cbat_word.to_int_exn |> sorted in
        (* Elements and raw runs must both be exactly [want] (same order),
           cardinality [List.length want], in [pieces] runs. *)
        let require what v want pieces =
          let got = sorted (nums v) in
          let raw = runs v in
          if
            got <> want || raw <> want
            || card v <> List.length want
            || List.length (Ex.to_pieces v) <> pieces
          then
            Alcotest.failf
              "PCS-17.%s: els=[%s] raw=[%s] card=%d pieces=%d want [%s] in \
               %d pieces"
              what (bshow got) (bshow raw) (card v)
              (List.length (Ex.to_pieces v)) (bshow want) pieces in
        let s =
          Ex.of_list ~width:8
            (List.map w8 [ 1; 2; 10; 11; 20; 21; 30; 31; 50 ]) in
        require "base" s [ 1; 2; 10; 11; 20; 21; 30; 31; 50 ] 5;
        let t =
          Ex.of_list ~width:8
            (List.map w8 [ 2; 3; 4; 10; 11; 12; 99 ]) in
        require "union" (Ex.union s t)
          [ 1; 2; 3; 4; 10; 11; 12; 20; 21; 30; 31; 50; 99 ] 5;
        require "intersection" (Ex.intersection s t) [ 2; 10; 11 ] 2;
        require "diff" (Ex.diff s t) [ 1; 20; 21; 30; 31; 50 ] 3);

    pin "PCS-18"
      "a 10x10 element product is still exact: the cardinality is the \
       concrete product count and every product is present"
      (fun () ->
        let width = 16 in
        let w = Cbat_word.of_int ~width in
        let a_els = [ 2; 3; 5; 7; 11; 13; 17; 19; 23; 29 ] in
        let b_els = [ 31; 37; 41; 43; 47; 53; 59; 61; 67; 71 ] in
        let a = Ex.of_list ~width (List.map w a_els) in
        let b = Ex.of_list ~width (List.map w b_els) in
        let concrete =
          List.concat_map
            (fun x -> List.map (fun y -> Cbat_word.mul (w x) (w y)) b_els)
            a_els
          |> List.sort_uniq Cbat_word.compare in
        let r = Ex.mul a b in
        let r_els = List.sort Cbat_word.compare (Ex.elements r) in
        let card = Cbat_word.to_int_exn (Ex.cardinality r) in
        let missing = List.filter (fun p -> not (Ex.elem p r)) concrete in
        let extra =
          List.filter
            (fun p -> not (List.exists (fun q -> Cbat_word.equal q p) concrete))
            r_els in
        if
          List.length concrete <> 100 || card <> 100
          || List.length r_els <> 100 || missing <> [] || extra <> []
        then
          Alcotest.failf
            "PCS-18: concrete=%d card=%d elements=%d missing=%d extra=%d"
            (List.length concrete) card (List.length r_els) (List.length missing)
            (List.length extra);
        check "PCS-18" true);

    pin "PCS-19"
      "the nearest pairing: correspondences pair by overlap and by the \
       smaller gap, and atoms without a counterpart stay their own pieces \
       (rank pairing would hull across the shift)"
      (fun () ->
        (* A one-piece shift: rank pairs (0..10, 20..30) and (20..30,
           40..50); the sweep pairs the equal middle pieces and carries
           the shifted ends. *)
        let shifted =
          P.widen_join
            (P.union (prog32 ~lo:0 ~hi:10) (prog32 ~lo:20 ~hi:30))
            (P.union (prog32 ~lo:20 ~hi:30) (prog32 ~lo:40 ~hi:50)) in
        check "PCS-19.shift"
          (List.length (P.to_list shifted) = 3
          && (not (P.elem (w32 15) shifted))
          && P.elem (w32 5) shifted && P.elem (w32 25) shifted
          && P.elem (w32 45) shifted);
        (* The nearer couple wins: {20..30} is closer to {35..45} than
           {0..10} is, so {0..10} carries. *)
        let nearest =
          P.widen_join
            (P.union (prog32 ~lo:0 ~hi:10) (prog32 ~lo:35 ~hi:45))
            (prog32 ~lo:20 ~hi:30) in
        check "PCS-19.nearest"
          (List.length (P.to_list nearest) = 2
          && P.elem (w32 5) nearest && P.elem (w32 40) nearest
          && not (P.elem (w32 15) nearest)));

  ]

let () = run "pieces" tests
