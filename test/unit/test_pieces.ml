(* Cbat_clp.Pieces pins: the canonical progression union.  One Alcotest
   group per pin; each pin builds its own fixture, so no state crosses
   pins. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common

(* The progression layer itself, not [Common]'s piece-union view. *)
module Clp = Cbat_clp
module P = Clp.Pieces
module Ex = Clp.Exact

(* Interval builder: the progression [lo, hi] step 1 at width 32. *)
let int32 ~lo ~hi =
  Clp.create ~width:32 ~step:(w32 1)
    ~cardn:(Cbat_word.of_int ~width:33 (hi - lo + 1)) (w32 lo)

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
               (P.of_arcs
                  (Clp.arcs ~width:32 ~step:(w32 2)
                     ~cardn:(Cbat_word.of_int ~width:33 3) (w32 0)))
          && List.length
               (P.to_list (P.union (p32 [ 0; 1; 2; 3; 4 ]) (P.singleton (w32 2))))
             = 1
          && List.length
               (P.to_list (P.union (p32 [ 0; 1; 2 ]) (p32 [ 3; 4; 5 ])))
             = 1
          && P.elem (w32 5) (P.union (p32 [ 0; 1; 2 ]) (p32 [ 3; 4; 5 ]))));





    pin "PCS-04"
      "the budget: a union of at most max_pieces pieces keeps every piece, \
       whatever their size; a larger one is its single hull piece, sound"
      (fun () ->
        let a = P.singleton (w32 0) in
        let b = P.of_progression (int32 ~lo:10 ~hi:20) in
        let c = P.of_progression (int32 ~lo:100 ~hi:110) in
        let d = P.of_progression (int32 ~lo:1000 ~hi:1010) in
        let e = P.of_progression (int32 ~lo:10000 ~hi:10100) in
        let u = P.union (P.union (P.union (P.union a b) c) d) e in
        check "PCS-04.within"
          (List.length (P.to_list u) = 5
          && mem_all u (List.map w32 [ 0; 10; 20; 100; 110; 1000; 1010; 10000; 10100 ])
          && not_mem_all u (List.map w32 [ 5; 50; 500; 5000 ]));
        let runs n = List.init n (fun i -> int32 ~lo:(i * 100) ~hi:((i * 100) + 2)) in
        check "PCS-04.boundary"
          (List.length (P.to_list (P.of_progressions (runs 64))) = 64);
        let many = P.of_progressions (runs 65) in
        check "PCS-04.over"
          (List.length (P.to_list many) = 1
          && mem_all many
               (List.concat_map (fun i -> List.map w32 [ i * 100; (i * 100) + 2 ])
                  (List.init 65 Fun.id))));

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
      "growth across incoming pieces widens and extrapolates the old range"
      (fun () ->
        let old = prog32 ~lo:10 ~hi:100 in
        let incoming = P.union (prog32 ~lo:10 ~hi:20) (prog32 ~lo:40 ~hi:110) in
        let widened = P.widen_join old incoming in
        check "PCS-09.widen"
          (P.max_elem widened = Some (Cbat_word.ones 32)
          && P.elem (w32 1000) widened);
        let extrapolated = P.extrapolate_steps ~steps:2 old incoming in
        check "PCS-09.extrapolate" (P.max_elem extrapolated = Some (w32 130)));

    pin "PCS-26" "widening overlapping translated iterates stabilizes" (fun () ->
        let rec converge n old =
          let incoming = P.translate old (w32 10) in
          let next = P.widen_join old incoming in
          check "PCS-26.old" (P.precedes old next);
          check "PCS-26.incoming" (P.precedes incoming next);
          if P.equal next old then true
          else n > 0 && converge (n - 1) next in
        check "PCS-26.converges" (converge 5 (prog32 ~lo:10 ~hi:100)));

    pin "PCS-10" "large strided meets retain their shared grid"
      (fun () ->
        List.iter (fun width ->
          let w = Cbat_word.of_int ~width in
          let prog base step count = P.of_arcs
            (Clp.arcs ~width ~step:(w step)
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
          let prog base step count = P.of_arcs
            (Clp.arcs ~width ~step:(scaled step)
               ~cardn:(Cbat_word.of_int ~width:(width + 1) count) (scaled base)) in
          let a = P.union (prog 59 10 20) (prog 7 1 11) in
          let b = Clp.interval ~width (w 0) (scaled 59) in
          check "PCS-11.disjoint" (List.length (P.to_list a) = 2);
          check "PCS-11.order" (not (P.precedes a b));
          check "PCS-11.extrapolate"
            (P.elem (scaled 69) (P.extrapolate_steps ~steps:2 a b))) [8;16;32;64]);

    pin "PCS-12" "subset checks each arc after rebasing"
      (fun () ->
        let w = Cbat_word.of_int ~width:8 in
        let a = Clp.interval ~width:8 (w 200) (w 100) in
        let b = Clp.interval ~width:8 (w 50) (w 220) in
        check "PCS-12" (not (P.precedes a b));
        let strided step count base =
          P.of_arcs
            (Clp.arcs ~width:8 ~step:(w step)
               ~cardn:(Cbat_word.of_int ~width:9 count) (w base)) in
        let sparse = strided 80 3 200 in
        check "PCS-12.sparse" (P.precedes sparse (Clp.interval ~width:8 (w 0) (w 220)));
        let misaligned = strided 6 3 252 in
        let grid = strided 3 85 0 in
        check "PCS-12.alignment" (not (P.precedes misaligned grid));
        let ray =
          P.of_progression (Clp.create_descending ~width:8 ~base:(w 252) ~step:(w 3)) in
        check "PCS-12.ray" (not (P.precedes misaligned ray)));

    pin "PCS-13" "directional membership, enumeration and complement agree"
      (fun () ->
        List.iter (fun width ->
          let w = Cbat_word.of_int ~width in
          let d = Clp.create_descending ~width ~base:(w 9) ~step:(w 5) in
          let a = Clp.create_ascending ~width ~base:(w 9) ~step:(w 5) in
          check "PCS-13.desc" (Clp.elem (w 4) d && not (Clp.elem (w 14) d));
          check "PCS-13.asc" (Clp.elem (w 14) a && not (Clp.elem (w 4) a));
          check "PCS-13.iter" (List.sort Cbat_word.compare (Clp.iter d) = [w 4;w 9]);
          let flipped = P.lnot (P.of_progression d) in
          check "PCS-13.lnot" (P.elem (Cbat_word.lnot (w 4)) flipped);
          check "PCS-13.meet"
            (P.equal (P.intersection (P.of_progression d) (P.singleton (w 4))) (P.singleton (w 4))))
          [8;16;32;64]);



    pin "PCS-08"
      "the parts exactness: a straddling lshift keeps the overshift and the \
       capped exact pieces apart"
      (fun () ->
        let a = P.singleton (w64 16) in
        let amt =
          Clp.interval ~width:64 (w64 8) (w64 70) in
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
          let t = P.translate (P.of_progression p) i in
          List.for_all (fun x -> P.elem (Cbat_word.add x i) t) (Clp.iter p)
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
        let shifted = P.add (P.of_progression full) (P.singleton (w64 8)) in
        check "PCS-14.full"
          (List.for_all (fun x -> P.elem (w64 x) shifted) [ 0; 8; -8; -16 ]);
        let ray = Clp.create_ascending ~width:64 ~base:(w64 (-0x58)) ~step:(w64 8) in
        let up = P.translate (P.of_progression ray) (w64 8) in
        check "PCS-14.ray" (P.elem (w64 0) up && P.elem (w64 (-0x50)) up));




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
          P.of_arcs (Clp.arcs ~width ~step ~cardn base) in
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
                 (fun q -> not (Clp.is_bottom q))
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

    pin "PCS-20"
      "widening from bottom is the new iterate, not top (the piece union and the landmark step)"
      (fun () ->
        let five = P.singleton (w32 5) in
        let w = P.widen_join (P.bottom 32) five in
        check "PCS-20.widen" (P.equal w five && not (P.is_top w));
        let e = P.extrapolate_steps ~steps:2 (P.bottom 32) five in
        check "PCS-20.extrapolate" (P.equal e five && not (P.is_top e)));

    pin "PCS-21"
      "the tier conversions equal the list builders: an exact \
       set's pieces and a piece union's elements equal what Pieces.of_list \
       and Exact.of_list build, across runs, scatter and a cap overflow"
      (fun () ->
        Random.init 20261015;
        let sets width =
          let top = (1 lsl width) - 1 in
          let wd = Cbat_word.of_int ~width in
          let run lo step n = List.init n (fun i -> lo + (i * step)) in
          let scattered n = List.init n (fun _ -> Random.int (min (top + 1) ((1 lsl 30) - 1))) in
          List.map (List.map wd)
            [ [ 0 ]; [ top ]; [ 0; top ]; run 3 1 12; run 0 4 9;
              run 1 2 5 @ run 40 3 4 @ [ 90; 91; 92 ];
              (* separated runs *)
              List.concat_map (fun k -> [ k * 20; (k * 20) + 7 ]) (List.init 12 Fun.id);
              scattered 6; scattered 16; scattered 40 ]
        in
        let random_sets width =
          let top = (1 lsl width) - 1 in
          List.init 100 (fun _ ->
              let n = 2 + Random.int 220 in
              let span = 1 + Random.int top in
              List.init n (fun _ -> Cbat_word.of_int ~width (Random.int (span + 1))))
        in
        List.iter
          (fun width ->
            List.iter
              (fun l ->
                let e = Ex.of_list ~width l in
                let slow = P.of_list ~width (Ex.elements e) in
                check "PCS-21.pieces" (P.equal (Ex.pieces e) slow);
                check "PCS-21.of_pieces"
                  (Ex.equal (Ex.of_pieces ~width slow)
                     (Ex.of_list ~width (P.elements slow))))
              (sets width @ random_sets width))
          [ 8; 16 ];
        let interleaved =
          P.union
            (P.of_arcs
               (Clp.arcs ~width:32 ~step:(w32 4)
                  ~cardn:(Cbat_word.of_int ~width:33 3) (w32 0)))
            (P.singleton (w32 2)) in
        let exact = Ex.of_pieces ~width:32 interleaved in
        check "PCS-21.interleaved"
          (Ex.equal exact (Ex.of_list ~width:32 (List.map w32 [ 0; 2; 4; 8 ]))
          && Ex.elem (w32 2) exact);
        let overflow =
          Ex.of_list ~width:32
            (List.concat_map
               (fun i -> List.map w32 [ i * 100; (i * 100) + 1; (i * 100) + 2 ])
               (List.init 65 Fun.id)) in
        check "PCS-21.overflow"
          (List.length (Ex.to_pieces overflow) = 65
          && P.equal (Ex.pieces overflow)
               (P.of_list ~width:32 (Ex.elements overflow))
          && List.length (P.to_list (Ex.pieces overflow)) = 1));

    pin "PCS-22"
      "a producer's output is canonical when a late piece overlaps an \
       earlier piece hidden behind an interleaved tail"
      (fun () ->
        let step10 n base =
          P.of_arcs
            (Clp.arcs ~width:32 ~step:(w32 10)
               ~cardn:(Cbat_word.of_int ~width:33 n) (w32 base)) in
        let a =
          P.union (P.union (P.singleton (w32 0)) (P.singleton (w32 1)))
            (P.singleton (w32 10)) in
        let b = step10 2 0 in
        let sum = P.add a b in
        let expected =
          P.union (P.union (step10 2 0) (step10 2 1)) (step10 2 10) in
        let disjoint =
          let rec go = function
            | x :: (y :: _ as rest) ->
              not (P.overlap (P.of_progressions [ x ]) (P.of_progressions [ y ]))
              && go rest
            | _ -> true in
          go (P.to_list sum) in
        check "PCS-22.equal" (P.equal sum expected);
        check "PCS-22.disjoint" disjoint;
        check "PCS-22.count"
          (Cbat_word.equal (P.cardinality sum) (P.cardinality expected)));

    pin "PCS-23"
      "difference removes every element of interleaved subtrahend pieces"
      (fun () ->
        let step10 base =
          P.of_arcs
            (Clp.arcs ~width:32 ~step:(w32 10)
               ~cardn:(Cbat_word.of_int ~width:33 2) (w32 base)) in
        let removed = P.union (step10 0) (step10 1) in
        let d = P.diff (prog32 ~lo:0 ~hi:100) removed in
        check "PCS-23.removed"
          (not_mem_all d (List.map w32 [ 0; 1; 10; 11 ]));
        check "PCS-23.kept" (mem_all d (List.map w32 [ 2; 9; 12; 100 ])));

    pin "PCS-24"
      "a multi-piece XOR equals the union of its single-piece pair XORs: \
       the operands' shared complements and facts change nothing"
      (fun () ->
        let step k lo n =
          P.of_arcs
            (Clp.arcs ~width:32 ~step:(w32 k)
               ~cardn:(Cbat_word.of_int ~width:33 n) (w32 lo)) in
        let a = P.union (step 4 8 5) (P.union (step 1 100 3) (p32 [ 1000 ])) in
        let b = P.union (step 6 3 4) (P.union (prog32 ~lo:64 ~hi:70) (p32 [ 5 ])) in
        let pair pa pb =
          P.logxor (P.of_progressions [ pa ]) (P.of_progressions [ pb ]) in
        let expected =
          List.fold_left
            (fun acc pa ->
               List.fold_left (fun acc pb -> P.union acc (pair pa pb)) acc
                 (P.to_list b))
            (P.bottom 32) (P.to_list a) in
        check "PCS-24.pieces"
          (List.length (P.to_list a) > 1 && List.length (P.to_list b) > 1);
        check "PCS-24.equal" (P.equal (P.logxor a b) expected));

    pin "PCS-25"
      "a union whose right pieces all sit inside the left value is the left \
       value itself, wherever the covering piece lies; a piece that adds an \
       element is not"
      (fun () ->
        let a = P.union (prog32 ~lo:0 ~hi:9) (prog32 ~lo:100 ~hi:200) in
        let inside = P.union (p32 [ 3; 4 ]) (p32 [ 150 ]) in
        check "PCS-25.inside" (P.union a inside == a);
        let grown = P.union a (p32 [ 150; 300 ]) in
        check "PCS-25.grown"
          (P.elem (w32 300) grown && P.elem (w32 150) grown
           && P.elem (w32 5) grown && not (P.elem (w32 50) grown)));

    pin "PCS-27"
      "the cached circular hull and extrema equal their recomputation from \
       the piece list, wrapped, capped, bottom and top values included"
      (fun () ->
        let recomputed_hull ps =
          match P.to_list ps with
          | [] -> []
          | p :: rest ->
            List.fold_left
              (fun acc q -> Cbat_clp_core.union_arcs acc [ q ]) [ p ] rest in
        let extreme f better ps =
          List.fold_left
            (fun acc p -> Cbat_word.keep_better ~better acc (f p))
            None (P.to_list ps) in
        let same_opt a b =
          match a, b with
          | None, None -> true
          | Some x, Some y -> Cbat_word.equal x y
          | _ -> false in
        let wrapped = Clp.interval ~width:32 (w32 0xFFFFFFF0) (w32 0x10) in
        let capped =
          P.of_progressions
            (List.init 65 (fun i -> int32 ~lo:(i * 100) ~hi:((i * 100) + 2))) in
        List.iteri
          (fun i ps ->
             let name = Printf.sprintf "PCS-27.%d" i in
             check (name ^ ".hull")
               (List.equal Clp.equal (P.to_list (P.circular_hull ps))
                  (recomputed_hull ps));
             check (name ^ ".idempotent")
               (P.circular_hull (P.circular_hull ps) == P.circular_hull ps);
             check (name ^ ".extrema")
               (same_opt (P.min_elem ps)
                  (extreme Clp.min_elem (Cbat_word.min_by ~signed:false) ps)
                && same_opt (P.max_elem ps)
                     (extreme Clp.max_elem (Cbat_word.max_by ~signed:false) ps)
                && same_opt (P.min_elem_signed ps)
                     (extreme Clp.min_elem_signed
                        (Cbat_word.min_by ~signed:true) ps)
                && same_opt (P.max_elem_signed ps)
                     (extreme Clp.max_elem_signed
                        (Cbat_word.max_by ~signed:true) ps)))
          [ P.bottom 32; P.top 32; P.singleton (w32 7); p32 [ 0; 1; 2; 6; 7; 8 ];
            P.union (prog32 ~lo:0 ~hi:9) (prog32 ~lo:100 ~hi:200); wrapped;
            P.union wrapped (p32 [ 0x7FFFFFF0; 0x80000010 ]); capped ]);

    pin "PCS-28"
      "add, sub and neg build their ascending result directly: it equals the \
       sorted, deduplicated image of the same per-pair results, over \
       multi-piece, wrapping, near-0/near-max, constant and over-budget \
       operands at widths 8, 32 and 64"
      (fun () ->
        let rs = Random.State.make [| 28; 2026 |] in
        let rnd n = Random.State.int rs n in
        let word width =
          let w k = Cbat_word.of_int ~width k in
          match rnd 4 with
          | 0 -> w (rnd 40)
          | 1 -> Cbat_word.neg (w (rnd 40))
          | 2 -> w (rnd (1 lsl (min width 29)))
          | _ ->
            Cbat_word.add
              (w (rnd (1 lsl (min width 29))))
              (Cbat_word.lshift (w (rnd 1000)) (w (max 0 (width - 12)))) in
        let piece width =
          if rnd 3 = 0 then Clp.singleton (word width)
          else
            let step = Cbat_word.of_int ~width (1 + rnd 6) in
            let cardn = Cbat_word.of_int ~width:(width + 1) (2 + rnd 12) in
            match Clp.arcs ~width ~step ~cardn (word width) with
            | [] -> Clp.singleton (word width)
            | l -> List.nth l (rnd (List.length l)) in
        let operand width =
          match rnd 8 with
          | 0 -> P.singleton (word width)
          | 6 | 7 ->
            (* Interleaving strides: offsets over a strided run. *)
            let stride = 2 + rnd 6 in
            let base = word width in
            let offs = List.init (1 + rnd 4) (fun _ -> rnd stride) in
            P.of_list ~width
              (List.sort_uniq Cbat_word.compare
                 (List.concat_map
                    (fun k ->
                       List.map
                         (fun o ->
                            Cbat_word.add base
                              (Cbat_word.of_int ~width (((k * stride) + o) land 255)))
                         offs)
                    (List.init (2 + rnd 20) Fun.id)))
          | 1 ->
            P.of_list ~width
              (List.sort_uniq Cbat_word.compare
                 (List.init (1 + rnd 90) (fun _ -> word width)))
          | _ ->
            List.fold_left
              (fun acc _ -> P.union acc (P.of_arcs [ piece width ]))
              (P.of_arcs [ piece width ])
              (List.init (rnd 6) Fun.id) in
        let image gen =
          P.of_progressions
            (List.sort_uniq P.compare_piece
               (List.filter (fun p -> not (Clp.is_bottom p)) (gen ()))) in
        let pairs a b f =
          List.concat_map
            (fun pa -> List.concat_map (fun pb -> f pa pb) (P.to_list b))
            (P.to_list a) in
        for i = 1 to 3000 do
          let width = [| 8; 32; 64 |].(i mod 3) in
          let a = operand width and b = operand width in
          check (Printf.sprintf "PCS-28.add.%d" i)
            (P.equal (P.add a b) (image (fun () -> pairs a b Cbat_clp_arith.add)));
          check (Printf.sprintf "PCS-28.sub.%d" i)
            (P.equal (P.sub a b) (image (fun () -> pairs a b Cbat_clp_arith.sub)));
          check (Printf.sprintf "PCS-28.neg.%d" i)
            (P.equal (P.neg a)
               (image (fun () ->
                    List.concat_map Cbat_clp_arith.neg (P.to_list a))))
        done);

  ]

let () = run "pieces" tests
