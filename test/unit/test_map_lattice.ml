(* Cbat_map_lattice (and the Mem axis-map) pins.  One Alcotest group per
   pin; each pin builds its own fixture, so no state crosses pins. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

(* The op_add fixture vocabulary: a 32/8 axis, keys from WordSets, and a
   point read that lands on a cell's lower bound. *)
let opadd_axis = { Mem.addr_width = 32; Mem.addressable_width = 8 }

let opadd_key_of ws =
  match Mem.Key.of_wordset ws with
  | [ k ] -> k
  | _ -> failwith "key"

let point c = opadd_key_of (Ws.singleton (w32 c))
let range lo hi = opadd_key_of (Ws.of_clp (Clp.interval ~width:32 (w32 lo) (w32 hi)))
let cell n = Mem.Val.create (Ws.singleton (w32 n)) LittleEndian
let read32 m c = Mem.Val.data (Mem.find (32, LittleEndian) m (point c))
let empty = Mem.top opadd_axis
let range_cell lo hi n = Mem.meet_add empty ~key:(range lo hi) ~data:(cell n)

(* The key namespace helpers: the origin a key carries, and a 64-bit cell. *)
let key_origin k = (Mem.Key.cell_key k).Cbat_landmarks.origin
let tests : unit Alcotest.test list =
  [
    pin "MAP-01" "ML1: add on bottom stays bottom"
      (fun () ->
        check "MAP-01" (Map.equal (Map.add Map.bottom ~key:0 ~data:1) Map.bottom));



    pin "MAP-03" "ML3: find on bottom/top returns bottom/top"
      (fun () ->
        check "MAP-03"
          (Map.find () Map.bottom 10 = IntLattice.bottom && Map.find () Map.top 10 = IntLattice.top));





    pin "MAP-06" "ML6: join_add/meet_add merge with the stored value"
      (fun () ->
        check "MAP-06"
          (let m = Map.join_add (Map.add Map.top ~key:5 ~data:3) ~key:5 ~data:10 in
           Map.find () m 5 = 10
           && Map.find () (Map.meet_add (Map.add Map.top ~key:5 ~data:10) ~key:5 ~data:3) 5 = 3));



    pin "MAP-08" "D2-4: Val.equal/precedes on idx-mismatched cells -> false (no assert)"
      (fun () ->
        let v32 = Mem.Val.create (Ws.of_list ~width:32 [ w32 1 ]) LittleEndian in
        let v64 = Mem.Val.create (Ws.of_list ~width:64 [ w64 1 ]) LittleEndian in
        let vbe = Mem.Val.create (Ws.of_list ~width:32 [ w32 1 ]) BigEndian in
        check "MAP-08"
          ((not (Mem.Val.equal v32 v64))
          && (not (Mem.Val.precedes v32 v64))
          && not (Mem.Val.equal v32 vbe)));









    pin "MAP-13" "D2-9: Mem.widen_join of non-preceding maps -> join fallback (no assert)"
      (fun () ->
        let m1 = mk_mem ~key:(Ws.singleton (w32 0)) ~data:(Ws.of_list ~width:32 [ w32 1; w32 2 ]) in
        let m2 = mk_mem ~key:(Ws.singleton (w32 0)) ~data:(Ws.of_list ~width:32 [ w32 3; w32 4 ]) in
        let mw = Mem.widen_join m1 m2 in
        check "MAP-13"
          (let v =
             Mem.find
               (Mem.Val.get_idx (Mem.Val.create (Ws.of_list ~width:32 [ w32 0 ]) LittleEndian))
               mw
               (key_of (Ws.singleton (w32 0)))
           in
           let d = Mem.Val.data v in
           Ws.elem (w32 1) d && Ws.elem (w32 2) d && Ws.elem (w32 3) d && Ws.elem (w32 4) d));



    pin "MAP-15"
      "opadd-a: join a key fully inside one node — interval_diff `two (low flank lo 10 = {1}, middle \
       lo 12 = {1,2}, high flank lo 19 = {1})"
      (fun () ->
        let m = range_cell 10 20 1 in
        let m = Mem.join_add m ~key:(range 12 18) ~data:(cell 2) in
        check "MAP-15"
          (Ws.equal (read32 m 10) (Ws.singleton (w32 1))
          && Ws.equal (read32 m 12) (Ws.of_list ~width:32 [ w32 1; w32 2 ])
          && Ws.equal (read32 m 19) (Ws.singleton (w32 1))
          && Ws.is_top (read32 m 11)
          && Ws.is_top (read32 m 9)
          && Ws.is_top (read32 m 21)));









    pin "MAP-20"
      "opadd-d1: a wrapped-interval WordSet fans per piece — both arcs carry the \
       fact (lo 0 = {7}, hi 0xFFFFFFF0 = {7}), the true interior 0x50 is top"
      (fun () ->
        let wrap_ws = Ws.of_clp (Clp.interval ~width:32 (w32 0xFFFFFFF0) (w32 0x0F)) in
        let m =
          Base.List.fold (Mem.Key.of_wordset wrap_ws) ~init:empty
            ~f:(fun m k -> Mem.meet_add m ~key:k ~data:(cell 7))
        in
        check "MAP-20"
          (Ws.equal (read32 m 0) (Ws.singleton (w32 7))
          && Ws.is_top (read32 m 0x50)
          && Ws.equal (read32 m 0xFFFFFFF0) (Ws.singleton (w32 7))));





    pin "MAP-23" "opadd-f: a 64-bit {5} meets a 32-bit {5} cell via meet_poly (widened to 64, no crash)"
      (fun () ->
        let m = range_cell 10 10 5 in
        let d64 = Mem.Val.create (Ws.singleton (w64 5)) LittleEndian in
        let m = Mem.meet_add m ~key:(point 10) ~data:d64 in
        check "MAP-23"
          (let v = Mem.Val.data (Mem.find (64, LittleEndian) m (point 10)) in
           Ws.equal v (Ws.singleton (w64 5))));



    pin "MAP-25"
      "ML8: a top-valued add stores no binding (absent reads top; the add is a remove)"
      (fun () ->
        let folded m =
          Map.fold m ~init:0 ~f:(fun ~key:_ ~data v -> v + data) in
        check "MAP-25"
          (folded (Map.add Map.top ~key:5 ~data:IntLattice.top) = 0
          && Map.find () (Map.add Map.top ~key:5 ~data:IntLattice.top) 5
             = IntLattice.top
          && folded (Map.add Map.top ~key:5 ~data:7) = 7
          && folded (Map.join_add Map.top ~key:5 ~data:IntLattice.top) = 0));

    (* The key namespace: a key carries the value's origin, and cells of
       different origins are disjoint. *)
    pin "MAP-26"
      "the key namespace: an origin-aware key round-trips (a stack word keys in \
       the Stack namespace, a plain out-of-band word on the absolute line) and two keys of the \
       same byte range but different origins do not overlap"
      (fun () ->
        let k_stack = key_of (Ws.stack_word_i64 (-8L)) in
        let k_abs = key_of (Ws.singleton (w64 (-8))) in
        check "MAP-26"
          (Option.equal Hike_origin.equal (key_origin k_stack) (Some Hike_origin.Stack)
          && Option.is_none (key_origin k_abs)
          && not (Mem.Key.overlap k_stack k_abs)));

    pin "MAP-27"
      "a write wider than the word is one cell per word: a 128-bit stack store \
       reads back exactly as two words (the code word keeps its origin) and as \
       one 128-bit value"
      (fun () ->
        Hike_origin.Regions.install [ (Hike_section.Text, 0x1000L, 0x1fffL) ];
        let fn = Ws.module_address 0x11F0L in
        Hike_origin.Regions.install [];
        let img = Ws.singleton (w64 0x11E0) in
        let v = Ws.concat fn img in
        let at off = key_of (Ws.stack_word_i64 off) in
        let m =
          Mem.add (Mem.top { Mem.addr_width = 64; addressable_width = 8 })
            ~key:(at (-0x38L)) ~data:(Mem.Val.create v LittleEndian) in
        let read bits off = Mem.Val.data (Mem.find (bits, LittleEndian) m (at off)) in
        check "MAP-27 (low word)" (Ws.equal (read 64 (-0x38L)) img);
        check "MAP-27 (high word, with its origin)"
          (Ws.equal (read 64 (-0x30L)) fn
           && Ws.origin (read 64 (-0x30L)) = Some (Ws.Origin.Rip Hike_section.Text));
        check "MAP-27 (the 128-bit read)" (Ws.equal (read 128 (-0x38L)) v));

    pin "MAP-28"
      "a strided read is the join of its grid points: every point a word cell \
       joins exactly; a point with no cell makes the read top"
      (fun () ->
        let at off = key_of (Ws.stack_word_i64 off) in
        let word off n m =
          Mem.add m ~key:(at off) ~data:(Mem.Val.create (Ws.singleton (w64 n)) LittleEndian) in
        let m =
          Mem.top { Mem.addr_width = 64; addressable_width = 8 }
          |> word (-0x38L) 1 |> word (-0x30L) 2 |> word (-0x28L) 3 in
        let grid lo n =
          key_of
            (Ws.add (Ws.stack_word_i64 lo)
               (Ws.of_list ~width:64 (List.init n (fun i -> w64 (8 * i))))) in
        let read k = Mem.Val.data (Mem.find (64, LittleEndian) m k) in
        check "MAP-28 (three cells)"
          (Ws.equal (read (grid (-0x38L) 3)) (Ws.of_list ~width:64 [ w64 1; w64 2; w64 3 ]));
        check "MAP-28 (a missing cell)" (Ws.is_top (read (grid (-0x38L) 4))));

    pin "MAP-29" "a read narrower than its cell is the bytes at the cell's start"
      (fun () ->
        let k = key_of (Ws.stack_word_i64 (-8L)) in
        let m =
          Mem.add (Mem.top { Mem.addr_width = 64; addressable_width = 8 }) ~key:k
            ~data:(Mem.Val.create (Ws.singleton (w64 0x1_0000_0002)) LittleEndian) in
        check "MAP-29"
          (Ws.equal (Mem.Val.data (Mem.find (32, LittleEndian) m k)) (Ws.singleton (w32 2))));

    pin "MAP-30"
      "a read that starts inside a wider cell extracts the bytes at its offset: the high dword \
       and byte 1 of a stored qword"
      (fun () ->
        let w8 = Cbat_word.of_int ~width:8 in
        let k = key_of (Ws.stack_word_i64 (-8L)) in
        let m =
          Mem.add (Mem.top { Mem.addr_width = 64; addressable_width = 8 }) ~key:k
            ~data:
              (Mem.Val.create (Ws.singleton (w64 0x1122334455667788)) LittleEndian) in
        let read bits off =
          Mem.Val.data
            (Mem.find (bits, LittleEndian) m (key_of (Ws.stack_word_i64 off))) in
        check "MAP-30.low" (Ws.equal (read 32 (-8L)) (Ws.singleton (w32 0x55667788)));
        check "MAP-30.high" (Ws.equal (read 32 (-4L)) (Ws.singleton (w32 0x11223344)));
        check "MAP-30.byte1" (Ws.equal (read 8 (-7L)) (Ws.singleton (w8 0x77)));
        check "MAP-30.byte7" (Ws.equal (read 8 (-1L)) (Ws.singleton (w8 0x11)));
        (* Big-endian: the offset selects the bytes the other way round. *)
        let mbe =
          Mem.add (Mem.top { Mem.addr_width = 64; addressable_width = 8 }) ~key:k
            ~data:
              (Mem.Val.create (Ws.singleton (w64 0x1122334455667788)) BigEndian) in
        let readbe off =
          Mem.Val.data
            (Mem.find (32, BigEndian) mbe (key_of (Ws.stack_word_i64 off))) in
        check "MAP-30.be-high" (Ws.equal (readbe (-8L)) (Ws.singleton (w32 0x11223344)));
        check "MAP-30.be-low" (Ws.equal (readbe (-4L)) (Ws.singleton (w32 0x55667788))));

    pin "MAP-31"
      "wrapped candidate windows deduplicate a spanning cell and keep the query's origin"
      (fun () ->
        let w8 = Cbat_word.of_int ~width:8 in
        let byte n = Mem.Val.create (Ws.singleton (w8 n)) LittleEndian in
        let read m k = Mem.Val.data (Mem.find (8, LittleEndian) m k) in
        (* The cell intersects both windows of a point query near zero. *)
        let spanning =
          Mem.meet_add empty ~key:(range 0 0xFFFFFFFF) ~data:(byte 0x11) in
        check "MAP-31.spanning"
          (Ws.equal (read spanning (point 0)) (Ws.singleton (w8 0x11)));
        let stored = Mem.add spanning ~key:(point 0) ~data:(byte 0x22) in
        check "MAP-31.store"
          (Ws.equal (read stored (point 0)) (Ws.singleton (w8 0x22)));
        let stack = key_of (Ws.stack_word_i64 0L) in
        let abs = key_of (Ws.singleton (w64 0)) in
        let m =
          Mem.top { Mem.addr_width = 64; addressable_width = 8 }
          |> fun m -> Mem.add m ~key:stack ~data:(byte 0x33)
          |> fun m -> Mem.add m ~key:abs ~data:(byte 0x44) in
        check "MAP-31.origin"
          (Ws.equal (read m stack) (Ws.singleton (w8 0x33))
          && Ws.equal (read m abs) (Ws.singleton (w8 0x44))));

    pin "MAP-32"
      "precedes compares a cell of the right map against the left map's gaps and cells"
      (fun () ->
        let w8 = Cbat_word.of_int ~width:8 in
        let byte n = Mem.Val.create (Ws.singleton (w8 n)) LittleEndian in
        let top = Mem.top { Mem.addr_width = 64; addressable_width = 8 } in
        let fact = Mem.add top ~key:(point 0) ~data:(byte 0x11) in
        let other = Mem.add top ~key:(point 0) ~data:(byte 0x22) in
        check "MAP-32.top-vs-fact" (not (Mem.precedes top fact));
        check "MAP-32.fact-vs-top" (Mem.precedes fact top);
        check "MAP-32.fact-vs-other" (not (Mem.precedes fact other)));


    pin "MAP-33"
      "join and meet of a memory with itself return it physically"
      (fun () ->
        let w8 = Cbat_word.of_int ~width:8 in
        let byte n = Mem.Val.create (Ws.singleton (w8 n)) LittleEndian in
        let top = Mem.top { Mem.addr_width = 64; addressable_width = 8 } in
        let m = Mem.add top ~key:(point 0) ~data:(byte 0x11) in
        check "MAP-33.join" (Mem.join m m == m);
        check "MAP-33.meet" (Mem.meet m m == m);
        let other = Mem.add top ~key:(point 0) ~data:(byte 0x22) in
        check "MAP-33.distinct" (Mem.join m other != m));





    pin "MAP-34"
      "equality and inclusion read an explicit top binding as an absent key, find a difference at any position, and a write that changes nothing keeps the wrapper"
      (fun () ->
        let widened = Map.widen_join (Map.add Map.top ~key:5 ~data:3)
            (Map.add Map.top ~key:5 ~data:4) in
        check "MAP-34.explicit-top-eq"
          (Map.equal widened Map.top && Map.equal Map.top widened);
        check "MAP-34.explicit-top-precedes"
          (Map.precedes widened Map.top && Map.precedes Map.top widened);
        let many v_last =
          List.fold_left (fun m k -> Map.add m ~key:k ~data:1)
            Map.top (List.init 20 Fun.id)
          |> fun m -> Map.add m ~key:99 ~data:v_last in
        check "MAP-34.differs-last" (not (Map.equal (many 1) (many 2)));
        check "MAP-34.differs-first"
          (not (Map.equal (Map.add (many 1) ~key:0 ~data:7) (many 1)));
        check "MAP-34.same" (Map.equal (many 1) (many 1));
        let m = Map.add Map.top ~key:5 ~data:3 in
        check "MAP-34.add-same" (Map.add m ~key:5 ~data:3 == m);
        check "MAP-34.add-top-absent" (Map.add m ~key:6 ~data:IntLattice.top == m);
        check "MAP-34.keep-all" (Map.filter_keys m ~f:(fun _ -> true) == m);
        check "MAP-34.drop" (not (Map.filter_keys m ~f:(fun _ -> false) == m));
        let e = AI.add_word AI.top ~key:(int_ret 0) ~data:(Ws.singleton (w64 1)) in
        let d = Ws.singleton (w64 2) in
        let e = AI.add_word e ~key:(callee_saved 0) ~data:d in
        check "MAP-34.ai-same-write" (AI.add_word e ~key:(callee_saved 0) ~data:d == e);
        check "MAP-34.ai-join-self" (AI.join e e == e));

    pin "MAP-35"
      "memory joins split unequal overlapping ranges and revisit their remaining tails"
      (fun () ->
        let byte n = Mem.Val.create (Ws.singleton (Cbat_word.of_int ~width:8 n)) LittleEndian in
        let facts rows =
          List.fold_left (fun m (lo, hi, n) ->
              Mem.meet_add m ~key:(range lo hi) ~data:(byte n)) empty rows in
        let read m i = Mem.Val.data (Mem.find (8, LittleEndian) m (point i)) in
        let check_join label left right =
          let joined = Mem.join left right in
          let rec disjoint = function
            | [] -> true
            | (k, _) :: rest ->
              List.for_all (fun (q, _) -> not (Mem.Key.overlap k q)) rest
              && disjoint rest in
          check (label ^ ".disjoint") (disjoint (Mem.cells joined));
          for i = 0 to 12 do
            check (Printf.sprintf "%s.read.%d" label i)
              (Ws.equal (read joined i) (Ws.join (read left i) (read right i)))
          done in
        let coarse = facts [ 0, 8, 1 ] in
        let split = facts [ 0, 7, 1; 8, 8, 2 ] in
        check_join "MAP-35.coarse-left" coarse split;
        check_join "MAP-35.coarse-right" split coarse;
        let whole = facts [ 0, 12, 1 ] in
        let pieces = facts [ 0, 2, 2; 5, 7, 3; 10, 12, 4 ] in
        check_join "MAP-35.tails-left" whole pieces;
        check_join "MAP-35.tails-right" pieces whole;
        for a = 0 to 4 do
          for b = a to 4 do
            for c = 0 to 4 do
              for d = c to 4 do
                check_join "MAP-35.bounds" (facts [ a, b, 1 ]) (facts [ c, d, 2 ])
              done
            done
          done
        done);


    pin "MAP-36"
      "a strided key split by a meet, a diff or a gap keeps its own grid: pieces start and end on \
       grid points and keep the stride; a gap holding no grid point vanishes"
      (fun () ->
        let grid lo step n =
          opadd_key_of
            (Ws.of_clp
               (Clp.create ~width:32 ~step:(w32 step) ~cardn:(w32 n) (w32 lo))) in
        let facts keys =
          List.fold_left (fun m k -> Mem.meet_add m ~key:k ~data:(cell 1)) empty keys in
        let shape m =
          List.map (fun (k, _) ->
              let d = Mem.Key.cell_key k in
              Int64.to_int d.Cbat_landmarks.lo_value,
              Int64.to_int d.Cbat_landmarks.hi_value,
              d.Cbat_landmarks.stride) (Mem.cells m) in
        check "MAP-36.same-grid-tail"
          (shape (Mem.meet (facts [ grid 0 4 11 ]) (facts [ grid 0 4 3 ]))
           = [ 0, 8, 4; 12, 40, 4 ]);
        check "MAP-36.off-grid-split"
          (shape (Mem.meet (facts [ grid 0 4 11 ]) (facts [ range 5 6 ]))
           = [ 0, 4, 4; 5, 6, 1; 8, 40, 4 ]);
        let add m k = Mem.meet_add m ~key:k ~data:(cell 1) in
        check "MAP-36.diff-remainders"
          (shape (add (facts [ grid 0 4 11 ]) (range 12 13))
           = [ 0, 8, 4; 12, 13, 1; 16, 40, 4 ]);
        check "MAP-36.gap-after-cell"
          (shape (add (facts [ range 5 6 ]) (grid 0 4 11))
           = [ 0, 4, 4; 5, 6, 1; 8, 40, 4 ]);
        check "MAP-36.gap-between-grid-points"
          (shape (add (facts [ range 1 3; range 5 7 ]) (grid 0 8 3))
           = [ 0, 0, 8; 1, 3, 1; 5, 7, 1; 8, 16, 8 ]));

  ]

let () = run "map_lattice" tests
