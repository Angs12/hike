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
       the Stack namespace, a plain out-of-band word in Abs) and two keys of the \
       same byte range but different origins do not overlap"
      (fun () ->
        let k_stack = key_of (Ws.stack_word_i64 (-8L)) in
        let k_abs = key_of (Ws.singleton (w64 (-8))) in
        check "MAP-26"
          (Hike_origin.equal (key_origin k_stack) Hike_origin.Stack
          && Hike_origin.equal (key_origin k_abs) Hike_origin.Abs
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




  ]

let () = run "map_lattice" tests
