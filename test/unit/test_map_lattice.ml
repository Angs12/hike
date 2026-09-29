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
let cell64 n = Mem.Val.create (Ws.singleton (w64 n)) LittleEndian
let read64 m k = Mem.Val.data (Mem.find (64, LittleEndian) m k)

let tests : unit Alcotest.test list =
  [
    pin "MAP-01" "ML1: add on bottom stays bottom"
      (fun () ->
        check "MAP-01" (Map.equal (Map.add Map.bottom ~key:0 ~data:1) Map.bottom));

    pin "MAP-02" "ML2: join_add/meet_add on bottom stay bottom"
      (fun () ->
        check "MAP-02"
          (Map.equal (Map.join_add Map.bottom ~key:3 ~data:(-1)) Map.bottom
          && Map.equal (Map.meet_add Map.bottom ~key:23 ~data:(-21)) Map.bottom));

    pin "MAP-03" "ML3: find on bottom/top returns bottom/top"
      (fun () ->
        check "MAP-03"
          (Map.find () Map.bottom 10 = IntLattice.bottom && Map.find () Map.top 10 = IntLattice.top));

    pin "MAP-04" "ML4: meet/join top-bottom combos"
      (fun () ->
        check "MAP-04"
          (Map.equal (Map.meet Map.top Map.bottom) Map.bottom
          && Map.equal (Map.meet Map.bottom Map.top) Map.bottom
          && Map.equal (Map.join Map.top Map.bottom) Map.top
          && Map.equal (Map.join Map.bottom Map.top) Map.top
          && Map.equal (Map.meet Map.top Map.top) Map.top
          && Map.equal (Map.join Map.bottom Map.bottom) Map.bottom));

    pin "MAP-05" "ML5: add then find roundtrip; missing key reads top"
      (fun () ->
        check "MAP-05"
          (let m = Map.add Map.top ~key:5 ~data:42 in
           Map.find () m 5 = 42 && Map.find () m 6 = IntLattice.top));

    pin "MAP-06" "ML6: join_add/meet_add merge with the stored value"
      (fun () ->
        check "MAP-06"
          (let m = Map.join_add (Map.add Map.top ~key:5 ~data:3) ~key:5 ~data:10 in
           Map.find () m 5 = 10
           && Map.find () (Map.meet_add (Map.add Map.top ~key:5 ~data:10) ~key:5 ~data:3) 5 = 3));

    pin "MAP-07" "ML7: equal/precedes on small maps"
      (fun () ->
        check "MAP-07"
          (Map.equal Map.bottom Map.bottom
          && (not (Map.equal Map.bottom Map.top))
          && Map.precedes Map.bottom Map.top
          && (not (Map.precedes Map.top Map.bottom))
          && Map.precedes (Map.add Map.top ~key:1 ~data:2) (Map.add Map.top ~key:1 ~data:3)));

    pin "MAP-08" "D2-4: Val.equal/precedes on idx-mismatched cells -> false (no assert)"
      (fun () ->
        let v32 = Mem.Val.create (Ws.of_list ~width:32 [ w32 1 ]) LittleEndian in
        let v64 = Mem.Val.create (Ws.of_list ~width:64 [ w64 1 ]) LittleEndian in
        let vbe = Mem.Val.create (Ws.of_list ~width:32 [ w32 1 ]) BigEndian in
        check "MAP-08"
          ((not (Mem.Val.equal v32 v64))
          && (not (Mem.Val.precedes v32 v64))
          && not (Mem.Val.equal v32 vbe)));

    pin "MAP-09" "D2-5: Val.join on idx-mismatched cells -> top fallback (no assert)"
      (fun () ->
        let v32 = Mem.Val.create (Ws.of_list ~width:32 [ w32 1 ]) LittleEndian in
        let v64 = Mem.Val.create (Ws.of_list ~width:64 [ w64 1 ]) LittleEndian in
        let vbe = Mem.Val.create (Ws.of_list ~width:32 [ w32 1 ]) BigEndian in
        check "MAP-09"
          (Mem.Val.is_top (Mem.Val.join v32 v64) && Mem.Val.is_top (Mem.Val.join v32 vbe)));

    pin "MAP-10" "D2-6: Val.meet on idx-mismatched cells -> bottom fallback (no assert)"
      (fun () ->
        let v32 = Mem.Val.create (Ws.of_list ~width:32 [ w32 1 ]) LittleEndian in
        let v64 = Mem.Val.create (Ws.of_list ~width:64 [ w64 1 ]) LittleEndian in
        check "MAP-10" (Mem.Val.is_bottom (Mem.Val.meet v32 v64)));

    pin "MAP-11" "D2-7: Val.widen_join on idx-mismatched cells -> top fallback (no assert)"
      (fun () ->
        let v32 = Mem.Val.create (Ws.of_list ~width:32 [ w32 1 ]) LittleEndian in
        let v64 = Mem.Val.create (Ws.of_list ~width:64 [ w64 1 ]) LittleEndian in
        check "MAP-11" (Mem.Val.is_top (Mem.Val.widen_join v32 v64)));

    pin "MAP-12" "D2-8: Val ops on matching indices still work (no regression)"
      (fun () ->
        let v32 = Mem.Val.create (Ws.of_list ~width:32 [ w32 1 ]) LittleEndian in
        check "MAP-12"
          (Mem.Val.equal
             (Mem.Val.create (Ws.of_list ~width:32 [ w32 1 ]) LittleEndian)
             v32
          && Ws.elem (w32 1) (Mem.Val.data (Mem.Val.join v32 v32))));

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

    pin "MAP-14" "D2-10: Mem.widen_join of equal maps stays equal (no regression)"
      (fun () ->
        let m1 = mk_mem ~key:(Ws.singleton (w32 0)) ~data:(Ws.of_list ~width:32 [ w32 1; w32 2 ]) in
        check "MAP-14" (Mem.equal (Mem.widen_join m1 m1) m1));

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

    pin "MAP-16"
      "opadd-b: join a key spanning several nodes — node lo 10 reads {1,3}, node lo 14 reads {2,3}, the \
       uncovered byte 13 is top"
      (fun () ->
        let m = Mem.meet_add (range_cell 10 12 1) ~key:(range 14 16) ~data:(cell 2) in
        let m = Mem.join_add m ~key:(range 10 16) ~data:(cell 3) in
        check "MAP-16"
          (Ws.equal (read32 m 10) (Ws.of_list ~width:32 [ w32 1; w32 3 ])
          && Ws.equal (read32 m 14) (Ws.of_list ~width:32 [ w32 2; w32 3 ])
          && Ws.is_top (read32 m 13)));

    pin "MAP-17"
      "opadd-c1: meet a key covering the node (interval_diff `none) — the fresh gap becomes {1,2} (meet \
       fills it); the node narrows"
      (fun () ->
        let m = range_cell 10 20 1 in
        let m =
          Mem.meet_add m ~key:(range 0 30)
            ~data:(Mem.Val.create (Ws.of_list ~width:32 [ w32 1; w32 2 ]) LittleEndian)
        in
        check "MAP-17"
          (Ws.equal (read32 m 0) (Ws.of_list ~width:32 [ w32 1; w32 2 ]) && Ws.is_top (read32 m 15)));

    pin "MAP-18"
      "opadd-c2: join a key overlapping the node's low half (interval_diff `one) — the high flank lo 16 \
       keeps {1}; the joined cell's lo 10 = {1,2}; the fresh gap lo 7 is top"
      (fun () ->
        let m = range_cell 10 20 1 in
        let m = Mem.join_add m ~key:(range 5 15) ~data:(cell 2) in
        check "MAP-18"
          (Ws.equal (read32 m 16) (Ws.singleton (w32 1))
          && Ws.equal (read32 m 10) (Ws.of_list ~width:32 [ w32 1; w32 2 ])
          && Ws.is_top (read32 m 7)));

    pin "MAP-19"
      "opadd-c3: join a key overlapping the node's high half (interval_diff `one) — the low flank lo 10 \
       keeps {1}, the joined cell lo 15 = {1,2}"
      (fun () ->
        let m = range_cell 10 20 1 in
        let m = Mem.join_add m ~key:(range 15 25) ~data:(cell 2) in
        check "MAP-19"
          (Ws.equal (read32 m 10) (Ws.singleton (w32 1))
          && Ws.equal (read32 m 15) (Ws.of_list ~width:32 [ w32 1; w32 2 ])
          && Ws.is_top (read32 m 23)));

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

    pin "MAP-21"
      "opadd-d2: a key with hi = 0xFFFFFFFF — the finishing gap terminates at max (lo 10 = {1}; no \
       wrapped spill at address 0)"
      (fun () ->
        let m = range_cell 10 20 1 in
        let m = Mem.meet_add m ~key:(range 10 0xFFFFFFFF) ~data:(cell 1) in
        check "MAP-21" (Ws.equal (read32 m 10) (Ws.singleton (w32 1)) && Ws.is_top (read32 m 0)));

    pin "MAP-22" "opadd-e: the bottom map stays bottom under add/meet_add/join_add/meet_range"
      (fun () ->
        let bot = Mem.bottom opadd_axis in
        check "MAP-22"
          (Mem.equal (Mem.add bot ~key:(point 10) ~data:(cell 1)) bot
          && Mem.equal (Mem.meet_add bot ~key:(range 0 20) ~data:(cell 1)) bot
          && Mem.equal (Mem.join_add bot ~key:(range 0 20) ~data:(cell 1)) bot
          && Mem.equal (Mem.meet_range bot ~key:(range 0 20) ~data:(cell 1)) bot));

    pin "MAP-23" "opadd-f: a 64-bit {5} meets a 32-bit {5} cell via meet_poly (widened to 64, no crash)"
      (fun () ->
        let m = range_cell 10 10 5 in
        let d64 = Mem.Val.create (Ws.singleton (w64 5)) LittleEndian in
        let m = Mem.meet_add m ~key:(point 10) ~data:d64 in
        check "MAP-23"
          (let v = Mem.Val.data (Mem.find (64, LittleEndian) m (point 10)) in
           Ws.equal v (Ws.singleton (w64 5))));

    pin "MAP-24"
      "opadd-f2: a 64-bit {5} joins a 32-bit {5} cell -> top (the idx-mismatched join fallback), no \
       crash"
      (fun () ->
        let m = range_cell 10 10 5 in
        let d64 = Mem.Val.create (Ws.singleton (w64 5)) LittleEndian in
        let m = Mem.join_add m ~key:(point 10) ~data:d64 in
        check "MAP-24"
          (let v = Mem.Val.data (Mem.find (64, LittleEndian) m (point 10)) in
           Ws.is_top v));

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
      "the key namespace: a wrapping out-of-band value names no bounded key — its \
       coordinate reaches the stack band, so it stays the top identity"
      (fun () ->
        let wrap =
          Ws.of_clp
            (Clp.create ~width:64 ~step:(w64 0x100000000)
               ~cardn:(Cbat_word.of_int ~width:65 0x200000000) (w64 0))
        in
        check "MAP-27" (Mem.Key.of_wordset wrap = []));

    pin "MAP-28"
      "the key namespace: a cross-origin coalesce keeps both cells — a Stack cell \
       and an Abs cell at the same byte range both survive a store-add"
      (fun () ->
        let axis = { Mem.addr_width = 64; Mem.addressable_width = 8 } in
        let m = Mem.add (Mem.top axis) ~key:(key_of (Ws.stack_word_i64 (-8L)))
            ~data:(cell64 1) in
        let m = Mem.add m ~key:(key_of (Ws.singleton (w64 (-8))))
            ~data:(cell64 2) in
        Format.eprintf "DBG MAP28 stack=%a abs=%a\n%!"
          Ws.pp (read64 m (key_of (Ws.stack_word_i64 (-8L))))
          Ws.pp (read64 m (key_of (Ws.singleton (w64 (-8)))));
        check "MAP-28 (Stack cell survives)"
          (Ws.equal (read64 m (key_of (Ws.stack_word_i64 (-8L))))
             (Ws.singleton (w64 1)));
        check "MAP-28 (Abs cell survives)"
          (Ws.equal (read64 m (key_of (Ws.singleton (w64 (-8)))))
               (Ws.singleton (w64 2))));
  ]

let () = run "map_lattice" tests
