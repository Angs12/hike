(* Hike_stack_bounds pins: the stack-scope bounds, the escape hulls, and
   the cell-key clamp shared by the sections model and the call
   abstraction.  One Alcotest group per pin; every fixture is built inside
   its closure, so no state crosses pins. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

module Hsb = Hike_stack_bounds

(* The test's word vocabulary: a width-64 word from an int64, and the two
   line ends. *)
let wof64 (v : int64) : Cbat_word.t = Cbat_word.of_int64 ~width:64 v
let zero64 = Cbat_word.zero 64
let ones64 = Cbat_word.ones 64
let base = Ws.stack_base
let floor = Int64.add base Int64.min_int
let cei = Int64.max_int

let wc (a : Cbat_word.t) (b : Cbat_word.t) : bool = Cbat_word.equal a b

let pair_w ((a, b) : Cbat_word.t * Cbat_word.t)
    ((c, d) : Cbat_word.t * Cbat_word.t) : bool =
  wc a c && wc b d

let some_pair_w (o : (Cbat_word.t * Cbat_word.t) option)
    (p : Cbat_word.t * Cbat_word.t) : bool =
  match o with Some q -> pair_w q p | None -> false

let tests : unit Alcotest.test list =
  [
    pin "HSB-01" "i64_opt: a width-64 word is representable (the high bit reads signed)"
      (fun () ->
        check "HSB-01"
          (Hsb.i64_opt (w64 5) = Some 5L
          && Hsb.i64_opt (wof64 (-8L)) = Some (-8L)
          && Hsb.i64_opt ones64 = Some (-1L)));

    pin "HSB-02" "i64_opt: a value past 2^64-1 is not representable"
      (fun () ->
        check "HSB-02"
          (Hsb.i64_opt (Cbat_word.ones 65) = None
          && Hsb.i64_opt (Cbat_word.of_int64 ~width:128 (-1L)) = None));

    pin "HSB-03" "position_pair: representable offsets map to base + offset"
      (fun () ->
        check "HSB-03"
          (Hsb.position_pair (wof64 (-16L)) (wof64 (-8L))
             = Some (Int64.add base (-16L), Int64.add base (-8L))
          && Hsb.position_pair (wof64 8L) (wof64 16L)
               = Some (Int64.add base 8L, Int64.add base 16L)));

    pin "HSB-04" "position_pair: an unrepresentable endpoint yields None"
      (fun () ->
        check "HSB-04"
          (Hsb.position_pair (Cbat_word.ones 65) (w64 0) = None
          && Hsb.position_pair (w64 0) (Cbat_word.ones 65) = None));

    pin "HSB-05" "position_pair: a positive offset whose position overflows yields None"
      (fun () ->
        let hi = Cbat_word.of_int64 ~width:64 0x4000000000000000L in
        check "HSB-05"
          (Hsb.position_pair hi (w64 0) = None
          && Hsb.position_pair (w64 0) hi = None));

    pin "HSB-06" "stack_floor: entry + Int64.min_int is the below-entry scope bound"
      (fun () ->
        check "HSB-06"
          (Hsb.stack_floor ~entry:base = -4611686018427387896L
          && Hsb.stack_floor ~entry:0L = Int64.min_int
          && Hsb.stack_floor ~entry:base = floor));

    pin "HSB-07" "args_ceiling: the top of the position line"
      (fun () -> check "HSB-07" (Hsb.args_ceiling = Int64.max_int && Hsb.args_ceiling = cei));

    pin "HSB-08"
      "positions_of_offsets: a finite offset interval projects to its exact positions"
      (fun () ->
        let ws = Ws.stack_word (Clp.interval ~width:64 (wof64 (-16L)) (wof64 (-8L))) in
        check "HSB-08"
          (Hsb.positions_of_offsets ws
             = Some (Int64.add base (-16L), Int64.add base (-8L))));

    pin "HSB-09" "positions_of_offsets: a plain (non-stack) set has no offset positions"
      (fun () ->
        check "HSB-09"
          (Hsb.positions_of_offsets (Ws.top 64) = None
          && Hsb.positions_of_offsets (Ws.of_list ~width:64 [ w64 1; w64 2 ]) = None));

    pin "HSB-10" "positions_of_offsets: an offset word wider than int64 yields None"
      (fun () ->
        check "HSB-10"
          (Hsb.positions_of_offsets
             (Ws.stack_word (Clp.singleton (Cbat_word.ones 65)))
             = None));

    pin "HSB-11" "positions_of_offsets: an offset whose position overflows yields None"
      (fun () ->
        check "HSB-11"
          (Hsb.positions_of_offsets (Ws.stack_word_i64 0x4000000000000000L) = None));

    pin "HSB-12"
      "unsigned_bounds: plain extrema as int64; a stack value projects absolutely"
      (fun () ->
        check "HSB-12"
          (Hsb.unsigned_bounds (Ws.of_list ~width:64 [ w64 5; w64 9 ]) = Some (5L, 9L)
          && Hsb.unsigned_bounds (Ws.stack_word_i64 (-8L))
               = Some (Int64.add base (-8L), Int64.add base (-8L))));

    pin "HSB-13" "unsigned_bounds: an empty set yields None"
      (fun () -> check "HSB-13" (Hsb.unsigned_bounds (Ws.bottom 64) = None));

    pin "HSB-14" "unsigned_bounds: an extremum past int64 yields None"
      (fun () ->
        check "HSB-14"
          (Hsb.unsigned_bounds (Ws.of_list ~width:65 [ Cbat_word.ones 65 ]) = None));

    pin "HSB-15" "full_bounds: a swapped hull spans the whole scope"
      (fun () ->
        check "HSB-15"
          (Hsb.full_bounds (Ws.stack_word_i64 0L) ~flo:(-100L) ~cei:100L 10L (-10L)
             = (-100L, 100L)));

    pin "HSB-16" "full_bounds: an ascending set reaches the ceiling while keeping lo"
      (fun () ->
        let asc = Ws.of_clp (Clp.create_ascending ~width:64 ~base:(w64 0) ~step:(w64 8)) in
        check "HSB-16"
          (Hsb.full_bounds asc ~flo:(-100L) ~cei:100L 5L 10L = (5L, 100L)));

    pin "HSB-17" "full_bounds: a descending set reaches the floor while keeping hi"
      (fun () ->
        let desc = Ws.of_clp (Clp.create_descending ~width:64 ~base:(w64 100) ~step:(w64 1)) in
        check "HSB-17"
          (Hsb.full_bounds desc ~flo:(-100L) ~cei:100L 0L 50L = (-100L, 50L)));

    pin "HSB-18" "full_bounds: a finite or circular set spans the whole scope"
      (fun () ->
        check "HSB-18"
          (Hsb.full_bounds (Ws.stack_word_i64 3L) ~flo:(-100L) ~cei:100L 0L 50L
             = (-100L, 100L)
          && Hsb.full_bounds (Ws.of_clp (Clp.top 64)) ~flo:(-100L) ~cei:100L 0L 50L
               = (-100L, 100L)));

    pin "HSB-19" "escape_extent: a plain value is not stack-symbolic"
      (fun () ->
        check "HSB-19"
          (Hsb.escape_extent ~entry:base (Ws.top 64) = None
          && Hsb.escape_extent ~entry:base (Ws.of_list ~width:64 [ w64 1 ]) = None));

    pin "HSB-20" "escape_extent: a finite stack value keeps its exact positions"
      (fun () ->
        let ws = Ws.stack_word (Clp.interval ~width:64 (wof64 (-16L)) (wof64 (-8L))) in
        check "HSB-20"
          (Hsb.escape_extent ~entry:base ws
             = Some (Int64.add base (-16L), Int64.add base (-8L))));

    pin "HSB-21" "escape_extent: unrepresentable positions become the whole scope"
      (fun () ->
        check "HSB-21"
          (Hsb.escape_extent ~entry:base
             (Ws.stack_word (Clp.singleton (Cbat_word.ones 65)))
             = Some (floor, cei)));

    pin "HSB-22" "escape_extent: a descending stack value reaches the floor"
      (fun () ->
        let desc =
          Ws.stack_word (Clp.create_descending ~width:64 ~base:(w64 100) ~step:(w64 1))
        in
        check "HSB-22"
          (Hsb.escape_extent ~entry:base desc = Some (floor, Int64.add base 100L)));

    pin "HSB-23" "escape_extent: a top stack value spans the whole scope"
      (fun () ->
        check "HSB-23"
          (Hsb.escape_extent ~entry:base (Ws.stack_word (Clp.top 64)) = Some (floor, cei)));

    pin "HSB-24"
      "escape_extent: an ascending stack value's signed max wraps to the whole scope"
      (fun () ->
        let asc =
          Ws.stack_word (Clp.create_ascending ~width:64 ~base:(w64 0) ~step:(w64 8))
        in
        check "HSB-24" (Hsb.escape_extent ~entry:base asc = Some (floor, cei)));

    pin "HSB-25" "key_extent: a finite stack value keeps its exact offset extrema"
      (fun () ->
        check "HSB-25"
          (some_pair_w (Hsb.key_extent (Ws.stack_word_i64 (-8L))) (wof64 (-8L), wof64 (-8L))));

    pin "HSB-26" "key_extent: an ascending stack value clamps the top to ones"
      (fun () ->
        let asc =
          Ws.stack_word (Clp.create_ascending ~width:64 ~base:(w64 0) ~step:(w64 8))
        in
        check "HSB-26" (some_pair_w (Hsb.key_extent asc) (zero64, ones64)));

    pin "HSB-27" "key_extent: a descending stack value clamps the bottom to zero"
      (fun () ->
        let desc =
          Ws.stack_word (Clp.create_descending ~width:64 ~base:(w64 100) ~step:(w64 1))
        in
        check "HSB-27" (some_pair_w (Hsb.key_extent desc) (zero64, w64 100)));

    pin "HSB-28" "key_extent: a circular (top) value spans the key line"
      (fun () ->
        check "HSB-28"
          (some_pair_w (Hsb.key_extent (Ws.stack_word (Clp.top 64))) (zero64, ones64)
          && some_pair_w (Hsb.key_extent (Ws.top 64)) (zero64, ones64)));

    pin "HSB-29" "key_extent: an empty stack value spans the key line"
      (fun () ->
        check "HSB-29"
          (some_pair_w (Hsb.key_extent (Ws.stack_word (Clp.bottom 64))) (zero64, ones64)));

    pin "HSB-30"
      "key_extent: a plain in-band set clamps its own segment-relative hull"
      (fun () ->
        let plain =
          Ws.of_clp (Clp.interval ~width:64 (wof64 base) (wof64 (Int64.add base 16L)))
        in
        check "HSB-30" (some_pair_w (Hsb.key_extent plain) (wof64 0L, wof64 16L)));

    pin "HSB-31" "key_extent: a plain out-of-band set keeps its own word extrema"
      (fun () ->
        check "HSB-31"
          (some_pair_w
             (Hsb.key_extent (Ws.of_list ~width:64 [ w64 1; w64 2 ]))
             (w64 1, w64 2)));

    pin "HSB-32" "key_extent: a plain empty set yields None"
      (fun () -> check "HSB-32" (Hsb.key_extent (Ws.bottom 64) = None));

    pin "HSB-33"
      "key_extent: an offset word wider than int64 is preserved, not dropped"
      (fun () ->
        let w = Cbat_word.ones 65 in
        check "HSB-33"
          (some_pair_w (Hsb.key_extent (Ws.stack_word (Clp.singleton w))) (w, w)));

    pin "HSB-34" "caller_window_bytes: the window capacity is 65536"
      (fun () -> check "HSB-34" (Hsb.caller_window_bytes = 65536L));

    pin "HSB-35" "stack_max: the below-entry clamp is 65536"
      (fun () -> check "HSB-35" (Hsb.stack_max = 65536L));
  ]

let () = run "hike_stack_bounds" tests
