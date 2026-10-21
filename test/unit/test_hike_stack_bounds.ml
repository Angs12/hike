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
let base = Ws.stack_base

let wc (a : Cbat_word.t) (b : Cbat_word.t) : bool = Cbat_word.equal a b

let pair_w ((a, b) : Cbat_word.t * Cbat_word.t)
    ((c, d) : Cbat_word.t * Cbat_word.t) : bool =
  wc a c && wc b d

let some_pair_w (o : (Cbat_word.t * Cbat_word.t) option)
    (p : Cbat_word.t * Cbat_word.t) : bool =
  match o with Some q -> pair_w q p | None -> false

let tests : unit Alcotest.test list =
  [
    pin "HSB-03" "position_pair: representable offsets map to base + offset"
      (fun () ->
        check "HSB-03"
          (Hsb.position_pair (wof64 (-16L)) (wof64 (-8L))
             = Some (Int64.add base (-16L), Int64.add base (-8L))
          && Hsb.position_pair (wof64 8L) (wof64 16L)
               = Some (Int64.add base 8L, Int64.add base 16L)));





    pin "HSB-06" "stack_floor: entry + Int64.min_int is the below-entry scope bound"
      (fun () ->
        check "HSB-06"
          (Hsb.stack_floor ~entry:0L = Int64.min_int
          && Hsb.stack_floor ~entry:1L = -9223372036854775807L
          && Hsb.stack_floor ~entry:(-1L) = Int64.max_int));



    pin "HSB-08"
      "positions_of_offsets: a finite offset interval projects to its exact positions"
      (fun () ->
        let ws = Ws.stack_word (Clp.interval ~width:64 (wof64 (-16L)) (wof64 (-8L))) in
        check "HSB-08"
          (Hsb.positions_of_offsets ws
             = Some (Int64.add base (-16L), Int64.add base (-8L))));







    pin "HSB-12"
      "unsigned_bounds: plain extrema as int64; a stack value projects absolutely"
      (fun () ->
        check "HSB-12"
          (Hsb.unsigned_bounds (Ws.of_list ~width:64 [ w64 5; w64 9 ]) = Some (5L, 9L)
          && Hsb.unsigned_bounds (Ws.stack_word_i64 (-8L))
               = Some (Int64.add base (-8L), Int64.add base (-8L))));





    pin "HSB-15" "full_bounds: a swapped hull spans the whole scope"
      (fun () ->
        check "HSB-15"
          (Hsb.full_bounds (Ws.stack_word_i64 0L) ~flo:(-100L) ~cei:100L 10L (-10L)
             = (-100L, 100L)));







    pin "HSB-19" "escape_extent: a plain value is not stack-symbolic"
      (fun () ->
        check "HSB-19"
          (Hsb.escape_extent ~entry:base (Ws.top 64) = None
          && Hsb.escape_extent ~entry:base (Ws.of_list ~width:64 [ w64 1 ]) = None));











    pin "HSB-25" "key_extent: a finite stack value keeps its exact offset extrema"
      (fun () ->
        check "HSB-25"
          (some_pair_w
             (Hsb.key_extent ~width:64 (Ws.stack_word_i64 (-8L)))
             (wof64 (-8L), wof64 (-8L))));

















    pin "HSB-34" "caller_window_bytes: the window capacity is 65536"
      (fun () -> check "HSB-34" (Hsb.caller_window_bytes = 65536L));


  ]

let () = run "hike_stack_bounds" tests
