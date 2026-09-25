(* Cbat_word pins.  One Alcotest group per pin; each pin builds its own
   fixture, so no state crosses pins. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

let tests : unit Alcotest.test list =
  [
    pin "WORD-01"
      "WO1: dom_size i ~width:w = 2^i as a w-bit word (zero if w = i)"
      (fun () ->
        check "WORD-01"
          (Cbat_word.to_int_exn (Wo.dom_size 3 ~width:4) = 8
          && Cbat_word.bitwidth (Wo.dom_size 3 ~width:4) = 4
          && Cbat_word.to_int_exn (Wo.dom_size 60 ~width:61) = 0x1000000000000000
          && Cbat_word.is_zero (Wo.dom_size 3 ~width:3)));

    pin "WORD-02" "WO2: cap_at_width keeps small words, saturates large ones"
      (fun () ->
        check "WORD-02"
          (let c255 = Wo.cap_at_width ~width:8 (Cbat_word.of_int ~width:32 255) in
           Cbat_word.to_int_exn c255 = 255
           && Cbat_word.bitwidth c255 = 8
           && Cbat_word.to_int_exn (Wo.cap_at_width ~width:2 (Cbat_word.of_int ~width:8 5)) = 3));

    pin "WORD-03" "WO3: add_exact/mul_exact widen to the exact result"
      (fun () ->
        check "WORD-03"
          (let s = Wo.add_exact (Cbat_word.of_int ~width:8 200) (Cbat_word.of_int ~width:8 100) in
           Cbat_word.bitwidth s = 9
           && Cbat_word.to_int_exn s = 300
           &&
           let p = Wo.mul_exact (Cbat_word.of_int ~width:4 15) (Cbat_word.of_int ~width:4 15) in
           Cbat_word.bitwidth p = 8 && Cbat_word.to_int_exn p = 225));

    pin "WORD-04" "WO4: factor_2s pulls out the 2-power"
      (fun () ->
        check "WORD-04"
          (let odd, twos = Wo.factor_2s (Cbat_word.of_int ~width:8 12) in
           Cbat_word.to_int_exn odd = 3
           && twos = 2
           &&
           let odd', twos' = Wo.factor_2s (Cbat_word.of_int ~width:8 16) in
           Cbat_word.to_int_exn odd' = 1 && twos' = 4));

    pin "WORD-05" "WO5: lead_1_bit"
      (fun () ->
        check "WORD-05"
          (Wo.lead_1_bit (Cbat_word.of_int ~width:8 5) = Some 2
          && Wo.lead_1_bit (Cbat_word.of_int ~width:8 128) = Some 7
          && Wo.lead_1_bit (Cbat_word.zero 8) = None));

    pin "WORD-06" "WO6: is_one / succ_exact / lshift_exact"
      (fun () ->
        check "WORD-06"
          (Wo.is_one (Cbat_word.of_int ~width:8 1)
          && (not (Wo.is_one (Cbat_word.of_int ~width:8 0)))
          &&
          let s = Wo.succ_exact (Cbat_word.of_int ~width:8 255) in
          Cbat_word.bitwidth s = 9
          && Cbat_word.to_int_exn s = 256
          &&
          let l = Wo.lshift_exact (Cbat_word.of_int ~width:8 1) 4 in
          Cbat_word.bitwidth l = 12 && Cbat_word.to_int_exn l = 16));

    pin "WORD-07" "WO7: gt_int"
      (fun () ->
        check "WORD-07"
          (Wo.gt_int (Cbat_word.of_int ~width:8 7) 5 && not (Wo.gt_int (Cbat_word.of_int ~width:8 3) 5)));

    pin "WORD-08" "CAST-W1: a negative 32-bit word's SIGNED cast to 64 sign-extends"
      (fun () ->
        let w32m1 = Cbat_word.of_int64 ~width:32 (-1L) in
        let widened = Cbat_word.cast Bil.SIGNED 64 w32m1 in
        check "WORD-08"
          (match Cbat_word.to_int64 widened with
           | Ok v -> Int64.equal v (-1L)
           | Error _ -> false));

    pin "WORD-09" "CAST-W2: a positive narrow word's SIGNED cast is the identity"
      (fun () ->
        let w32pos = Cbat_word.of_int64 ~width:32 0x7fffffffL in
        let widened_pos = Cbat_word.cast Bil.SIGNED 64 w32pos in
        check "WORD-09"
          (match Cbat_word.to_int64 widened_pos with
           | Ok v -> Int64.equal v 0x7fffffffL
           | Error _ -> false));

    pin "WORD-10" "CAST-W3: a SIGNED cast to a narrower width keeps the truncated bit pattern"
      (fun () ->
        let narrowed = Cbat_word.cast Bil.SIGNED 32 (Cbat_word.of_int64 ~width:64 (-1L)) in
        check "WORD-10"
          (match Cbat_word.to_int64 narrowed with
           | Ok v -> Int64.equal v 0xFFFFFFFFL
           | Error _ -> false));

    pin "WORD-11" "WORD-BC: of_word keeps the unsigned value (all-ones stays 2^64-1)"
      (fun () ->
        let word64 v = Word.of_int64 ~width:64 v in
        check "WORD-11"
          (match Cbat_word.of_word (word64 (-1L)) with
           | Cbat_word.Big (z, 64, false) -> Z.equal z (Z.of_string "18446744073709551615")
           | _ -> false));

    pin "WORD-12" "WORD-BC: of_word of a small word is the Small immediate"
      (fun () ->
        check "WORD-12"
          (Cbat_word.of_word (Word.one 64) = Cbat_word.Small (1, 64, false)));

    pin "WORD-13"
      "WORD-BC: to_word of a signed negative keeps the two's-complement payload and the sign flag"
      (fun () ->
        check "WORD-13"
          (let t = Cbat_word.of_string "-1:64s" in
           String.equal (Word.to_string (Cbat_word.to_word t)) "-1:64s"));

    pin "WORD-14" "WORD-BC: to_word of a signed zero keeps the sign flag"
      (fun () ->
        check "WORD-14"
          (let t = Cbat_word.signed (Cbat_word.of_string "0:64u") in
           String.equal (Word.to_string (Cbat_word.to_word t)) "0:64s"));

    pin "WORD-15" "WORD-BC: to_word of an unsigned small value is the same bits at the same width"
      (fun () ->
        check "WORD-15"
          (Word.equal (Cbat_word.to_word (Cbat_word.Small (42, 16, false)))
             (Word.of_int ~width:16 42)));

    pin "WORD-16" "WORD-BC: of_word (to_word t) is value-identity for unsigned words"
      (fun () ->
        check "WORD-16"
          (let t = Cbat_word.of_string "0x8000000000000000:64u" in
           Cbat_word.equal (Cbat_word.of_word (Cbat_word.to_word t)) t));

    pin "WORD-17" "WORD-BC: the high-bit unsigned word's int64 bit pattern survives"
      (fun () ->
        let word64 v = Word.of_int64 ~width:64 v in
        check "WORD-17"
          (Word.equal
             (Cbat_word.to_word (Cbat_word.of_string "0x8000000000000000:64u"))
             (word64 Int64.min_int)));

    pin "WORD-18" "WORD-BC: a 80-bit word round-trips with no string path"
      (fun () ->
        check "WORD-18"
          (let wide = Word.ones 80 in
           Cbat_word.equal
             (Cbat_word.of_word (Cbat_word.to_word (Cbat_word.of_word wide)))
             (Cbat_word.of_word wide)
           && Word.equal (Cbat_word.to_word (Cbat_word.of_word wide)) wide));
  ]

let () = run "word" tests
