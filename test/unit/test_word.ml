(* Cbat_word pins.  One Alcotest group per pin; each pin builds its own
   fixture, so no state crosses pins. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

let tests : unit Alcotest.test list =
  [








    pin "WORD-05" "WO5: lead_1_bit"
      (fun () ->
        check "WORD-05"
          (Wo.lead_1_bit (Cbat_word.of_int ~width:8 5) = Some 2
          && Wo.lead_1_bit (Cbat_word.of_int ~width:8 128) = Some 7
          && Wo.lead_1_bit (Cbat_word.zero 8) = None));



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




















  ]

let () = run "word" tests
