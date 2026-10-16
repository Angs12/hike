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

    pin "WORD-50" "gt_int and leq_int are the word compare against of_int at the word's width: wrapped, negative and signed arguments included"
      (fun () ->
        let ints = [ 0; 1; 5; 255; 256; 300; -1; -300; max_int; min_int ] in
        let words =
          List.concat_map
            (fun width ->
               List.concat_map
                 (fun v ->
                    let w = Cbat_word.of_int ~width v in
                    [ w; Cbat_word.signed w ])
                 [ 0; 1; 5; 255; 300; -1; max_int ])
            [ 8; 32; 62; 63; 64; 65; 128 ] in
        let ok =
          List.for_all (fun w ->
              List.for_all (fun i ->
                  let r = Cbat_word.compare w
                      (Cbat_word.of_int ~width:(Cbat_word.bitwidth w) i) in
                  Cbat_word.gt_int w i = (r > 0)
                  && Cbat_word.leq_int w i = (r <= 0))
                ints)
            words in
        check "WORD-50" ok);

    pin "WORD-08" "CAST-W1: a negative 32-bit word's SIGNED cast to 64 sign-extends"
      (fun () ->
        let w32m1 = Cbat_word.of_int64 ~width:32 (-1L) in
        let widened = Cbat_word.cast Bil.SIGNED 64 w32m1 in
        check "WORD-08"
          (match Cbat_word.to_int64 widened with
           | Ok v -> Int64.equal v (-1L)
           | Error _ -> false));

    pin "WORD-09" "signed/unsigned return the word itself when the flag already matches"
      (fun () ->
        let u = Cbat_word.of_int ~width:8 5 in
        let s = Cbat_word.signed u in
        check "WORD-09"
          (Cbat_word.unsigned u == u
           && Cbat_word.signed s == s
           && Cbat_word.is_signed s
           && not (Cbat_word.is_signed (Cbat_word.unsigned s))));




















  ]

let () = run "word" tests
