open Bap.Std
open Hike_test.Harness
open Hike_test.Common

let tests =
  [
    case "highest set bit includes zero and the sign bit" (fun () ->
        List.iter
          (fun (input, expected) ->
            Alcotest.(check (option int))
              (string_of_int input) expected
              (Wo.lead_1_bit (Wo.of_int ~width:8 input)))
          [ (0, None); (5, Some 2); (128, Some 7) ]);
    case "integer comparisons wrap the integer to the word's width" (fun () ->
        let ints =
          [ 0; 1; 3; 5; 7; 255; 256; 300; -1; -300; max_int; min_int ]
        in
        List.iter
          (fun width ->
            List.iter
              (fun value ->
                let word = Wo.of_int ~width value in
                List.iter
                  (fun word ->
                    List.iter
                      (fun i ->
                        let comparison = Wo.compare word (Wo.of_int ~width i) in
                        let label =
                          Format.asprintf "%a against %d" Wo.pp word i
                        in
                        Alcotest.(check bool)
                          (label ^ " >") (comparison > 0) (Wo.gt_int word i);
                        Alcotest.(check bool)
                          (label ^ " <=") (comparison <= 0) (Wo.leq_int word i))
                      ints)
                  [ word; Wo.signed word ])
              [ 0; 1; 3; 5; 7; 255; 300; -1; max_int ])
          [ 8; 32; 62; 63; 64; 65; 128 ]);
    case "signed widening preserves a negative value" (fun () ->
        let result = Wo.cast Bil.SIGNED 64 (Wo.of_int ~width:32 (-1)) in
        Alcotest.(check int) "width" 64 (Wo.bitwidth result);
        Alcotest.(check int64) "value" (-1L) (Wo.to_int64_exn result));
    case "an already signed or unsigned word is reused" (fun () ->
        let unsigned = Wo.of_int ~width:8 5 in
        let signed = Wo.signed unsigned in
        check "unsigned sharing" (Wo.unsigned unsigned == unsigned);
        check "signed sharing" (Wo.signed signed == signed);
        check "signed flag" (Wo.is_signed signed);
        check "unsigned flag" (not (Wo.is_signed (Wo.unsigned signed))));
  ]

let () = run "word" [ ("operations", tests) ]
