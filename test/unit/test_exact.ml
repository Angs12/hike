open Bap.Std
open Hike_test.Harness
open Hike_test.Common

let set width xs = Ex.of_list ~width (List.map (Wo.of_int ~width) xs)
let check_set = Alcotest.check (Alcotest.testable Ex.pp Ex.equal)

let tests =
  [
    case "construction sorts and deduplicates at small and large word widths"
      (fun () ->
        List.iter
          (fun width ->
            let word z = Wo.of_z z width in
            let high = Z.shift_left Z.one (width - 1) in
            let expected =
              List.map word [ Z.zero; Z.one; Z.of_int 3; high; Z.succ high ]
            in
            let input =
              List.map word
                [ Z.succ high; Z.of_int 3; high; Z.zero; Z.one; high ]
            in
            let image =
              Ex.of_iter ~width ~iter:(fun emit -> List.iter emit input)
            in
            Alcotest.(check int) "width" width (Ex.bitwidth image);
            Alcotest.(check int)
              "cardinality" 5
              (Wo.to_int_exn (Ex.cardinality image));
            Alcotest.(check (list (testable Wo.pp Wo.equal)))
              "ordered elements" expected (Ex.elements image);
            let check_word =
              Alcotest.(check (option (testable Wo.pp Wo.equal)))
            in
            check_word "minimum" (Some (word Z.zero)) (Ex.min_elem image);
            check_word "maximum" (Some (word (Z.succ high))) (Ex.max_elem image);
            check "membership excludes an absent value"
              (not (Ex.elem (word (Z.of_int 2)) image));
            check_set "list and streamed construction agree"
              (Ex.of_list ~width input) image)
          [ 8; 63; 64; 128 ]);
    case "unary operations compute their modular images" (fun () ->
        let input = set 8 [ 0; 1; 127; 128; 255 ] in
        check_set "negation" (set 8 [ 0; 255; 129; 128; 1 ]) (Ex.neg input);
        check_set "complement" (set 8 [ 255; 254; 128; 127; 0 ]) (Ex.lnot input));
    case "binary operations retain exactly the resulting alternatives"
      (fun () ->
        let a = set 8 [ 1; 2 ] and b = set 8 [ 2; 3 ] in
        List.iter
          (fun (name, expected, actual) ->
            check_set name (set 8 expected) actual)
          [
            ("union", [ 1; 2; 3 ], Ex.union a b);
            ("intersection", [ 2 ], Ex.intersection a b);
            ("addition", [ 11; 12 ], Ex.add a (set 8 [ 10 ]));
            ("wrapping addition", [ 0; 255 ], Ex.add a (set 8 [ 254 ]));
            ( "xor across the sign bit",
              [ 0; 1; 2; 3; 4; 6; 126; 128; 129; 131; 134; 252; 254 ],
              Ex.logxor (set 8 [ 0; 1; 7; 128; 255 ]) (set 8 [ 1; 3; 129 ]) );
          ]);
    case "extract, extension and concat preserve the selected bits" (fun () ->
        List.iter
          (fun (name, width, expected, actual) ->
            check_set name (set width [ expected ]) actual)
          [
            ( "middle byte",
              8,
              0xab,
              Ex.extract ~hi:15 ~lo:8 (set 32 [ 0x12abcd ]) );
            ( "zero extension",
              64,
              0x80000001,
              Ex.cast Bil.UNSIGNED 64 (set 32 [ 0x80000001 ]) );
            ("sign extension", 64, -128, Ex.cast Bil.SIGNED 64 (set 8 [ 0x80 ]));
            ( "concat",
              48,
              0x12345678abcd,
              Ex.concat (set 32 [ 0x12345678 ]) (set 16 [ 0xabcd ]) );
          ]);
    case "different word widths are unequal in either operand order" (fun () ->
        let a = set 32 [ 1; 2 ] and b = set 64 [ 1; 2 ] in
        check "32 versus 64" (not (Ex.equal a b));
        check "64 versus 32" (not (Ex.equal b a)));
    case "filter visits each element once and preserves an unchanged set"
      (fun () ->
        let input = set 8 [ 1; 4; 7; 200 ] in
        let seen = ref [] in
        let filtered =
          Ex.filter input ~f:(fun word ->
              seen := word :: !seen;
              true)
        in
        check "unchanged set is shared" (filtered == input);
        check_set "all survive" input filtered;
        Alcotest.(check (list int))
          "visit order" [ 1; 4; 7; 200 ]
          (List.rev_map Wo.to_int_exn !seen);
        check_set "some survive"
          (set 8 [ 1; 7 ])
          (Ex.filter input ~f:(fun word -> Wo.to_int_exn word mod 2 = 1));
        check_set "none survive" (Ex.bottom 8)
          (Ex.filter input ~f:(fun _ -> false)));
    case "signed extrema include the sign boundary and the empty set" (fun () ->
        List.iter
          (fun (values, expected) ->
            let input = set 8 values in
            let actual =
              match (Ex.min_elem_signed input, Ex.max_elem_signed input) with
              | None, None -> None
              | Some lo, Some hi ->
                  check "extrema are signed words"
                    (Wo.is_signed lo && Wo.is_signed hi);
                  let signed word =
                    let n = Wo.to_int_exn word in
                    if n < 128 then n else n - 256
                  in
                  Some (signed lo, signed hi)
              | _ -> Alcotest.fail "only one signed extremum exists"
            in
            Alcotest.(check (option (pair int int)))
              "signed bounds" expected actual)
          [
            ([], None);
            ([ 5 ], Some (5, 5));
            ([ 200 ], Some (-56, -56));
            ([ 1; 2; 3 ], Some (1, 3));
            ([ 130; 200; 255 ], Some (-126, -1));
            ([ 0; 127; 128; 255 ], Some (-128, 127));
            ([ 3; 100; 250 ], Some (-6, 100));
          ]);
    case "stride divisibility uses consecutive gaps" (fun () ->
        let splits values divisor =
          Ex.splits_by (set 8 values) (Wo.of_int ~width:8 divisor)
        in
        check "grid divides" (splits [ 2; 6; 10 ] 4);
        check "larger stride does not divide" (not (splits [ 2; 6; 10 ] 8));
        check "empty set" (splits [] 3);
        check "singleton" (splits [ 9 ] 3));
  ]

let () = run "exact sets" [ ("operations", tests) ]
