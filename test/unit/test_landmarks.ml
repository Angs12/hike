open Bap.Std
open Hike_test.Harness
open Hike_test.Common
module L = Cbat_landmarks

let key = L.Word (v64 "landmark_word")

let record ?(warmed = false) table head bound distance =
  L.record table ~key ~head ~bound:(w32 bound) ~is_upper:true ~warmed
    ~dist:distance

let check_steps label expected table head =
  let pp ppf = function
    | L.Zero -> Format.pp_print_string ppf "Zero"
    | L.Inf -> Format.pp_print_string ppf "Inf"
    | L.Finite n -> Format.fprintf ppf "Finite %d" n
  in
  Alcotest.check
    (Alcotest.testable pp L.equal_arm)
    label expected (L.steps table head key)

let observe table head p cstr =
  L.with_widening_head table (Some head) (fun () ->
      L.observe_unsat table ~key ~p ~cstr ~m:(Ws.meet p cstr))

let tests =
  [
    case "readings retain history across advances and ignore stale boundaries"
      (fun () ->
        let table = L.create () and head = Tid.create () in
        record table head 100 10;
        check_steps "first reading waits" L.Zero table head;
        L.advance table head key;
        record table head 100 6;
        check_steps "6 / (10 - 6)" (L.Finite 1) table head;
        Alcotest.(check int)
          "one entry for the same boundary" 1
          (List.length (L.entries table head key));
        L.advance table head key;
        L.advance table head key;
        record table head 100 5;
        check_steps "an empty round keeps the previous distance" (L.Finite 5)
          table head;
        L.advance table head key;
        record table head 200 5;
        L.advance table head key;
        record table head 200 4;
        check_steps "stale boundary 100 cannot hold the head" (L.Finite 4) table
          head);
    case "a moving bound keeps one identity within its guard" (fun () ->
        List.iter
          (fun guarded ->
            let table = L.create () and head = Tid.create () in
            let add bound distance =
              L.with_widening_head table (Some head) (fun () ->
                  if guarded then
                    L.with_guard table
                      (fun () -> "i < n")
                      (fun () -> record table head bound distance)
                  else record table head bound distance)
            in
            add 100 10;
            L.advance table head key;
            add 101 9;
            Alcotest.(check int)
              "boundary identities"
              (if guarded then 1 else 2)
              (List.length (L.entries table head key));
            if guarded then
              check_steps "moving guard's remaining steps" (L.Finite 9) table
                head)
          [ true; false ]);
    case
      "both narrowing directions acquire a warm boundary and pair their \
       distances" (fun () ->
        let range lo hi =
          Ws.of_clp (Clp.interval ~width:32 (w32 lo) (w32 hi))
        in
        List.iter
          (fun (name, first, second, constraint_) ->
            let table = L.create () and head = Tid.create () in
            check
              (name ^ " first observation")
              (observe table head first constraint_);
            check_steps "a lone narrowed reading allows widening" L.Inf table
              head;
            check
              (name ^ " second observation")
              (observe table head second constraint_);
            check_steps "39 / (49 - 39)" (L.Finite 3) table head)
          [
            ("lower bound", range 0 100, range 10 100, range 50 100);
            ("upper bound", range 0 100, range 0 90, range 0 50);
          ]);
    case
      "observations outside a cycle or across coordinate lines record nothing"
      (fun () ->
        let table = L.create () and head = Tid.create () in
        let p = Ws.singleton (w64 0) and cstr = Ws.singleton (w64 4) in
        check "outside a cycle"
          (not (L.observe_unsat table ~key ~p ~cstr ~m:(Ws.meet p cstr)));
        check "different lines"
          (not (observe table head (Ws.stack_word_i64 0L) cstr));
        check "no entries" (L.entries table head key = []));
    case "distance uses signed magnitude and caps the int64 overflow" (fun () ->
        List.iter
          (fun (start, expected) ->
            let table = L.create () and head = Tid.create () in
            check "excluded value records a boundary"
              (observe table head
                 (Ws.singleton (Wo.of_int64 ~width:64 start))
                 (Ws.singleton (w64 0)));
            match L.entries table head key with
            | [ entry ] ->
                Alcotest.(check (option int))
                  "distance" (Some expected) entry.L.dist
            | _ -> Alcotest.fail "expected one excluded boundary")
          [ (-99999L, 99999); (Int64.min_int, 1 lsl 40) ]);
    case "word and cell rows retain every distinct boundary independently"
      (fun () ->
        let table = L.create () and head = Tid.create () in
        for i = 0 to 99 do
          let cell =
            L.Cell
              {
                L.origin = Some Hike_origin.Stack;
                lo_width = 64;
                lo_value = Int64.of_int i;
                hi_width = 64;
                hi_value = Int64.of_int i;
                stride = 1;
              }
          in
          L.record table ~head ~key:cell ~bound:(w64 i) ~is_upper:true
            ~warmed:false ~dist:1;
          record table head i 1
        done;
        let count kind =
          List.fold_left
            (fun total k ->
              if kind k then total + List.length (L.entries table head k)
              else total)
            0 (L.keys_at table head)
        in
        Alcotest.(check int)
          "cell boundaries" 100
          (count (function L.Cell _ -> true | _ -> false));
        Alcotest.(check int)
          "word boundaries" 100
          (count (function L.Word _ -> true | _ -> false)));
  ]

let () = run "landmarks" [ ("landmarks", tests) ]
