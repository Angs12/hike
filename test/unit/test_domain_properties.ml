open Bap.Std
open Hike_test.Harness
open Hike_test.Common

let widths = [ 8; 16; 32; 64 ]
let check_clp = Alcotest.check (Alcotest.testable Clp.pp Clp.equal)
let modulus width = Z.shift_left Z.one width

let random_word rng width =
  let bits =
    Z.(
      logor
        (of_int (Random.State.bits rng))
        (logor
           (shift_left (of_int (Random.State.bits rng)) 30)
           (shift_left (of_int (Random.State.bits rng)) 60)))
  in
  Wo.of_z bits width

(* The witness list is computed independently of abstract enumeration. *)
let progression width base step count =
  let elements =
    List.init count (fun i ->
        Word.add (Wo.to_word base)
          (Word.mul (Wo.to_word step) (Word.of_int ~width i))
        |> Wo.of_word)
  in
  ( Clp.create ~width ~step ~cardn:(Wo.of_int ~width:(width + 1) count) base,
    elements )

let operands width =
  let w = Wo.of_int ~width in
  let half = Wo.half width and ones = Wo.ones width in
  let finite =
    [
      (w 0, w 1, 1);
      (w 1, w 1, 1);
      (w 8, w 1, 1);
      (w 0xaa, w 1, 1);
      (half, w 1, 1);
      (ones, w 1, 1);
      (w 0, w 1, 4);
      (w 1, w 1, 17);
      (w 16, w 1, 32);
      (w 0, w 1, 100);
      (Wo.sub half (w 3), w 1, 7);
      (Wo.sub ones (w 8), w 1, 9);
      (ones, w 1, 3);
      (w 0, w 2, 40);
      (w 2, w 4, 12);
      (w 8, w 8, 10);
      (w 1, w 3, 20);
      (w 3, w 5, 15);
      (w 8, w 16, 6);
      (w 4, w 12, 9);
      (w 8, w 16, 2);
      (Wo.sub ones (w 4), w 8, 4);
      (w 0, half, 2);
      (w 1, half, 2);
    ]
    @ if width = 8 then [ (w 200, w 1, 157); (w 3, w 11, 24) ] else []
  in
  List.map (fun (base, step, count) -> progression width base step count) finite
  @ List.map
      (fun (base, step) ->
        let indices = List.init 64 w @ [ half; Wo.pred ones; ones ] in
        let points = List.map (fun i -> Wo.add base (Wo.mul step i)) indices in
        ( Clp.create ~width ~step
            ~cardn:(Wo.dom_size ~width:(width + 1) width)
            base,
          points ))
      [ (w 0, w 1); (w 0, w 4); (w 6, w 6) ]

let tests =
  [
    case
      "AND preserves concrete results for finite, wrapped, strided and full \
       sets" (fun () ->
        let check_pair wa (a, xs) wb (b, ys) =
          let width = max wa wb in
          let extend x = Word.extract_exn ~hi:(width - 1) (Wo.to_word x) in
          let clp = Clp.logand a b
          and ws = Ws.logand (Ws.of_clp a) (Ws.of_clp b) in
          List.iter
            (fun x ->
              List.iter
                (fun y ->
                  let expected =
                    Word.logand (extend x) (extend y) |> Wo.of_word
                  in
                  if not (Clp.elem expected clp && Ws.elem expected ws) then
                    Alcotest.failf "%a AND %a excludes %a" Wo.pp x Wo.pp y Wo.pp
                      expected)
                ys)
            xs
        in
        List.iter
          (fun width ->
            let rec pairs = function
              | [] -> ()
              | a :: rest ->
                  List.iter (check_pair width a width) (a :: rest);
                  pairs rest
            in
            pairs (operands width))
          widths;
        List.iter
          (fun (wa, wb) ->
            let a =
              progression wa (Wo.of_int ~width:wa 1) (Wo.of_int ~width:wa 1) 17
            in
            let b =
              progression wb (Wo.of_int ~width:wb 2) (Wo.of_int ~width:wb 4) 12
            in
            check_pair wa a wb b;
            check_pair wb b wa a)
          [ (8, 16); (16, 32); (32, 64) ]);
    case
      "circular interval intersections equal ordinary integer interval \
       intersections" (fun () ->
        let rng = Random.State.make [| 0x5eed2026 |] in
        List.iter
          (fun width ->
            let n = modulus width in
            let interval start length =
              Clp.create ~width ~step:(Wo.one width)
                ~cardn:(Wo.of_z length (width + 1))
                (Wo.of_z start width)
            in
            let arcs start length =
              let length = Z.min length n in
              let stop = Z.add start length in
              if Z.equal length Z.zero then []
              else if Z.leq stop n then [ (start, Z.pred stop) ]
              else [ (start, Z.pred n); (Z.zero, Z.pred (Z.sub stop n)) ]
            in
            let check_pair (a, alen) (b, blen) =
              let expected =
                List.concat_map
                  (fun (lo, hi) ->
                    List.filter_map
                      (fun (lo', hi') ->
                        let lo = Z.max lo lo' and hi = Z.min hi hi' in
                        if Z.gt lo hi then None
                        else Some (interval lo Z.(succ (sub hi lo))))
                      (arcs b blen))
                  (arcs a alen)
                |> List.fold_left Clp.union (Clp.bottom width)
              in
              check_clp
                (Printf.sprintf "intersection at width %d" width)
                expected
                (Clp.intersection (interval a alen) (interval b blen))
            in
            let z = Z.of_int in
            let cases =
              [
                (z 10, z 41);
                (z 20, z 11);
                (z 40, z 41);
                (z 21, z 10);
                (z 42, z 1);
                (Z.sub n (z 56), z 156);
                (Z.sub n (z 36), z 96);
                (Z.sub n (z 36), z 300);
                (z 5, Z.pred n);
                (z 4, Z.pred n);
                (z 3, z 4);
                (z 0, z 9);
                (Z.sub n (z 4), z 9);
                (z 0, n);
                (z 0, Z.zero);
              ]
            in
            List.iter (fun a -> List.iter (check_pair a) cases) cases;
            for
              _ = 1
              to if width <= 16 then 400 else if width = 32 then 200 else 80
            do
              let draw () =
                ( Wo.to_z (random_word rng width),
                  Wo.to_z (random_word rng width) )
              in
              check_pair (draw ()) (draw ())
            done)
          widths);
    case "strided intersections retain every known common value" (fun () ->
        List.iter
          (fun width ->
            let sets = operands width in
            List.iter
              (fun (a, xs) ->
                List.iter
                  (fun (b, ys) ->
                    let result = Clp.intersection a b in
                    List.iter
                      (fun x ->
                        if
                          List.exists (Wo.equal x) ys && not (Clp.elem x result)
                        then Alcotest.failf "intersection loses %a" Wo.pp x)
                      xs)
                  sets)
              sets)
          widths);
    case "rebuilding progressions and arbitrary lists preserves every input"
      (fun () ->
        let rng = Random.State.make [| 20260823 |] in
        let rebuild width points =
          let result = Clp.of_list ~width (List.sort_uniq Wo.compare points) in
          List.iter
            (fun point ->
              if not (Clp.elem point result) then
                Alcotest.failf "rebuild loses %a" Wo.pp point)
            points;
          result
        in
        List.iter
          (fun width ->
            List.iter
              (fun step ->
                let full = Z.div (modulus width) (Z.of_int step) in
                if
                  Z.leq full (Z.of_int 2048)
                  && Z.equal Z.(mul full (of_int step)) (modulus width)
                then begin
                  let original, points =
                    progression width (random_word rng width)
                      (Wo.of_int ~width step) (Z.to_int full)
                  in
                  check_clp "a full residue class rebuilds exactly" original
                    (rebuild width points)
                end;
                for _ = 1 to 40 do
                  let limit = Z.min (Z.of_int 2048) full |> Z.to_int in
                  let _, points =
                    progression width (random_word rng width)
                      (Wo.of_int ~width step)
                      (1 + Random.State.int rng limit)
                  in
                  ignore (rebuild width points)
                done)
              [ 1; 2; 3; 4; 5; 6; 7; 8 ])
          widths;
        for _ = 1 to 300 do
          let width = List.nth widths (Random.State.int rng 4) in
          ignore
            (rebuild width
               (List.init
                  (1 + Random.State.int rng 40)
                  (fun _ -> random_word rng width)))
        done);
  ]

let () = run "domain properties" [ ("properties", tests) ]
