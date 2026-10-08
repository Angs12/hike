(* Deterministic small-width soundness audit; machine-width regressions are
   pinned in test/unit/test_pieces.ml. *)
module W = Cbat_word
module C = Cbat_clp
module P = C.Pieces

let pp p = String.concat " | " (List.map (Format.asprintf "%a" C.pp) (P.to_list p))

let () =
  Random.init 20261008;
  let failures = Hashtbl.create 16 in
  let checked = ref 0 in
  let fail op a b r x =
    if not (Hashtbl.mem failures op) then begin
      Hashtbl.add failures op ();
      Printf.printf "FAIL %s witness=%d\n  a=%s\n  b=%s\n  r=%s\n%!" op x (pp a) (pp b) (pp r)
    end in
  List.iter (fun width ->
    let size = 1 lsl width in
    let word = W.of_int ~width in
    let make () =
      let raws = List.init (1 + Random.int 6) (fun _ ->
        let base = word (Random.int size) in
        let step = word (Random.int (min size 12)) in
        let direction = Random.int 6 in
        let p = match direction with
        | 0 -> C.create_ascending ~width ~base ~step
        | 1 -> C.create_descending ~width ~base ~step
        | 2 -> C.infinite (base, step)
        | _ -> C.create ~width ~step
                 ~cardn:(W.of_int ~width:(width + 1) (1 + Random.int 20)) base in
        if direction < 2 then begin
          let base = W.to_int_exn base and step = W.to_int_exn step in
          for x = 0 to size - 1 do
            incr checked;
            let expected =
              if step = 0 then x = base
              else if direction = 0 then x >= base && (x - base) mod step = 0
              else x <= base && (base - x) mod step = 0 in
            if expected <> C.elem (word x) p then
              fail "directional membership" (P.of_progression p) (P.bottom width) (P.of_progression p) x
          done
        end;
        p) in
      let p = List.fold_left (fun acc q -> P.union acc (P.of_progression q)) (P.bottom width) raws in
      List.iter (fun q -> for x = 0 to size - 1 do
        if C.elem (word x) q && not (P.elem (word x) p) then
          fail "normalize" (P.of_progression q) (P.bottom width) p x
      done) raws;
      if List.exists C.is_wrapped (P.to_list p) then fail "wrapped" p p p 0;
      p in
    for _trial = 1 to 2000 do
      let a = make () and b = make () in
      let values p = Array.init size (fun x -> P.elem (word x) p) in
      let va = values a and vb = values b in
      List.iter (fun pa -> List.iter (fun pb ->
        let result = C.intersection pa pb in
        for x = 0 to size - 1 do
          incr checked;
          if C.elem (word x) pa && C.elem (word x) pb && not (C.elem (word x) result) then
            fail "core intersection" (P.of_progression pa) (P.of_progression pb) (P.of_progression result) x
        done) (P.to_list b)) (P.to_list a);
      let operations =
        [ "union", P.union a b, (fun x -> va.(x) || vb.(x));
          "intersection", P.intersection a b, (fun x -> va.(x) && vb.(x));
          "diff", P.diff a b, (fun x -> va.(x) && not vb.(x));
          "widen", P.widen_join a b, (fun x -> va.(x) || vb.(x));
          "extrapolate", P.extrapolate_steps ~steps:2 a b, (fun x -> va.(x) || vb.(x)) ] in
      List.iter (fun (name, result, required) ->
        for x = 0 to size - 1 do
          incr checked;
          if required x && not (P.elem (word x) result) then fail name a b result x
        done) operations;
      if P.precedes a b then
        for x = 0 to size - 1 do
          if va.(x) && not vb.(x) then fail "precedes" a b b x
        done;
      let card = W.to_int_exn (P.cardinality a) in
      let actual = Array.fold_left (fun n present -> if present then n + 1 else n) 0 va in
      if card < actual then fail "cardinality" a b a actual
    done) [4;5;8];
  Printf.printf "checked=%d failing_operations=%d\n%!" !checked (Hashtbl.length failures);
  if Hashtbl.length failures > 0 then exit 1
