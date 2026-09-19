open Bap.Std
let () =
  ignore (Bap_main.init ~argv:[| Sys.executable_name |] () : (unit, _) result);
  let j = Jmp.create (Ret (Direct (Tid.create ()))) in
  Printf.printf "fresh: %s\n%!" (Jmp.to_string j);
  let b = Blk.Builder.create () in
  Blk.Builder.add_jmp b j;
  let blk = Blk.Builder.result b in
  Term.enum jmp_t blk |> Seq.iter ~f:(fun j -> Printf.printf "in blk: %s\n%!" (Jmp.to_string j));
  (* through Term.map blk_t (the Term-based rebuild path) *)
  let j2 = Jmp.create (Ret (Direct (Tid.create ()))) in
  let blk2 = Blk.create ~jmps:[ j2 ] () in
  Term.enum jmp_t blk2 |> Seq.iter ~f:(fun j -> Printf.printf "blk2: %s\n%!" (Jmp.to_string j))
