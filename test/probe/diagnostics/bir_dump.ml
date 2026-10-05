(* Pipeline BIR dump: prints a sub's blocks after chosen pass stages.
   Usage: bir_dump.exe <binary> <subname> <stage>  (stage: fp|split|ssa|dce) *)

open Bap.Std
open Probe_common

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  init ();
  match args with
  | [ path; name; stage ] ->
    let proj = load_project path in
    let prog = production_input proj in
    let target = Project.target proj in
    let prog = Hike.Fp.run_program prog in
    let prog =
      match stage with
      | "fp" -> prog
      | _ ->
        (* the vsa/attribution stages run inside the plugin; the caller
           wants post-split/ssa/dce shapes, which need the full solve *)
        failwith "stage needs the full pipeline; use fp"
    in
    (match find_sub prog name with
     | Some sub ->
       Term.enum blk_t sub
       |> Seq.iter ~f:(fun b ->
             Printf.printf "== blk %s ==\n%s" (Tid.name (Term.tid b))
               (blk_bil_to_string b))
     | None -> Printf.printf "sub %s not found\n" name);
    ignore target
  | _ -> usage Sys.argv.(0) "<binary> <subname> fp"
