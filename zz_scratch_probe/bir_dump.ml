(* T13 lane diagnostic: dump the lifted BIR of every sub (or the named
   subs) — the flag-effects table's ground-truth source.  Usage:
     bir_dump.exe <binary> [name1,name2,...]
   No names: every sub.  Prints defs and jmps per block. *)

open Bap.Std
open Probe_common

let () =
  init ();
  let path, wanted =
    match Sys.argv with
    | [| _; path |] -> (path, [])
    | [| _; path; ns |] ->
      (path, String.split_on_char ',' ns
             |> Base.List.filter ~f:(fun s -> not (Base.String.is_empty s)))
    | _ -> Printf.printf "usage: bir_dump.exe <binary> [names]\n"; exit 0
  in
  let proj = load_project path in
  let prog = Project.program proj in
  let subs =
    all_subs prog
    |> Base.List.filter ~f:(fun s ->
        match wanted with
        | [] -> true
        | _ ->
          Base.List.exists wanted ~f:(fun n ->
              Base.String.is_substring (Sub.name s) ~substring:n))
  in
  Base.List.iter subs ~f:(fun s ->
      Printf.printf "=== sub %s\n" (Sub.name s);
      Term.enum blk_t s
      |> Seq.iter ~f:(fun b ->
          Printf.printf "-- blk %s\n" (Tid.name (Term.tid b));
          Term.enum def_t b
          |> Seq.iter ~f:(fun d -> Printf.printf "  %s\n" (def_to_string d));
          Term.enum jmp_t b
          |> Seq.iter ~f:(fun j ->
              let cond = Format.asprintf "%a" Exp.pp (Jmp.cond j) in
              Printf.printf "  %s  if %s\n" (jmp_to_string j) cond)))
