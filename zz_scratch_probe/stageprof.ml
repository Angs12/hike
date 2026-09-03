(* Per-stage fixpoint cost breakdown; vsa-debug profile only.
   Usage: stageprof.exe <binary> [subname ...] *)

open Bap.Std
open Probe_common

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  init ();
  match args with
  | [] -> usage Sys.argv.(0) "<binary> [subname ...]"
  | path :: rest ->
    Printf.printf "stage counters enabled: %b\n" Cbat_vsa.Stages.enabled;
    let proj = load_project path in
    let prog = Project.program proj in
    let sp = sp_of proj in
    let names = if rest = [] then [ "main" ] else rest in
    let rec go = function
      | [] -> ()
      | name :: rest ->
        (match find_sub prog name with
        | None -> Printf.printf "sub %s: not found\n" name
        | Some sub ->
          let sub' = Hike.Relevance.analyze sp sub in
          let prog' = Program.create ~subs:[ sub' ] () in
          let t0 = Unix.gettimeofday () in
          let _ = Vsa.static_graph_vsa [] prog' sub' (Vsa.init_sol sub') in
          let dt = Unix.gettimeofday () -. t0 in
          Printf.printf "  fixpoint total %.3fs\n%!" dt);
        go rest
    in
    go names
