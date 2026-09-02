(* stageprof — the per-stage fixpoint breakdown (the Q6 harness).

   WHY: the fixpoint's per-visit cost is (denotation + join + equal + widen)
   plus the deep walk, and nothing in the tree could previously attribute
   time between them — which is how three separate changes this session got
   reported as "wins" while sitting inside measurement noise. The bar we
   agreed: a change is a perf win only if a NAMED stage moves, measured as
   the median of N interleaved rounds.

   The counters only exist in the vsa-debug profile (the production build
   links a no-op adapter), so this probe MUST run with:

     dune exec --profile vsa-debug zz_scratch_probe/stageprof.exe -- <bin>

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
