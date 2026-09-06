(* Non-convergence autopsy for Candidate 3.
   Runs the fixpoint on one sub; on Fixpoint_not_converged, dumps the
   vsa-debug STAGES counters + memo stats accumulated up to the trip.
   Usage: nc_autopsy.exe <binary> <subname> (vsa-debug profile only). *)

open Bap.Std
open Probe_common

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  init ();
  match args with
  | [] -> usage Sys.argv.(0) "<binary> <subname>"
  | [_] -> usage Sys.argv.(0) "<binary> <subname>"
  | path :: name :: _ ->
    let proj = load_project path in
    let prog = Project.program proj in
    let sub =
      match find_sub prog name with
      | Some s -> s
      | None -> usage Sys.argv.(0) (Printf.sprintf "sub %s not found" name)
    in
    let prog' = Program.create ~subs:[ sub ] () in
    let t0 = Unix.gettimeofday () in
    (try
       let _sol = Cbat_vsa.static_graph_vsa [] prog' sub (Cbat_vsa.init_sol sub) in
       Printf.printf "CONVERGED in %.3fs\n" (Unix.gettimeofday () -. t0);
       let (denote_t, denote_n, walk_t, walk_n, join_t, join_n, pops,
            blocks, truncs, max_pops, minor_words) =
         Vsa.Stages.stats ()
       in
       Printf.printf
         "STAGES-AT-SUCCESS denote %.3fs/%d walk %.3fs/%d join %.3fs/%d\n"
         denote_t denote_n walk_t walk_n join_t join_n;
       Printf.printf "WALKS-AT-SUCCESS pops %d truncs %d\n" pops truncs
     with Cbat_vsa.Fixpoint_not_converged (n, _, _) ->
       Printf.printf "TRIPPED after %d visits, %.3fs wall\n" n
         (Unix.gettimeofday () -. t0);
       let (denote_t, denote_n, walk_t, walk_n, join_t, join_n, pops,
            blocks, truncs, max_pops, minor_words) =
         Vsa.Stages.stats ()
       in
       Printf.printf
         "STAGES-AT-TRIP denote %.3fs/%d walk %.3fs/%d join %.3fs/%d\n" denote_t
         denote_n walk_t walk_n join_t join_n;
       Printf.printf "WALKS-AT-TRIP pops %d blocks %d truncs %d max_pops %d\n"
         pops blocks truncs max_pops;
       Printf.printf "GC-AT-TRIP minor_words %.0f\n" minor_words;
       let (lookups, hits, stale, stores, _empty) =
         Vsa.Stages.memo_stats ()
       in
       Printf.printf "MEMO-AT-TRIP lookups %d hits %d stale %d stores %d\n"
         lookups hits stale stores)
