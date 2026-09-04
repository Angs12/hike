(* Per-stage pipeline wall-time breakdown.
   Usage: stage_timer.exe <binary> [subname] (default "main").
   Pass 1 times the whole producer; pass 2 decomposes it on a second fixpoint. *)

open Bap.Std
open Probe_common

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  init ();
  match args with
  | [] -> usage Sys.argv.(0) "<binary> [subname]"
  | path :: rest ->
    let proj = load_project path in
    let prog = Project.program proj in
    let target = Project.target proj in
    let sp = sp_of proj in
    let name = match rest with n :: _ -> n | [] -> "main" in
    let sub =
      match find_sub prog name with
      | Some s -> s
      | None -> usage Sys.argv.(0) (Printf.sprintf "<binary> [subname] — %s not found" name)
    in
    Printf.printf "=== stage_timer %s (%s) ===\n" (Filename.basename path)
      (Sub.name sub);

    (* Production single call: the total the pass pays per sub. *)
    let t0 = Unix.gettimeofday () in
    let _info = Hike.Vsa.offsets_of_sub target sp sub in
    let t_total = Unix.gettimeofday () -. t0 in
    Printf.printf "STAGE producer(offsets_of_sub)  %8.3fs   (whole producer: fixpoint+walk+merge+regions+split_plan — what the pass pays)\n"
      t_total;

    (* Decomposition over a second fixpoint on the same sub. *)
    let t0 = Unix.gettimeofday () in
    let _alloc_tids = Cbat_vsa.Cbat_extraction.detect_dynamic_alloc sp sub in
    let t_analyze = Unix.gettimeofday () -. t0 in
    Printf.printf "STAGE seed-detect              %8.3fs\n" t_analyze;

    let prog' = Program.create ~subs:[ sub ] () in
    let t0 = Unix.gettimeofday () in
    let sol = Vsa.static_graph_vsa [] prog' sub (Vsa.init_sol sub) in
    let t_fix = Unix.gettimeofday () -. t0 in
    Printf.printf "STAGE fixpoint (inline refines) %8.3fs\n" t_fix;

    (* Refinement is inline in the fixpoint; per-block IN-states are the solution. *)
    let t0 = Unix.gettimeofday () in
    let _tags = sol in
    let t_part = Unix.gettimeofday () -. t0 in
    Printf.printf "STAGE (merged, no post-pass)     %8.3fs\n" t_part;

    Printf.printf "STAGE walk+merge (tags)         (inside offsets_of_sub — not separable through the Hike seam)\n";
    Printf.printf "STAGE stack_to_locals / dce     (separate pipeline passes — time via the pipeline, not this probe)\n";
    Printf.printf "TOTAL (pass 1, production)      %8.3fs\n" t_total;
    Printf.printf "TOTAL (pass 2, decomposition)   %8.3fs   (seed-detect+fixpoint)\n"
      (t_analyze +. t_fix +. t_part)