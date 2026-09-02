(* stage_timer — the profiling driver: the per-stage pipeline wall-time
   breakdown. Recreated 2026-08-31 (Item 1 of the architecture program).

   Usage: stage_timer.exe <binary> [subname]   (default subname "main")

   Pass 1 — the PRODUCTION single-call path: [Hike.Vsa.offsets_of_sub] — the
   whole producer (relevance + fixpoint+views + partitioned + walk+merge +
   regions + split_plan), the TOTAL the pass pays per sub.

   Pass 2 — the decomposition the Hike seam exposes, on the SAME sub (a
   second fixpoint): analyze / fixpoint+views / partitioned. The
   walk+merge (tag) stage is INSIDE offsets_of_sub and is not
   separable through the seam — it is labeled, not faked.
   [stack_to_locals] and [dce] are SEPARATE pipeline passes (not inside
   the producer); time them with the pipeline, not with this probe.

   Pair with `perf record --call-graph dwarf -- dune exec
   zz_scratch_probe/stage_timer.exe -- <bin> <subname>` (the exe links -g). *)

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

    (* Pass 1: the production single call. *)
    let t0 = Unix.gettimeofday () in
    let _info = Hike.Vsa.offsets_of_sub target sp sub in
    let t_total = Unix.gettimeofday () -. t0 in
    Printf.printf "STAGE producer(offsets_of_sub)  %8.3fs   (whole producer: relevance+fixpoint+views+partitioned+walk+merge+regions+split_plan — what the pass pays)\n"
      t_total;

    (* Pass 2: the decomposition (second fixpoint over the same sub). *)
    let t0 = Unix.gettimeofday () in
    let sub' = Hike.Relevance.analyze sp sub in
    let t_analyze = Unix.gettimeofday () -. t0 in
    Printf.printf "STAGE analyze                   %8.3fs\n" t_analyze;

    let prog' = Program.create ~subs:[ sub' ] () in
    let t0 = Unix.gettimeofday () in
    let sol = Vsa.static_graph_vsa [] prog' sub' (Vsa.init_sol sub') in
    let t_fix = Unix.gettimeofday () -. t0 in
    Printf.printf "STAGE fixpoint (inline refines) %8.3fs\n" t_fix;

    (* The fused world: the refinement is INLINE in the fixpoint (there is no
       separate partitioned-states stage); the per-block TAG states are the
       solution's IN-states. *)
    let t0 = Unix.gettimeofday () in
    let _tags = sol in
    let t_part = Unix.gettimeofday () -. t0 in
    Printf.printf "STAGE (merged, no post-pass)     %8.3fs\n" t_part;

    Printf.printf "STAGE walk+merge (tags)         (inside offsets_of_sub — not separable through the Hike seam)\n";
    Printf.printf "STAGE stack_to_locals / dce     (separate pipeline passes — time via the pipeline, not this probe)\n";
    Printf.printf "TOTAL (pass 1, production)      %8.3fs\n" t_total;
    Printf.printf "TOTAL (pass 2, decomposition)   %8.3fs   (analyze+fixpoint+views+partitioned)\n"
      (t_analyze +. t_fix +. t_part)