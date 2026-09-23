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
    let facts =
      Hike.Kb.build ~block_envs:Tid.Map.empty
        ~block_addrs:(Core.Map.empty (module Addr)) ~target
    in
    let _envs, _sub', _ =
      Hike.Vsa.fixpoint target ~prog:(Program.create ~subs:[ sub ] ())
        ~symtab:None ~images:[]
        ~written:(Hike.Vsa.kill_summaries ~abi:facts.Hike.Kb.abi
                    (Program.create ~subs:[ sub ] ()))
        ~lift_at:(fun _ -> None)
        ~block_addrs:(Core.Map.empty (module Addr)) sub
      |> Base.Option.value ~default:(Tid.Map.empty, sub, Core.Map.empty (module Addr))
    in
    let t_total = Unix.gettimeofday () -. t0 in
    Printf.printf "STAGE producer (fixpoint)        %8.3fs   (the pass pays the solve and the completion rounds)\n"
      t_total;

    (* Decomposition: the VLA events are the shape test. *)
    let t0 = Unix.gettimeofday () in
    let _events =
      Hike.Promote.dynamic_alloc_tids_of ~facts:(Hike.Kb.build ~block_envs:Tid.Map.empty ~block_addrs:(Core.Map.empty (module Addr)) ~target) sub in
    let t_analyze = Unix.gettimeofday () -. t0 in
    Printf.printf "STAGE event-detect             %8.3fs\n" t_analyze;

    let t0 = Unix.gettimeofday () in
    let sol = Probe_common.run_sub_fixpoint sub in
    let t_fix = Unix.gettimeofday () -. t0 in
    Printf.printf "STAGE fixpoint (inline refines) %8.3fs\n" t_fix;

    (* Refinement is inline in the fixpoint; per-block IN-states are the solution. *)
    let t0 = Unix.gettimeofday () in
    let _tags = sol in
    let t_part = Unix.gettimeofday () -. t0 in
    Printf.printf "STAGE (merged, no post-pass)     %8.3fs\n" t_part;

    Printf.printf "STAGE walk+merge (tags)         (inside the producer — not separable through the Hike seam)\n";
    Printf.printf "STAGE stack_to_locals / dce     (separate pipeline passes — time via the pipeline, not this probe)\n";
    Printf.printf "TOTAL (pass 1, production)      %8.3fs\n" t_total;
    Printf.printf "TOTAL (pass 2, decomposition)   %8.3fs   (seed-detect+fixpoint)\n"
      (t_analyze +. t_fix +. t_part)