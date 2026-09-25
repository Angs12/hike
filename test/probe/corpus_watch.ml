(* Corpus assert-watch driver: runs the full VSA fixpoint per sub of each argv binary.
   Usage: dune exec test/probe/corpus_watch.exe -- <binary> [<binary> ...] *)

open Bap.Std
open Probe_common

let () = Printexc.record_backtrace true

(* Slow-sub threshold, seconds. *)
let slow_threshold = 10.0

type outcome =
  | Ok of float              (* fixpoint wall time, seconds *)
  | Crash of string * string (* exception description * backtrace *)

(* One sub, one full fixpoint on the raw sub (spec §2.1). *)
let run_sub (sub : sub term) : outcome =
  let t0 = Unix.gettimeofday () in
  try
    let _sol = Probe_common.run_sub_fixpoint sub in
    let t1 = Unix.gettimeofday () in
    Ok (t1 -. t0)
  with e ->
    Crash (describe_exn e, Printexc.get_backtrace ())

type bin_report = {
  bname : string;
  mutable nsubs : int;
  mutable nok : int;
  mutable ncrashes : int;
  mutable nloadfail : int;
  mutable ftime : float;          (* summed fixpoint time, seconds *)
  mutable slow : (string * float) list;
}

let run_binary (path : string) : bin_report =
  let r = { bname = path; nsubs = 0; nok = 0; ncrashes = 0;
            nloadfail = 0; ftime = 0.0; slow = [] } in
  let run_one sub =
    let tid = Term.tid sub in
    let name = Sub.name sub in
    r.nsubs <- r.nsubs + 1;
    match run_sub sub with
    | Ok dt ->
      r.nok <- r.nok + 1;
      r.ftime <- r.ftime +. dt;
      if dt > slow_threshold then r.slow <- (name, dt) :: r.slow;
      Printf.printf "%s\t%s\t%s\tOK\t%.1fs\n" path name (Tid.to_string tid) dt
    | Crash (es, bt) ->
      r.ncrashes <- r.ncrashes + 1;
      Printf.printf "%s\t%s\t%s\tCRASH\t%s\n" path name (Tid.to_string tid) es;
      (match bt with
       | "" -> ()
       | _ -> Printf.printf "  backtrace:\n%s\n" bt)
  in
  match Probe_common.ws_run_binary path run_one with
  | Ok _ -> flush stdout; r
  | Error (Probe_common.Load_error e) ->
    r.nloadfail <- 1;
    ws_load_fail path e;
    r
  | Error (Probe_common.Run_error e) ->
    r.nloadfail <- 1;
    ws_load_exn path e;
    r

let () =
  let paths = List.tl (Array.to_list Sys.argv) in
  match paths with
  | [] -> ws_usage Sys.argv.(0)
  | _ ->
    (* Init the BAP environment (loads plugins, incl. the x86 backend). *)
    ws_init "corpus_watch";
    Printf.printf "=== corpus watch (gate-free) ===\n";
    flush stdout;
    let reports = List.map run_binary paths in
    Printf.printf "\n=== corpus watch summary ===\n";
    Printf.printf "%-28s %7s %6s %8s %10s %10s\n"
      "binary" "subs" "ok" "crashes" "loadfail" "ftime_s";
    List.iter
      (fun r ->
        Printf.printf "%-28s %7d %6d %8d %10d %10.1f\n"
          (Filename.basename r.bname) r.nsubs r.nok r.ncrashes r.nloadfail
          r.ftime;
        if r.slow <> [] then
          Printf.printf "  slow subs (>%.0fs): %s\n" slow_threshold
            (String.concat "; "
               (List.map (fun (n, t) -> Printf.sprintf "%s(%.1fs)" n t) r.slow)))
      reports;
    let crashes = List.fold_left (fun acc r -> acc + r.ncrashes) 0 reports in
    let loadfails = List.fold_left (fun acc r -> acc + r.nloadfail) 0 reports in
    ws_finish ~pass:"CORPUS WATCH: PASS (no crashes)"
      ~fail:"CORPUS WATCH: FAIL (crashes present)" crashes loadfails
