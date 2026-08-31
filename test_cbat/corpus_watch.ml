(* test_cbat/corpus_watch.ml — CORPUS ASSERT-WATCH driver for the CBAT VSA
   port (src/cbat_vsa/).

   Usage:  dune exec test_cbat/corpus_watch.exe -- <binary> [<binary> ...]

   For each binary on argv:
     - load it as a BAP Project (Project.create (Project.Input.file
       ~filename:path));
     - enumerate ALL subs of the program;
     - for EACH sub, run the full VSA fixpoint exactly the way the D4-9
       test does (test_cbat/test_cbat.ml:581):
         Vsa.static_graph_vsa [] ctx sub (Vsa.init_sol sub)
     - every sub's fixpoint run is wrapped in try/with; a crash is
       reported with the exact exception (Assert_failure location, Failure
       msg, Invalid_argument msg, anything else) and the backtrace.

   The "hike: cbat_vsa: not_implemented <component> (degrading to top)"
   warnings are Format.eprintf'd to stderr by the vendored code
   (cbat_vsa_utils.ml, policy #5) and flow through untouched; the caller
   script counts them per binary from the stderr file.

   Exit code: 0 if no fixpoint crash and every binary loaded; 1 otherwise.
   Per-binary wall-clock timeout (300s) is the caller script's business,
   not the driver's. *)

open Bap.Std

(* Same module aliases as the D4-9 test (test_cbat.ml:44-46); the fixpoint
   entry point is Cbat_vsa.static_graph_vsa. *)
module AI = Cbat_vsa.AI
module Mem = Cbat_vsa.Mem
module Vsa = Cbat_vsa

(* hike port: P2d-1b (lane B) — the relevance-restriction analyzer.
   Each sub is run through [Hike_vsa_relevance.analyze] before the
   fixpoint (it tags the relevant defs and arms the restriction
   switch); the env toggle [HIKE_VSA_RESTRICTION=0] skips analyze
   (restriction OFF measurement path, byte-identical to the pre-P2d
   behavior).  [Hike_vsa_relevance] is hike's production relevance pass
   (src/hike_vsa_relevance.ml), reached through the wrapped [hike]
   library's flat module name; [sp] comes from the project target. *)
module Relevance = Hike.Relevance

(* [restriction_on]: default ON; HIKE_VSA_RESTRICTION=0 disables. *)
let restriction_on () : bool =
  match Sys.getenv_opt "HIKE_VSA_RESTRICTION" with
  | Some "0" -> false
  | _ -> true

let () = Printexc.record_backtrace true

(* A sub's fixpoint run is "suspiciously long" if it exceeds this. *)
let slow_threshold = 10.0

type outcome =
  | Ok of float              (* fixpoint wall time, seconds *)
  | Crash of string * string (* exception description * backtrace *)

let describe_exn (e : exn) : string =
  match e with
  | Assert_failure (file, line, col) ->
    Printf.sprintf "Assert_failure (%s:%d:%d)" file line col
  | Failure msg -> Printf.sprintf "Failure(%s)" msg
  | Invalid_argument msg -> Printf.sprintf "Invalid_argument(%s)" msg
  | _ -> Printexc.to_string e

(* One sub, one full fixpoint — the D4-9 invocation shape, with the
   relevance-analyze hookup: the sub is tagged by
   [Relevance.analyze] first (which also arms the restriction), then
   the fixpoint runs on the TAGGED sub inside a program carrying the
   tagged sub (the consumer contract). *)
let run_sub (sp : var) (prog : program term) (sub : sub term) : outcome =
  let t0 = Unix.gettimeofday () in
  try
    let sub' = Relevance.analyze sp sub in
    let prog' = Program.create ~subs:[ sub' ] () in
    let _sol = Vsa.static_graph_vsa [] prog' sub' (Vsa.init_sol sub') in
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
  try
    match Project.create (Project.Input.file ~loader:"llvm" ~filename:path) with
    | Error e ->
      r.nloadfail <- 1;
      Printf.printf "LOAD-FAIL\t%s\t%s\n" path (Core_kernel.Error.to_string_hum e);
      flush stdout;
      r
    | Ok proj ->
      let prog = Project.program proj in
      let sp = Hike.Target.sp (Project.target proj) in
      Term.enum sub_t prog
      |> Seq.iter ~f:(fun sub ->
          let tid = Term.tid sub in
          let name = Sub.name sub in
          r.nsubs <- r.nsubs + 1;
          match run_sub sp prog sub with
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
             | _ -> Printf.printf "  backtrace:\n%s\n" bt));
      flush stdout;
      r
  with e ->
    (* Project.create / enumeration blew up (it catches most things
       itself, but not, e.g., the empty-input assert). *)
    r.nloadfail <- 1;
    Printf.printf "LOAD-FAIL\t%s\texception: %s\n" path (describe_exn e);
    flush stdout;
    r

let () =
  let paths = List.tl (Array.to_list Sys.argv) in
  match paths with
  | [] ->
    Printf.printf "usage: %s <binary> [<binary> ...]\n" Sys.argv.(0);
    flush stdout;
    exit 0
  | _ ->
    (* Initializes the BAP environment (loads the installed plugins,
       incl. the x86 disassembler backend). *)
     (match Bap_main.init ~argv:[|Sys.executable_name|] () with
      | Ok () -> ()
      | Error failed ->
        Format.eprintf "corpus_watch: BAP initialization failed: %a@\n%!"
          Bap_main.Extension.Error.pp failed;
        exit 1);
    Printf.printf "=== corpus watch (relevance restriction %s) ===\n"
      (if restriction_on () then "ON" else "OFF (HIKE_VSA_RESTRICTION=0)");
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
    Printf.printf "TOTAL: %d crashes, %d load failures\n" crashes loadfails;
    Printf.printf "%s\n"
      (if crashes = 0 && loadfails = 0 then
         "CORPUS WATCH: PASS (no crashes)"
       else "CORPUS WATCH: FAIL (crashes present)");
    flush stdout;
    exit (if crashes = 0 && loadfails = 0 then 0 else 1)
