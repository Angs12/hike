(* The batch lift driver: N binaries through the hike chain in one
   process, so every once-per-process cost (BAP load, plugin dynlink,
   LLVM init) amortizes across the batch. Not a bap plugin — the
   pipeline scripts call it where a per-binary bap spawn dominates.

   Usage: hike_batch [--output-dir=DIR] [--prefix=P] [--timeout=SECS]
                     <binary>...
   Writes DIR/PREFIX<name>.ll per binary. Every binary runs; a
   failing binary never stops the batch. The exit code is nonzero iff
   any binary failed. *)

open Bap.Std

(* A per-binary timeout is a batch-continuation guard: the alarm
   interrupts the lift, the binary counts as failed, the rest run. *)
exception Timed_out

let timeout_after_secs () =
  Sys.set_signal Sys.sigalrm
    (Sys.Signal_handle (fun _ -> raise Timed_out))

let name_of file = Filename.basename file

let output_path ~dir ~prefix file =
  Filename.concat dir (prefix ^ name_of file ^ ".ll")

let remove_partial path =
  match Unix.stat path with
  | _ -> (try Unix.unlink path with Sys_error _ -> ())
  | exception _ -> ()

(* Runs the whole chain over one binary; the per-binary protocol rides
   the Hike_diag channel so scripts can split the stderr stream into
   per-binary diagnostics on the begin/end markers. *)
let lift_one ~timeout ~dir ~prefix file =
  let name = name_of file in
  let output = output_path ~dir ~prefix file in
  Hike.Diag.warn "batch: begin %s" name;
  let t0 = Unix.gettimeofday () in
  ignore (Unix.alarm timeout);
  let finish rc =
    ignore (Unix.alarm 0);
    let ms = (Unix.gettimeofday () -. t0) *. 1000. in
    Hike.Diag.warn "batch: end %s rc=%d ms=%.0f" name rc ms;
    if rc <> 0 then remove_partial output;
    rc
  in
  match Project.create (Project.Input.file ~loader:"llvm" ~filename:file) with
  | Error e ->
    Hike.Diag.warn "batch: %s: %s" name (Core.Error.to_string_hum e);
    finish 1
  | Ok proj -> (
    try finish (Hike.run_chain ~output proj; 0) with
    | Timed_out ->
      Hike.Diag.warn "batch: %s: timed out after %ds" name timeout;
      finish 124
    | exn ->
      Hike.Diag.warn "batch: %s: %s" name (Printexc.to_string exn);
      finish 1)

let fail usage msg =
  Hike.Diag.warn "batch: %s" msg;
  Hike.Diag.warn "batch: usage: %s" usage;
  exit 2

(* The Bap_main init the project machinery requires before the first
   project opens: it dynlinks the installed plugin world (llvm loader,
   x86 targets) and evaluates the extensions. Same pattern as the
   probe harnesses; the driver must run in that (dune exec) env. *)
let init_backends () =
  match Bap_main.init ~argv:[|Sys.executable_name|] () with
  | Ok () -> ()
  | Error e ->
    Hike.Diag.warn "batch: BAP init failed: %s"
      (Format.asprintf "%a" Bap_main.Extension.Error.pp e);
    exit 1

let () =
  timeout_after_secs ();
  init_backends ();
  let usage =
    "hike_batch [--output-dir=DIR] [--prefix=P] [--timeout=SECS] <binary>..."
  in
  let dir = ref "." in
  let prefix = ref "out_" in
  let timeout = ref 600 in
  let files = ref [] in
  let args = Sys.argv in
  for i = 1 to Array.length args - 1 do
    let a = args.(i) in
    let prefix_value ~flag v =
      let v = String.sub v (String.length flag) (String.length v - String.length flag) in
      if String.length v > 0 then v else fail usage ("missing value for " ^ flag)
    in
    if String.starts_with ~prefix:"--output-dir=" a then
      dir := prefix_value ~flag:"--output-dir=" a
    else if String.starts_with ~prefix:"--prefix=" a then
      prefix := prefix_value ~flag:"--prefix=" a
    else if String.starts_with ~prefix:"--timeout=" a then
      (match int_of_string_opt (prefix_value ~flag:"--timeout=" a) with
      | Some n when n > 0 -> timeout := n
      | _ -> fail usage "--timeout expects a positive integer")
    else if String.starts_with ~prefix:"-" a then fail usage ("unknown flag " ^ a)
    else files := a :: !files
  done;
  match List.rev !files with
  | [] -> fail usage "no input binaries"
  | files ->
    (try ignore (Unix.mkdir !dir 0o755) with
    | Unix.Unix_error (Unix.EEXIST, _, _) -> ());
    let t0 = Unix.gettimeofday () in
    let failures =
      Stdlib.List.fold_left
        (fun acc file -> acc + lift_one ~timeout:!timeout ~dir:!dir ~prefix:!prefix file)
        0 files
    in
    let wall_ms = (Unix.gettimeofday () -. t0) *. 1000. in
    let n = List.length files in
    Hike.Diag.warn "batch: %d/%d ok, wall %.0fms" (n - failures) n wall_ms;
    if failures > 0 then exit 1
