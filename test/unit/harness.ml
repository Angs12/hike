(* The unit harness: BAP initialization, Alcotest wiring (one group per pin),
   the assertion vocabulary, stderr capture, and the reset bracket that keeps
   tests deterministic. *)

open Bap.Std

(* BAP registers its Theory.Target facts only through the main entry; every
   test process initializes once, before any fixture is built.  The argv is the
   synthetic singleton so BAP never sees Alcotest's command line. *)
let initialized = ref false

let init () =
  if not !initialized then (
    initialized := true;
    match Bap_main.init ~argv:[| Sys.executable_name |] () with
    | Ok () -> ()
    | Error _ ->
      Format.eprintf "hike-test: Bap_main.init failed@.";
      exit 1)

exception Timeout of string

(* A test body that hangs would hang the whole module; the alarm turns the
   wait into an ordinary exception Alcotest records as a failure. *)
let with_timeout (secs : int) (f : unit -> unit) : unit =
  let handler = Sys.Signal_handle (fun _ -> raise (Timeout "test case timed out")) in
  let old = Sys.signal Sys.sigalrm handler in
  ignore (Unix.alarm secs);
  Fun.protect
    ~finally:(fun () ->
      ignore (Unix.alarm 0);
      Sys.set_signal Sys.sigalrm old)
    f

(* One Alcotest group per pin id: the group name is the stable, filterable id
   (`test_dce.exe test 'DCE-01'`), the case string is the human description.
   Alcotest records a raised exception as a failure and runs the next group, so
   one broken fixture never hides the rest of the module. *)
let pin ?(timeout = 300) (id : string) (desc : string) (f : unit -> unit) :
    unit Alcotest.test =
  (id, [ Alcotest.test_case desc `Quick (fun () -> with_timeout timeout f) ])

let run (name : string) (tests : unit Alcotest.test list) : unit =
  init ();
  Alcotest.run ~and_exit:true name tests

(* The assertion vocabulary.  A missing optional bound fails the pin. *)
let check (name : string) (b : bool) : unit = Alcotest.(check bool) name true b

let check_bound name o f = check name (match o with Some v -> f v | None -> false)

let contains_substring (hay : string) (needle : string) : bool =
  let n = String.length hay and m = String.length needle in
  let rec go i = i + m <= n && (String.sub hay i m = needle || go (i + 1)) in
  m = 0 || go 0

(* Capture stderr emitted by [f] as a string. *)
let capture_stderr (f : unit -> unit) : string =
  let path = Filename.temp_file "hike_cap" ".err" in
  let fd = Unix.openfile path [ Unix.O_WRONLY; Unix.O_TRUNC; Unix.O_CREAT ] 0o600 in
  let saved = Unix.dup Unix.stderr in
  Unix.dup2 fd Unix.stderr;
  Unix.close fd;
  (try f ()
   with e ->
     Unix.dup2 saved Unix.stderr;
     Unix.close saved;
     Sys.remove path;
     raise e);
  flush stderr;
  Unix.dup2 saved Unix.stderr;
  Unix.close saved;
  let ic = open_in path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  Sys.remove path;
  s

(* Did the not_implemented hit for [comp] log its stderr line while [f] ran? *)
let fired (comp : string) (f : unit -> unit) : bool =
  contains_substring (capture_stderr f) comp

(* Determinism: a production global a test must arm is restored by its bracket,
   which also runs when the body raises. *)
let protect ~(set : unit -> unit) ~(restore : unit -> unit) (f : unit -> unit) : unit =
  set ();
  Fun.protect ~finally:restore f
