(* The unit harness: BAP initialization, Alcotest wiring,
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
    match Bap_main.init ~requires:[ "disassembler" ] ~argv:[| Sys.executable_name |] () with
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

let case ?(timeout = 300) desc f =
  Alcotest.test_case desc `Quick (fun () -> with_timeout timeout f)

(* One Alcotest group per pin id: the group name is the stable, filterable id
   (`<suite>.exe test '<ID>'`), the case string is the human description.
   Alcotest records a raised exception as a failure and runs the next group, so
   one broken fixture never hides the rest of the module. *)
let pin ?timeout (id : string) (desc : string) (f : unit -> unit) :
    unit Alcotest.test =
  (id, [ case ?timeout desc f ])

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

(* A minimal x86-64 ELF over [code] at 0x400078 (its entry), with a .text
   section: binary fixtures need no compiler or external corpus.  [load]
   creates the project (default: BAP's, with its disassembly).  [data]
   adds one allocated [.rodata] section at [data_addr] for the fixtures
   that need a dispatch table outside the text. *)
let with_binary ?(pie = false) ?(data = "") ?(data_addr = 0x401000L)
    ?(load = fun file -> Project.create (Project.Input.load ~loader:"llvm" file))
    code f =
  let has_data = String.length data > 0 in
  let names =
    if has_data then "\000.text\000.rodata\000.shstrtab\000"
    else "\000.text\000.shstrtab\000"
  in
  let names_off = 120 + String.length code in
  (* With data the file keeps a page-aligned slot for it, so the single
     load segment maps it at [data_addr]; the headers follow the data. *)
  let data_off = if has_data then Int64.to_int (Int64.sub data_addr 0x400000L) else 0 in
  let sections_off =
    if has_data then data_off + String.length data
    else names_off + String.length names
  in
  let sections_off = (sections_off + 7) land lnot 7 in
  let section_count = if has_data then 4 else 3 in
  let bytes = Bytes.make (sections_off + section_count * 64) '\000' in
  let put off size value =
    for i = 0 to size - 1 do
      Bytes.set bytes (off + i)
        (Char.chr (Int64.to_int (Int64.logand
          (Int64.shift_right_logical value (8 * i)) 255L)))
    done in
  Bytes.blit_string "\x7fELF\x02\x01\x01" 0 bytes 0 7;
  put 16 2 (if pie then 3L else 2L); put 18 2 62L; put 20 4 1L;
  put 24 8 0x400078L; put 32 8 64L;
  put 40 8 (Int64.of_int sections_off);
  put 60 2 (Int64.of_int section_count);
  put 62 2 (Int64.of_int (section_count - 1));
  put 52 2 64L; put 54 2 56L; put 56 2 1L; put 58 2 64L;
  put 64 4 1L; put 68 4 5L;
  put 80 8 0x400000L; put 88 8 0x400000L;
  put 96 8 (Int64.of_int (Bytes.length bytes));
  put 104 8 (Int64.of_int (Bytes.length bytes)); put 112 8 4096L;
  Bytes.blit_string code 0 bytes 120 (String.length code);
  Bytes.blit_string names 0 bytes names_off (String.length names);
  if has_data then Bytes.blit_string data 0 bytes data_off (String.length data);
  let text = sections_off + 64 in
  put text 4 1L; put (text + 4) 4 1L; put (text + 8) 8 6L;
  put (text + 16) 8 0x400078L; put (text + 24) 8 120L;
  put (text + 32) 8 (Int64.of_int (String.length code));
  put (text + 48) 8 1L;
  let strings = if has_data then sections_off + 192 else sections_off + 128 in
  put strings 4 (if has_data then 15L else 7L);
  put (strings + 4) 4 3L;
  put (strings + 24) 8 (Int64.of_int names_off);
  put (strings + 32) 8 (Int64.of_int (String.length names));
  put (strings + 48) 8 1L;
  if has_data then begin
    let rodata = sections_off + 128 in
    put rodata 4 7L; put (rodata + 4) 4 1L; put (rodata + 8) 8 2L;
    put (rodata + 16) 8 data_addr;
    put (rodata + 24) 8 (Int64.of_int data_off);
    put (rodata + 32) 8 (Int64.of_int (String.length data));
    put (rodata + 48) 8 8L
  end;
  let file = Filename.temp_file "hike-drive" ".elf" in
  Fun.protect ~finally:(fun () -> Sys.remove file) (fun () ->
      let out = open_out_bin file in
      output_bytes out bytes;
      close_out out;
      if pie then begin
        let input = open_in_bin file in
        seek_in input 16;
        let low = input_byte input and high = input_byte input in
        close_in input;
        check "PIE fixture has an ET_DYN ELF header" (low = 3 && high = 0)
      end;
      match load file with
      | Ok project -> f project
      | Error error -> failwith (Core.Error.to_string_hum error))
