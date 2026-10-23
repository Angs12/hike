(* hike <binary> [-o <out.ll>]: lifts an x86-64 ELF to LLVM IR
   with Hike's discovery as the sole decoder (ADR 0032).  The project is
   loaded without BAP's disassembly and runs the plugin's pass chain. *)

open Bap.Std
open Bap_core_theory

let usage () =
  Hike.Diag.warn "usage: hike <binary> --signatures <file> [--signatures <file>]... [-o <out.ll>]";
  exit 2

let refuse fmt = Printf.ksprintf (fun s -> Hike.Diag.warn "%s" s; exit 1) fmt

let arguments () =
  let rec go binary out signatures = function
    | [] -> (binary, out, List.rev signatures)
    | "-o" :: file :: rest -> go binary (Some file) signatures rest
    | "--signatures" :: file :: rest -> go binary out (file :: signatures) rest
    | arg :: rest when binary = None && not (String.starts_with ~prefix:"-" arg) ->
      go (Some arg) out signatures rest
    | _ -> usage () in
  match go None None [] (Array.to_list Sys.argv |> List.tl) with
  | Some binary, out, signatures ->
    (binary, Option.value out ~default:(Filename.basename binary ^ ".ll"), signatures)
  | None, _, _ -> usage ()

(* The GC parameters the bap front end sets: the lift's memory profile
   is the plugin path's. *)
let setup_gc () =
  Gc.set { (Gc.get ()) with
           minor_heap_size = 2 * 1024 * 1024;
           major_heap_increment = 64 * 1024 * 1024 }

(* An error's own message, without the backtrace BAP attaches. *)
let message err =
  match Core.Error.sexp_of_t err with
  | Sexplib0.Sexp.Atom m -> m
  | Sexplib0.Sexp.List (Sexplib0.Sexp.Atom m :: Sexplib0.Sexp.Atom detail :: _) ->
    m ^ ": " ^ detail
  | Sexplib0.Sexp.List (Sexplib0.Sexp.Atom m :: _) -> m
  | sexp -> Sexplib0.Sexp.to_string sexp

(* Whether the lifted program defines a function: an empty module is a
   refusal, never an output. *)
let defines_code proj =
  Term.enum sub_t (Project.program proj)
  |> Seq.exists ~f:(fun sub -> not (Seq.is_empty (Term.enum blk_t sub)))

let () =
  let binary, out, signature_files = arguments () in
  if not (Sys.file_exists binary) || Sys.is_directory binary then
    refuse "cannot read %s" binary;
  setup_gc ();
  (match Bap_main.init ~name:"hike" ~argv:[| Sys.executable_name |] () with
   | Ok () -> ()
   | Error err ->
     refuse "BAP initialization failed: %s"
       (Format.asprintf "%a" Bap_main.Extension.Error.pp err));
  let proj =
    match Hike.Drive.load binary with
    | Ok proj -> proj
    | Error err -> refuse "cannot load %s: %s" binary (message err)
  in
  let target = Project.target proj in
  if not (Hike.Abi.is_primary_target target) then
    refuse "%s: target %s is not x86_64-gnu-elf" binary
      (KB.Name.to_string (Theory.Target.name target));
  (* Without signatures the lift cannot tell which imports never return. *)
  if signature_files = [] then
    refuse "no signatures: pass --signatures FILE (data/glibc.sexp for glibc)";
  let signatures =
    match Hike.Signatures.load signature_files with
    | Ok db -> db
    | Error err -> refuse "signatures: %s" (message err)
  in
  match Hike.lift ~signatures proj with
  | exception exn -> refuse "lifting %s failed: %s" binary (Printexc.to_string exn)
  | lifted when not (defines_code lifted) -> refuse "%s: no function was discovered" binary
  | lifted -> (
    match Hike.emit out lifted with
    | () -> ()
    | exception exn -> refuse "emitting %s failed: %s" out (Printexc.to_string exn))
