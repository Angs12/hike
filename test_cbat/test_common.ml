(* Shared test infrastructure: check harness, BIR fixture builders, stderr capture, emitter runner, domain aliases. *)
open Bap.Std
open Bap_core_theory
module W = Word
module Clp = Cbat_clp
module Fs = Cbat_fin_set

module Wo = Cbat_word
module Ws = Cbat_clp_set_composite

(* Wrapped BIR-fixpoint library; siblings re-exported by cbat_vsa.mli. *)
module AI = Cbat_vsa.AI
module Mem = Cbat_vsa.Mem
module Vsa = Cbat_vsa

(* Memmap fusion pipeline under test. *)
module MK = Cbat_vsa.Mem.Key
module MV = Cbat_vsa.Mem.Val

(* Explicit anchored entry state (RSP = the symbolic segment base,
   offset 0 — the production universe, T3); fixtures pass it to the
   fixpoint so unit pins exercise the same representation the default
   entry seeds. *)
let anchored_entry () : AI.t =
  let rsp = Var.create ~is_virtual:false ~fresh:false "RSP" (Type.Imm 64) in
  let rbp = Var.create ~is_virtual:false ~fresh:false "RBP" (Type.Imm 64) in
  let e = AI.add_word AI.top ~key:rsp ~data:(Ws.stack_word_i64 0L) in
  AI.add_word e ~key:rbp ~data:(Ws.stack_word_i64 0L)

(* AI word environment from (var, word-set) binds over top. *)
let failures = ref 0

let check (name : string) (b : bool) : unit =
  if b then Printf.printf "ok: %s\n" name
  else (
    Printf.printf "FAIL: %s\n" name;
    incr failures)

let contains_substring (hay : string) (needle : string) : bool =
  let n = String.length hay and m = String.length needle in
  let rec go i = i + m <= n && (String.sub hay i m = needle || go (i + 1)) in
  m = 0 || go 0

(* Capture stderr emitted by [f] as a string. *)
let capture_stderr (f : unit -> unit) : string =
  let path = Filename.temp_file "cbat_cap" ".err" in
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
let fired (comp : string) (f : unit -> unit) : bool = contains_substring (capture_stderr f) comp
let w32 = Cbat_word.of_int ~width:32
let w33 = Cbat_word.of_int ~width:33
let w64 = Cbat_word.of_int ~width:64

(* create n (defaults) = singleton {n} *)
module IntLattice : Cbat_lattice_intf.S_val with type t = int = struct
  (* Local open: supplies bin_io helpers without shadowing (=) file-wide. *)
  open! Core_kernel

  type t = int [@@deriving bin_io, sexp, compare]

  let pp = Int.pp
  let meet = min
  let join = max
  let bottom = Int.min_value
  let top = Int.max_value
  let widen_join a b = if a = b then a else top
  let equal = ( = )
  let precedes = ( <= )
end

module Map = Cbat_map_lattice.Make_val (IntLattice) (IntLattice)

(* Every def is denoted (spec §2.1); all-tracked is the only mode. *)

let v64 (n : string) : var = Var.create ~is_virtual:false ~fresh:false n (Type.Imm 64)
let v1 (n : string) : var = Var.create ~is_virtual:false ~fresh:false n (Type.Imm 1)
let memv (n : string) : var = Var.create ~is_virtual:false ~fresh:false n (Type.Mem (`r64, `r8))

(* Fixture stack pointer. *)
let sp = v64 "RSP"

module Kb = Hike.Kb
module Sm = Hike.Stack_model
module Stl = Hike.Stack_to_locals
module Cu = Hike.Convutils
module B2l = Hike.Bil2llvm
module Hv = Hike.Vsa

(* Full-range 64-bit word; [w64] takes a native int. *)
