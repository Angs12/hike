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

(* Explicit anchored entry state (RSP = {0}); fixtures pass it to the fixpoint. *)
let anchored_entry () : AI.t =
  let rsp = Var.create ~is_virtual:false ~fresh:false "RSP" (Type.Imm 64) in
  let rbp = Var.create ~is_virtual:false ~fresh:false "RBP" (Type.Imm 64) in
  let e = AI.add_word AI.top ~key:rsp ~data:(Ws.singleton (Cbat_word.of_int ~width:64 0)) in
  AI.add_word e ~key:rbp ~data:(Ws.singleton (Cbat_word.of_int ~width:64 0))

(* AI word environment from (var, word-set) binds over top. *)
let mk_env binds = List.fold_left (fun e (v, ws) -> AI.add_word e ~key:v ~data:ws) AI.top binds

(* A conditional/terminal jump to an explicit target tid. *)
let mk_jmp_to tgt cond = Jmp.create ~cond (Goto (Direct tgt))

(* An unconditional jump to an explicit target tid. *)
let mk_goto (tgt : tid) : jmp term = Jmp.create (Goto (Direct tgt))

(* One block from a def list (phase 1 of the two-phase builder dance:
   tids are captured from the result before jumps are wired). *)
let blk_of_defs (defs : def term list) : blk term =
  let b = Blk.Builder.create () in
  List.iter (Blk.Builder.add_def b) defs;
  Blk.Builder.result b

(* Wire jumps onto a phase-1 block (phase 2: re-init, add jumps). *)
let with_jmps (b0 : blk term) (jmps : jmp term list) : blk term =
  let b = Blk.Builder.init ~copy_defs:true b0 in
  List.iter (Blk.Builder.add_jmp b) jmps;
  Blk.Builder.result b


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

(* Mem fixture: a singleton map holding one key/data cell. *)
let key_of ws =
  match Mem.Key.of_wordset ws with Some k -> k | None -> failwith "key_of"

let mk_mem ~key ~data =
  let k = key_of key in
  let v = Mem.Val.create data LittleEndian in
  Mem.add (Mem.top { Mem.addr_width = 32; Mem.addressable_width = 8 }) ~key:k ~data:v

(* Seed fixture: entry state with RSP/RBP at {0} plus an explicit frame. *)
let mk_seed_state rsp rbp frame () =
  AI.set_frame
    (AI.add_word
       (AI.add_word AI.top ~key:rsp ~data:(Ws.singleton (w64 0)))
       ~key:rbp
       ~data:(Ws.singleton (w64 0)))
    frame

(* VSA fixture builders (moved verbatim from test_vsa.ml). *)
let mk_counter_loop ~(exit_defs : var -> def term list) : var * Program.t * sub term * tid =
  let i = Var.create ~is_virtual:false ~fresh:false "i" (Type.Imm 32) in
  let t = Var.create ~is_virtual:false ~fresh:false "t" (Type.Imm 32) in
  let iv = Bil.Var i in
  let tv = Bil.Var t in
  let lt = Bil.BinOp (Bil.LT, iv, tv) in
  let nlt = Bil.UnOp (Bil.NOT, lt) in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b (Def.create i (Bil.Int (Cbat_word.to_word (w32 0))));
  Blk.Builder.add_def body_b (Def.create i (Bil.BinOp (Bil.PLUS, iv, Bil.Int (Cbat_word.to_word (w32 1)))));
  List.iter (Blk.Builder.add_def exit_b) (exit_defs i);
  let entry0 = Blk.Builder.result entry_b in
  let body0 = Blk.Builder.result body_b in
  let header0 = Blk.Builder.result header_b in
  let exit0 = Blk.Builder.result exit_b in
  let body_tid = Term.tid body0 in
  let header_tid = Term.tid header0 in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct body_tid)));
  let body_b = Blk.Builder.init ~copy_defs:true body0 in
  Blk.Builder.add_jmp body_b (Jmp.create (Goto (Direct header_tid)));
  let header_b = Blk.Builder.init ~copy_defs:true header0 in
  Blk.Builder.add_jmp header_b (Jmp.create ~cond:lt (Goto (Direct exit_tid)));
  Blk.Builder.add_jmp header_b (Jmp.create ~cond:nlt (Goto (Direct body_tid)));
  let entry = Blk.Builder.result entry_b in
  let body = Blk.Builder.result body_b in
  let header = Blk.Builder.result header_b in
  let exit = Blk.Builder.result exit_b in
  let sub_b = Sub.Builder.create ~name:"counter_loop" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  let ctx = Program.create ~subs:[ sub ] () in
  (i, ctx, sub, exit_tid)

(* Flag-guard fixture: mixed vs single def shapes. *)
let mk_flag_sub ~(mixed : bool) :
    var * Program.t * sub term * tid * def term * def term option * def term =
  let f = v1 "t3_f" in
  let g = v1 "t3_g" in
  let h = v1 "t3_h" in
  let t = v64 "t3_t" in
  let m = memv "t3_m" in
  let defA = Def.create f (Bil.Var g) in
  let defB = Def.create f (Bil.Var h) in
  let defU = Def.create (v64 "t3_u") (Bil.Int (Cbat_word.to_word (w64 42))) in
  let defC =
    Def.create t
      (Bil.Load (Bil.Var m, Bil.BinOp (Bil.PLUS, Bil.Var g, Bil.Var (v64 "RSP")), LittleEndian, `r64))
  in
  let exit_b = Blk.Builder.create () in
  let exit0 = Blk.Builder.result exit_b in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b defA;
  if mixed then Blk.Builder.add_def entry_b defB;
  Blk.Builder.add_def entry_b defC;
  Blk.Builder.add_def entry_b defU;
  Blk.Builder.add_jmp entry_b (Jmp.create ~cond:(Bil.Var f) (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let sub_b = Sub.Builder.create ~name:"t3_flag" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b exit0;
  let sub = Sub.Builder.result sub_b in
  let ctx = Program.create ~subs:[ sub ] () in
  (f, ctx, sub, exit_tid, defA, (if mixed then Some defB else None), defU)

(* Single self-looping block sub (a never-analyzed callee; calls abstract it).
   Shared by the alias-shape fixture below and the prologue/outgoing escape family. *)
let mk_selfloop_callee (name : string) : sub term =
  let cb = Blk.Builder.create () in
  let cblk0 = Blk.Builder.result cb in
  let cb = Blk.Builder.init ~copy_defs:true cblk0 in
  Blk.Builder.add_jmp cb (Jmp.create (Goto (Direct (Term.tid cblk0))));
  let cblk = Blk.Builder.result cb in
  let callee_b = Sub.Builder.create ~name () in
  Sub.Builder.add_blk callee_b cblk;
  Sub.Builder.result callee_b

(* Call jump with a return continuation. *)
let mk_call_jmp (post_tid : tid) (callee_tid : tid) : jmp term =
  Jmp.create (Call (Call.create ~return:(Label.direct post_tid) ~target:(Label.direct callee_tid) ()))

(* T3: frozen-flag guard — assume_jump_cond refines every var, gate-free. *)
type caller_alias_fixture = {
  ca_ctx : Program.t;
  ca_sub : sub term;
  ca_entry_blk : blk term;
  ca_post_tid : tid;
  ca_m : var;
  ca_r2 : var;
  ca_rsp : var;
  ca_rbp : var;
  ca_rbx : var;
  ca_rdi : var;
  ca_def_rbp : def term;
  ca_def_rdi : def term;
  ca_def_store : def term;
  ca_def_store_disjoint : def term;
}

let mk_caller_alias () : caller_alias_fixture =
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let rbx = v64 "RBX" in
  let rdi = v64 "rdi" in
  let r2 = v64 "t4_r2" in
  let m = memv "t4_m" in
  let m2 = memv "t4_m2" in
  let v = v64 "t4_v" in
  let w = v64 "t4_w" in
  let w2 = v64 "t4_w2" in
  (* Callee: single self-looping block; never analyzed (call abstracted). *)
  let callee = mk_selfloop_callee "t4_callee" in
  let callee_tid = Term.tid callee in
  let def_rsp = Def.create rsp (Bil.Int (Cbat_word.to_word (w64 0x2000))) in
  let def_rbp = Def.create rbp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 0x1f00)))) in
  let def_rdi = Def.create rdi (Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 0x30)))) in
  let def_rbx = Def.create rbx (Bil.BinOp (Bil.PLUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 0x40)))) in
  (* Call PUSH model (rsp := RSP - 8); placed after defs using pre-push RSP. *)
  let def_push = Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 8)))) in
  let def_v =
    Def.create v
      (Bil.Load
         (Bil.Var m, Bil.BinOp (Bil.PLUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 0x10))), LittleEndian, `r64))
  in
  let def_w2 =
    Def.create w2
      (Bil.Load (Bil.Var m, Bil.BinOp (Bil.PLUS, Bil.Var rbx, Bil.Var rsp), LittleEndian, `r64))
  in
  let def_w = Def.create w (Bil.Load (Bil.Var m, Bil.Var rdi, LittleEndian, `r64)) in
  let def_store =
    Def.create m (Bil.Store (Bil.Var m, Bil.Var rdi, Bil.Int (Cbat_word.to_word (w64 42)), LittleEndian, `r64))
  in
  let def_store_disjoint =
    Def.create m2
      (Bil.Store
         ( Bil.Var m2,
           Bil.BinOp (Bil.PLUS, Bil.Var rdi, Bil.Int (Cbat_word.to_word (w64 0x80))),
           Bil.Int (Cbat_word.to_word (w64 43)),
           LittleEndian,
           `r64 ))
  in
  let post_b = Blk.Builder.create () in
  let def_reload = Def.create r2 (Bil.Load (Bil.Var m, Bil.Var rdi, LittleEndian, `r64)) in
  Blk.Builder.add_def post_b def_reload;
  let post0 = Blk.Builder.result post_b in
  let post_tid = Term.tid post0 in
  let entry_b = Blk.Builder.create () in
  List.iter (Blk.Builder.add_def entry_b)
    [
      def_rsp;
      def_rbp;
      def_rdi;
      def_rbx;
      def_push;
      def_v;
      def_w2;
      def_w;
      def_store;
      def_store_disjoint;
    ];
  Blk.Builder.add_jmp entry_b (mk_call_jmp post_tid callee_tid);
  let entry = Blk.Builder.result entry_b in
  let caller_b = Sub.Builder.create ~name:"t4_caller" () in
  Sub.Builder.add_arg caller_b (Arg.create rdi (Bil.Var rdi));
  Sub.Builder.add_arg caller_b (Arg.create r2 (Bil.Var r2));
  Sub.Builder.add_blk caller_b entry;
  Sub.Builder.add_blk caller_b post0;
  let caller = Sub.Builder.result caller_b in
  let ctx = Program.create ~subs:[ caller; callee ] () in
  {
    ca_ctx = ctx;
    ca_sub = caller;
    ca_entry_blk = entry;
    ca_post_tid = post_tid;
    ca_m = m;
    ca_r2 = r2;
    ca_rsp = rsp;
    ca_rbp = rbp;
    ca_rbx = rbx;
    ca_rdi = rdi;
    ca_def_rbp = def_rbp;
    ca_def_rdi = def_rdi;
    ca_def_store = def_store;
    ca_def_store_disjoint = def_store_disjoint;
  }

(* T4: caller-alias soundness — post-call reload reads TOP; RSP/RBP/RBX kept, rdi TOPed.
   The alias prologue (rdi through rbp, push def, dual mems) is a different
   shape from the fp/outgoing escape family (mk_escape_caller); it shares only
   the callee/call wiring above. *)
(* F1: map-lattice fold visits explicitly-stored bindings only; absent = top. *)
(* RSP-anchored seeds: RBP enters only via RSP-derivation. *)

(* -O0 prologue (rbp := RSP) + load + overlapping store. Returns (def_rbp, def_store, sub). *)
let mk_rsp_prologue_sub () : def term * def term * def term * sub term =
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let m = memv "t21_m" in
  let t = v64 "t21_t" in
  let def_rbp = Def.create rbp (Bil.Var rsp) in
  let def_load =
    Def.create t
      (Bil.Load
         (Bil.Var m, Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 0x30))), LittleEndian, `r64))
  in
  let def_store =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 0x30))),
           Bil.Int (Cbat_word.to_word (w64 42)),
           LittleEndian,
           `r64 ))
  in
  let b = Blk.Builder.create () in
  Blk.Builder.add_def b def_rbp;
  Blk.Builder.add_def b def_load;
  Blk.Builder.add_def b def_store;
  let blk = Blk.Builder.result b in
  let sub_b = Sub.Builder.create ~name:"t21_prologue" () in
  Sub.Builder.add_blk sub_b blk;
  let sub = Sub.Builder.result sub_b in
  (def_rbp, def_load, def_store, sub)

let mk_rsp_index_sub () : def term * def term * sub term =
  let rsp = v64 "RSP" in
  let rdi = v64 "t21_rdi" in
  let idx = v64 "t21_idx" in
  let m = memv "t21_m" in
  let t = v64 "t21_t" in
  let def_base = Def.create rdi (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 8)))) in
  let def_idx = Def.create idx (Bil.Int (Cbat_word.to_word (w64 5))) in
  let def_load =
    Def.create t
      (Bil.Load
         ( Bil.Var m,
           Bil.BinOp (Bil.PLUS, Bil.Var rdi, Bil.BinOp (Bil.TIMES, Bil.Var idx, Bil.Int (Cbat_word.to_word (w64 8)))),
           LittleEndian,
           `r64 ))
  in
  let b = Blk.Builder.create () in
  Blk.Builder.add_def b def_base;
  Blk.Builder.add_def b def_idx;
  Blk.Builder.add_def b def_load;
  let blk = Blk.Builder.result b in
  let sub_b = Sub.Builder.create ~name:"t21_idx" () in
  Sub.Builder.add_blk sub_b blk;
  let sub = Sub.Builder.result sub_b in
  (def_idx, def_load, sub)

let mk_gpr_rbp_sub () : def term * def term * def term * def term * def term * sub term =
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let idx = v64 "t21_n_idx" in
  let m = memv "t21_n_m" in
  let m2 = memv "t21_n_m2" in
  let v = v64 "t21_n_v" in
  let w = v64 "t21_n_w" in
  let def_rbp = Def.create rbp (Bil.Int (Cbat_word.to_word (w64 0x400000))) in
  let def_idx = Def.create idx (Bil.Int (Cbat_word.to_word (w64 5))) in
  let def_load =
    Def.create v
      (Bil.Load
         ( Bil.Var m,
           Bil.BinOp (Bil.PLUS, Bil.Var rbp, Bil.BinOp (Bil.TIMES, Bil.Var idx, Bil.Int (Cbat_word.to_word (w64 8)))),
           LittleEndian,
           `r64 ))
  in
  let def_store_disjoint =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.PLUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 0x100))),
           Bil.Int (Cbat_word.to_word (w64 9)),
           LittleEndian,
           `r64 ))
  in
  let def_load_rsp =
    Def.create w
      (Bil.Load (Bil.Var m2, Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 8))), LittleEndian, `r64))
  in
  let def_store_rsp =
    Def.create m2
      (Bil.Store
         ( Bil.Var m2,
           Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 8))),
           Bil.Int (Cbat_word.to_word (w64 7)),
           LittleEndian,
           `r64 ))
  in
  let b = Blk.Builder.create () in
  List.iter (Blk.Builder.add_def b)
    [ def_rbp; def_idx; def_load; def_store_disjoint; def_load_rsp; def_store_rsp ];
  let blk = Blk.Builder.result b in
  let sub_b = Sub.Builder.create ~name:"t21_gpr_rbp" () in
  Sub.Builder.add_blk sub_b blk;
  let sub = Sub.Builder.result sub_b in
  (def_rbp, def_idx, def_load, def_store_disjoint, def_store_rsp, sub)

(* One-path heap shapes: the use-store's address joins to TOP. *)

(* One-path fixture: the rdi use is reachable only via B1. Returns (def_prologue, def_load, def_other, def_use, sub). *)
let mk_one_path_sub () : def term * def term * def term * def term * sub term =
  let rsp = v64 "RSP" in
  let rbp = v64 "t22_rbp" in
  let rdi = v64 "t22_rdi" in
  let m = memv "t22_m" in
  let m2 = memv "t22_m2" in
  let f1 = v1 "t22_f1" in
  let f2 = v1 "t22_f2" in
  let def_prologue = Def.create rbp (Bil.Var rsp) in
  let def_load =
    Def.create rdi
      (Bil.Load
         (Bil.Var m, Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 0x30))), LittleEndian, `r64))
  in
  let def_other = Def.create rdi (Bil.Int (Cbat_word.to_word (w64 7))) in
  let def_use =
    Def.create m2
      (Bil.Store
         ( Bil.Var m2,
           Bil.BinOp (Bil.PLUS, Bil.Var rdi, Bil.Int (Cbat_word.to_word (w64 8))),
           Bil.Int (Cbat_word.to_word (w64 42)),
           LittleEndian,
           `r64 ))
  in
  let b_use_b = Blk.Builder.create () in
  Blk.Builder.add_def b_use_b def_use;
  let b_use = Blk.Builder.result b_use_b in
  let b1_b = Blk.Builder.create () in
  Blk.Builder.add_def b1_b def_load;
  Blk.Builder.add_jmp b1_b (Jmp.create (Goto (Direct (Term.tid b_use))));
  let b1 = Blk.Builder.result b1_b in
  let b2_b = Blk.Builder.create () in
  Blk.Builder.add_def b2_b def_other;
  let b2 = Blk.Builder.result b2_b in
  let entry_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b def_prologue;
  Blk.Builder.add_jmp entry_b (Jmp.create ~cond:(Bil.Var f1) (Goto (Direct (Term.tid b1))));
  Blk.Builder.add_jmp entry_b (Jmp.create ~cond:(Bil.Var f2) (Goto (Direct (Term.tid b2))));
  let entry = Blk.Builder.result entry_b in
  let sub_b = Sub.Builder.create ~name:"t22_onepath" () in
  List.iter (Sub.Builder.add_blk sub_b) [ entry; b1; b2; b_use ];
  let sub = Sub.Builder.result sub_b in
  (def_prologue, def_load, def_other, def_use, sub)

let mk_high0_cast_sub () : var * Program.t * sub term * tid =
  let rax = Var.create ~is_virtual:false ~fresh:false "rax" (Type.Imm 64) in
  let entry_b = Blk.Builder.create () in
  let cast_b = Blk.Builder.create () in
  let final_b = Blk.Builder.create () in
  let entry0 = Blk.Builder.result entry_b in
  let cast0 = Blk.Builder.result cast_b in
  let final0 = Blk.Builder.result final_b in
  let cast_tid = Term.tid cast0 in
  let final_tid = Term.tid final0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b
    (Jmp.create
       (Call (Call.create ~return:(Direct cast_tid) ~target:(Indirect (Bil.Int (Cbat_word.to_word (w64 0)))) ())));
  let cast_b = Blk.Builder.init ~copy_defs:true cast0 in
  Blk.Builder.add_def cast_b (Def.create rax (Bil.Cast (Bil.HIGH, 0, Bil.Var rax)));
  Blk.Builder.add_jmp cast_b (Jmp.create (Goto (Direct final_tid)));
  let entry = Blk.Builder.result entry_b in
  let cast = Blk.Builder.result cast_b in
  let final = Blk.Builder.result final_b in
  let sub_b = Sub.Builder.create ~name:"d7_high0_cast" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b cast;
  Sub.Builder.add_blk sub_b final;
  let sub = Sub.Builder.result sub_b in
  let ctx = Program.create ~subs:[ sub ] () in
  (rax, ctx, sub, final_tid)

(* Stack-only residue closure: heap-indexed stores fall out; top-addr stores skipped. *)

(* Heap-indexed store negative. Returns (def_base, def_idx, def_data, def_store, sub, exit tid). *)
let mk_e2ed_heap_sub () : def term * def term * def term * def term * sub term * tid =
  let rdi = v64 "e2ed_rdi" in
  let i = v64 "e2ed_i" in
  let v = v64 "e2ed_v" in
  let m = memv "e2ed_m" in
  let def_base = Def.create rdi (Bil.Int (Cbat_word.to_word (w64 0x400000))) in
  let def_idx = Def.create i (Bil.Int (Cbat_word.to_word (w64 5))) in
  let def_data = Def.create v (Bil.Int (Cbat_word.to_word (w64 99))) in
  let def_store =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.PLUS, Bil.Var rdi, Bil.BinOp (Bil.TIMES, Bil.Var i, Bil.Int (Cbat_word.to_word (w64 8)))),
           Bil.Var v,
           LittleEndian,
           `r64 ))
  in
  let exit_b = Blk.Builder.create () in
  let exit0 = Blk.Builder.result exit_b in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.create () in
  List.iter (Blk.Builder.add_def entry_b) [ def_base; def_idx; def_data; def_store ];
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let sub_b = Sub.Builder.create ~name:"e2ed_heap" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b exit0;
  let sub = Sub.Builder.result sub_b in
  (def_base, def_idx, def_data, def_store, sub, exit_tid)

let mk_e2ed_rsp_store_sub () : def term * def term * def term * sub term * tid =
  let rsp = v64 "RSP" in
  let rbp = v64 "e2ed_rbp" in
  let i2 = v64 "e2ed_i2" in
  let m2 = memv "e2ed_m2" in
  let def_prologue = Def.create rbp (Bil.Var rsp) in
  let def_idx = Def.create i2 (Bil.Int (Cbat_word.to_word (w64 3))) in
  let def_store =
    Def.create m2
      (Bil.Store
         ( Bil.Var m2,
           Bil.BinOp
             ( Bil.PLUS,
               Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 0x30))),
               Bil.BinOp (Bil.TIMES, Bil.Var i2, Bil.Int (Cbat_word.to_word (w64 8))) ),
           Bil.Int (Cbat_word.to_word (w64 42)),
           LittleEndian,
           `r64 ))
  in
  let exit_b = Blk.Builder.create () in
  let exit0 = Blk.Builder.result exit_b in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.create () in
  List.iter (Blk.Builder.add_def entry_b) [ def_prologue; def_idx; def_store ];
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let sub_b = Sub.Builder.create ~name:"e2ed_rsp_store" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b exit0;
  let sub = Sub.Builder.result sub_b in
  (def_prologue, def_idx, def_store, sub, exit_tid)

(* RSP := 0 anchor def is tagged, so the entry state carries RSP = {0}. *)

(* Smallest sub running the fixpoint: one block, one trivial def. *)
let mk_p3_anchor_sub () : sub term =
  let t = v64 "p3_t" in
  let b = Blk.Builder.create () in
  Blk.Builder.add_def b (Def.create t (Bil.Int (Cbat_word.to_word (w64 0))));
  let blk = Blk.Builder.result b in
  let sub_b = Sub.Builder.create ~name:"p3_anchor" () in
  Sub.Builder.add_blk sub_b blk;
  Sub.Builder.result sub_b

(* Backward-refinement loop fixtures (moved verbatim from test_backward.ml). *)
let mk_l3a_loop ~(cmp : Bil.binop) ~(c : Cbat_word.t) ~(rhs : exp) : sub term * tid =
  let m = memv "l3a_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let t = Var.create ~is_virtual:false ~fresh:false "l3a_t" (Type.Imm 32) in
  let v = Var.create ~is_virtual:false ~fresh:false "l3a_v" (Type.Imm 32) in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
  let cond = Bil.BinOp (cmp, Bil.Var v, Bil.Int (Cbat_word.to_word c)) in
  let ncond = Bil.UnOp (Bil.NOT, cond) in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  (* Prologue def: RBP copies RSP. *)
  Blk.Builder.add_def entry_b (Def.create rbp (Bil.Var rsp));
  Blk.Builder.add_def header_b (Def.create t (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  Blk.Builder.add_def header_b (Def.create v rhs);
  let entry0 = Blk.Builder.result entry_b in
  let body0 = Blk.Builder.result body_b in
  let header0 = Blk.Builder.result header_b in
  let exit0 = Blk.Builder.result exit_b in
  let body_tid = Term.tid body0 in
  let header_tid = Term.tid header0 in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct header_tid)));
  let body_b = Blk.Builder.init ~copy_defs:true body0 in
  Blk.Builder.add_jmp body_b (Jmp.create (Goto (Direct header_tid)));
  let header_b = Blk.Builder.init ~copy_defs:true header0 in
  Blk.Builder.add_jmp header_b (Jmp.create ~cond (Goto (Direct body_tid)));
  Blk.Builder.add_jmp header_b (Jmp.create ~cond:ncond (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let body = Blk.Builder.result body_b in
  let header = Blk.Builder.result header_b in
  let exit = Blk.Builder.result exit_b in
  let sub_b = Sub.Builder.create ~name:"l3a_loop" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  (sub, body_tid)

(* Cell at [base-8] in [st], read back as the load denotation reads it. *)
let cell_at (m : var) (base : var) (st : AI.t) : Ws.t =
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var base, Bil.Int (Cbat_word.to_word (w64 8))) in
  match Vsa.denote_imm_exp (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)) st with
  | Ok ws -> ws
  | Error _ -> Ws.top 32

(* Finite non-top non-bottom set bounded above by [maxv]. *)
let bounded_above (ws : Ws.t) (maxv : Cbat_word.t) : bool =
  (not (Ws.is_top ws))
  && (not (Ws.is_bottom ws))
  && match Ws.max_elem ws with Some w -> Cbat_word.( <= ) w maxv | None -> false

(* Tagged-sub fixpoint; walk's cell meet observable at BODY input. *)
(* Iterate state of an edge is the single-predecessor target's IN-state. *)
(* Anchored fixpoint run (defaults: the anchored entry; fixtures rely on it). *)
let run_anchored (sub : sub term) : Vsa.vsa_sol =
  let prog = Program.create ~subs:[ sub ] () in
  Vsa.static_graph_vsa [] prog sub (Vsa.init_sol ~entry:(anchored_entry ()) sub)

(* Anchored fixpoint + extraction (defaults: anchored entry, empty alloc tids). *)
let extract_anchored (sub : sub term) : Cu.vsa_kind Tid.Map.t * (int64 * int64) Tid.Map.t * (int64 * int64) Tid.Map.t =
  let sol = run_anchored sub in
  Vsa.Cbat_extraction.extract ~sp ~dynamic_alloc:(fun _ -> false) ~alloc_tids:Tid.Set.empty ~sol sub
let iter_state_of (_sub : sub term) (sol : Vsa.vsa_sol) (target_tid : tid) : AI.t =
  Graphlib.Std.Solution.get sol target_tid

let iter_cell_of (sub : sub term) (sol : Vsa.vsa_sol) (target_tid : tid) (cell_of : AI.t -> Ws.t) :
    Ws.t =
  cell_of (iter_state_of sub sol target_tid)

let l3a_run_analyzed (sub : sub term) (body_tid : tid) : Ws.t =
  (* Gate-free (spec §2.1): the raw sub runs; every def is denoted. *)
  iter_cell_of sub (run_anchored sub) body_tid (cell_at (memv "l3a_m") (v64 "RBP"))

(* L3c-1: flag-state mechanism — bare-flag guards recover the comparison constraint. *)

(* Flag-indirected loop fixture. Returns (sub, body tid, back-edge jump). *)
let mk_l3c1_loop ~(extra_header_defs : def term list) : sub term * tid * jmp term =
  let m = memv "l3c1_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let t = Var.create ~is_virtual:false ~fresh:false "l3c1_t" (Type.Imm 32) in
  let cf = v1 "l3c1_cf" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  (* Prologue def: RBP copies RSP. *)
  Blk.Builder.add_def entry_b (Def.create rbp (Bil.Var rsp));
  Blk.Builder.add_def header_b (Def.create t (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  Blk.Builder.add_def header_b (Def.create cf (Bil.BinOp (Bil.LT, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 10)))));
  List.iter (Blk.Builder.add_def header_b) extra_header_defs;
  let entry0 = Blk.Builder.result entry_b in
  let body0 = Blk.Builder.result body_b in
  let header0 = Blk.Builder.result header_b in
  let exit0 = Blk.Builder.result exit_b in
  let body_tid = Term.tid body0 in
  let header_tid = Term.tid header0 in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct header_tid)));
  let body_b = Blk.Builder.init ~copy_defs:true body0 in
  Blk.Builder.add_jmp body_b (Jmp.create (Goto (Direct header_tid)));
  let header_b = Blk.Builder.init ~copy_defs:true header0 in
  Blk.Builder.add_jmp header_b (Jmp.create ~cond:(Bil.Var cf) (Goto (Direct body_tid)));
  Blk.Builder.add_jmp header_b
    (Jmp.create ~cond:(Bil.UnOp (Bil.NOT, Bil.Var cf)) (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let body = Blk.Builder.result body_b in
  let header = Blk.Builder.result header_b in
  let exit = Blk.Builder.result exit_b in
  let sub_b = Sub.Builder.create ~name:"l3c1_loop" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  let jmp =
    match Term.enum jmp_t header |> Seq.to_list with [ j1; _ ] -> j1 | _ -> assert false
  in
  (sub, body_tid, jmp)

(* L3c-2: signed comparison rows (SLT/SLE). *)

(* Seeded counter loop; [flag] selects the flag-indirected guard, [prologue] drops it. Returns (sub, body tid). *)
let mk_l3c2_loop ~(prologue : bool) ~(seed : Cbat_word.t option) ~(cmp : Bil.binop) ~(c : Cbat_word.t)
    ~(body_op : Bil.binop) ~(body_k : Cbat_word.t) ~(flag : bool) : sub term * tid =
  let m = memv "l3c2_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let t = Var.create ~is_virtual:false ~fresh:false "l3c2_t" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "l3c2_u" (Type.Imm 32) in
  let cf = v1 "l3c2_cf" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
  let cond = Bil.BinOp (cmp, Bil.Var t, Bil.Int (Cbat_word.to_word c)) in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  (match seed with
  | Some v ->
      Blk.Builder.add_def entry_b
        (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int (Cbat_word.to_word v), LittleEndian, `r32)))
  | None -> ());
  if prologue then Blk.Builder.add_def entry_b (Def.create rbp (Bil.Var rsp));
  Blk.Builder.add_def header_b (Def.create t (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  if flag then Blk.Builder.add_def header_b (Def.create cf (Bil.BinOp (cmp, Bil.Var t, Bil.Int (Cbat_word.to_word c))));
  Blk.Builder.add_def body_b (Def.create u (Bil.BinOp (body_op, Bil.Var t, Bil.Int (Cbat_word.to_word body_k))));
  Blk.Builder.add_def body_b
    (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Var u, LittleEndian, `r32)));
  let entry0 = Blk.Builder.result entry_b in
  let body0 = Blk.Builder.result body_b in
  let header0 = Blk.Builder.result header_b in
  let exit0 = Blk.Builder.result exit_b in
  let body_tid = Term.tid body0 in
  let header_tid = Term.tid header0 in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct header_tid)));
  let body_b = Blk.Builder.init ~copy_defs:true body0 in
  Blk.Builder.add_jmp body_b (Jmp.create (Goto (Direct header_tid)));
  let header_b = Blk.Builder.init ~copy_defs:true header0 in
  let jcond = if flag then Bil.Var cf else cond in
  Blk.Builder.add_jmp header_b (Jmp.create ~cond:jcond (Goto (Direct body_tid)));
  Blk.Builder.add_jmp header_b
    (Jmp.create ~cond:(Bil.UnOp (Bil.NOT, jcond)) (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let body = Blk.Builder.result body_b in
  let header = Blk.Builder.result header_b in
  let exit = Blk.Builder.result exit_b in
  let sub_b = Sub.Builder.create ~name:"l3c2_loop" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  (sub, body_tid)

(* Finite non-top non-bottom, all values in [lo, hi]. *)
let l3c2_in_high (ws : Ws.t) (lo : Cbat_word.t) (hi : Cbat_word.t) : bool =
  (not (Ws.is_top ws))
  && (not (Ws.is_bottom ws))
  &&
  match (Ws.min_elem ws, Ws.max_elem ws) with
  | Some mn, Some mx -> Cbat_word.( >= ) mn lo && Cbat_word.( <= ) mx hi
  | _ -> false

(* L3c-3: PLUS-hull, TIMES-const, RSHIFT/ARSHIFT-const rows. *)

(* Chain loop fixture: header loads, applies chain, guards. Returns (sub, body tid). *)
let mk_l3c3_loop ~(seed : Cbat_word.t option) ~(chain : exp) ~(cmp : Bil.binop) ~(c : Cbat_word.t)
    ~(body_k : Cbat_word.t) : sub term * tid =
  let m = memv "l3c3_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let t = Var.create ~is_virtual:false ~fresh:false "l3c3_t" (Type.Imm 32) in
  let v = Var.create ~is_virtual:false ~fresh:false "l3c3_v" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "l3c3_u" (Type.Imm 32) in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
  let cond = Bil.BinOp (cmp, Bil.Var v, Bil.Int (Cbat_word.to_word c)) in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  (match seed with
  | Some sv ->
      Blk.Builder.add_def entry_b
        (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int (Cbat_word.to_word sv), LittleEndian, `r32)))
  | None -> ());
  (* Prologue def: RBP copies RSP. *)
  Blk.Builder.add_def entry_b (Def.create rbp (Bil.Var rsp));
  Blk.Builder.add_def header_b (Def.create t (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  Blk.Builder.add_def header_b (Def.create v chain);
  Blk.Builder.add_def body_b (Def.create u (Bil.BinOp (Bil.PLUS, Bil.Var t, Bil.Int (Cbat_word.to_word body_k))));
  Blk.Builder.add_def body_b
    (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Var u, LittleEndian, `r32)));
  let entry0 = Blk.Builder.result entry_b in
  let body0 = Blk.Builder.result body_b in
  let header0 = Blk.Builder.result header_b in
  let exit0 = Blk.Builder.result exit_b in
  let body_tid = Term.tid body0 in
  let header_tid = Term.tid header0 in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct header_tid)));
  let body_b = Blk.Builder.init ~copy_defs:true body0 in
  Blk.Builder.add_jmp body_b (Jmp.create (Goto (Direct header_tid)));
  let header_b = Blk.Builder.init ~copy_defs:true header0 in
  Blk.Builder.add_jmp header_b (Jmp.create ~cond (Goto (Direct body_tid)));
  Blk.Builder.add_jmp header_b
    (Jmp.create ~cond:(Bil.UnOp (Bil.NOT, cond)) (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let body = Blk.Builder.result body_b in
  let header = Blk.Builder.result header_b in
  let exit = Blk.Builder.result exit_b in
  let sub_b = Sub.Builder.create ~name:"l3c3_loop" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  (sub, body_tid)

(* Plain fixpoint; BODY input cell at RBP-8. *)
let l3c3_run (sub : sub term) (body_tid : tid) : Ws.t =
  iter_cell_of sub (run_anchored sub) body_tid (cell_at (memv "l3c3_m") (v64 "RBP"))

(* L3c-4: Var-vs-Var overlap, DIVIDE-const, HIGH-extract rows. *)

(* Chain loop with compared-var width. Returns (sub, body tid). *)
let mk_l3c4_loop ~(seed : Cbat_word.t option) ~(chain : exp) ~(v_w : int) ~(cmp : Bil.binop) ~(c : Cbat_word.t)
    ~(body_k : Cbat_word.t) : sub term * tid =
  let m = memv "l3c4_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let t = Var.create ~is_virtual:false ~fresh:false "l3c4_t" (Type.Imm 32) in
  let v = Var.create ~is_virtual:false ~fresh:false "l3c4_v" (Type.Imm v_w) in
  let u = Var.create ~is_virtual:false ~fresh:false "l3c4_u" (Type.Imm 32) in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
  let cond = Bil.BinOp (cmp, Bil.Var v, Bil.Int (Cbat_word.to_word c)) in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  (match seed with
  | Some sv ->
      Blk.Builder.add_def entry_b
        (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int (Cbat_word.to_word sv), LittleEndian, `r32)))
  | None -> ());
  (* Prologue def: RBP copies RSP. *)
  Blk.Builder.add_def entry_b (Def.create rbp (Bil.Var rsp));
  Blk.Builder.add_def header_b (Def.create t (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  Blk.Builder.add_def header_b (Def.create v chain);
  Blk.Builder.add_def body_b (Def.create u (Bil.BinOp (Bil.PLUS, Bil.Var t, Bil.Int (Cbat_word.to_word body_k))));
  Blk.Builder.add_def body_b
    (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Var u, LittleEndian, `r32)));
  let entry0 = Blk.Builder.result entry_b in
  let body0 = Blk.Builder.result body_b in
  let header0 = Blk.Builder.result header_b in
  let exit0 = Blk.Builder.result exit_b in
  let body_tid = Term.tid body0 in
  let header_tid = Term.tid header0 in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct header_tid)));
  let body_b = Blk.Builder.init ~copy_defs:true body0 in
  Blk.Builder.add_jmp body_b (Jmp.create (Goto (Direct header_tid)));
  let header_b = Blk.Builder.init ~copy_defs:true header0 in
  Blk.Builder.add_jmp header_b (Jmp.create ~cond (Goto (Direct body_tid)));
  Blk.Builder.add_jmp header_b
    (Jmp.create ~cond:(Bil.UnOp (Bil.NOT, cond)) (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let body = Blk.Builder.result body_b in
  let header = Blk.Builder.result header_b in
  let exit = Blk.Builder.result exit_b in
  let sub_b = Sub.Builder.create ~name:"l3c4_loop" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  (sub, body_tid)

(* Two-load Var-vs-Var shape. Returns (sub, body tid). *)
let mk_l3c4_vv_loop ~(seed : Cbat_word.t option) ~(seed2 : Cbat_word.t option) ~(cmp : Bil.binop) ~(body_k : Cbat_word.t)
    : sub term * tid =
  let m = memv "l3c4_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let t = Var.create ~is_virtual:false ~fresh:false "l3c4_t" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "l3c4_u" (Type.Imm 32) in
  let w = Var.create ~is_virtual:false ~fresh:false "l3c4_w" (Type.Imm 32) in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
  let addr2 = Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 16))) in
  let cond = Bil.BinOp (cmp, Bil.Var t, Bil.Var u) in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  (match seed with
  | Some sv ->
      Blk.Builder.add_def entry_b
        (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int (Cbat_word.to_word sv), LittleEndian, `r32)))
  | None -> ());
  (match seed2 with
  | Some sv ->
      Blk.Builder.add_def entry_b
        (Def.create m (Bil.Store (Bil.Var m, addr2, Bil.Int (Cbat_word.to_word sv), LittleEndian, `r32)))
  | None -> ());
  (* Prologue def: RBP copies RSP. *)
  Blk.Builder.add_def entry_b (Def.create rbp (Bil.Var rsp));
  Blk.Builder.add_def header_b (Def.create t (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  Blk.Builder.add_def header_b (Def.create u (Bil.Load (Bil.Var m, addr2, LittleEndian, `r32)));
  Blk.Builder.add_def body_b (Def.create w (Bil.BinOp (Bil.PLUS, Bil.Var t, Bil.Int (Cbat_word.to_word body_k))));
  Blk.Builder.add_def body_b
    (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Var w, LittleEndian, `r32)));
  let entry0 = Blk.Builder.result entry_b in
  let body0 = Blk.Builder.result body_b in
  let header0 = Blk.Builder.result header_b in
  let exit0 = Blk.Builder.result exit_b in
  let body_tid = Term.tid body0 in
  let header_tid = Term.tid header0 in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct header_tid)));
  let body_b = Blk.Builder.init ~copy_defs:true body0 in
  Blk.Builder.add_jmp body_b (Jmp.create (Goto (Direct header_tid)));
  let header_b = Blk.Builder.init ~copy_defs:true header0 in
  Blk.Builder.add_jmp header_b (Jmp.create ~cond (Goto (Direct body_tid)));
  Blk.Builder.add_jmp header_b
    (Jmp.create ~cond:(Bil.UnOp (Bil.NOT, cond)) (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let body = Blk.Builder.result body_b in
  let header = Blk.Builder.result header_b in
  let exit = Blk.Builder.result exit_b in
  let sub_b = Sub.Builder.create ~name:"l3c4_vv" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  (sub, body_tid)

(* Plain fixpoint; BODY input cell at RBP-8. *)
let l3c4_run (sub : sub term) (body_tid : tid) : Ws.t =
  iter_cell_of sub (run_anchored sub) body_tid (cell_at (memv "l3c4_m") (v64 "RBP"))

(* L3c-5: structural closure — identity rows, const-first arm, shrunk catch-all. *)

(* Optional-chain loop fixture. Returns (sub, body tid). *)
let mk_l3c5_loop ~(seed : Cbat_word.t option) ~(chain : exp option) ~(cond : exp) ~(body_k : Cbat_word.t) :
    sub term * tid =
  let m = memv "l3c5_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let t = Var.create ~is_virtual:false ~fresh:false "l3c5_t" (Type.Imm 32) in
  let v = Var.create ~is_virtual:false ~fresh:false "l3c5_v" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "l3c5_u" (Type.Imm 32) in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  (match seed with
  | Some sv ->
      Blk.Builder.add_def entry_b
        (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int (Cbat_word.to_word sv), LittleEndian, `r32)))
  | None -> ());
  (* Prologue def: RBP copies RSP. *)
  Blk.Builder.add_def entry_b (Def.create rbp (Bil.Var rsp));
  Blk.Builder.add_def header_b (Def.create t (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  (match chain with Some ch -> Blk.Builder.add_def header_b (Def.create v ch) | None -> ());
  Blk.Builder.add_def body_b (Def.create u (Bil.BinOp (Bil.PLUS, Bil.Var t, Bil.Int (Cbat_word.to_word body_k))));
  Blk.Builder.add_def body_b
    (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Var u, LittleEndian, `r32)));
  let entry0 = Blk.Builder.result entry_b in
  let body0 = Blk.Builder.result body_b in
  let header0 = Blk.Builder.result header_b in
  let exit0 = Blk.Builder.result exit_b in
  let body_tid = Term.tid body0 in
  let header_tid = Term.tid header0 in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct header_tid)));
  let body_b = Blk.Builder.init ~copy_defs:true body0 in
  Blk.Builder.add_jmp body_b (Jmp.create (Goto (Direct header_tid)));
  let header_b = Blk.Builder.init ~copy_defs:true header0 in
  Blk.Builder.add_jmp header_b (Jmp.create ~cond (Goto (Direct body_tid)));
  Blk.Builder.add_jmp header_b
    (Jmp.create ~cond:(Bil.UnOp (Bil.NOT, cond)) (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let body = Blk.Builder.result body_b in
  let header = Blk.Builder.result header_b in
  let exit = Blk.Builder.result exit_b in
  let sub_b = Sub.Builder.create ~name:"l3c5_loop" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  (sub, body_tid)

(* Plain fixpoint; BODY input cell at RBP-8. *)
let l3c5_run (sub : sub term) (body_tid : tid) : Ws.t =
  iter_cell_of sub (run_anchored sub) body_tid (cell_at (memv "l3c5_m") (v64 "RBP"))

(* Interrupt denotation: unknown external callee via call_abstraction. *)
(* L-3b: coalesce equal-lower merge arm — piles collapse, reads preserved. *)

(* Seeded RMW counter (traverse shape). Returns (sub, body tid, header tid). *)
let mk_l3b1_loop () : sub term * tid * tid =
  let m = memv "l3b1_m" in
  let rsp = v64 "RSP" in
  let t = Var.create ~is_virtual:false ~fresh:false "l3b1_t" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "l3b1_u" (Type.Imm 32) in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 8))) in
  let cond = Bil.BinOp (Bil.LT, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 8))) in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b
    (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int (Cbat_word.to_word (w32 0)), LittleEndian, `r32)));
  Blk.Builder.add_def header_b (Def.create t (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  Blk.Builder.add_def body_b (Def.create u (Bil.BinOp (Bil.PLUS, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 1)))));
  Blk.Builder.add_def body_b
    (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Var u, LittleEndian, `r32)));
  let entry0 = Blk.Builder.result entry_b in
  let body0 = Blk.Builder.result body_b in
  let header0 = Blk.Builder.result header_b in
  let exit0 = Blk.Builder.result exit_b in
  let body_tid = Term.tid body0 in
  let header_tid = Term.tid header0 in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct header_tid)));
  let body_b = Blk.Builder.init ~copy_defs:true body0 in
  Blk.Builder.add_jmp body_b (Jmp.create (Goto (Direct header_tid)));
  let header_b = Blk.Builder.init ~copy_defs:true header0 in
  Blk.Builder.add_jmp header_b (Jmp.create ~cond (Goto (Direct body_tid)));
  Blk.Builder.add_jmp header_b
    (Jmp.create ~cond:(Bil.UnOp (Bil.NOT, cond)) (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let body = Blk.Builder.result body_b in
  let header = Blk.Builder.result header_b in
  let exit = Blk.Builder.result exit_b in
  let sub_b = Sub.Builder.create ~name:"l3b1_loop" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  (sub, body_tid, header_tid)

(* Diamond: both branches store {7} at [RSP-8]/[RSP-7]; merge unions them. Returns (sub, merge tid). *)
let mk_l3b4_diamond () : sub term * tid =
  let m = memv "l3b4_m" in
  let rsp = v64 "RSP" in
  let i = Var.create ~is_virtual:false ~fresh:false "l3b4_i" (Type.Imm 32) in
  let addr8 = Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 8))) in
  let addr7 = Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 7))) in
  let cond = Bil.BinOp (Bil.LT, Bil.Var i, Bil.Int (Cbat_word.to_word (w32 1))) in
  let entry_b = Blk.Builder.create () in
  let a_b = Blk.Builder.create () in
  let b_b = Blk.Builder.create () in
  let merge_b = Blk.Builder.create () in
  Blk.Builder.add_def a_b
    (Def.create m (Bil.Store (Bil.Var m, addr8, Bil.Int (Cbat_word.to_word (w32 7)), LittleEndian, `r32)));
  Blk.Builder.add_def a_b
    (Def.create m (Bil.Store (Bil.Var m, addr7, Bil.Int (Cbat_word.to_word (w32 7)), LittleEndian, `r32)));
  Blk.Builder.add_def b_b
    (Def.create m (Bil.Store (Bil.Var m, addr8, Bil.Int (Cbat_word.to_word (w32 7)), LittleEndian, `r32)));
  Blk.Builder.add_def b_b
    (Def.create m (Bil.Store (Bil.Var m, addr7, Bil.Int (Cbat_word.to_word (w32 7)), LittleEndian, `r32)));
  let entry0 = Blk.Builder.result entry_b in
  let a0 = Blk.Builder.result a_b in
  let b0 = Blk.Builder.result b_b in
  let merge0 = Blk.Builder.result merge_b in
  let a_tid = Term.tid a0 in
  let b_tid = Term.tid b0 in
  let merge_tid = Term.tid merge0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create ~cond (Goto (Direct a_tid)));
  Blk.Builder.add_jmp entry_b (Jmp.create ~cond:(Bil.UnOp (Bil.NOT, cond)) (Goto (Direct b_tid)));
  let a_b = Blk.Builder.init ~copy_defs:true a0 in
  Blk.Builder.add_jmp a_b (Jmp.create (Goto (Direct merge_tid)));
  let b_b = Blk.Builder.init ~copy_defs:true b0 in
  Blk.Builder.add_jmp b_b (Jmp.create (Goto (Direct merge_tid)));
  let entry = Blk.Builder.result entry_b in
  let a = Blk.Builder.result a_b in
  let b = Blk.Builder.result b_b in
  let merge = Blk.Builder.result merge_b in
  let sub_b = Sub.Builder.create ~name:"l3b4_diamond" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b a;
  Sub.Builder.add_blk sub_b b;
  Sub.Builder.add_blk sub_b merge;
  let sub = Sub.Builder.result sub_b in
  (sub, merge_tid)

(* Cell count in [st]'s memory: counts "(height " sexp markers. *)
let l3b_cells_of (mv : var) (st : AI.t) : int =
  let mem = AI.find_memory { Mem.addr_width = 64; Mem.addressable_width = 8 } st mv in
  let s = Core_kernel.Sexp.to_string (Mem.sexp_of_t mem) in
  let marker = "(height " in
  let mlen = String.length marker in
  let n = ref 0 in
  for i = 0 to String.length s - mlen do
    if String.sub s i mlen = marker then incr n
  done;
  !n

(* L-B: jcc-decoder pins — exact -O0 corpus block fixture. *)

(* jle/jl/ja guard nestings the decoder matcher accepts. *)
let l39_jle (zf : var) (sf : var) (ofv : var) : exp =
  Bil.BinOp
    ( Bil.OR,
      Bil.Var zf,
      Bil.BinOp
        ( Bil.AND,
          Bil.BinOp (Bil.OR, Bil.Var sf, Bil.Var ofv),
          Bil.UnOp (Bil.NOT, Bil.BinOp (Bil.AND, Bil.Var sf, Bil.Var ofv)) ) )

let l39_jl (sf : var) (ofv : var) : exp =
  Bil.BinOp
    ( Bil.AND,
      Bil.BinOp (Bil.OR, Bil.Var sf, Bil.Var ofv),
      Bil.UnOp (Bil.NOT, Bil.BinOp (Bil.AND, Bil.Var sf, Bil.Var ofv)) )

let l39_ja (cf : var) (zf : var) : exp =
  Bil.UnOp (Bil.NOT, Bil.BinOp (Bil.OR, Bil.Var cf, Bil.Var zf))

(* Canonical -O0 cmp emission, fixed order: temp, CF, OF, SF, ZF (the decoder is order-sensitive). *)
let mk_cmp_emission b ~(e : exp) ~(c : Cbat_word.t) ~(t : var) ~(cf : var) ~(ofv : var) ~(sf : var)
    ~(zf : var) : unit =
  Blk.Builder.add_def b (Def.create t (Bil.BinOp (Bil.MINUS, e, Bil.Int (Cbat_word.to_word c))));
  Blk.Builder.add_def b (Def.create cf (Bil.BinOp (Bil.LT, e, Bil.Int (Cbat_word.to_word c))));
  Blk.Builder.add_def b
    (Def.create ofv
       (Bil.Cast
          ( Bil.HIGH,
            1,
            Bil.BinOp
              ( Bil.AND,
                Bil.BinOp (Bil.XOR, e, Bil.Int (Cbat_word.to_word c)),
                Bil.BinOp (Bil.XOR, e, Bil.Var t) ) )));
  Blk.Builder.add_def b (Def.create sf (Bil.Cast (Bil.HIGH, 1, Bil.Var t)));
  Blk.Builder.add_def b
    (Def.create zf (Bil.BinOp (Bil.EQ, Bil.Int (Word.zero (Cbat_word.bitwidth c)), Bil.Var t)))

(* Exact corpus block fixture: seeded store, canonical cmp emission, compound guard. Returns (sub, body tid). *)
let mk_l39_loop ~(seed : Cbat_word.t) ~(c : Cbat_word.t) ~(body_op : Bil.binop) ~(body_k : Cbat_word.t)
    ~(mk_cond : cf:var -> ofv:var -> sf:var -> zf:var -> exp)
    ~(extra_header_defs : var -> def term list) : sub term * tid =
  let m = memv "l39_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let t = Var.create ~is_virtual:false ~fresh:false "l39_t" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "l39_u" (Type.Imm 32) in
  let cf = v1 "CF" in
  let ofv = v1 "OF" in
  let sf = v1 "SF" in
  let zf = v1 "ZF" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
  let load_e = Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32) in
  let cond = mk_cond ~cf ~ofv ~sf ~zf in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b
    (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int (Cbat_word.to_word seed), LittleEndian, `r32)));
  (* Prologue def: RBP copies RSP. *)
  Blk.Builder.add_def entry_b (Def.create rbp (Bil.Var rsp));
  (* Canonical -O0 cmp emission, fixed order: temp, CF, OF, SF, ZF. *)
  mk_cmp_emission header_b ~e:load_e ~c ~t ~cf ~ofv ~sf ~zf;
  List.iter (Blk.Builder.add_def header_b) (extra_header_defs m);
  Blk.Builder.add_def body_b (Def.create u (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  Blk.Builder.add_def body_b
    (Def.create m
       (Bil.Store
          (Bil.Var m, addr_e, Bil.BinOp (body_op, Bil.Var u, Bil.Int (Cbat_word.to_word body_k)), LittleEndian, `r32)));
  let entry0 = Blk.Builder.result entry_b in
  let body0 = Blk.Builder.result body_b in
  let header0 = Blk.Builder.result header_b in
  let exit0 = Blk.Builder.result exit_b in
  let body_tid = Term.tid body0 in
  let header_tid = Term.tid header0 in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct header_tid)));
  let body_b = Blk.Builder.init ~copy_defs:true body0 in
  Blk.Builder.add_jmp body_b (Jmp.create (Goto (Direct header_tid)));
  let header_b = Blk.Builder.init ~copy_defs:true header0 in
  Blk.Builder.add_jmp header_b (Jmp.create ~cond (Goto (Direct body_tid)));
  Blk.Builder.add_jmp header_b
    (Jmp.create ~cond:(Bil.UnOp (Bil.NOT, cond)) (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let body = Blk.Builder.result body_b in
  let header = Blk.Builder.result header_b in
  let exit = Blk.Builder.result exit_b in
  let sub_b = Sub.Builder.create ~name:"l39_loop" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  (sub, body_tid)

(* Record-path fixture: bare-flag guard with unique def. Returns (sub, body tid). *)
let mk_l39b5_loop () : sub term * tid =
  let m = memv "l39_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let v = Var.create ~is_virtual:false ~fresh:false "l39b5_v" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "l39b5_u" (Type.Imm 32) in
  let cf = v1 "CF" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b
    (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int (Cbat_word.to_word (w32 0)), LittleEndian, `r32)));
  (* Prologue def: RBP copies RSP. *)
  Blk.Builder.add_def entry_b (Def.create rbp (Bil.Var rsp));
  Blk.Builder.add_def header_b (Def.create v (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  Blk.Builder.add_def header_b (Def.create cf (Bil.BinOp (Bil.LT, Bil.Var v, Bil.Int (Cbat_word.to_word (w32 3)))));
  Blk.Builder.add_def body_b (Def.create u (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  Blk.Builder.add_def body_b
    (Def.create m
       (Bil.Store
          (Bil.Var m, addr_e, Bil.BinOp (Bil.PLUS, Bil.Var u, Bil.Int (Cbat_word.to_word (w32 1))), LittleEndian, `r32)));
  let entry0 = Blk.Builder.result entry_b in
  let body0 = Blk.Builder.result body_b in
  let header0 = Blk.Builder.result header_b in
  let exit0 = Blk.Builder.result exit_b in
  let body_tid = Term.tid body0 in
  let header_tid = Term.tid header0 in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct header_tid)));
  let body_b = Blk.Builder.init ~copy_defs:true body0 in
  Blk.Builder.add_jmp body_b (Jmp.create (Goto (Direct header_tid)));
  let header_b = Blk.Builder.init ~copy_defs:true header0 in
  Blk.Builder.add_jmp header_b (Jmp.create ~cond:(Bil.Var cf) (Goto (Direct body_tid)));
  Blk.Builder.add_jmp header_b
    (Jmp.create ~cond:(Bil.UnOp (Bil.NOT, Bil.Var cf)) (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let body = Blk.Builder.result body_b in
  let header = Blk.Builder.result header_b in
  let exit = Blk.Builder.result exit_b in
  let sub_b = Sub.Builder.create ~name:"l39b5_loop" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  (sub, body_tid)

(* Plain fixpoint; BODY input cell at RBP-8. *)
let l39_run (sub : sub term) (body_tid : tid) : Ws.t =
  iter_cell_of sub (run_anchored sub) body_tid (cell_at (memv "l39_m") (v64 "RBP"))

(* L-E1: ON-path matched-pair RSP restoration (RSP := RSP + 8 on return). *)

(* Call-in-loop fixture. Returns (sub, header tid, rsp). *)
let mk_e1_loop_sub () : sub term * tid * var =
  let rsp = v64 "RSP" in
  let m = memv "e1_m" in
  let entry_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let cont_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b (Def.create rsp (Bil.Int (Cbat_word.to_word (w64 0x1000))));
  Blk.Builder.add_def body_b (Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 8)))));
  Blk.Builder.add_def body_b
    (Def.create m (Bil.Store (Bil.Var m, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 0xdead)), LittleEndian, `r64)));
  let entry0 = Blk.Builder.result entry_b in
  let header0 = Blk.Builder.result header_b in
  let body0 = Blk.Builder.result body_b in
  let cont0 = Blk.Builder.result cont_b in
  let header_tid = Term.tid header0 in
  let body_tid = Term.tid body0 in
  let cont_tid = Term.tid cont0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct header_tid)));
  let header_b = Blk.Builder.init ~copy_defs:true header0 in
  Blk.Builder.add_jmp header_b (Jmp.create (Goto (Direct body_tid)));
  let body_b = Blk.Builder.init ~copy_defs:true body0 in
  Blk.Builder.add_jmp body_b
    (Jmp.create
       (Call (Call.create ~return:(Label.direct cont_tid) ~target:(Indirect (Bil.Int (Cbat_word.to_word (w64 0)))) ())));
  let cont_b = Blk.Builder.init ~copy_defs:true cont0 in
  Blk.Builder.add_jmp cont_b (Jmp.create (Goto (Direct header_tid)));
  let entry = Blk.Builder.result entry_b in
  let header = Blk.Builder.result header_b in
  let body = Blk.Builder.result body_b in
  let cont = Blk.Builder.result cont_b in
  let sub_b = Sub.Builder.create ~name:"e1_loop" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b cont;
  let sub = Sub.Builder.result sub_b in
  (sub, header_tid, rsp)

(* Straight-line call fixture. Returns (sub, post tid, rsp). *)
let mk_e1_flat_sub () : sub term * tid * var =
  let rsp = v64 "RSP" in
  let m = memv "e1_m" in
  let entry_b = Blk.Builder.create () in
  let post_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b (Def.create rsp (Bil.Int (Cbat_word.to_word (w64 0x2000))));
  Blk.Builder.add_def entry_b (Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 8)))));
  Blk.Builder.add_def entry_b
    (Def.create m (Bil.Store (Bil.Var m, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 0xcafe)), LittleEndian, `r64)));
  let entry0 = Blk.Builder.result entry_b in
  let post0 = Blk.Builder.result post_b in
  let post_tid = Term.tid post0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b
    (Jmp.create
       (Call (Call.create ~return:(Label.direct post_tid) ~target:(Indirect (Bil.Int (Cbat_word.to_word (w64 0)))) ())));
  let post_b = Blk.Builder.init ~copy_defs:true post0 in
  let entry = Blk.Builder.result entry_b in
  let post = Blk.Builder.result post_b in
  let sub_b = Sub.Builder.create ~name:"e1_flat" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b post;
  let sub = Sub.Builder.result sub_b in
  (sub, post_tid, rsp)

(* ON-path fixpoint; RSP value-set at [tid]. *)
let e1_rsp_at (sub : sub term) (tid : tid) (rsp : var) : Ws.t =
  AI.find_word 64 (Graphlib.Std.Solution.get (run_anchored sub) tid) rsp

(* L-D6: RBP-anchored gate-free fixture — the dead epilogue def is denoted too. *)

(* RBP loop with dead epilogue def. Returns (sub, body tid). *)
let mk_l6_rbp_loop () : sub term * tid =
  let m = memv "l6_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let t = Var.create ~is_virtual:false ~fresh:false "l6_t" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "l6_u" (Type.Imm 32) in
  let cf = v1 "CF" in
  let ofv = v1 "OF" in
  let sf = v1 "SF" in
  let zf = v1 "ZF" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
  let load_e = Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32) in
  let c = w32 63 in
  let cond = l39_jle zf sf ofv in
  let prologue_b = Blk.Builder.create () in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  let epilogue_b = Blk.Builder.create () in
  Blk.Builder.add_def prologue_b (Def.create rbp (Bil.Var rsp));
  Blk.Builder.add_def entry_b
    (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int (Cbat_word.to_word (w32 0)), LittleEndian, `r32)));
  (* Canonical -O0 cmp emission, RBP-based. *)
  mk_cmp_emission header_b ~e:load_e ~c ~t ~cf ~ofv ~sf ~zf;
  Blk.Builder.add_def body_b (Def.create u (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  Blk.Builder.add_def body_b
    (Def.create m
       (Bil.Store
          (Bil.Var m, addr_e, Bil.BinOp (Bil.PLUS, Bil.Var u, Bil.Int (Cbat_word.to_word (w32 1))), LittleEndian, `r32)));
  (* Dead epilogue def: RBP := mem[RSP]. *)
  Blk.Builder.add_def epilogue_b
    (Def.create rbp (Bil.Load (Bil.Var m, Bil.Var rsp, LittleEndian, `r64)));
  let prologue0 = Blk.Builder.result prologue_b in
  let entry0 = Blk.Builder.result entry_b in
  let body0 = Blk.Builder.result body_b in
  let header0 = Blk.Builder.result header_b in
  let exit0 = Blk.Builder.result exit_b in
  let epilogue0 = Blk.Builder.result epilogue_b in
  let body_tid = Term.tid body0 in
  let header_tid = Term.tid header0 in
  let entry_tid = Term.tid entry0 in
  let exit_tid = Term.tid exit0 in
  let epilogue_tid = Term.tid epilogue0 in
  let prologue_b = Blk.Builder.init ~copy_defs:true prologue0 in
  Blk.Builder.add_jmp prologue_b (Jmp.create (Goto (Direct entry_tid)));
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct header_tid)));
  let body_b = Blk.Builder.init ~copy_defs:true body0 in
  Blk.Builder.add_jmp body_b (Jmp.create (Goto (Direct header_tid)));
  let header_b = Blk.Builder.init ~copy_defs:true header0 in
  Blk.Builder.add_jmp header_b (Jmp.create ~cond (Goto (Direct body_tid)));
  Blk.Builder.add_jmp header_b
    (Jmp.create ~cond:(Bil.UnOp (Bil.NOT, cond)) (Goto (Direct exit_tid)));
  let exit_b = Blk.Builder.init ~copy_defs:true exit0 in
  Blk.Builder.add_jmp exit_b (Jmp.create (Goto (Direct epilogue_tid)));
  let prologue = Blk.Builder.result prologue_b in
  let entry = Blk.Builder.result entry_b in
  let body = Blk.Builder.result body_b in
  let header = Blk.Builder.result header_b in
  let exit = Blk.Builder.result exit_b in
  let epilogue = Blk.Builder.result epilogue_b in
  let sub_b = Sub.Builder.create ~name:"l6_rbp_loop" () in
  Sub.Builder.add_blk sub_b prologue;
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  Sub.Builder.add_blk sub_b epilogue;
  let sub = Sub.Builder.result sub_b in
  (sub, body_tid)

(* ON-path fixpoint; BODY input cell at RBP-8. *)
let l6_run (sub : sub term) (body_tid : tid) : Ws.t =
  cell_at (memv "l6_m") (v64 "RBP") (Graphlib.Std.Solution.get (run_anchored sub) body_tid)

(* Refactor-2 new-shape pins: inline-arithmetic, NOT-edge, const-first flip, nested BinOp. *)

(* RBP-anchored ON-path fixture with optional two-path seed. Returns (sub, body tid). *)
let mk_r2_loop ~(seed : Cbat_word.t) ~(seed2 : Cbat_word.t option) ~(body_op : Bil.binop) ~(body_k : Cbat_word.t)
    ~(mk_cond : t:var -> exp) : sub term * tid =
  let m = memv "r2_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let t = Var.create ~is_virtual:false ~fresh:false "r2_t" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "r2_u" (Type.Imm 32) in
  let f = v1 "r2_f" in
  let g = v1 "r2_g" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
  let load_e = Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32) in
  let prologue_b = Blk.Builder.create () in
  let split_b = Blk.Builder.create () in
  let entry_b = Blk.Builder.create () in
  let entry2_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  Blk.Builder.add_def prologue_b (Def.create rbp (Bil.Var rsp));
  Blk.Builder.add_def split_b (Def.create f (Bil.Var g));
  Blk.Builder.add_def entry_b
    (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int (Cbat_word.to_word seed), LittleEndian, `r32)));
  (match seed2 with
  | Some s2 ->
      Blk.Builder.add_def entry2_b
        (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int (Cbat_word.to_word s2), LittleEndian, `r32)))
  | None -> ());
  Blk.Builder.add_def header_b (Def.create t load_e);
  Blk.Builder.add_def body_b (Def.create u load_e);
  Blk.Builder.add_def body_b
    (Def.create m
       (Bil.Store
          (Bil.Var m, addr_e, Bil.BinOp (body_op, Bil.Var u, Bil.Int (Cbat_word.to_word body_k)), LittleEndian, `r32)));
  let prologue0 = Blk.Builder.result prologue_b in
  let split0 = Blk.Builder.result split_b in
  let entry0 = Blk.Builder.result entry_b in
  let entry20 = Blk.Builder.result entry2_b in
  let body0 = Blk.Builder.result body_b in
  let header0 = Blk.Builder.result header_b in
  let exit0 = Blk.Builder.result exit_b in
  let body_tid = Term.tid body0 in
  let header_tid = Term.tid header0 in
  let entry_tid = Term.tid entry0 in
  let entry2_tid = Term.tid entry20 in
  let split_tid = Term.tid split0 in
  let exit_tid = Term.tid exit0 in
  let prologue_b = Blk.Builder.init ~copy_defs:true prologue0 in
  let split_b = Blk.Builder.init ~copy_defs:true split0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  let entry2_b = Blk.Builder.init ~copy_defs:true entry20 in
  let body_b = Blk.Builder.init ~copy_defs:true body0 in
  let header_b = Blk.Builder.init ~copy_defs:true header0 in
  let exit_b = Blk.Builder.init ~copy_defs:true exit0 in
  (match seed2 with
  | Some _ ->
      Blk.Builder.add_jmp prologue_b (Jmp.create (Goto (Direct split_tid)));
      Blk.Builder.add_jmp split_b (Jmp.create ~cond:(Bil.Var f) (Goto (Direct entry_tid)));
      Blk.Builder.add_jmp split_b
        (Jmp.create ~cond:(Bil.UnOp (Bil.NOT, Bil.Var f)) (Goto (Direct entry2_tid)));
      Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct header_tid)));
      Blk.Builder.add_jmp entry2_b (Jmp.create (Goto (Direct header_tid)))
  | None ->
      Blk.Builder.add_jmp prologue_b (Jmp.create (Goto (Direct entry_tid)));
      Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct header_tid))));
  Blk.Builder.add_jmp body_b (Jmp.create (Goto (Direct header_tid)));
  let cond = mk_cond ~t in
  Blk.Builder.add_jmp header_b (Jmp.create ~cond (Goto (Direct body_tid)));
  Blk.Builder.add_jmp header_b
    (Jmp.create ~cond:(Bil.UnOp (Bil.NOT, cond)) (Goto (Direct exit_tid)));
  let prologue = Blk.Builder.result prologue_b in
  let split = Blk.Builder.result split_b in
  let entry = Blk.Builder.result entry_b in
  let entry2 = Blk.Builder.result entry2_b in
  let body = Blk.Builder.result body_b in
  let header = Blk.Builder.result header_b in
  let exit = Blk.Builder.result exit_b in
  let sub_b = Sub.Builder.create ~name:"r2_loop" () in
  Sub.Builder.add_blk sub_b prologue;
  (match seed2 with
  | Some _ ->
      Sub.Builder.add_blk sub_b split;
      Sub.Builder.add_blk sub_b entry;
      Sub.Builder.add_blk sub_b entry2
  | None -> Sub.Builder.add_blk sub_b entry);
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  (sub, body_tid)

(* ON-path fixpoint; BODY input cell at RBP-8. *)
let r2_run (sub : sub term) (body_tid : tid) : Ws.t =
  iter_cell_of sub (run_anchored sub) body_tid (cell_at (memv "r2_m") (v64 "RBP"))

(* Indexed-loop twin (C4a/R11): i := 0; body indexed store + inc; exit singleton store.
   The two tests differ only in the var-name prefix; the divergent pins stay in the tests. *)
let mk_indexed_loop ~pfx : sub term * def term =
  let rsp = v64 "RSP" in
  let i = Var.create ~is_virtual:false ~fresh:false (pfx ^ "_i") (Type.Imm 32) in
  let t = Var.create ~is_virtual:false ~fresh:false (pfx ^ "_t") (Type.Imm 32) in
  let m = memv (pfx ^ "_m") in
  let iv = Bil.Var i in
  let lt = Bil.BinOp (Bil.LT, iv, Bil.Var t) in
  let nlt = Bil.UnOp (Bil.NOT, lt) in
  let idx_addr =
    Bil.BinOp
      ( Bil.PLUS,
        Bil.Var rsp,
        Bil.BinOp (Bil.MINUS, Bil.Cast (Bil.UNSIGNED, 64, iv), Bil.Int (Cbat_word.to_word (w64 32))) )
  in
  let def_idx_store =
    Def.create m (Bil.Store (Bil.Var m, idx_addr, Bil.Int (Cbat_word.to_word (w64 7)), LittleEndian, `r64))
  in
  let def_inc = Def.create i (Bil.BinOp (Bil.PLUS, iv, Bil.Int (Cbat_word.to_word (w32 1)))) in
  let def_exit =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 16))),
           Bil.Int (Cbat_word.to_word (w64 9)),
           LittleEndian,
           `r64 ))
  in
  let entry0 = blk_of_defs [ Def.create i (Bil.Int (Cbat_word.to_word (w32 0))) ] in
  let body0 = blk_of_defs [ def_idx_store; def_inc ] in
  let header0 = blk_of_defs [] in
  let exit0 = blk_of_defs [ def_exit ] in
  let body_tid = Term.tid body0 in
  let header_tid = Term.tid header0 in
  let exit_tid = Term.tid exit0 in
  let sub_b = Sub.Builder.create ~name:(pfx ^ "_merge") () in
  Sub.Builder.add_blk sub_b (with_jmps entry0 [ mk_goto body_tid ]);
  Sub.Builder.add_blk sub_b (with_jmps body0 [ mk_goto header_tid ]);
  Sub.Builder.add_blk sub_b (with_jmps header0 [ mk_jmp_to exit_tid nlt; mk_jmp_to body_tid lt ]);
  Sub.Builder.add_blk sub_b exit0;
  (Sub.Builder.result sub_b, def_idx_store)

(* Escape fixtures (the caller/callee family): prologue + outgoing-slot shape. *)

(* Outgoing-slot payload: a constant or a register's (possibly TOP) value. *)
type escape_payload = C of int | R of var

type escape_fixture = {
  es_sub : sub term;
  es_blk0 : blk term;
  es_blk1 : blk term;
  es_post_tid : tid;
  es_m : var;
}

(* Caller/callee escape fixture: fp-seeded frame + prologue + outgoing slots
   + call + post reload. The C3/A1/A4c near-copies differ only in the prefix,
   the fp offset, and the outgoing payloads; the divergent pins stay in the tests. *)
let mk_escape_caller ~pfx ~fp_off ~seed ~(outs : (int * escape_payload) list) () : escape_fixture =
  let rsp = v64 "RSP" in
  let fp = v64 (pfx ^ "_fp") in
  let rdi = v64 "RDI" in
  let r2 = v64 (pfx ^ "_r2") in
  let m = memv (pfx ^ "_m") in
  let callee = mk_selfloop_callee (pfx ^ "_callee") in
  let callee_tid = Term.tid callee in
  let post_b = Blk.Builder.create () in
  Blk.Builder.add_def post_b (Def.create r2 (Bil.Load (Bil.Var m, Bil.Var fp, LittleEndian, `r64)));
  let post0 = Blk.Builder.result post_b in
  let post_tid = Term.tid post0 in
  let def_fp = Def.create fp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 fp_off)))) in
  let def_seed =
    Def.create m (Bil.Store (Bil.Var m, Bil.Var fp, Bil.Int (Cbat_word.to_word (w64 seed)), LittleEndian, `r64))
  in
  let def_prologue = Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 0x20)))) in
  let def_rdi = Def.create rdi (Bil.BinOp (Bil.PLUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 0x30)))) in
  let def_out (off, p) =
    let data = match p with C v -> Bil.Int (Cbat_word.to_word (w64 v)) | R v -> Bil.Var v in
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.PLUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 off))),
           data,
           LittleEndian,
           `r64 ))
  in
  let b0 = Blk.Builder.create () in
  List.iter (Blk.Builder.add_def b0) [ def_fp; def_seed; def_prologue ];
  let b00 = Blk.Builder.result b0 in
  let b1 = Blk.Builder.create () in
  List.iter (Blk.Builder.add_def b1) (def_rdi :: List.map def_out outs);
  let b10 = Blk.Builder.result b1 in
  let b0' = Blk.Builder.init ~copy_defs:true b00 in
  Blk.Builder.add_jmp b0' (Jmp.create (Goto (Direct (Term.tid b10))));
  let b1' = Blk.Builder.init ~copy_defs:true b10 in
  Blk.Builder.add_jmp b1' (mk_call_jmp post_tid callee_tid);
  let blk0 = Blk.Builder.result b0' in
  let blk1 = Blk.Builder.result b1' in
  let sub_b = Sub.Builder.create ~name:(pfx ^ "_caller") () in
  Sub.Builder.add_arg sub_b (Arg.create rdi (Bil.Var rdi));
  Sub.Builder.add_arg sub_b (Arg.create r2 (Bil.Var r2));
  Sub.Builder.add_blk sub_b blk0;
  Sub.Builder.add_blk sub_b blk1;
  Sub.Builder.add_blk sub_b post0;
  let caller = Sub.Builder.result sub_b in
  ignore callee;
  { es_sub = caller; es_blk0 = blk0; es_blk1 = blk1; es_post_tid = post_tid; es_m = m }

(* Store builder, MINUS/rsp-rooted with explicit size. *)
let mk_store_minus m rsp lo data sz =
  Def.create m
    (Bil.Store
       ( Bil.Var m,
         Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 lo))),
         Bil.Int (Cbat_word.to_word (w64 data)),
         LittleEndian,
         sz ))

(* When-chain fixture (moved verbatim from test_properties.ml). *)
let mk_when_chain () : sub term * tid * tid * tid * tid * var =
  let m = memv "wc_m" in
  let rbp = v64 "RBP" in
  let x = Var.create ~is_virtual:false ~fresh:false "wc_x" (Type.Imm 32) in
  let g1 = v1 "wc_g1" in
  let g2 = v1 "wc_g2" in
  let f1 = v1 "wc_f1" in
  let f2 = v1 "wc_f2" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
  let load_e = Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32) in
  let c1 = Bil.BinOp (Bil.LT, Bil.Var x, Bil.Int (Cbat_word.to_word (w32 10))) in
  let c2 = Bil.BinOp (Bil.LT, Bil.Var x, Bil.Int (Cbat_word.to_word (w32 20))) in
  let mk_store_blk (k : Cbat_word.t) : blk term =
    let b = Blk.Builder.create () in
    Blk.Builder.add_def b
      (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int (Cbat_word.to_word k), LittleEndian, `r32)));
    Blk.Builder.result b in
  let mk_jmp_blk () : blk term = Blk.Builder.result (Blk.Builder.create ()) in
  let prologue0 =
    let b = Blk.Builder.create () in
    Blk.Builder.add_def b (Def.create rbp (Bil.Var (v64 "RSP")));
    Blk.Builder.result b in
  let s1_0 = mk_jmp_blk () in
  let s2_0 = mk_jmp_blk () in
  let e1_0 = mk_store_blk (w32 5) in
  let e2_0 = mk_store_blk (w32 15) in
  let e3_0 = mk_store_blk (w32 25) in
  let chain_b = Blk.Builder.create () in
  Blk.Builder.add_def chain_b (Def.create x load_e);
  let chain0 = Blk.Builder.result chain_b in
  let l1_0 = mk_jmp_blk () in
  let l2_0 = mk_jmp_blk () in
  let l3_0 = mk_jmp_blk () in
  let chain_tid = Term.tid chain0 in
  let l1_tid = Term.tid l1_0 in
  let l2_tid = Term.tid l2_0 in
  let l3_tid = Term.tid l3_0 in
  let prologue_b = Blk.Builder.init ~copy_defs:true prologue0 in
  Blk.Builder.add_jmp prologue_b (Jmp.create (Goto (Direct (Term.tid s1_0))));
  let s1_b = Blk.Builder.init ~copy_defs:true s1_0 in
  Blk.Builder.add_def s1_b (Def.create f1 (Bil.Var g1));
  Blk.Builder.add_jmp s1_b (Jmp.create ~cond:(Bil.Var f1) (Goto (Direct (Term.tid e1_0))));
  Blk.Builder.add_jmp s1_b (Jmp.create (Goto (Direct (Term.tid s2_0))));
  let s2_b = Blk.Builder.init ~copy_defs:true s2_0 in
  Blk.Builder.add_def s2_b (Def.create f2 (Bil.Var g2));
  Blk.Builder.add_jmp s2_b (Jmp.create ~cond:(Bil.Var f2) (Goto (Direct (Term.tid e2_0))));
  Blk.Builder.add_jmp s2_b (Jmp.create (Goto (Direct (Term.tid e3_0))));
  let mk_goto (b0 : blk term) (dst : tid) : blk term =
    let b = Blk.Builder.init ~copy_defs:true b0 in
    Blk.Builder.add_jmp b (Jmp.create (Goto (Direct dst)));
    Blk.Builder.result b in
  let e1 = mk_goto e1_0 chain_tid in
  let e2 = mk_goto e2_0 chain_tid in
  let e3 = mk_goto e3_0 chain_tid in
  let chain_b = Blk.Builder.init ~copy_defs:true chain0 in
  Blk.Builder.add_jmp chain_b (Jmp.create ~cond:c1 (Goto (Direct l1_tid)));
  Blk.Builder.add_jmp chain_b (Jmp.create ~cond:c2 (Goto (Direct l2_tid)));
  Blk.Builder.add_jmp chain_b (Jmp.create (Goto (Direct l3_tid)));
  let l1 = mk_goto l1_0 l1_tid in
  let l2 = mk_goto l2_0 l2_tid in
  let l3 = mk_goto l3_0 l3_tid in
  let sub_b = Sub.Builder.create ~name:"wc_chain" () in
  List.iter (Sub.Builder.add_blk sub_b)
    [ Blk.Builder.result prologue_b; Blk.Builder.result s1_b; Blk.Builder.result s2_b;
      e1; e2; e3; Blk.Builder.result chain_b; l1; l2; l3 ];
  let sub = Sub.Builder.result sub_b in
  (sub, l1_tid, l2_tid, l3_tid, chain_tid, x)

(* T01-1: accumulated-cond acceptance — mid edge by c2 & ~c1, tail by ~c1 & ~c2. *)

(* Store builder, PLUS/base-rooted at fixed `r64 (the fission shape). *)
let mk_store_plus sm base off dat =
  Def.create sm
    (Bil.Store
       ( Bil.Var sm,
         Bil.BinOp (Bil.PLUS, Bil.Var base, Bil.Int (Cbat_word.to_word (w64 off))),
         Bil.Int (Cbat_word.to_word (w64 dat)),
         LittleEndian,
         `r64 ))

(* Single-block sub with a cond read (the D4 production shape). *)
let mk_cond_sub nm defs cond_var =
  let bb = Blk.Builder.create () in
  List.iter (Blk.Builder.add_def bb) defs;
  Blk.Builder.add_jmp bb
    (Jmp.create ~cond:(Bil.BinOp (Bil.EQ, Bil.Var cond_var, Bil.Int (Cbat_word.to_word (w64 0))))
       (Goto (Direct (Tid.create ()))));
  let sb = Sub.Builder.create ~name:nm () in
  Sub.Builder.add_blk sb (Blk.Builder.result bb);
  Sub.Builder.result sb

(* Emitter fixtures (moved verbatim from test_bil2llvm.ml). *)
let emit_ir (subs : sub term list) : string =
  let llvm_ctx = Llvm.create_context () in
  let llvm_module = Llvm.create_module llvm_ctx "Test" in
  let prog = Program.create ~subs () in
  B2l.emit_program llvm_ctx llvm_module
    ~target:Theory.Target.unknown ~ptrsize:64
    ~symtab:None ~text_section:None ~section_remap:[] ~copy_relocs:[]
    [] prog;
  let s = Llvm.string_of_llmodule llvm_module in
  Llvm.dispose_module llvm_module;
  Llvm.dispose_context llvm_ctx;
  s

let check_ir (name : string) (must : string) (ir : string) : unit =
  check name (contains_substring ir must)

(* Blocks of a sub holding no jumps (the exit-block idiom). *)
let exit_blocks_of (sub : sub term) : blk term list =
  Term.enum blk_t sub |> Seq.to_list |> List.filter (fun b -> Term.enum jmp_t b |> Seq.to_list = [])

(* ------------------------------------------------------------------ *)
(* Family 1: the FP-intrinsic table — every row emits its native op.  *)
(* ------------------------------------------------------------------ *)

let ivar64 (n : string) : var = Var.create ~is_virtual:false ~fresh:false n (Type.Imm 64)

(* A terminal block: build-first so callers can reference its tid. *)
let mk_exit_blk () : blk term =
  let b0 = Blk.Builder.create () in
  let b = Blk.Builder.init ~copy_defs:true (Blk.Builder.result b0) in
  Blk.Builder.add_jmp b (Jmp.create (Ret (Direct (Tid.create ()))));
  Blk.Builder.result b

(* One mapped-intrinsic call site, the production shape:
   [intrinsic:x0 := src; call @<name> with return <cont>; cont: ...]. *)
let mk_fp_call_sub (intr : string) (arg_defs : def term list) : sub term =
  let callee_tid = Tid.for_name intr in
  let caller = Blk.Builder.create () in
  let exit_blk = mk_exit_blk () in
  (* The writeback reads the ret lane, the production shape. *)
  let cont0 = Blk.Builder.create () in
  let cont = Blk.Builder.init ~copy_defs:true (Blk.Builder.result cont0) in
  Blk.Builder.add_def cont (Def.create (v64 "fp_wb") (Bil.Var (ivar64 "intrinsic:y0")));
  Blk.Builder.add_jmp cont
    (Jmp.create ~cond:(Bil.BinOp (Bil.EQ, Bil.Var (v64 "fp_wb"), Bil.Int (Cbat_word.to_word (w64 0))))
       (Goto (Direct (Term.tid exit_blk))));
  Blk.Builder.add_jmp cont (Jmp.create (Goto (Direct (Term.tid exit_blk))));
  let cont_blk = Blk.Builder.result cont in
  let cont_tid = Term.tid cont_blk in
  List.iter (Blk.Builder.add_def caller) arg_defs;
  Blk.Builder.add_jmp caller
    (Jmp.create
       (Call
          (Call.create ~return:(Direct cont_tid) ~target:(Direct callee_tid) ())));
  let sb = Sub.Builder.create ~name:"fp_caller" () in
  Sub.Builder.add_blk sb (Blk.Builder.result caller);
  Sub.Builder.add_blk sb cont_blk;
  Sub.Builder.add_blk sb exit_blk;
  Sub.Builder.result sb

(* The bodyless mapped-intrinsic stub (the model interface sig). *)
let mk_fp_stub (intr : string) : sub term =
  let sb = Sub.Builder.create ~name:intr () in
  let sub = Sub.Builder.result sb in
  let sub = Term.set_attr sub Sub.intrinsic () in
  sub

let mk_fp_program (intr : string) (arg_defs : def term list) : sub term list =
  [ mk_fp_call_sub intr arg_defs; mk_fp_stub intr ]

(* Single-block sub over caller-supplied defs with a terminal Ret. *)
let mk_lds_sub nm defs =
  let caller = Blk.Builder.create () in
  List.iter (Blk.Builder.add_def caller) defs;
  Blk.Builder.add_jmp caller (Jmp.create (Ret (Direct (Tid.create ()))));
  let sb = Sub.Builder.create ~name:nm () in
  Sub.Builder.add_blk sb (Blk.Builder.result caller);
  Sub.Builder.result sb
