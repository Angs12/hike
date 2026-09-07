(* Shared test infrastructure: check harness, BIR fixture sugar, stderr capture, domain aliases. *)
open Bap.Std
open Bap_core_theory

open Bap.Std
open Bap_core_theory
module W = Word
module Clp = Cbat_clp
module Fs = Cbat_fin_set

module Wo = Cbat_word_ops
module Ws = Cbat_clp_set_composite

(* Wrapped BIR-fixpoint library; siblings re-exported by cbat_vsa.mli. *)
module AI = Cbat_vsa.AI
module Mem = Cbat_vsa.Mem
module Vsa = Cbat_vsa

(* Memmap fusion pipeline under test. *)
module MM = Cbat_vsa.Mem
module MK = Cbat_vsa.Mem.Key
module MV = Cbat_vsa.Mem.Val

(* Explicit anchored entry state (RSP = {0}); fixtures pass it to the fixpoint. *)
let anchored_entry () : AI.t =
  let rsp = Var.create ~is_virtual:false ~fresh:false "RSP" (Type.Imm 64) in
  let rbp = Var.create ~is_virtual:false ~fresh:false "RBP" (Type.Imm 64) in
  let e = AI.add_word AI.top ~key:rsp ~data:(Ws.singleton (W.of_int ~width:64 0)) in
  AI.add_word e ~key:rbp ~data:(Ws.singleton (W.of_int ~width:64 0))

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
let w32 = W.of_int ~width:32
let w33 = W.of_int ~width:33
let w64 = W.of_int ~width:64

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
  Blk.Builder.add_def entry_b (Def.create i (Bil.Int (w32 0)));
  Blk.Builder.add_def body_b (Def.create i (Bil.BinOp (Bil.PLUS, iv, Bil.Int (w32 1))));
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
  let defU = Def.create (v64 "t3_u") (Bil.Int (w64 42)) in
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
  let cb = Blk.Builder.create () in
  let cblk0 = Blk.Builder.result cb in
  let cb = Blk.Builder.init ~copy_defs:true cblk0 in
  Blk.Builder.add_jmp cb (Jmp.create (Goto (Direct (Term.tid cblk0))));
  let cblk = Blk.Builder.result cb in
  let callee_b = Sub.Builder.create ~name:"t4_callee" () in
  Sub.Builder.add_blk callee_b cblk;
  let callee = Sub.Builder.result callee_b in
  let callee_tid = Term.tid callee in
  let def_rsp = Def.create rsp (Bil.Int (w64 0x2000)) in
  let def_rbp = Def.create rbp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 0x1f00))) in
  let def_rdi = Def.create rdi (Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 0x30))) in
  let def_rbx = Def.create rbx (Bil.BinOp (Bil.PLUS, Bil.Var rsp, Bil.Int (w64 0x40))) in
  (* Call PUSH model (rsp := RSP - 8); placed after defs using pre-push RSP. *)
  let def_push = Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 8))) in
  let def_v =
    Def.create v
      (Bil.Load
         (Bil.Var m, Bil.BinOp (Bil.PLUS, Bil.Var rsp, Bil.Int (w64 0x10)), LittleEndian, `r64))
  in
  let def_w2 =
    Def.create w2
      (Bil.Load (Bil.Var m, Bil.BinOp (Bil.PLUS, Bil.Var rbx, Bil.Var rsp), LittleEndian, `r64))
  in
  let def_w = Def.create w (Bil.Load (Bil.Var m, Bil.Var rdi, LittleEndian, `r64)) in
  let def_store =
    Def.create m (Bil.Store (Bil.Var m, Bil.Var rdi, Bil.Int (w64 42), LittleEndian, `r64))
  in
  let def_store_disjoint =
    Def.create m2
      (Bil.Store
         ( Bil.Var m2,
           Bil.BinOp (Bil.PLUS, Bil.Var rdi, Bil.Int (w64 0x80)),
           Bil.Int (w64 43),
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
  Blk.Builder.add_jmp entry_b
    (Jmp.create
       (Call (Call.create ~return:(Label.direct post_tid) ~target:(Label.direct callee_tid) ())));
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

(* T4: caller-alias soundness — post-call reload reads TOP; RSP/RBP/RBX kept, rdi TOPed. *)
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
         (Bil.Var m, Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 0x30)), LittleEndian, `r64))
  in
  let def_store =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 0x30)),
           Bil.Int (w64 42),
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
  let def_base = Def.create rdi (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 8))) in
  let def_idx = Def.create idx (Bil.Int (w64 5)) in
  let def_load =
    Def.create t
      (Bil.Load
         ( Bil.Var m,
           Bil.BinOp (Bil.PLUS, Bil.Var rdi, Bil.BinOp (Bil.TIMES, Bil.Var idx, Bil.Int (w64 8))),
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
  let def_rbp = Def.create rbp (Bil.Int (w64 0x400000)) in
  let def_idx = Def.create idx (Bil.Int (w64 5)) in
  let def_load =
    Def.create v
      (Bil.Load
         ( Bil.Var m,
           Bil.BinOp (Bil.PLUS, Bil.Var rbp, Bil.BinOp (Bil.TIMES, Bil.Var idx, Bil.Int (w64 8))),
           LittleEndian,
           `r64 ))
  in
  let def_store_disjoint =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.PLUS, Bil.Var rbp, Bil.Int (w64 0x100)),
           Bil.Int (w64 9),
           LittleEndian,
           `r64 ))
  in
  let def_load_rsp =
    Def.create w
      (Bil.Load (Bil.Var m2, Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 8)), LittleEndian, `r64))
  in
  let def_store_rsp =
    Def.create m2
      (Bil.Store
         ( Bil.Var m2,
           Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 8)),
           Bil.Int (w64 7),
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
         (Bil.Var m, Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 0x30)), LittleEndian, `r64))
  in
  let def_other = Def.create rdi (Bil.Int (w64 7)) in
  let def_use =
    Def.create m2
      (Bil.Store
         ( Bil.Var m2,
           Bil.BinOp (Bil.PLUS, Bil.Var rdi, Bil.Int (w64 8)),
           Bil.Int (w64 42),
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
       (Call (Call.create ~return:(Direct cast_tid) ~target:(Indirect (Bil.Int (w64 0))) ())));
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
  let def_base = Def.create rdi (Bil.Int (w64 0x400000)) in
  let def_idx = Def.create i (Bil.Int (w64 5)) in
  let def_data = Def.create v (Bil.Int (w64 99)) in
  let def_store =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.PLUS, Bil.Var rdi, Bil.BinOp (Bil.TIMES, Bil.Var i, Bil.Int (w64 8))),
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
  let def_idx = Def.create i2 (Bil.Int (w64 3)) in
  let def_store =
    Def.create m2
      (Bil.Store
         ( Bil.Var m2,
           Bil.BinOp
             ( Bil.PLUS,
               Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 0x30)),
               Bil.BinOp (Bil.TIMES, Bil.Var i2, Bil.Int (w64 8)) ),
           Bil.Int (w64 42),
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
  Blk.Builder.add_def b (Def.create t (Bil.Int (w64 0)));
  let blk = Blk.Builder.result b in
  let sub_b = Sub.Builder.create ~name:"p3_anchor" () in
  Sub.Builder.add_blk sub_b blk;
  Sub.Builder.result sub_b
