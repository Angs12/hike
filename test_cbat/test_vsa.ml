(* Branch-assume/fixpoint smoke, channel pins, seeds, casts, anchor pins. *)
open Bap.Std
open Bap_core_theory
open Test_common

(* Fixpoint-level mixed-width smoke test. *)

(* Cyclic counter loop; doubt-valued cond keeps both edges live, back edge widens.
   [exit_defs] adds defs to the exit block. Returns (i, program, sub, exit tid). *)
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

(* FinSet cardinality reads at width+1 bits, so full {0,1} reads cardn 2, not empty. *)

(* L2b-1: full 1-bit domain reads cardn 2. *)
let run () =
(* SP anchor removed: fixtures pin the anchored entry explicitly. *)
(* Branch-assume refinement pins. *)
(  let ivar = Var.create ~is_virtual:false ~fresh:false "i" (Type.Imm 32) in
  let tgt = Tid.create () in
  let mk_jmp cond = Jmp.create ~cond (Goto (Direct tgt)) in
  let env = AI.top in
  (* x < 5 taken -> x in [0,4] *)
  let c1 =
    AI.find_word 32
      (Vsa.assume_jump_cond env
         (mk_jmp (Bil.BinOp (Bil.LT, Bil.Var ivar, Bil.Int (w32 5)))))
      ivar
  in
  check "D4-1: assume (x < 5) refines x to [0,4]"
    (Ws.min_elem c1 = Some (w32 0) && Ws.max_elem c1 = Some (w32 4));
  (* x <= 5 -> [0,5] *)
  let c2 =
    AI.find_word 32
      (Vsa.assume_jump_cond env
         (mk_jmp (Bil.BinOp (Bil.LE, Bil.Var ivar, Bil.Int (w32 5)))))
      ivar
  in
  check "D4-2: assume (x <= 5) refines x to [0,5]"
    (Ws.min_elem c2 = Some (w32 0) && Ws.max_elem c2 = Some (w32 5));
  (* x == 5 -> {5} *)
  let c3 =
    AI.find_word 32
      (Vsa.assume_jump_cond env
         (mk_jmp (Bil.BinOp (Bil.EQ, Bil.Var ivar, Bil.Int (w32 5)))))
      ivar
  in
  check "D4-3: assume (x == 5) refines x to {5}"
    (Ws.min_elem c3 = Some (w32 5) && Ws.max_elem c3 = Some (w32 5));
  let c4 = AI.find_word 32 (Vsa.assume_jump_cond env (mk_jmp (Bil.Int (w32 1)))) ivar in
  check "D4-4: doubt — constant condition keeps the state (top)" (Ws.is_top c4);
  let c5 =
    AI.find_word 32
      (Vsa.assume_jump_cond env (mk_jmp (Bil.BinOp (Bil.LT, Bil.Var ivar, Bil.Int (w64 5)))))
      ivar
  in
  check "D4-5: doubt — width-mismatched guard keeps the state (top)" (Ws.is_top c5);
  let c6 =
    AI.find_word 32
      (Vsa.assume_jump_cond env (mk_jmp (Bil.BinOp (Bil.NEQ, Bil.Var ivar, Bil.Int (w32 5)))))
      ivar
  in
  check "D4-6: gate-free (spec §2.1) — the NEQ guard refines to TOP−{5} (5 ∉, 0 ∈, non-top)"
    ((not (Ws.is_top c6)) && (not (Ws.elem (w32 5) c6)) && Ws.elem (w32 0) c6);
  let fv = Var.create ~is_virtual:false ~fresh:false "zf" (Type.Imm 1) in
  let c7 =
    AI.find_word 1
      (Vsa.assume_jump_cond env (mk_jmp (Bil.Var fv)))
      fv
  in
  check "D4-7: assume (flag) forces the flag to {1}" (Ws.elem Word.b1 c7 && not (Ws.elem Word.b0 c7));
  let c8 =
    AI.find_word 1
      (Vsa.assume_jump_cond env
         (mk_jmp (Bil.UnOp (Bil.NOT, Bil.Var fv))))
      fv
  in
  check "D4-8: assume (NOT flag) forces the flag to {0}"
    (Ws.elem Word.b0 c8 && not (Ws.elem Word.b1 c8));
  ()

(* Every fixture def is denoted; there is no tag gate. *))
(* BIR-level loop: back-edge refined by "i < 5", exit bounded. *)
;
(  (* Back-edge refined by "i < 5": header converges before widening fires. *)
  let i = Var.create ~is_virtual:false ~fresh:false "i" (Type.Imm 32) in
  let iv = Bil.Var i in
  let lt5 = Bil.BinOp (Bil.LT, iv, Bil.Int (w32 5)) in
  let nlt5 = Bil.UnOp (Bil.NOT, lt5) in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b (Def.create i (Bil.Int (w32 0)));
  Blk.Builder.add_def body_b (Def.create i (Bil.BinOp (Bil.PLUS, iv, Bil.Int (w32 1))));
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
  Blk.Builder.add_jmp header_b (Jmp.create ~cond:nlt5 (Goto (Direct exit_tid)));
  Blk.Builder.add_jmp header_b (Jmp.create ~cond:lt5 (Goto (Direct body_tid)));
  let entry = Blk.Builder.result entry_b in
  let body = Blk.Builder.result body_b in
  let header = Blk.Builder.result header_b in
  let exit = Blk.Builder.result exit_b in
  let sub_b = Sub.Builder.create ~name:"d4_loop" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  let ctx = Program.create ~subs:[ sub ] () in
  let sol =
    Vsa.static_graph_vsa [] ctx sub (Vsa.init_sol ~entry:(anchored_entry ()) sub)
  in
  (* Per-edge states read from single-predecessor targets' IN-states. *)
  let c_iter = AI.find_word 32 (Graphlib.Std.Solution.get sol body_tid) i in
  let c_exit = AI.find_word 32 (Graphlib.Std.Solution.get sol exit_tid) i in
  check
    "D4-9 (BIR loop): the partition — the iterate view's counter is bounded by the guard (⊆ [0,4]) \
     and the exit view carries the exit-iteration values (min ≥ 5)"
    ((not (Ws.is_top c_iter))
    && (match Ws.max_elem c_iter with Some w -> Word.( <= ) w (w32 4) | None -> false)
    && (not (Ws.is_top c_exit))
    && match Ws.min_elem c_exit with Some w -> Word.( >= ) w (w32 5) | None -> false);
  ())
(* Ite else-arm joins both arms. *)
;
(  (* {0,1}-valued Ite cond must not kill the else value. *)
  let f32 = Var.create ~is_virtual:false ~fresh:false "flag32" (Type.Imm 32) in
  let env = AI.add_word AI.top ~key:f32 ~data:(Ws.of_list ~width:32 [ w32 0; w32 1 ]) in
  let e = Bil.Ite (Bil.Var f32, Bil.Int (w32 10), Bil.Int (w32 20)) in
  match Vsa.denote_imm_exp e env with
  | Ok ws ->
      check "E3-1: Ite with a {0,1}-valued flag joins both arms (no bottom)"
        (Ws.elem (w32 10) ws && Ws.elem (w32 20) ws && not (Ws.is_bottom ws))
  | Error _ ->
      check "E3-1: Ite with a {0,1}-valued flag joins both arms (no bottom)" false;
      ())
(* rshift/arshift width handling: mixed widths compute, overshift is zero. *)
;
(  let c32 = Clp.create (w32 16) in
  let c64 = Clp.create (w64 16) in
  (* Mixed-width operands compute via coerce-to-max (16 >> 16 = 0). *)
  check
    "D5-1: CLP rshift on mixed-width operands COMPUTES (lane A) — {0} exactly, no assert, no top"
    (Clp.equal (Clp.rshift c32 c64) (Clp.create (w32 0)));
  check
    "D5-2: CLP arshift on mixed-width operands COMPUTES (lane A) — {0} exactly, no assert, no top"
    (Clp.equal (Clp.arshift c32 c64) (Clp.create (w32 0)));
  check "D5-3: CLP rshift/arshift on same-width singletons still exact"
    (let r = Clp.rshift (Clp.create (w32 16)) (Clp.create (w32 2)) in
     Clp.min_elem r = Some (w32 4)
     && Clp.max_elem r = Some (w32 4)
     &&
     let a = Clp.arshift (Clp.create (w32 16)) (Clp.create (w32 2)) in
     Clp.min_elem a = Some (w32 4) && Clp.max_elem a = Some (w32 4));
  (* Overshift amount (>= width) is bitvec zero, not top. *)
  check "D5-4: rshift by an amount >= the operand width -> {0} exactly (overshift=zero, no raise)"
    (let r = Clp.rshift (Clp.create (w32 1)) (Clp.create (w32 32)) in
     Clp.min_elem r = Some (w32 0)
     && Clp.max_elem r = Some (w32 0)
     && W.to_int_exn (Clp.cardinality r) = 1
     && (not (Clp.is_top r))
     && not (Clp.is_bottom r));
  check "D5-5: rshift by an amount < the operand width still computes"
    (let r = Clp.rshift (Clp.create (w32 8)) (Clp.create (w32 3)) in
     Clp.min_elem r = Some (w32 1) && Clp.max_elem r = Some (w32 1));
  (* Composite level: mixed-width CLPs via WordSet. *)
  let big32 = Ws.of_list ~width:32 (List.init 11 (fun i -> w32 (i * 2))) in
  let big64 = Ws.of_list ~width:64 (List.init 11 (fun i -> w64 (i * 2))) in
  check "D5-6: composite rshift on mixed-width CLPs COMPUTES (lane A) — non-top, no assert"
    (not (Ws.is_top (Ws.rshift big32 big64)));
  check "D5-7: composite arshift on mixed-width CLPs COMPUTES (lane A) — non-top, no assert"
    (not (Ws.is_top (Ws.arshift big32 big64)));
  check "D5-8: composite rshift on same-width singletons still exact"
    (let r = Ws.rshift (Ws.singleton (w32 16)) (Ws.singleton (w32 2)) in
     Ws.elem (w32 4) r && (not (Ws.is_top r)) && not (Ws.is_bottom r));
  ())
(* Coercing width helper: mismatched ops coerce, never raise. *)
;
(  let p32 = Clp.of_list ~width:32 [ w32 1; w32 2 ] in
  let p64 = Clp.of_list ~width:64 [ w64 1; w64 2 ] in
  check "D6-1: CLP equal on width-mismatched CLPs -> false (no raise)"
    ((not (Clp.equal p32 p64)) && not (Clp.equal p64 p32));
  check "D6-2: CLP subset on width-mismatched CLPs -> false (no raise)"
    ((not (Clp.subset p32 p64)) && not (Clp.subset p64 p32));
  check "D6-3: CLP intersection on width-mismatched CLPs -> wider operand"
    (let r = Clp.intersection p32 p64 in
     Clp.bitwidth r = 64 && Clp.equal r p64);
  check "D6-4: CLP add on width-mismatched CLPs -> coerced result (no raise)"
    (let r = Clp.add p32 p64 in
     Clp.bitwidth r = 64 && Clp.elem (w64 2) r && Clp.elem (w64 3) r && Clp.elem (w64 4) r);
  check "D6-5: CLP mul on width-mismatched CLPs -> coerced result (no raise)"
    (let r = Clp.mul p32 p64 in
     Clp.bitwidth r = 64 && Clp.elem (w64 1) r && Clp.elem (w64 4) r);
  check "D6-6: CLP logand on width-mismatched CLPs -> no raise, width 64"
    (let r = Clp.logand p32 p64 in
     Clp.bitwidth r = 64 && not (Clp.is_bottom r));
  check "D6-7: CLP logxor on width-mismatched CLPs -> no raise, width 64"
    (let r = Clp.logxor p32 p64 in
     Clp.bitwidth r = 64 && not (Clp.is_bottom r));
  check "D6-8: CLP div on width-mismatched CLPs -> no raise, width 64"
    (let r = Clp.div p32 p64 in
     Clp.bitwidth r = 64 && not (Clp.is_bottom r));
  check "D6-9: CLP sdiv on width-mismatched CLPs -> no raise, width 64"
    (let r = Clp.sdiv p32 p64 in
     Clp.bitwidth r = 64 && not (Clp.is_bottom r));
  check "D6-10: CLP union/join on width-mismatched CLPs -> no raise, width 64"
    (let r = Clp.join p32 p64 in
     Clp.bitwidth r = 64 && Clp.elem (w64 1) r && Clp.elem (w64 2) r);
  check "D6-11: CLP widen_join on width-mismatched CLPs -> no raise"
    (let r = Clp.widen_join p32 p64 in
     Clp.bitwidth r = 64 && Clp.elem (w64 1) r);
  check "D6-12: CLP meet (alias) on width mismatch -> wider operand"
    (let r = Clp.meet p32 p64 in
     Clp.bitwidth r = 64 && Clp.equal r p64);
  check "D6-13: same-width CLP ops unaffected (regression)"
    (let q = Clp.of_list ~width:32 [ w32 10; w32 12 ] in
     let r = Clp.add p32 q in
     Clp.bitwidth r = 32 && Clp.elem (w32 11) r && Clp.elem (w32 13) r);
  ())
;
(  (* Exit state is block INPUT (j absent): denote the def to read the postcond. *)
  let j = Var.create ~is_virtual:false ~fresh:false "j" (Type.Imm 32) in
  let _, ctx, sub, exit_tid =
    mk_counter_loop ~exit_defs:(fun i ->
        [ Def.create j (Bil.BinOp (Bil.RSHIFT, Bil.Var i, Bil.Int (w64 1))) ])
  in
  (* Mixed-width rshift computes: no guard fire, j non-top. *)
  let comp = "rshift: mixed-width shift operands (32 and 64 bits)" in
  let fired_r =
    fired comp (fun () ->
        ignore (Vsa.static_graph_vsa [] ctx sub (Vsa.init_sol ~entry:(anchored_entry ()) sub)))
  in
  let sol = Vsa.static_graph_vsa [] ctx sub (Vsa.init_sol ~entry:(anchored_entry ()) sub) in
  let exit_ai = Graphlib.Std.Solution.get sol exit_tid in
  let i = Var.create ~is_virtual:false ~fresh:false "i" (Type.Imm 32) in
  let j_after =
    Vsa.denote_def
      (Def.create j (Bil.BinOp (Bil.RSHIFT, Bil.Var i, Bil.Int (w64 1))))
      exit_ai
  in
  check "D6-14 (BIR loop): mixed-width rshift COMPUTES (lane A), no crash, no guard fire"
    ((not fired_r) && not (Ws.is_top (AI.find_word 32 j_after j)));
  ())
(* FinSet lift2 default width: mismatched sets widen to 64, never raise. *)
;
(  let f32 = Fs.of_list ~width:32 [ w32 1; w32 2 ] in
  let f64 = Fs.of_list ~width:64 [ w64 1; w64 2 ] in
  check "D6b-1: FinSet union on width-mismatched sets -> no assert, width 64"
    (let r = Fs.union f32 f64 in
     Fs.bitwidth r = 64);
  check "D6b-2: FinSet intersection on width-mismatched sets -> no assert, width 64"
    (let r = Fs.intersection f32 f64 in
     Fs.bitwidth r = 64);
  check "D6b-3: FinSet add on width-mismatched sets -> no assert, width 64"
    (let r = Fs.add f32 f64 in
     Fs.bitwidth r = 64);
  check "D6b-4: same-width FinSet union/intersection still exact (regression)"
    (let a = Fs.of_list ~width:32 [ w32 1; w32 2 ] in
     let b = Fs.of_list ~width:32 [ w32 2; w32 3 ] in
     Fs.equal (Fs.union a b) (Fs.of_list ~width:32 [ w32 1; w32 2; w32 3 ])
     && Fs.equal (Fs.intersection a b) (Fs.of_list ~width:32 [ w32 2 ]));
  ())
(* not_implemented logging: Event.Log only, stderr stays clean. *)
;
(  let probe = "e6-log-probe" in
  let captured =
    capture_stderr (fun () ->
        List.iter (fun _ -> ignore (Cbat_vsa_utils.not_implemented ~top:42 probe)) [ 1; 2; 3; 4; 5 ])
  in
  let probe_lines =
    String.split_on_char '\n' captured |> List.filter (fun l -> contains_substring l probe)
  in
  (* not_implemented logs through BAP Event.Log only. *)
  check "E6-1: no per-hit stderr line naming the component (Event.Log only)"
    (List.length probe_lines = 0);
  check "E6-2: no not_implemented marker leaks to stderr at all"
    ((not (contains_substring captured "not_implemented"))
    && not (contains_substring captured "(degrading to top)"));
  ())
;
(* T1 deleted (spec §2.1): every def is denoted, no tag needed. *)
(  let iv = v64 "t2_iv" in
  let d = Def.create iv (Bil.Int (w64 7)) in
  let e_den = Vsa.denote_def d AI.top in
  check "T2-1: gate-free — every def is denoted, no tag needed"
    (Ws.equal (AI.find_word 64 e_den iv) (Ws.singleton (w64 7)));
  ()

(* Frozen-flag fixture: f := g/h, stack-access load, unrelated-def control, jmp exit if f. *))
;
(  let x = v64 "t3_x" in
  let tgt = Tid.create () in
  let mk_jmp cond = Jmp.create ~cond (Goto (Direct tgt)) in
  let c_in =
    AI.find_word 64
      (Vsa.assume_jump_cond AI.top
         (mk_jmp (Bil.BinOp (Bil.EQ, Bil.Var x, Bil.Int (w64 5)))))
      x
  in
  check "T3-1: gate-free — the guard refines x to {5}"
    (Ws.min_elem c_in = Some (w64 5) && Ws.max_elem c_in = Some (w64 5));
  let c_out =
    AI.find_word 64
      (Vsa.assume_jump_cond AI.top
         (mk_jmp (Bil.BinOp (Bil.EQ, Bil.Var x, Bil.Int (w64 5)))))
      x
  in
  check "T3-2: gate-free (spec §2.1) — the guard refines x to {5}"
    (Ws.min_elem c_out = Some (w64 5) && Ws.max_elem c_out = Some (w64 5));
  ())
;
(  (* G3: gate-free flag-guard refinement (spec §2.1). *)
  let f, ctx, sub, exit_tid, _, _, _ = mk_flag_sub ~mixed:true in
  let ctx' = Program.create ~subs:[ sub ] () in
  let sol =
    Vsa.static_graph_vsa [] ctx' sub (Vsa.init_sol ~entry:(anchored_entry ()) sub)
  in
  ignore sol;
  (* Exit IN-state is the taken-edge refined state; the fallthrough edge has no target block. *)
  let c = AI.find_word 1 (Graphlib.Std.Solution.get sol exit_tid) f in
  check "T3-7: mixed-def — f IS refined to {1} on the taken edge"
    (Ws.elem Word.b1 c && not (Ws.elem Word.b0 c));
  check "T3-7b (UNASSERTABLE in the fused world — the fixture's fallthrough edge has no target block; kept for the ignore-list bookkeeping, see the comment above)" false;
  (* Single-def control refines identically. *)
  let f2, ctx2, sub2, exit_tid2, _, _, _ = mk_flag_sub ~mixed:false in
  let ctx2' = Program.create ~subs:[ sub2 ] () in
  let sol2 =
    Vsa.static_graph_vsa [] ctx2' sub2 (Vsa.init_sol ~entry:(anchored_entry ()) sub2)
  in
  let c2 = AI.find_word 1 (Graphlib.Std.Solution.get sol2 exit_tid2) f2 in
  check "T3-8: single-def flag — f2 IS refined to {1} on the taken edge"
    (Ws.elem Word.b1 c2 && not (Ws.elem Word.b0 c2));
  ()

(* Caller-alias fixture: aliased slot, tracked load, call, post reload. Returns the record. *))
;
(  let fx = mk_caller_alias () in
  let sub = fx.ca_sub in
  (* Pre-call state makes the post-call check non-vacuous. *)
  let entry_blk' =
    match Term.find blk_t sub (Term.tid fx.ca_entry_blk) with Some b -> b | None -> assert false
  in
  let pre = Vsa.denote_defs entry_blk' AI.top in
  let mkey =
    match Mem.Key.of_wordset (Ws.singleton (w64 0xd0)) with Some k -> k | None -> assert false
  in
  let pre_val =
    Mem.Val.data
      (Mem.find (64, LittleEndian)
         (AI.find_memory { addr_width = 64; addressable_width = 8 } pre fx.ca_m)
         mkey)
  in
  check "T4-5: pre-call the aliased slot holds {42} (non-vacuous pin)"
    (Ws.equal pre_val (Ws.singleton (w64 42)));
  check "T4-6: pre-call rdi is the concrete address {0xd0} (the alias)"
    (Ws.equal (AI.find_word 64 pre fx.ca_rdi) (Ws.singleton (w64 0xd0)));
  (* Gate-free fixpoint on the raw sub. *)
  let ctx' = Program.create ~subs:[ sub ] () in
  let sol = Vsa.static_graph_vsa [] ctx' sub (Vsa.init_sol ~entry:(anchored_entry ()) sub) in
  let post_ai = Graphlib.Std.Solution.get sol fx.ca_post_tid in
  check "T4-7: caller-alias — the post-call reload reads TOP (sound)"
    (Ws.is_top (AI.find_word 64 post_ai fx.ca_r2));
  check "T4-8: post-call memory is TOP entirely (find_memory = Mem.top)"
    (Mem.equal
       (AI.find_memory { addr_width = 64; addressable_width = 8 } post_ai fx.ca_m)
       (Mem.top { addr_width = 64; addressable_width = 8 }));
  check "T4-9: RSP is preserved across the call"
    (Ws.equal (AI.find_word 64 post_ai fx.ca_rsp) (Ws.singleton (w64 0x2000)));
  check "T4-10: RBP is preserved across the call"
    (Ws.equal (AI.find_word 64 post_ai fx.ca_rbp) (Ws.singleton (w64 0x100)));
  check "T4-11: callee-saved RBX is preserved across the call"
    (Ws.equal (AI.find_word 64 post_ai fx.ca_rbx) (Ws.singleton (w64 0x2040)));
  check "T4-12: caller-saved rdi is TOPed across the call"
    (Ws.is_top (AI.find_word 64 post_ai fx.ca_rdi));
  ())
;
(  let m = Map.add (Map.add Map.top ~key:1 ~data:10) ~key:2 ~data:20 in
  let seen = Map.fold m ~init:[] ~f:(fun ~key ~data acc -> (key, data) :: acc) in
  check "F1-1: fold enumerates the explicitly-stored bindings (keys+data)"
    (List.sort compare seen = [ (1, 10); (2, 20) ]);
  check "F1-2: fold over top (absent = top) visits nothing"
    (Map.fold Map.top ~init:[] ~f:(fun ~key ~data acc -> (key, data) :: acc) = []);
  ()

(* C1: call_abstraction — preserved words kept, rest TOPed, memory TOPed. *))
;
(  let x = v64 "c1_x" in
  let y = v64 "c1_y" in
  let rsp = v64 "RSP" in
  let env =
    AI.add_word
      (AI.add_word AI.top ~key:x ~data:(Ws.singleton (w64 5)))
      ~key:y
      ~data:(Ws.singleton (w64 7))
  in
  let env' = AI.call_abstraction ~preserved:(Var.Set.singleton x) env in
  check "C1-1: a preserved word keeps its value-set"
    (Ws.equal (AI.find_word 64 env' x) (Ws.singleton (w64 5)));
  check "C1-2: a non-preserved word is TOPed" (Ws.is_top (AI.find_word 64 env' y));
  let env'' = AI.add_word env ~key:rsp ~data:(Ws.singleton (w64 0x10)) in
  let e' = AI.call_abstraction ~preserved:(Var.Set.of_list [ x; rsp ]) env'' in
  check "C1-3: RSP is preserved when it is in the preserved set"
    (Ws.equal (AI.find_word 64 e' rsp) (Ws.singleton (w64 0x10))
    && Ws.equal (AI.find_word 64 e' x) (Ws.singleton (w64 5)));
  let m0 = memv "c1_m0" in
  let mkey =
    match Mem.Key.of_wordset (Ws.singleton (w64 0x10)) with Some k -> k | None -> assert false
  in
  let mem =
    Mem.add
      (Mem.top { addr_width = 64; addressable_width = 8 })
      ~key:mkey
      ~data:(Mem.Val.create (Ws.singleton (w64 0x11)) LittleEndian)
  in
  let env_m = AI.add_memory AI.top ~key:m0 ~data:mem in
  let e_m = AI.call_abstraction ~preserved:Var.Set.empty env_m in
  check "C1-4: memory is TOPed entirely (a stored value reads as top)"
    (Mem.equal
       (AI.find_memory { addr_width = 64; addressable_width = 8 } e_m m0)
       (Mem.top { addr_width = 64; addressable_width = 8 }));
  let vv = Var.create ~is_virtual:true ~fresh:false "c1_vv" (Type.Imm 64) in
  let env_v = AI.add_word AI.top ~key:vv ~data:(Ws.singleton (w64 3)) in
  let e_v = AI.call_abstraction ~preserved:(Var.Set.singleton vv) env_v in
  check "C1-5: a virtual var is preserved when it is in the preserved set"
    (Ws.equal (AI.find_word 64 e_v vv) (Ws.singleton (w64 3)));
  ())
;
(  (* Channel-1 pin (spec §2.2): the prologue + frame-affine accesses seed. *)
  let extract_of (sub : sub term) : Cu.vsa_kind Tid.Map.t =
    let prog = Program.create ~subs:[ sub ] () in
    let sol =
      Vsa.static_graph_vsa [] prog sub (Vsa.init_sol ~entry:(anchored_entry ()) sub)
    in
    let offsets, _, _ =
      Vsa.Cbat_extraction.extract ~sp ~dynamic_alloc:(fun _ -> false) ~sol sub
    in
    offsets
  in
  let _, def_load, def_store, sub = mk_rsp_prologue_sub () in
  let tags = extract_of sub in
  check "P21-1: channel 1 — the load at [RBP - 0x30] seeds Range(-48,-48)"
    (Core.Map.find tags (Term.tid def_load) = Some (Cu.Range (-48L, -48L)));
  check "P21-2: channel 1 — the store at [RBP - 0x30] seeds Range(-48,-48)"
    (Core.Map.find tags (Term.tid def_store) = Some (Cu.Range (-48L, -48L)));
  ()

(* RSP-derived base with index; the indexed load seeds. *))
;
(  let _, def_load, sub = mk_rsp_index_sub () in
  let prog = Program.create ~subs:[ sub ] () in
  let sol =
    Vsa.static_graph_vsa [] prog sub (Vsa.init_sol ~entry:(anchored_entry ()) sub)
  in
  let tags, _, _ =
    Vsa.Cbat_extraction.extract ~sp ~dynamic_alloc:(fun _ -> false) ~sol sub
  in
  check "P22-1: channel 1 — the indexed load at [rdi + idx*8] seeds Range(32,32)"
    (Core.Map.find tags (Term.tid def_load) = Some (Cu.Range (32L, 32L)));
  ()

(* Heap-shaped addresses do not seed; the RSP-direct access does. *))
;
(  let _, _, def_load, def_store_disjoint, def_store_rsp, sub = mk_gpr_rbp_sub () in
  let prog = Program.create ~subs:[ sub ] () in
  let sol =
    Vsa.static_graph_vsa [] prog sub (Vsa.init_sol ~entry:(anchored_entry ()) sub)
  in
  let tags, _, _ =
    Vsa.Cbat_extraction.extract ~sp ~dynamic_alloc:(fun _ -> false) ~sol sub
  in
  check "P23-1: channel 2 — the load at [rbp + idx*8] (denotes outside the neighborhood) is NOT seeded"
    (Core.Map.find tags (Term.tid def_load) = None);
  check "P23-2: channel 2 — the disjoint store at [rbp + 0x100] is NOT seeded"
    (Core.Map.find tags (Term.tid def_store_disjoint) = None);
  check "P23-3: channel 1 — the RSP-direct store at [RSP - 8] seeds Range(-8,-8)"
    (Core.Map.find tags (Term.tid def_store_rsp) = Some (Cu.Range (-8L, -8L)));
  ())
;
(  let _, def_load, _, def_use, sub = mk_one_path_sub () in
  let prog = Program.create ~subs:[ sub ] () in
  let sol =
    Vsa.static_graph_vsa [] prog sub (Vsa.init_sol ~entry:(anchored_entry ()) sub)
  in
  let tags, _, _ =
    Vsa.Cbat_extraction.extract ~sp ~dynamic_alloc:(fun _ -> false) ~sol sub
  in
  check "F1-1: channel 1 — the on-path load at [rbp - 0x30] seeds Range(-48,-48)"
    (Core.Map.find tags (Term.tid def_load) = Some (Cu.Range (-48L, -48L)));
  check "F1-2: channel 2 — the use store at [rdi + 8] (rdi joins the TOP cell value) is NOT seeded"
    (Core.Map.find tags (Term.tid def_use) = None);
  ())
(* Degenerate cast/extract sizes degrade to top; shift guards compare magnitudes. *)
;
(  let c64 = Clp.create (w64 16) in
  let c32 = Clp.create (w32 16) in
  check "D7-1: Clp.cast HIGH sz=0 -> top(64), no raise" (Clp.is_top (Clp.cast Bil.HIGH 0 c64));
  check "D7-2: Clp.cast HIGH sz>width -> top(64), no raise" (Clp.is_top (Clp.cast Bil.HIGH 128 c64));
  check "D7-3: Clp.cast UNSIGNED sz=0 -> top(32), no raise"
    (Clp.is_top (Clp.cast Bil.UNSIGNED 0 c32));
  check "D7-4: Clp.cast SIGNED sz=0 -> top(32), no raise" (Clp.is_top (Clp.cast Bil.SIGNED 0 c32));
  check "D7-5: Clp.cast LOW sz=0 -> top(32), no raise" (Clp.is_top (Clp.cast Bil.LOW 0 c32));
  check "D7-6: Clp.extract ~lo:width -> top (no assert)" (Clp.is_top (Clp.extract ~lo:32 c32));
  check "D7-7: Clp.extract ~hi:(-1) -> top (no raise)" (Clp.is_top (Clp.extract ~hi:(-1) c32));
  ())
;
(  (* FinSet singleton exercises the composite guard first. *)
  check "D7-8: composite cast HIGH sz=0 -> top(64) (CLP-backed top, not the FinSet.top stub)"
    (Ws.is_top (Ws.cast Bil.HIGH 0 (Ws.singleton (w64 16))));
  check "D7-9: composite extract hi<lo -> top(32)"
    (Ws.is_top (Ws.extract ~hi:0 ~lo:5 (Ws.singleton (w32 16))));
  check "D7-9b: composite extract hi<0 (lo defaults 0) -> top(32)"
    (Ws.is_top (Ws.extract ~hi:(-1) (Ws.singleton (w32 16))));
  ())
;
(  (* 2-bit amount vs 64-bit operand: magnitudes compared, no spurious fire. *)
  let w2 = W.of_int ~width:2 in
  let amt2 = Clp.of_list ~width:2 [ w2 2 ] in
  let lshift_comp = "During lshift, maximum element of CLP2 is >= CLP1's width" in
  let rshift_comp = "During rshift, maximum element of CLP2 is >= CLP1's width" in
  let arshift_comp = "During arshift, maximum element of CLP2 is >= CLP1's width" in
  (* Guard's stderr line must NOT appear. *)
  let fire_l = fired lshift_comp (fun () -> ignore (Clp.lshift (Clp.create (w64 16)) amt2)) in
  let fire_r = fired rshift_comp (fun () -> ignore (Clp.rshift (Clp.create (w64 16)) amt2)) in
  let fire_a = fired arshift_comp (fun () -> ignore (Clp.arshift (Clp.create (w64 16)) amt2)) in
  let r = Clp.lshift (Clp.create (w64 16)) amt2 in
  check "D7-10: lshift 2-bit {2} amount vs 64-bit operand -> computes {64}, no spurious fire"
    (Clp.bitwidth r = 64 && Clp.min_elem r = Some (w64 64) && (not (Clp.is_top r)) && not fire_l);
  (* Overshift is bitvec zero ({0} exactly), no fire. *)
  check "D7-11: lshift overshift (6-bit {40} amount vs 32-bit operand) -> {0} exactly, no fire"
    (let r = Clp.lshift (Clp.create (w32 8)) (Clp.of_list ~width:6 [ W.of_int ~width:6 40 ]) in
     Clp.min_elem r = Some (w32 0)
     && Clp.max_elem r = Some (w32 0)
     && W.to_int_exn (Clp.cardinality r) = 1
     && (not (Clp.is_top r))
     && not fire_l);
  (* 2-bit amounts take the mixed-width path (sound top); wrapped guard stays silent. *)
  (* 2-bit amount coerces to operand width; shift computes. *)
  check
    "D7-12: rshift 2-bit {2} amount vs 64-bit operand COMPUTES {4} (lane A), wrapped guard never \
     fires"
    (Clp.equal (Clp.rshift (Clp.create (w64 16)) amt2) (Clp.create (w64 4)) && not fire_r);
  check
    "D7-13: arshift 2-bit {2} amount vs 64-bit operand COMPUTES {4} (lane A), wrapped guard never \
     fires"
    (Clp.equal (Clp.arshift (Clp.create (w64 16)) amt2) (Clp.create (w64 4)) && not fire_a);
  (* Same-width overshift: rshift/arshift give {0} exactly. *)
  check "D7-14: rshift/arshift overshift ({40} vs 32-bit) -> {0} exactly, no fire"
    (let r = Clp.rshift (Clp.create (w32 8)) (Clp.of_list ~width:32 [ w32 40 ]) in
     let a = Clp.arshift (Clp.create (w32 8)) (Clp.of_list ~width:32 [ w32 40 ]) in
     Clp.min_elem r = Some (w32 0)
     && Clp.max_elem r = Some (w32 0)
     && W.to_int_exn (Clp.cardinality r) = 1
     && (not (Clp.is_top r))
     && Clp.min_elem a = Some (w32 0)
     && Clp.max_elem a = Some (w32 0)
     && W.to_int_exn (Clp.cardinality a) = 1
     && (not (Clp.is_top a))
     && (not fire_r) && not fire_a);
  ()

(* Crash shape: RAX := high:0[RAX] in the call's return target. Returns (rax, ctx, sub, final tid). *))
;
(  (* Restriction stays OFF: ON would skip the untagged cast, making the test vacuous. *)
  let rax, ctx, sub, final_tid = mk_high0_cast_sub () in
  let sol = Vsa.static_graph_vsa [] ctx sub (Vsa.init_sol ~entry:(anchored_entry ()) sub) in
  let final_ai = Graphlib.Std.Solution.get sol final_tid in
  check "D7-15 (BIR): RAX := high:0[RAX] after a call — fixpoint completes rc=0, RAX = top(64)"
    (Ws.is_top (AI.find_word 64 final_ai rax));
  ())
;
(  (* E2e-H: equal short-circuit changes no observable result. *)
  let p = Clp.of_list ~width:32 [ w32 1; w32 2; w32 4 ] in
  check "E2eH-1: equal on the SAME CLP value (physical identity) -> true" (Clp.equal p p);
  let q = Clp.of_list ~width:32 [ w32 1; w32 2; w32 4 ] in
  check "E2eH-2: equal on structurally-equal separately-built CLPs -> true" (Clp.equal p q);
  let r = Clp.of_list ~width:32 [ w32 1; w32 2; w32 3 ] in
  check "E2eH-3: unequal CLPs still compare false (canonize path intact)" (not (Clp.equal p r));
  check "E2eH-4: width-mismatched CLPs still compare false, no raise"
    (not (Clp.equal p (Clp.top 64)));
  ())
;
(  (* Guard's stderr line must NOT appear. *)
  let lshift_comp = "During lshift, maximum element of CLP2 is >= CLP1's width" in
  let rshift_comp = "During rshift, maximum element of CLP2 is >= CLP1's width" in
  let arshift_comp = "During arshift, maximum element of CLP2 is >= CLP1's width" in
  let fire_l =
    fired lshift_comp (fun () ->
        ignore (Clp.lshift (Clp.create (w64 16)) (Clp.of_list ~width:64 [ w64 64 ])))
  in
  let fire_r =
    fired rshift_comp (fun () ->
        ignore (Clp.rshift (Clp.create (w64 16)) (Clp.of_list ~width:64 [ w64 64 ])))
  in
  let fire_a =
    fired arshift_comp (fun () ->
        ignore (Clp.arshift (Clp.create (w64 16)) (Clp.of_list ~width:64 [ w64 64 ])))
  in
  let is_zero_clp (r : Clp.t) : bool =
    Clp.min_elem r = Some (w64 0)
    && Clp.max_elem r = Some (w64 0)
    && W.to_int_exn (Clp.cardinality r) = 1
    && (not (Clp.is_top r))
    && not (Clp.is_bottom r)
  in
  (* Fully overshifted (min >= width): exactly {0}. *)
  check "E2eC-1: lshift {16} by {64} (min >= width) -> EXACTLY {0}, no fire"
    (is_zero_clp (Clp.lshift (Clp.create (w64 16)) (Clp.of_list ~width:64 [ w64 64 ])) && not fire_l);
  check "E2eC-2: lshift {16} by multi-card overshift {64,68,72} stride 4 -> {0}, no fire"
    (let amt = Clp.create ~width:64 ~step:(w64 4) ~cardn:(W.of_int ~width:65 3) (w64 64) in
     is_zero_clp (Clp.lshift (Clp.create (w64 16)) amt) && not fire_l);
  check "E2eC-3: rshift {16} by {64} (min >= width) -> EXACTLY {0}, no fire"
    (is_zero_clp (Clp.rshift (Clp.create (w64 16)) (Clp.of_list ~width:64 [ w64 64 ])) && not fire_r);
  (* Overshift arshift: mixed-sign gives {0, all-ones}; pure signs collapse. *)
  check "E2eC-4: arshift overshift of a mixed-sign operand -> {0, all-ones}, no fire"
    (let mixed = Clp.of_list ~width:64 [ w64 1; W.lshift (w64 1) (w64 63) ] in
     let r = Clp.arshift mixed (Clp.of_list ~width:64 [ w64 64 ]) in
     W.to_int_exn (Clp.cardinality r) = 2
     && Clp.elem (w64 0) r
     && Clp.elem (W.ones 64) r
     && (not (Clp.elem (w64 1) r))
     && (not (Clp.is_top r))
     && not fire_a);
  check "E2eC-5: arshift overshift of a nonneg operand -> {0} exactly (sign-extension)"
    (is_zero_clp (Clp.arshift (Clp.create (w64 16)) (Clp.of_list ~width:64 [ w64 64 ]))
    && not fire_a);
  check "E2eC-6: arshift overshift of a negative operand -> {all-ones} exactly"
    (let r =
       Clp.arshift (Clp.create (W.lshift (w64 1) (w64 63))) (Clp.of_list ~width:64 [ w64 64 ])
     in
     Clp.min_elem r = Some (W.ones 64)
     && Clp.max_elem r = Some (W.ones 64)
     && W.to_int_exn (Clp.cardinality r) = 1
     && (not (Clp.is_top r))
     && not fire_a);
  (* Straddling (min < width <= max): capped exact path UNION overshift class. *)
  let straddle = Clp.create ~width:64 ~step:(w64 2) ~cardn:(W.of_int ~width:65 32) (w64 8) in
  check "E2eC-7: lshift {16} by straddling [8,70] step 2 -> non-top, contains capped image ∪ {0}"
    (let r = Clp.lshift (Clp.create (w64 16)) straddle in
     (not (Clp.is_top r))
     && (not (Clp.is_bottom r))
     && Clp.elem (w64 0) r (* overshift (and 16<<62 mod 2^64) *)
     && Clp.elem (w64 0x1000) r (* 16<<8 = capped min *)
     && Clp.elem (w64 0x4000) r (* 16<<10 *)
     && Clp.elem (w64 0x40000000) r (* 16<<30 *)
     && not fire_l);
  check "E2eC-8: rshift {2^40} by straddling [8,70] step 2 -> non-top, contains capped image ∪ {0}"
    (let r = Clp.rshift (Clp.create (W.lshift (w64 1) (w64 40))) straddle in
     (not (Clp.is_top r))
     && (not (Clp.is_bottom r))
     && Clp.elem (w64 0) r (* 2^40>>a = 0 for a >= 41 *)
     && Clp.elem (w64 1) r (* 2^40>>40 *)
     && Clp.elem (w64 4) r (* 2^40>>38 *)
     && Clp.elem (w64 0x100000000) r (* 2^40>>8 = capped min *)
     && not fire_r);
  check
    "E2eC-9: arshift {2^63} by straddling [8,70] step 2 -> non-top, contains capped base ∪ \
     {all-ones}"
    (let r = Clp.arshift (Clp.create (W.lshift (w64 1) (w64 63))) straddle in
     (not (Clp.is_top r))
     && (not (Clp.is_bottom r))
     && Clp.elem (W.ones 64) r (* overshift: amount 70 *)
     && Clp.elem (W.neg (W.lshift (w64 1) (w64 55))) r (* amount 8: sign-ext of 2^63>>8 = -2^55 *)
     && not fire_a);
  (* Full capped image of straddling arshift not asserted element-wise (step collapse). *)
  (* TOP amount caps to [0, width-1] at reachable stride. *)
  check
    "E2eC-10: lshift {16} by top(64) amount -> stride-class result (non-bottom, contains 0 and \
     16), no fire"
    (let r = Clp.lshift (Clp.create (w64 16)) (Clp.top 64) in
     (not (Clp.is_bottom r)) && Clp.elem (w64 0) r && Clp.elem (w64 16) r && not fire_l);
  (* Segment-width shifts fully overshifted give exactly {0}. *)
  check "E2eC-11: array_local pattern — 32-bit operand shifted by {32} -> {0} exactly, no fire"
    (let r = Clp.lshift (Clp.create (w32 1)) (Clp.of_list ~width:32 [ w32 32 ]) in
     Clp.min_elem r = Some (w32 0)
     && Clp.max_elem r = Some (w32 0)
     && W.to_int_exn (Clp.cardinality r) = 1
     && (not (Clp.is_top r))
     && not fire_l);
  check "E2eC-12: array_local pattern — 8-bit operand shifted by {8} -> {0} exactly, no fire"
    (let r =
       Clp.lshift (Clp.create (W.of_int ~width:8 1)) (Clp.of_list ~width:8 [ W.of_int ~width:8 8 ])
     in
     Clp.min_elem r = Some (W.of_int ~width:8 0)
     && Clp.max_elem r = Some (W.of_int ~width:8 0)
     && (not (Clp.is_top r))
     && not fire_l);
  ()

(* BIR loop with counter-shift: [0,N) window survives the shift. *))
;
(  let i = Var.create ~is_virtual:false ~fresh:false "i" (Type.Imm 32) in
  let x = Var.create ~is_virtual:false ~fresh:false "x" (Type.Imm 64) in
  let y = Var.create ~is_virtual:false ~fresh:false "y" (Type.Imm 64) in
  let iv = Bil.Var i in
  let xv = Bil.Var x in
  let lt5 = Bil.BinOp (Bil.LT, iv, Bil.Int (w32 5)) in
  let nlt5 = Bil.UnOp (Bil.NOT, lt5) in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b (Def.create i (Bil.Int (w32 0)));
  Blk.Builder.add_def entry_b (Def.create x (Bil.Int (w64 16)));
  Blk.Builder.add_def body_b (Def.create i (Bil.BinOp (Bil.PLUS, iv, Bil.Int (w32 1))));
  (* Body increments first: y = x << (i+1) ∈ {32..512}, in case 1. *)
  Blk.Builder.add_def body_b (Def.create y (Bil.BinOp (Bil.LSHIFT, xv, iv)));
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
  Blk.Builder.add_jmp header_b (Jmp.create ~cond:nlt5 (Goto (Direct exit_tid)));
  Blk.Builder.add_jmp header_b (Jmp.create ~cond:lt5 (Goto (Direct body_tid)));
  let entry = Blk.Builder.result entry_b in
  let body = Blk.Builder.result body_b in
  let header = Blk.Builder.result header_b in
  let exit = Blk.Builder.result exit_b in
  let sub_b = Sub.Builder.create ~name:"e2ec_loop" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  let ctx = Program.create ~subs:[ sub ] () in
  let sol =
    Vsa.static_graph_vsa [] ctx sub (Vsa.init_sol ~entry:(anchored_entry ()) sub)
  in
  (* Single-predecessor IN-states are the per-edge refined states. *)
  let c_iter = AI.find_word 32 (Graphlib.Std.Solution.get sol body_tid) i in
  let c_exit = AI.find_word 32 (Graphlib.Std.Solution.get sol exit_tid) i in
  check
    "E2eC-13 (BIR loop): the partition — the iterate view's counter is bounded by the guard (⊆ \
     [0,4]) and the exit view carries the exit-iteration values (min ≥ 5)"
    ((not (Ws.is_top c_iter))
    && (match Ws.max_elem c_iter with Some w -> Word.( <= ) w (w32 4) | None -> false)
    && (not (Ws.is_top c_exit))
    && match Ws.min_elem c_exit with Some w -> Word.( >= ) w (w32 5) | None -> false);
  (* Shifted value's window: counter ⊆ [0,4] at the guard. *)
  let c_iter = AI.find_word 32 (Graphlib.Std.Solution.get sol body_tid) i in
  check
    "E2eC-14 (BIR loop): the counter window survives the body shift — the iterate view's counter \
     stays ⊆ [0,4] (y = x << (i+1) ∈ {32..512})"
    ((not (Ws.is_top c_iter))
    && match Ws.max_elem c_iter with Some w -> Word.( <= ) w (w32 4) | None -> false);
  ())
;
(  (* Channel-2 negative (spec §2.2): the heap-indexed store never seeds. *)
  let _, _, _, _, sub, exit_tid = mk_e2ed_heap_sub () in
  (* Gate-free: every def is denoted, so the store's data var reads {99}. *)
  let ctx' = Program.create ~subs:[ sub ] () in
  let sol = Vsa.static_graph_vsa [] ctx' sub (Vsa.init_sol ~entry:(anchored_entry ()) sub) in
  let exit_ai = Graphlib.Std.Solution.get sol exit_tid in
  let vv = AI.find_word 64 exit_ai (v64 "e2ed_v") in
  check "E2eD-4: gate-free — the heap store's data var is denoted ({99})"
    (Ws.equal vv (Ws.singleton (w64 99)));
  ()

(* Channel-1 indexed-store pin: same shape seeds without any tagger. *))
;
(  let _, _, def_store, sub, _ = mk_e2ed_rsp_store_sub () in
  let prog = Program.create ~subs:[ sub ] () in
  let sol =
    Vsa.static_graph_vsa [] prog sub (Vsa.init_sol ~entry:(anchored_entry ()) sub)
  in
  let tags, _, _ =
    Vsa.Cbat_extraction.extract ~sp ~dynamic_alloc:(fun _ -> false) ~sol sub
  in
  check "E2eD-5: channel 1 — the indexed store at [(rbp - 0x30) + i*8] seeds Range(-24,-24)"
    (Core.Map.find tags (Term.tid def_store) = Some (Cu.Range (-24L, -24L)));
  ()

(* E3: top-address stores leave memory unchanged; the slot load reads through. *))
;
(  let m = memv "e2ed_m3" in
  let t = v64 "e2ed_t3" in
  let d1 =
    Def.create m
      (Bil.Store (Bil.Var m, Bil.Int (w64 0x100), Bil.Int (w64 42), LittleEndian, `r64))
  in
  let env1 = Vsa.denote_def d1 AI.top in
  let d2 =
    Def.create m
      (Bil.Store
         (Bil.Var m, Bil.Unknown ("e2ed_top", Type.Imm 64), Bil.Int (w64 7), LittleEndian, `r64))
  in
  let dload = Def.create t (Bil.Load (Bil.Var m, Bil.Int (w64 0x100), LittleEndian, `r64)) in
  let env2 = Vsa.denote_def d2 env1 in
  check "E2eD-7: gate-free — a top-addr store leaves memory unchanged"
    (AI.equal env2 env1);
  let env3 = Vsa.denote_def dload env2 in
  let tv = AI.find_word 64 env3 t in
  check
    "E2eD-8: gate-free — the load at the slot reads exactly the pre-store value {42} (no \
     full-range-cell pollution)"
    (Ws.equal tv (Ws.singleton (w64 42)));
  ())
;
(  let rsp_var = v64 "RSP" in
  let entry_tid_of (sub : sub term) : tid =
    match Term.first blk_t sub with Some b -> Term.tid b | None -> assert false
  in
  (* Gate-free production shape: entry input carries RSP = {0}. *)
  let sub = mk_p3_anchor_sub () in
  let prog' = Program.create ~subs:[ sub ] () in
  let sol = Vsa.static_graph_vsa [] prog' sub (Vsa.init_sol ~entry:(anchored_entry ()) sub) in
  let st = Graphlib.Std.Solution.get sol (entry_tid_of sub) in
  check
    "P3-1: gate-free — the RSP := 0 anchor is denoted (entry input state \
     carries RSP = {0})"
    (Ws.equal (AI.find_word 64 st rsp_var) (Ws.singleton (w64 0)));
  ())
;
(  let full = Ws.top 1 in
  let full_l = Ws.of_list ~width:1 [ W.b0; W.b1 ] in
  check
    "L2b-1: the full 1-bit domain {0,1} reads cardn 2 (non-bottom; the FinSet cardinality no \
     longer wraps at the set width)"
    ((not (Ws.is_bottom full))
    && Word.( = ) (Ws.cardinality full) (W.of_int ~width:2 2)
    && (not (Ws.is_bottom full_l))
    && Word.( = ) (Ws.cardinality full_l) (W.of_int ~width:2 2));
  ()

(* L2b-2: EQ over {0,1} — is_zero guard sees unwrapped cardn. *))
;
(  let zf = v1 "l2b_zf2" in
  let env = AI.add_word AI.top ~key:zf ~data:(Ws.of_list ~width:1 [ W.b0; W.b1 ]) in
  let e = Bil.BinOp (Bil.EQ, Bil.Var zf, Bil.Int W.b0) in
  match Vsa.denote_imm_exp e env with
  | Ok ws ->
      check
        "L2b-2: EQ over a {0,1} operand is {0,1} (bool_top), not bottom — the is_zero guard sees \
         cardn 2"
        ((not (Ws.is_bottom ws)) && Word.( = ) (Ws.cardinality ws) (W.of_int ~width:2 2))
  | Error _ ->
      check
        "L2b-2: EQ over a {0,1} operand is {0,1} (bool_top), not bottom — the is_zero guard sees \
         cardn 2"
        false;
      ()

(* L2b-3: lifted 1-bit flag value via unknown[bits]:u1 def. *))
;
(  let pf = v1 "l2b_pf3" in
  let env_after = Vsa.denote_def (Def.create pf (Bil.Unknown ("l2b_bits", Type.Imm 1))) AI.top in
  let ws = AI.find_word 1 env_after pf in
  check "L2b-3: a lifted 1-bit flag def (val_top (Imm 1)) is {0,1} with cardn 2, not bottom"
    ((not (Ws.is_bottom ws)) && Word.( = ) (Ws.cardinality ws) (W.of_int ~width:2 2));
  ()

(* L2b-4: overlap comparisons return bool_top, not bottom. *))
;
(  let x = v64 "l2b_x4" in
  let y = v64 "l2b_y4" in
  let z = v64 "l2b_z4" in
  let ok_lt =
    match Vsa.denote_imm_exp (Bil.BinOp (Bil.LT, Bil.Var x, Bil.Var y)) AI.top with
    | Ok ws -> (not (Ws.is_bottom ws)) && Word.( = ) (Ws.cardinality ws) (W.of_int ~width:2 2)
    | Error _ -> false
  in
  let ok_eq =
    match Vsa.denote_imm_exp (Bil.BinOp (Bil.EQ, Bil.Int (w64 0), Bil.Var z)) AI.top with
    | Ok ws -> (not (Ws.is_bottom ws)) && Word.( = ) (Ws.cardinality ws) (W.of_int ~width:2 2)
    | Error _ -> false
  in
  check
    "L2b-4: overlap comparisons (LT over two top64 operands; EQ(0, top64)) are {0,1} (bool_top), \
     not bottom"
    (ok_lt && ok_eq);
  ()

(* L2b-5: flag-gated branch survives — no unsound pruning. *))
;
(  let zf = v1 "l2b_zf5" in
  let x = v64 "l2b_x5" in
  let flag_env =
    Vsa.denote_def (Def.create zf (Bil.BinOp (Bil.EQ, Bil.Int (w64 0), Bil.Var x))) AI.top
  in
  let flag_val = AI.find_word 1 flag_env zf in
  (* (a) direct reachable_jumps on a flag-gated jump *)
  let b1 = Blk.Builder.create () in
  let b2 = Blk.Builder.create () in
  let blk1 = Blk.Builder.result b1 in
  let blk2 = Blk.Builder.result b2 in
  let t2 = Term.tid blk2 in
  let b1' = Blk.Builder.init ~copy_defs:true blk1 in
  Blk.Builder.add_jmp b1' (Jmp.create ~cond:(Bil.Var zf) (Goto (Direct t2)));
  let blk1' = Blk.Builder.result b1' in
  let jmp = match Term.enum jmp_t blk1' |> Seq.to_list with [ j ] -> j | _ -> assert false in
  let kept = Vsa.reachable_jumps flag_env (Seq.of_list [ jmp ]) |> Seq.to_list in
  (* (b) loop with flag-gated back-edge. *)
  let cnt = v64 "l2b_cnt5" in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b (Def.create zf (Bil.BinOp (Bil.EQ, Bil.Int (w64 0), Bil.Var x)));
  Blk.Builder.add_def body_b (Def.create cnt (Bil.BinOp (Bil.PLUS, Bil.Var cnt, Bil.Int (w64 1))));
  let entry0 = Blk.Builder.result entry_b in
  let body0 = Blk.Builder.result body_b in
  let header0 = Blk.Builder.result header_b in
  let exit0 = Blk.Builder.result exit_b in
  let body_tid = Term.tid body0 in
  let exit_tid = Term.tid exit0 in
  let header_tid = Term.tid header0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct header_tid)));
  let body_b = Blk.Builder.init ~copy_defs:true body0 in
  Blk.Builder.add_jmp body_b (Jmp.create (Goto (Direct header_tid)));
  let header_b = Blk.Builder.init ~copy_defs:true header0 in
  Blk.Builder.add_jmp header_b (Jmp.create ~cond:(Bil.Var zf) (Goto (Direct body_tid)));
  Blk.Builder.add_jmp header_b
    (Jmp.create ~cond:(Bil.UnOp (Bil.NOT, Bil.Var zf)) (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let body = Blk.Builder.result body_b in
  let header = Blk.Builder.result header_b in
  let exit = Blk.Builder.result exit_b in
  let sub_b = Sub.Builder.create ~name:"l2b_flag_loop" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  let ctx = Program.create ~subs:[ sub ] () in
  let sol = Vsa.static_graph_vsa [] ctx sub (Vsa.init_sol ~entry:(anchored_entry ()) sub) in
  let body_st = Graphlib.Std.Solution.get sol body_tid in
  let body_flag = AI.find_word 1 body_st zf in
  check
    "L2b-5: a flag-gated branch survives — reachable_jumps keeps the {0,1}-flag jump and the loop \
     body's solution input is non-bottom with a non-bottom flag (no unsound pruning)"
    ((not (Ws.is_bottom flag_val))
    && List.length kept = 1
    && (not (AI.equal body_st AI.bottom))
    && (not (Ws.is_bottom body_flag))
    (* Taken edge narrows {0,1} to {1}; both contain b1. *)
    && Ws.elem W.b1 body_flag);
  ())
