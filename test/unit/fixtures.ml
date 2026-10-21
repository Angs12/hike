(* Shared fixture vocabulary: BIR builders, loop families, run helpers.
   Split from test_common.ml (harness stays there). *)

open Bap.Std
open Bap_core_theory
open Common
open Harness

let mk_env binds = List.fold_left (fun e (v, ws) -> AI.add_word e ~key:v ~data:ws) AI.top binds

(* A conditional/terminal jump to an explicit target tid. *)
let mk_jmp_to tgt cond = Jmp.create ~cond (Goto (Direct tgt))

(* An unconditional jump to an explicit target tid. *)
let mk_goto (tgt : tid) : jmp term = Jmp.create (Goto (Direct tgt))

(* A terminal Ret to a fresh tid (the exit-block idiom); the edge maker
   ignores the node index. *)
let mk_ret : tid -> jmp term = fun _ -> Hike_return.create ()

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

(* The j-th jmp of the i-th block (the DSL's read-back for jmp tids). *)
let sub_jmp (sub : sub term) (i : int) (j : int) : jmp term =
  let blk = List.nth (Term.enum blk_t sub |> Seq.to_list) i in
  List.nth (Term.enum jmp_t blk |> Seq.to_list) j

(* One raw sub from nodes: a node is its defs plus out-edges, each edge
   a (target index, jump maker) pair — the maker receives the target's
   tid. Node order is the sub's block order (the VSA reads its
   taken/fallthrough edge order from it); the tids come back in that
   order. *)
let raw_sub_of ?(tid = Tid.create ()) ?(args = []) (name : string)
    (nodes : (def term list * (int * (tid -> jmp term)) list) list) :
    sub term * tid array =
  let b0s = List.map (fun (defs, _) -> blk_of_defs defs) nodes in
  let tids = Array.of_list (List.map Term.tid b0s) in
  let blks =
    List.map2
      (fun b0 (_, edges) -> with_jmps b0 (List.map (fun (i, mk) -> mk tids.(i)) edges))
      b0s nodes
  in
  let sb = Sub.Builder.create ~tid ~name () in
  List.iter (Sub.Builder.add_arg sb) args;
  List.iter (Sub.Builder.add_blk sb) blks;
  (Sub.Builder.result sb, tids)

(* The fixtures' target: the flag roles name the fixture flag vars
   (Theory.Var.define is pure in (sort, name), so Var.same matches
   them). *)
let jump_target =
  let flag name = Theory.Var.forget (Theory.Var.define Theory.Bool.t name) in
  Theory.Target.declare ~package:"test" "jump-flags" ~bits:64 ~byte:8
    ~regs:Theory.Role.Register.[
        [zero_flag], [flag (Var.name sysv.Hike.Abi.zero_flag)];
        [carry_flag], [flag (Var.name sysv.Hike.Abi.carry_flag)];
        [sign_flag], [flag (Var.name sysv.Hike.Abi.sign_flag)];
        [overflow_flag], [flag (Var.name sysv.Hike.Abi.overflow_flag)];
        [parity_flag], [flag (Var.name sysv.Hike.Abi.parity_flag)]]

let run_anchored (sub : sub term) : Vsa.vsa_sol =
  static_graph_vsa ~synth:Hike.Synth.empty ~abi:Hike_abi.x86_64_sysv sub (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv ~entry:(anchored_entry ()) sub)

(* The jump-compiled sub, as [run_anchored] runs it. *)
let jump_compiled (sub : sub term) : sub term =
  snd (Hike.Jump.compile_sub ~synth:Hike.Synth.empty jump_target sub)

(* The analysis's input form: the jump-compiled sub in SSA form.  The
   pins work on this form from the start — there is no other form. *)
let ssa_sub (raw : sub term) : sub term =
  ssa_form (jump_compiled raw)

(* One sub from nodes, in the analysis's input form: the pins see the
   SSA sub the VSA consumes.  The block tids are the raw ones — the SSA
   construction keeps them and adds the synthetic entry. *)
let sub_of ?tid ?args (name : string)
    (nodes : (def term list * (int * (tid -> jmp term)) list) list) :
    sub term * tid array =
  let raw, tids = raw_sub_of ?tid ?args name nodes in
  (ssa_sub raw, tids)

(* A one-entry sub over the defs, exiting through a real terminal
   block (CFG-honest: the Goto target is built first). *)
let straight_sub (name : string) (defs : def term list) : sub term =
  fst (sub_of name [ defs, [ (1, mk_goto) ]; [], [ (0, mk_ret) ] ])

(* Mem fixture: a singleton map holding one key/data cell. *)
let key_of ws =
  match Mem.Key.of_wordset ws with
  | [ k ] -> k
  | _ -> failwith "key_of"

let mk_mem ~key ~data =
  let k = key_of key in
  let v = Mem.Val.create data LittleEndian in
  Mem.add (Mem.top { Mem.addr_width = 32; Mem.addressable_width = 8 }) ~key:k ~data:v

(* Seed fixture: entry state with RSP/RBP at the symbolic segment base
   (offset 0 — the production universe). *)
let mk_seed_state rsp rbp () =
  AI.add_word
    (AI.add_word AI.top ~key:rsp ~data:(Ws.stack_word_i64 0L))
    ~key:rbp
    ~data:(Ws.stack_word_i64 0L)

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
      (Bil.Load (Bil.Var m, Bil.BinOp (Bil.PLUS, Bil.Var g, Bil.Var sp), LittleEndian, `r64))
  in
  let sub, tids =
    sub_of "t3_flag"
      [ [ defA ] @ (if mixed then [ defB ] else []) @ [ defC; defU ],
        [ (1, fun t -> mk_jmp_to t (Bil.Var f)) ];
        [], [] ]
  in
  let ctx = Program.create ~subs:[ sub ] () in
  (f, ctx, sub, tids.(1), defA, (if mixed then Some defB else None), defU)

(* Single self-looping block sub (a never-analyzed callee; calls abstract it).
   Shared by the alias-shape fixture below and the prologue/outgoing escape family. *)
let mk_selfloop_callee (name : string) : sub term =
  fst (sub_of name [ ([], [ (0, mk_goto) ]) ])

(* Call jump with a return continuation. *)
let mk_call_jmp (post_tid : tid) (callee_tid : tid) : jmp term =
  Jmp.create (Call (Call.create ~return:(Label.direct post_tid) ~target:(Label.direct callee_tid) ()))

(* Frozen-flag guard — constrain_edge refines every var, gate-free. *)
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
  let rsp = sp in
  let rbp = frame_ptr in
  let rbx = callee_saved 0 in
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
  let def_reload = Def.create r2 (Bil.Load (Bil.Var m, Bil.Var rdi, LittleEndian, `r64)) in
  let caller, tids =
    sub_of ~args:[ Arg.create rdi (Bil.Var rdi); Arg.create r2 (Bil.Var r2) ]
      "t4_caller"
      [ [ def_rsp;
          def_rbp;
          def_rdi;
          def_rbx;
          def_push;
          def_v;
          def_w2;
          def_w;
          def_store;
          def_store_disjoint ],
        [ (1, fun t -> mk_call_jmp t callee_tid) ];
        [ def_reload ], [] ]
  in
  let entry = List.hd (Term.enum blk_t caller |> Seq.to_list) in
  let ctx = Program.create ~subs:[ caller; callee ] () in
  {
    ca_ctx = ctx;
    ca_sub = caller;
    ca_entry_blk = entry;
    ca_post_tid = tids.(1);
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

(* Caller-alias soundness — post-call reload reads TOP; RSP/RBP/RBX kept, rdi TOPed.
   The alias prologue (rdi through rbp, push def, dual mems) is a different
   shape from the fp/outgoing escape family (mk_escape_caller); it shares only
   the callee/call wiring above. *)
(* F1: map-lattice fold visits explicitly-stored bindings only; absent = top. *)
(* RSP-anchored seeds: RBP enters only via RSP-derivation. *)

(* -O0 prologue (rbp := RSP) + load + overlapping store. Returns (def_rbp, def_store, sub). *)

(* One-path heap shapes: the use-store's address joins to TOP. *)

(* One-path fixture: the rdi use is reachable only via B1. Returns (def_prologue, def_load, def_other, def_use, sub). *)

let mk_high0_cast_sub () : var * Program.t * sub term * tid =
  let rax = Var.create ~is_virtual:false ~fresh:false "rax" (Type.Imm 64) in
  let sub, tids =
    sub_of "d7_high0_cast"
      [ [],
        [ (1, fun t ->
              Jmp.create (Call (Call.create ~return:(Direct t) ~target:(Indirect (Bil.Int (Cbat_word.to_word (w64 0)))) ()))) ];
        [ Def.create rax (Bil.Cast (Bil.HIGH, 0, Bil.Var rax)) ], [ (2, mk_goto) ];
        [], [] ]
  in
  let ctx = Program.create ~subs:[ sub ] () in
  (rax, ctx, sub, tids.(2))

(* Stack-only residue closure: heap-indexed stores fall out; top-addr stores skipped. *)

let mk_p3_anchor_sub () : sub term =
  let t = v64 "p3_t" in
  fst (sub_of "p3_anchor" [ [ Def.create t (Bil.Int (Cbat_word.to_word (w64 0))) ], [] ])

(* Backward-refinement loop fixtures (moved verbatim from test_backward.ml). *)
let mk_l3a_loop ~(cmp : Bil.binop) ~(c : Cbat_word.t) ~(rhs : exp) : sub term * tid =
  let m = memv "l3a_m" in
  let rsp = sp in
  let rbp = frame_ptr in
  let t = Var.create ~is_virtual:false ~fresh:false "l3a_t" (Type.Imm 32) in
  let v = Var.create ~is_virtual:false ~fresh:false "l3a_v" (Type.Imm 32) in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
  let cond = Bil.BinOp (cmp, Bil.Var v, Bil.Int (Cbat_word.to_word c)) in
  let ncond = Bil.UnOp (Bil.NOT, cond) in
  let sub, tids =
    sub_of "l3a_loop"
      [ [ Def.create rbp (Bil.Var rsp) ], [ (2, mk_goto) ];
        [], [ (2, mk_goto) ];
        [ Def.create t (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)); Def.create v rhs ],
        [ (1, fun t -> mk_jmp_to t cond); (3, fun t -> mk_jmp_to t ncond) ];
        [], [] ]
  in
  (sub, tids.(1))

(* Cell at [base-8] in [st], read back as the load denotation reads it.
   [base] is the version the block holds of the frame pointer. *)
let cell_at (m : var) (base : var) (st : AI.t) : Ws.t =
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var base, Bil.Int (Cbat_word.to_word (w64 8))) in
  Result.fold
    (Vsa.Test_seam.denote_imm_exp ~synth:Hike.Synth.empty (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)) st)
    ~ok:Fun.id ~error:(fun _ -> Ws.top 32)

(* Finite non-top non-bottom set bounded above by [maxv]. *)
let bounded_above (ws : Ws.t) (maxv : Cbat_word.t) : bool =
  (not (Ws.is_top ws))
  && (not (Ws.is_bottom ws))
  && Option.is_some (Base.Option.filter (Ws.max_elem ws) ~f:(fun w -> Cbat_word.( <= ) w maxv))

(* Tagged-sub fixpoint; walk's cell meet observable at BODY input. *)
(* Iterate state of an edge is the single-predecessor target's IN-state. *)
(* Anchored fixpoint run (defaults: the anchored entry; fixtures rely on
   it).  The sub runs through the jump compiler first — the pipeline's
   reality: the analysis reads value comparisons, never flag idioms. *)

(* Sub [name] of [subs] after SSA construction (the VSA's input form). *)
let ssa_of_subs (subs : sub term list) (name : string) : sub term =
  let prog = Program.create ~subs () in
  let prog = Hike.Ssa.ssa_program ~synth:Hike.Synth.empty ~target:(x86_target ()) prog in
  Term.enum sub_t prog
  |> Seq.find ~f:(fun s -> String.equal (Sub.name s) name)
  |> Base.Option.value_exn

(* The VSA from the anchored entry on a sub in SSA form. *)
let run_ssa_anchored (sub : sub term) : Vsa.vsa_sol =
  static_graph_vsa ~synth:Hike.Synth.empty ~abi:Hike_abi.x86_64_sysv sub
    (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv ~entry:(anchored_entry ()) sub)

(* The SP's value at the end of block [tid]'s defs in an SSA solve: its
   last version defined in the block, or the block's SP phi. *)
let sp_after_block (sub : sub term) (sol : Vsa.vsa_sol) (tid : tid) : Ws.t =
  let blk = Term.find blk_t sub tid |> Base.Option.value_exn in
  let is_sp v = Var.same v sp in
  let version =
    match
      Term.enum def_t blk |> Seq.map ~f:Def.lhs |> Seq.filter ~f:is_sp
      |> Seq.to_list |> List.rev
    with
    | v :: _ -> v
    | [] ->
      Term.enum phi_t blk |> Seq.map ~f:Phi.lhs |> Seq.find ~f:is_sp
      |> Base.Option.value_exn
  in
  let _, after = Vsa.fold_block_states ~synth:Hike.Synth.empty ~sol blk ~init:() ~f:(fun _ _ _ () -> ()) in
  AI.find_word 64 after version

let iter_state_of (_sub : sub term) (sol : Vsa.vsa_sol) (target_tid : tid) : AI.t =
  Graphlib.Std.Solution.get sol target_tid

let iter_cell_of (sub : sub term) (sol : Vsa.vsa_sol) (target_tid : tid) (cell_of : AI.t -> Ws.t) :
    Ws.t =
  cell_of (iter_state_of sub sol target_tid)

let l3a_run_analyzed (sub : sub term) (body_tid : tid) : Ws.t =
  (* Gate-free (spec §2.1): every def is denoted. *)
  let sol = run_anchored sub in
  let base = version_at sub body_tid frame_ptr in
  iter_cell_of sub sol body_tid (cell_at (memv "l3a_m") base)

(* L3c-1: flag-state mechanism — bare-flag guards recover the comparison constraint. *)

(* Flag-indirected loop fixture. Returns (sub, body tid, back-edge jump). *)
let mk_l3c1_loop ~(extra_header_defs : def term list) ~(pre_cf_defs : def term list)
    : sub term * tid * jmp term =
  let m = memv "l3c1_m" in
  let rsp = sp in
  let rbp = frame_ptr in
  let t = Var.create ~is_virtual:false ~fresh:false "l3c1_t" (Type.Imm 32) in
  let cf = v1 "l3c1_cf" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
  let sub, tids =
    sub_of "l3c1_loop"
      [ [ Def.create rbp (Bil.Var rsp) ], [ (2, mk_goto) ];
        [], [ (2, mk_goto) ];
        [ Def.create t (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)) ] @ pre_cf_defs
        @ [ Def.create cf (Bil.BinOp (Bil.LT, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 10)))) ]
        @ extra_header_defs,
        [ (1, fun t -> mk_jmp_to t (Bil.Var cf)); (3, fun t -> mk_jmp_to t (Bil.UnOp (Bil.NOT, Bil.Var cf))) ];
        [], [] ]
  in
  let header = List.nth (Term.enum blk_t sub |> Seq.to_list) 2 in
  let jmp = match Term.enum jmp_t header |> Seq.to_list with [ j1; _ ] -> j1 | _ -> assert false in
  (sub, tids.(1), jmp)

(* L3c-2: signed comparison rows (SLT/SLE). *)

(* Seeded counter loop; [flag] selects the flag-indirected guard, [prologue] drops it. Returns (sub, body tid). *)
let mk_l3c2_loop ~(prologue : bool) ~(seed : Cbat_word.t option) ~(cmp : Bil.binop) ~(c : Cbat_word.t)
    ~(body_op : Bil.binop) ~(body_k : Cbat_word.t) ~(flag : bool) : sub term * tid =
  let m = memv "l3c2_m" in
  let rsp = sp in
  let rbp = frame_ptr in
  let t = Var.create ~is_virtual:false ~fresh:false "l3c2_t" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "l3c2_u" (Type.Imm 32) in
  let cf = v1 "l3c2_cf" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
  let cond = Bil.BinOp (cmp, Bil.Var t, Bil.Int (Cbat_word.to_word c)) in
  let jcond = if flag then Bil.Var cf else cond in
  let sub, tids =
    sub_of "l3c2_loop"
      [ (match seed with
         | Some v ->
             [ Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int (Cbat_word.to_word v), LittleEndian, `r32)) ]
         | None -> [])
        @ (if prologue then [ Def.create rbp (Bil.Var rsp) ] else []),
        [ (2, mk_goto) ];
        [ Def.create u (Bil.BinOp (body_op, Bil.Var t, Bil.Int (Cbat_word.to_word body_k)));
          Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Var u, LittleEndian, `r32)) ],
        [ (2, mk_goto) ];
        [ Def.create t (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)) ]
        @ (if flag then [ Def.create cf cond ] else []),
        [ (1, fun t -> mk_jmp_to t jcond); (3, fun t -> mk_jmp_to t (Bil.UnOp (Bil.NOT, jcond))) ];
        [], [] ]
  in
  (sub, tids.(1))

(* Finite non-top non-bottom, all values in [lo, hi]. *)
let l3c2_in_high (ws : Ws.t) (lo : Cbat_word.t) (hi : Cbat_word.t) : bool =
  (not (Ws.is_top ws))
  && (not (Ws.is_bottom ws))
  &&
  match (Ws.min_elem ws, Ws.max_elem ws) with
  | Some mn, Some mx -> Cbat_word.( >= ) mn lo && Cbat_word.( <= ) mx hi
  | _ -> false

(* L3c loop fixtures: header seeds/loads, body increments and stores,
   latch loads the cell and guards.  The vars carry the fixture's name
   prefix, so a caller rebuilds them to spell its chain/cond. *)
let mk_l3_chain_loop ~(name : string) ~(seed : Cbat_word.t option)
    ~(v_w : int) ~(chain : exp option) ~(cond : exp) ~(body_k : Cbat_word.t) :
    sub term * tid =
  let m = memv (name ^ "_m") in
  let rsp = sp in
  let rbp = frame_ptr in
  let t = Var.create ~is_virtual:false ~fresh:false (name ^ "_t") (Type.Imm 32) in
  let v = Var.create ~is_virtual:false ~fresh:false (name ^ "_v") (Type.Imm v_w) in
  let u = Var.create ~is_virtual:false ~fresh:false (name ^ "_u") (Type.Imm 32) in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
  let sub, tids =
    sub_of (name ^ "_loop")
      [ (match seed with
         | Some sv ->
             [ Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int (Cbat_word.to_word sv), LittleEndian, `r32)) ]
         | None -> [])
        @ [ Def.create rbp (Bil.Var rsp) ],
        [ (2, mk_goto) ];
        [ Def.create u (Bil.BinOp (Bil.PLUS, Bil.Var t, Bil.Int (Cbat_word.to_word body_k)));
          Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Var u, LittleEndian, `r32)) ],
        [ (2, mk_goto) ];
        [ Def.create t (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)) ]
        @ (match chain with Some ch -> [ Def.create v ch ] | None -> []),
        [ (1, fun t -> mk_jmp_to t cond); (3, fun t -> mk_jmp_to t (Bil.UnOp (Bil.NOT, cond))) ];
        [], [] ]
  in
  (sub, tids.(1))

let mk_l3c3_loop ~(seed : Cbat_word.t option) ~(chain : exp) ~(cmp : Bil.binop) ~(c : Cbat_word.t)
    ~(body_k : Cbat_word.t) : sub term * tid =
  let v = Var.create ~is_virtual:false ~fresh:false "l3c3_v" (Type.Imm 32) in
  mk_l3_chain_loop ~name:"l3c3" ~seed ~v_w:32 ~chain:(Some chain)
    ~cond:(Bil.BinOp (cmp, Bil.Var v, Bil.Int (Cbat_word.to_word c))) ~body_k

(* Plain fixpoint; BODY input cell at RBP-8. *)
let l3c3_run (sub : sub term) (body_tid : tid) : Ws.t =
  iter_cell_of sub (run_anchored sub) body_tid (cell_at (memv "l3c3_m") (version_at sub body_tid frame_ptr))

(* L3c-4: Var-vs-Var overlap, DIVIDE-const, HIGH-extract rows. *)

(* Chain loop with compared-var width. Returns (sub, body tid). *)
let mk_l3c4_loop ~(seed : Cbat_word.t option) ~(chain : exp) ~(v_w : int) ~(cmp : Bil.binop) ~(c : Cbat_word.t)
    ~(body_k : Cbat_word.t) : sub term * tid =
  let m = memv "l3c4_m" in
  let rsp = sp in
  let rbp = frame_ptr in
  let t = Var.create ~is_virtual:false ~fresh:false "l3c4_t" (Type.Imm 32) in
  let v = Var.create ~is_virtual:false ~fresh:false "l3c4_v" (Type.Imm v_w) in
  let u = Var.create ~is_virtual:false ~fresh:false "l3c4_u" (Type.Imm 32) in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
  let cond = Bil.BinOp (cmp, Bil.Var v, Bil.Int (Cbat_word.to_word c)) in
  let sub, tids =
    sub_of "l3c4_loop"
      [ (match seed with
         | Some sv ->
             [ Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int (Cbat_word.to_word sv), LittleEndian, `r32)) ]
         | None -> [])
        @ [ Def.create rbp (Bil.Var rsp) ],
        [ (2, mk_goto) ];
        [ Def.create u (Bil.BinOp (Bil.PLUS, Bil.Var t, Bil.Int (Cbat_word.to_word body_k)));
          Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Var u, LittleEndian, `r32)) ],
        [ (2, mk_goto) ];
        [ Def.create t (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)); Def.create v chain ],
        [ (1, fun t -> mk_jmp_to t cond); (3, fun t -> mk_jmp_to t (Bil.UnOp (Bil.NOT, cond))) ];
        [], [] ]
  in
  (sub, tids.(1))

(* Two-load Var-vs-Var shape. Returns (sub, body tid). *)
let mk_l3c4_vv_loop ~(seed : Cbat_word.t option) ~(seed2 : Cbat_word.t option) ~(cmp : Bil.binop) ~(body_k : Cbat_word.t)
    : sub term * tid =
  let m = memv "l3c4_m" in
  let rsp = sp in
  let rbp = frame_ptr in
  let t = Var.create ~is_virtual:false ~fresh:false "l3c4_t" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "l3c4_u" (Type.Imm 32) in
  let w = Var.create ~is_virtual:false ~fresh:false "l3c4_w" (Type.Imm 32) in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
  let addr2 = Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 16))) in
  let cond = Bil.BinOp (cmp, Bil.Var t, Bil.Var u) in
  let sub, tids =
    sub_of "l3c4_vv"
      [ (match seed with
         | Some sv ->
             [ Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int (Cbat_word.to_word sv), LittleEndian, `r32)) ]
         | None -> [])
        @ (match seed2 with
           | Some sv ->
               [ Def.create m (Bil.Store (Bil.Var m, addr2, Bil.Int (Cbat_word.to_word sv), LittleEndian, `r32)) ]
           | None -> [])
        @ [ Def.create rbp (Bil.Var rsp) ],
        [ (2, mk_goto) ];
        [ Def.create w (Bil.BinOp (Bil.PLUS, Bil.Var t, Bil.Int (Cbat_word.to_word body_k)));
          Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Var w, LittleEndian, `r32)) ],
        [ (2, mk_goto) ];
        [ Def.create t (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32));
          Def.create u (Bil.Load (Bil.Var m, addr2, LittleEndian, `r32)) ],
        [ (1, fun t -> mk_jmp_to t cond); (3, fun t -> mk_jmp_to t (Bil.UnOp (Bil.NOT, cond))) ];
        [], [] ]
  in
  (sub, tids.(1))

(* Plain fixpoint; BODY input cell at RBP-8. *)
let l3c4_run (sub : sub term) (body_tid : tid) : Ws.t =
  iter_cell_of sub (run_anchored sub) body_tid (cell_at (memv "l3c4_m") (version_at sub body_tid frame_ptr))

(* L3c-5: structural closure — identity rows, const-first arm, shrunk catch-all. *)

(* Optional-chain loop fixture. Returns (sub, body tid). *)
let mk_l3c5_loop ~(seed : Cbat_word.t option) ~(chain : exp option) ~(cond : exp) ~(body_k : Cbat_word.t) :
    sub term * tid =
  mk_l3_chain_loop ~name:"l3c5" ~seed ~v_w:32 ~chain ~cond ~body_k

(* Plain fixpoint; BODY input cell at RBP-8. *)
let l3c5_run (sub : sub term) (body_tid : tid) : Ws.t =
  iter_cell_of sub (run_anchored sub) body_tid (cell_at (memv "l3c5_m") (version_at sub body_tid frame_ptr))

(* L3c-6: the -O0 store-head loop — the counter's increment store lives
   in the WALKED head block (the do-while merge), the guard's bound is a
   second cell, and the increment is either the nested-load store
   (mem[c] := mem[c] + 1) or the def-carried one (v := t + 1;
   mem[c] := v).  The counter cell sits at RBP-8, the bound cell at
   RSP-16.  Returns (sub, body tid). *)
let mk_l3c6_storehead_loop ~(nested : bool) ~(seed : Cbat_word.t option)
    ~(bound : Cbat_word.t) : sub term * tid =
  let m = memv "l3c6_m" in
  let rsp = sp in
  let rbp = frame_ptr in
  let t = Var.create ~is_virtual:false ~fresh:false "l3c6_t" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "l3c6_u" (Type.Imm 32) in
  let v = Var.create ~is_virtual:false ~fresh:false "l3c6_v" (Type.Imm 32) in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
  let addr_b = Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 16))) in
  let cond = Bil.BinOp (Bil.SLT, Bil.Var t, Bil.Var u) in
  let increment =
    if nested then
      [ Def.create m
          (Bil.Store (Bil.Var m, addr_e,
                      Bil.BinOp (Bil.PLUS,
                                 Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32),
                                 Bil.Int (Cbat_word.to_word (w32 1))),
                      LittleEndian, `r32)) ]
    else
      [ Def.create v (Bil.BinOp (Bil.PLUS, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 1))));
        Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Var v, LittleEndian, `r32)) ]
  in
  let seed_defs =
    (match seed with
     | Some sv ->
       [ Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int (Cbat_word.to_word sv), LittleEndian, `r32)) ]
     | None -> [])
    @ [ Def.create m (Bil.Store (Bil.Var m, addr_b, Bil.Int (Cbat_word.to_word bound), LittleEndian, `r32));
        Def.create rbp (Bil.Var rsp) ]
  in
  let sub, tids =
    sub_of "l3c6_loop"
      [ seed_defs, [ (1, mk_goto) ];
        [ Def.create t (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)) ]
        @ increment
        @ [ Def.create u (Bil.Load (Bil.Var m, addr_b, LittleEndian, `r32)) ],
        [ (1, fun t -> mk_jmp_to t cond); (2, fun t -> mk_jmp_to t (Bil.UnOp (Bil.NOT, cond))) ];
        [], [] ]
  in
  (sub, tids.(1))

(* Interrupt denotation: unknown external callee via call_abstraction. *)
(* L-3b: coalesce equal-lower merge arm — piles collapse, reads preserved. *)

(* Seeded RMW counter (traverse shape). Returns (sub, body tid, header tid). *)
let mk_l3b1_loop () : sub term * tid * tid =
  let m = memv "l3b1_m" in
  let rsp = sp in
  let t = Var.create ~is_virtual:false ~fresh:false "l3b1_t" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "l3b1_u" (Type.Imm 32) in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 8))) in
  let cond = Bil.BinOp (Bil.LT, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 8))) in
  let sub, tids =
    sub_of "l3b1_loop"
      [ [ Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int (Cbat_word.to_word (w32 0)), LittleEndian, `r32)) ],
        [ (2, mk_goto) ];
        [ Def.create u (Bil.BinOp (Bil.PLUS, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 1))));
          Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Var u, LittleEndian, `r32)) ],
        [ (2, mk_goto) ];
        [ Def.create t (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)) ],
        [ (1, fun t -> mk_jmp_to t cond); (3, fun t -> mk_jmp_to t (Bil.UnOp (Bil.NOT, cond))) ];
        [], [] ]
  in
  (sub, tids.(1), tids.(2))
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
let mk_cmp_defs ~(e : exp) ~(c : Cbat_word.t) ~(t : var) ~(cf : var) ~(ofv : var) ~(sf : var)
    ~(zf : var) : def term list =
  [ Def.create t (Bil.BinOp (Bil.MINUS, e, Bil.Int (Cbat_word.to_word c)));
    Def.create cf (Bil.BinOp (Bil.LT, e, Bil.Int (Cbat_word.to_word c)));
    Def.create ofv
      (Bil.Cast
         ( Bil.HIGH,
           1,
           Bil.BinOp
             ( Bil.AND,
               Bil.BinOp (Bil.XOR, e, Bil.Int (Cbat_word.to_word c)),
               Bil.BinOp (Bil.XOR, e, Bil.Var t) ) ));
    Def.create sf (Bil.Cast (Bil.HIGH, 1, Bil.Var t));
    Def.create zf (Bil.BinOp (Bil.EQ, Bil.Int (Word.zero (Cbat_word.bitwidth c)), Bil.Var t)) ]

(* Widening landmarks: empty guard meets record landmarks; widening extrapolates. *)

(* Corpus jle shape, one or two chained loops. Returns (sub, l1, b1, l2 option). *)
let lm_jle_loop ~(k1 : Cbat_word.t) ?(k2 : Cbat_word.t option) () : sub term * tid * tid * tid option =
  let rsp = sp in
  let rbp = frame_ptr in
  let i = Var.create ~is_virtual:false ~fresh:false "lm_i" (Type.Imm 32) in
  let iv = Bil.Var i in
  (* Canonical -O0 cmp emission; returns the defs and the jle cond. *)
  let cmp_defs (c : Cbat_word.t) : def term list * exp =
    let t = Var.create ~is_virtual:false ~fresh:false "lm_t" (Type.Imm 32) in
    let cf = abi_cf in
    let ofv = abi_of in
    let sf = abi_sf in
    let zf = abi_zf in
    (mk_cmp_defs ~e:iv ~c ~t ~cf ~ofv ~sf ~zf, l39_jle zf sf ofv)
  in
  let defs1, cond1 = cmp_defs k1 in
  let inc () = Def.create i (Bil.BinOp (Bil.PLUS, iv, Bil.Int (Cbat_word.to_word (w32 1)))) in
  (* Drop the unused second loop: empty blocks break CFG/WTO plumbing. *)
  let keep_l2 = Option.is_some k2 in
  let exit_i = if keep_l2 then 5 else 3 in
  let l2_nodes =
    match k2 with
    | Some c ->
      let defs2, cond2 = cmp_defs c in
      [ defs2, [ (4, fun t -> mk_jmp_to t cond2); (exit_i, fun t -> mk_jmp_to t (Bil.UnOp (Bil.NOT, cond2))) ];
        [ inc () ], [ (3, mk_goto) ] ]
    | None -> []
  in
  let sub, tids =
    sub_of "lm_landmark_counter"
      ([ [ Def.create i (Bil.Int (Cbat_word.to_word (w32 0))); Def.create rbp (Bil.Var rsp) ],
         [ (1, mk_goto) ];
         defs1,
         [ (2, fun t -> mk_jmp_to t cond1);
           (* l1's fallthrough: l2 when kept, exit otherwise — both node 3. *)
           (3, fun t -> mk_jmp_to t (Bil.UnOp (Bil.NOT, cond1))) ];
         [ inc () ], [ (1, mk_goto) ] ]
       @ l2_nodes
       @ [ [], [] ])
  in
  (sub, tids.(1), tids.(2), if Option.is_some k2 then Some tids.(3) else None)

(* NEQ-counter loop; landmarks are the only precision mechanism. Returns (sub, l1, b1). *)
let lm_jne_loop ~(k : Cbat_word.t) () : sub term * tid * tid =
  let kw = Cbat_word.to_word k in
  let rsp = sp in
  let rbp = frame_ptr in
  let i = Var.create ~is_virtual:false ~fresh:false "lm_ne_i" (Type.Imm 32) in
  let t = Var.create ~is_virtual:false ~fresh:false "lm_ne_t" (Type.Imm 32) in
  let zf = abi_zf in
  let iv = Bil.Var i in
  let cond_taken = Bil.UnOp (Bil.NOT, Bil.Var zf) in
  let cond_fallthrough = Bil.Var zf in
  let sub, tids =
    sub_of "lm_ne_landmark"
      [ [ Def.create i (Bil.Int (Cbat_word.to_word (w32 0))); Def.create rbp (Bil.Var rsp) ],
        [ (1, mk_goto) ];
        (* ZF compares the program var directly (recovery binds the right var). *)
        [ Def.create t (Bil.BinOp (Bil.MINUS, iv, Bil.Int kw));
          Def.create zf
            (Bil.BinOp
               (Bil.EQ,
                Bil.BinOp (Bil.MINUS, iv, Bil.Int kw),
                Bil.Int (Word.zero 32))) ],
        [ (2, fun t -> mk_jmp_to t cond_taken); (3, fun t -> mk_jmp_to t cond_fallthrough) ];
        [ Def.create i (Bil.BinOp (Bil.PLUS, iv, Bil.Int (Cbat_word.to_word (w32 1)))) ],
        [ (1, mk_goto) ];
        [], [] ]
  in
  (sub, tids.(1), tids.(2))

(* Shared F1-FT/B4 build: the same jne-counter loop + anchored run.
   Returns (k, sub, sol, head tid, body tid); the distinct pins stay in the tests. *)
let lm_jne_run () : Cbat_word.t * sub term * Vsa.vsa_sol * tid * tid =
  let k = w32 100 in
  let sub, l1_tid, b1_tid = lm_jne_loop ~k () in
  (k, sub, run_anchored sub, l1_tid, b1_tid)

(* Exact corpus block fixture: seeded store, canonical cmp emission, compound guard. Returns (sub, body tid). *)
let mk_l39_loop ~(seed : Cbat_word.t) ~(c : Cbat_word.t) ~(body_op : Bil.binop) ~(body_k : Cbat_word.t)
    ~(mk_cond : cf:var -> ofv:var -> sf:var -> zf:var -> exp)
    ~(extra_header_defs : var -> def term list) : sub term * tid =
  let m = memv "l39_m" in
  let rsp = sp in
  let rbp = frame_ptr in
  let t = Var.create ~is_virtual:false ~fresh:false "l39_t" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "l39_u" (Type.Imm 32) in
  let cf = abi_cf in
  let ofv = abi_of in
  let sf = abi_sf in
  let zf = abi_zf in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
  let load_e = Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32) in
  let cond = mk_cond ~cf ~ofv ~sf ~zf in
  let sub, tids =
    sub_of "l39_loop"
      [ [ Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int (Cbat_word.to_word seed), LittleEndian, `r32));
          Def.create rbp (Bil.Var rsp) ],
        [ (2, mk_goto) ];
        [ Def.create u load_e;
          Def.create m
            (Bil.Store
               (Bil.Var m, addr_e, Bil.BinOp (body_op, Bil.Var u, Bil.Int (Cbat_word.to_word body_k)), LittleEndian, `r32)) ],
        [ (2, mk_goto) ];
        mk_cmp_defs ~e:load_e ~c ~t ~cf ~ofv ~sf ~zf @ extra_header_defs m,
        [ (1, fun t -> mk_jmp_to t cond); (3, fun t -> mk_jmp_to t (Bil.UnOp (Bil.NOT, cond))) ];
        [], [] ]
  in
  (sub, tids.(1))

(* Record-path fixture: bare-flag guard with unique def. Returns (sub, body tid). *)
let mk_l39b5_loop () : sub term * tid =
  let m = memv "l39_m" in
  let rsp = sp in
  let rbp = frame_ptr in
  let v = Var.create ~is_virtual:false ~fresh:false "l39b5_v" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "l39b5_u" (Type.Imm 32) in
  let cf = abi_cf in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
  let sub, tids =
    sub_of "l39b5_loop"
      [ [ Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int (Cbat_word.to_word (w32 0)), LittleEndian, `r32));
          Def.create rbp (Bil.Var rsp) ],
        [ (2, mk_goto) ];
        [ Def.create u (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32));
          Def.create m
            (Bil.Store
               (Bil.Var m, addr_e, Bil.BinOp (Bil.PLUS, Bil.Var u, Bil.Int (Cbat_word.to_word (w32 1))), LittleEndian, `r32)) ],
        [ (2, mk_goto) ];
        [ Def.create v (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32));
          Def.create cf (Bil.BinOp (Bil.LT, Bil.Var v, Bil.Int (Cbat_word.to_word (w32 3)))) ],
        [ (1, fun t -> mk_jmp_to t (Bil.Var cf)); (3, fun t -> mk_jmp_to t (Bil.UnOp (Bil.NOT, Bil.Var cf))) ];
        [], [] ]
  in
  (sub, tids.(1))

(* Plain fixpoint; BODY input cell at RBP-8. *)
let l39_run (sub : sub term) (body_tid : tid) : Ws.t =
  iter_cell_of sub (run_anchored sub) body_tid (cell_at (memv "l39_m") (version_at sub body_tid frame_ptr))

(* L-E1: ON-path matched-pair RSP restoration (RSP := RSP + 8 on return). *)

(* Call-in-loop fixture. Returns (sub, header tid, rsp). *)
let mk_e1_loop_sub () : sub term * tid * var =
  let rsp = sp in
  let m = memv "e1_m" in
  let sub, tids =
    sub_of "e1_loop"
      [ [ Def.create rsp (Bil.Int (Cbat_word.to_word (w64 0x1000))) ], [ (1, mk_goto) ];
        [], [ (2, mk_goto) ];
        [ Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 8))));
          Def.create m (Bil.Store (Bil.Var m, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 0xdead)), LittleEndian, `r64)) ],
        [ (3, fun t ->
              Jmp.create (Call (Call.create ~return:(Label.direct t) ~target:(Indirect (Bil.Int (Cbat_word.to_word (w64 0)))) ()))) ];
        [], [ (1, mk_goto) ] ]
  in
  (sub, tids.(1), rsp)

(* Straight-line call fixture. Returns (sub, post tid, rsp). *)
let mk_e1_flat_sub () : sub term * tid * var =
  let rsp = sp in
  let m = memv "e1_m" in
  let sub, tids =
    sub_of "e1_flat"
      [ [ Def.create rsp (Bil.Int (Cbat_word.to_word (w64 0x2000)));
          Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 8))));
          Def.create m (Bil.Store (Bil.Var m, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 0xcafe)), LittleEndian, `r64)) ],
        [ (1, fun t ->
              Jmp.create (Call (Call.create ~return:(Label.direct t) ~target:(Indirect (Bil.Int (Cbat_word.to_word (w64 0)))) ()))) ];
        [], [] ]
  in
  (sub, tids.(1), rsp)

(* ON-path fixpoint; RSP value-set at [tid]. *)
let e1_rsp_at (sub : sub term) (tid : tid) (rsp : var) : Ws.t =
  AI.find_word 64 (Graphlib.Std.Solution.get (run_anchored sub) tid) rsp

(* L-D6: RBP-anchored gate-free fixture — the dead epilogue def is denoted too. *)

(* RBP loop with dead epilogue def. Returns (sub, body tid). *)
let mk_l6_rbp_loop () : sub term * tid =
  let m = memv "l6_m" in
  let rsp = sp in
  let rbp = frame_ptr in
  let t = Var.create ~is_virtual:false ~fresh:false "l6_t" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "l6_u" (Type.Imm 32) in
  let cf = abi_cf in
  let ofv = abi_of in
  let sf = abi_sf in
  let zf = abi_zf in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
  let load_e = Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32) in
  let c = w32 63 in
  let cond = l39_jle zf sf ofv in
  let sub, tids =
    sub_of "l6_rbp_loop"
      [ [ Def.create rbp (Bil.Var rsp) ], [ (1, mk_goto) ];
        [ Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int (Cbat_word.to_word (w32 0)), LittleEndian, `r32)) ],
        [ (3, mk_goto) ];
        [ Def.create u load_e;
          Def.create m
            (Bil.Store
               (Bil.Var m, addr_e, Bil.BinOp (Bil.PLUS, Bil.Var u, Bil.Int (Cbat_word.to_word (w32 1))), LittleEndian, `r32)) ],
        [ (3, mk_goto) ];
        mk_cmp_defs ~e:load_e ~c ~t ~cf ~ofv ~sf ~zf,
        [ (2, fun t -> mk_jmp_to t cond); (4, fun t -> mk_jmp_to t (Bil.UnOp (Bil.NOT, cond))) ];
        [], [ (5, mk_goto) ];
        (* Dead epilogue def: RBP := mem[RSP]. *)
        [ Def.create rbp (Bil.Load (Bil.Var m, Bil.Var rsp, LittleEndian, `r64)) ],
        [] ]
  in
  (sub, tids.(2))

(* ON-path fixpoint; BODY input cell at RBP-8. *)
let l6_run (sub : sub term) (body_tid : tid) : Ws.t =
  cell_at (memv "l6_m") (version_at sub body_tid frame_ptr)
    (Graphlib.Std.Solution.get (run_anchored sub) body_tid)

(* The secondary guarded-refinement shapes: inline-arithmetic record
   operand, NOT-edge, const-first flip, nested BinOp. *)

(* RBP-anchored ON-path fixture with optional two-path seed. Returns (sub, body tid). *)
let mk_r2_loop ~(seed : Cbat_word.t) ~(seed2 : Cbat_word.t option) ~(body_op : Bil.binop) ~(body_k : Cbat_word.t)
    ~(mk_cond : t:var -> exp) : sub term * tid =
  let m = memv "r2_m" in
  let rsp = sp in
  let rbp = frame_ptr in
  let t = Var.create ~is_virtual:false ~fresh:false "r2_t" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "r2_u" (Type.Imm 32) in
  let f = v1 "r2_f" in
  let g = v1 "r2_g" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
  let load_e = Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32) in
  let cond = mk_cond ~t in
  let seed_store s = Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int (Cbat_word.to_word s), LittleEndian, `r32)) in
  let body_defs =
    [ Def.create u load_e;
      Def.create m
        (Bil.Store
           (Bil.Var m, addr_e, Bil.BinOp (body_op, Bil.Var u, Bil.Int (Cbat_word.to_word body_k)), LittleEndian, `r32)) ]
  in
  let not_cond = Bil.UnOp (Bil.NOT, cond) in
  match seed2 with
  | Some s2 ->
      let sub, tids =
        sub_of "r2_loop"
          [ [ Def.create rbp (Bil.Var rsp) ], [ (1, mk_goto) ];
            [ Def.create f (Bil.Var g) ],
            [ (2, fun t -> mk_jmp_to t (Bil.Var f)); (3, fun t -> mk_jmp_to t (Bil.UnOp (Bil.NOT, Bil.Var f))) ];
            [ seed_store seed ], [ (5, mk_goto) ];
            [ seed_store s2 ], [ (5, mk_goto) ];
            body_defs, [ (5, mk_goto) ];
            [ Def.create t load_e ], [ (4, fun t -> mk_jmp_to t cond); (6, fun t -> mk_jmp_to t not_cond) ];
            [], [] ]
      in
      (sub, tids.(4))
  | None ->
      let sub, tids =
        sub_of "r2_loop"
          [ [ Def.create rbp (Bil.Var rsp) ], [ (1, mk_goto) ];
            [ seed_store seed ], [ (3, mk_goto) ];
            body_defs, [ (3, mk_goto) ];
            [ Def.create t load_e ], [ (2, fun t -> mk_jmp_to t cond); (4, fun t -> mk_jmp_to t not_cond) ];
            [], [] ]
      in
      (sub, tids.(2))

(* ON-path fixpoint; BODY input cell at RBP-8. *)
let r2_run (sub : sub term) (body_tid : tid) : Ws.t =
  iter_cell_of sub (run_anchored sub) body_tid (cell_at (memv "r2_m") (version_at sub body_tid frame_ptr))

(* Indexed-loop twin (C4a/R11): i := 0; body indexed store + inc; exit singleton store.
   The two tests differ only in the var-name prefix; the divergent pins stay in the tests. *)
let mk_indexed_loop ~pfx : sub term * def term =
  let rsp = sp in
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
  let sub, _ =
    sub_of (pfx ^ "_merge")
      [ [ Def.create i (Bil.Int (Cbat_word.to_word (w32 0))) ], [ (1, mk_goto) ];
        [ def_idx_store; def_inc ], [ (2, mk_goto) ];
        [], [ (3, fun t -> mk_jmp_to t nlt); (1, fun t -> mk_jmp_to t lt) ];
        [ def_exit ], [] ]
  in
  (sub, def_idx_store)

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
  let rsp = sp in
  let fp = v64 (pfx ^ "_fp") in
  let rdi = int_param 0 in
  let r2 = v64 (pfx ^ "_r2") in
  let m = memv (pfx ^ "_m") in
  let callee = mk_selfloop_callee (pfx ^ "_callee") in
  let callee_tid = Term.tid callee in
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
  let caller, tids =
    sub_of ~args:[ Arg.create rdi (Bil.Var rdi); Arg.create r2 (Bil.Var r2) ]
      (pfx ^ "_caller")
      [ [ def_fp; def_seed; def_prologue ], [ (1, mk_goto) ];
        def_rdi :: List.map def_out outs, [ (2, fun t -> mk_call_jmp t callee_tid) ];
        [ Def.create r2 (Bil.Load (Bil.Var m, Bil.Var fp, LittleEndian, `r64)) ], [] ]
  in
  let blks = Term.enum blk_t caller |> Seq.to_list in
  { es_sub = caller; es_blk0 = List.nth blks 0; es_blk1 = List.nth blks 1; es_post_tid = tids.(2); es_m = m }

let mk_when_chain () : sub term * tid * tid * tid * tid * var =
  let m = memv "wc_m" in
  let rbp = frame_ptr in
  let x = Var.create ~is_virtual:false ~fresh:false "wc_x" (Type.Imm 32) in
  let g1 = v1 "wc_g1" in
  let g2 = v1 "wc_g2" in
  let f1 = v1 "wc_f1" in
  let f2 = v1 "wc_f2" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
  let load_e = Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32) in
  let c1 = Bil.BinOp (Bil.LT, Bil.Var x, Bil.Int (Cbat_word.to_word (w32 10))) in
  let c2 = Bil.BinOp (Bil.LT, Bil.Var x, Bil.Int (Cbat_word.to_word (w32 20))) in
  let store_k k = Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int (Cbat_word.to_word k), LittleEndian, `r32)) in
  let sub, tids =
    sub_of "wc_chain"
      [ [ Def.create rbp (Bil.Var sp) ], [ (1, mk_goto) ];
        [ Def.create f1 (Bil.Var g1) ], [ (3, fun t -> mk_jmp_to t (Bil.Var f1)); (2, mk_goto) ];
        [ Def.create f2 (Bil.Var g2) ], [ (4, fun t -> mk_jmp_to t (Bil.Var f2)); (5, mk_goto) ];
        [ store_k (w32 5) ], [ (6, mk_goto) ];
        [ store_k (w32 15) ], [ (6, mk_goto) ];
        [ store_k (w32 25) ], [ (6, mk_goto) ];
        [ Def.create x load_e ], [ (7, fun t -> mk_jmp_to t c1); (8, fun t -> mk_jmp_to t c2); (9, mk_goto) ];
        [], [ (7, mk_goto) ];
        [], [ (8, mk_goto) ];
        [], [ (9, mk_goto) ] ]
  in
  (sub, tids.(7), tids.(8), tids.(9), tids.(6), x)

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
  fst
    (sub_of nm
       [ defs,
         [ (0,
            fun _ ->
              Jmp.create ~cond:(Bil.BinOp (Bil.EQ, Bil.Var cond_var, Bil.Int (Cbat_word.to_word (w64 0))))
                (Goto (Direct (Tid.create ())))) ] ])

(* Emitter fixtures. *)
let empty_spec : B2l.section_spec =
  { spec_comps = []; spec_whole = []; spec_word = 8;
    spec_sections = []; spec_tls = None;
    spec_relative = []; spec_externals = [] }

let with_emitted_module ~synth ?(types = fun prog -> prog)
    (spec : B2l.section_spec) (subs : sub term list) f =
  let llvm_ctx = Llvm.create_context () in
  let llvm_module = Llvm.create_module llvm_ctx "Test" in
  Fun.protect
    ~finally:(fun () ->
      Llvm.dispose_module llvm_module;
      Llvm.dispose_context llvm_ctx)
    (fun () ->
      (* Name fallthrough successors before emission (ADR 0024). *)
      let subs =
        Base.List.map subs ~f:Hike.Cfg_complete.materialize_fallthroughs
      in
      let prog = Program.create ~subs () in
      (* Run the production normalization, SSA and signature passes. *)
      let prog = Hike.Atomic.normalize ~addr_bits:64 prog in
      let synth = Hike.Synth.union (top_facts ()).Hike.Kb.synth synth in
      (* A fixture's storage declarations create their canonical variables. *)
      let storage synth storage =
        let synth, _ = Hike.Synth.mint_base ~addr_bits:64 storage synth in
        fst (Hike.Synth.mint_bytes ~addr_bits:64 storage synth)
      in
      let synth =
        Base.List.fold spec.spec_comps ~init:synth ~f:(fun synth c ->
            storage synth (Hike.Synth.Global c.Hike.Stack_model.comp_id))
      in
      let synth =
        Base.List.fold spec.spec_whole ~init:synth ~f:(fun synth (id, _, _) ->
            storage synth (Hike.Synth.Global id))
      in
      let synth =
        Base.List.fold subs ~init:synth ~f:(fun synth sub ->
            match Term.get_attr sub Hike.Stack_model.layout_tag with
            | None -> synth
            | Some layout ->
                Base.List.fold layout.Hike.Stack_model.regions
                  ~init:(storage synth Hike.Synth.Window) ~f:(fun synth r ->
                    storage synth (Hike.Synth.Stack r.Hike.Stack_model.r_id)))
      in
      let synth, prog = Hike.Fp.run_program ~word_bits:64 ~synth prog in
      (* Fixtures may already be SSA; construction consumes base names. *)
      let prog = Term.map sub_t prog ~f:Hike.Ssa.unssa_sub in
      let prog = Hike.Ssa.ssa_program ~synth ~target:(x86_target ()) prog in
      let prog =
        Hike.Split_blocks.normalize ~synth ~target:(x86_target ()) prog
      in
      let prog = Hike.Types.sign_program ~synth ~target:(x86_target ()) prog in
      (* The types pass runs on the SSA program; a fixture stamps its own. *)
      let prog = types prog in
      B2l.emit_program llvm_ctx llvm_module ~target:(x86_target ())
        ~addr_bits:64 ~symtab:None ~synth spec prog;
      Base.Option.iter
        (Llvm_analysis.verify_module llvm_module)
        ~f:Alcotest.fail;
      f llvm_module)

let emit_ir_spec ~synth ?types spec subs =
  with_emitted_module ~synth ?types spec subs Llvm.string_of_llmodule

let llvm_instructions llvm_module =
  Llvm.fold_left_functions (fun instructions fn ->
      Llvm.fold_left_blocks (fun instructions block ->
          Llvm.fold_left_instrs (fun instructions insn -> insn :: instructions)
            instructions block) instructions fn) [] llvm_module

let emit_ir ~synth ?types (subs : sub term list) : string =
  emit_ir_spec ~synth ?types empty_spec subs

let check_ir (name : string) (must : string) (ir : string) : unit =
  check name (contains_substring ir must)

(* Blocks of a sub holding no jumps (the exit-block idiom). *)
let exit_blocks_of (sub : sub term) : blk term list =
  Term.enum blk_t sub |> Seq.to_list |> List.filter (fun b -> Term.enum jmp_t b |> Seq.to_list = [])

(* Family 1: the FP-intrinsic table — every row emits its native op.  *)

let ivar64 (n : string) : var = Var.create ~is_virtual:false ~fresh:false n (Type.Imm 64)

(* One mapped-intrinsic call site, the production shape:
   [intrinsic:x0 := src; call @<name> with return <cont>; cont: ...]. *)
let mk_fp_call_sub (intr : string) (arg_defs : def term list) : sub term =
  let callee_tid = Tid.for_name intr in
  fst
    (sub_of "fp_caller"
       [ arg_defs,
         [ (1, fun t -> Jmp.create (Call (Call.create ~return:(Direct t) ~target:(Direct callee_tid) ()))) ];
         (* The writeback reads the ret lane, the production shape. *)
         [ Def.create (v64 "fp_wb") (Bil.Var (ivar64 "intrinsic:y0")) ],
         [ (2,
            fun t ->
              Jmp.create ~cond:(Bil.BinOp (Bil.EQ, Bil.Var (v64 "fp_wb"), Bil.Int (Cbat_word.to_word (w64 0))))
                (Goto (Direct t)));
           (2, mk_goto) ];
         [], [ (0, fun _ -> Jmp.create (Ret (Direct (Tid.create ())))) ] ])

(* The bodyless mapped-intrinsic stub (the model interface sig). *)
let mk_fp_stub (intr : string) : sub term =
  let sub, _ = sub_of intr [] in
  Term.set_attr sub Sub.intrinsic ()

let mk_fp_program (intr : string) (arg_defs : def term list) : sub term list =
  [ mk_fp_call_sub intr arg_defs; mk_fp_stub intr ]

(* Single-block sub over caller-supplied defs with a terminal Ret. *)
