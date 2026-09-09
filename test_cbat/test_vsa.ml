(* Branch-assume/fixpoint smoke, channel pins, seeds, casts, anchor pins. *)
open Bap.Std
open Bap_core_theory
open Test_common
open Test_fixtures

(* Fixpoint-level mixed-width smoke test. *)

(* Cyclic counter loop; doubt-valued cond keeps both edges live, back edge widens.
   [exit_defs] adds defs to the exit block. Returns (i, program, sub, exit tid). *)


(* FinSet cardinality reads at width+1 bits, so full {0,1} reads cardn 2, not empty. *)

(* L2b-1: full 1-bit domain reads cardn 2. *)
let run () =
(* SP anchor removed: fixtures pin the anchored entry explicitly. *)
(* Branch-assume refinement pins. *)
(  let ivar = Var.create ~is_virtual:false ~fresh:false "i" (Type.Imm 32) in
  let tgt = Tid.create () in
  let env = AI.top in
  (* x < 5 taken -> x in [0,4] *)
  let c1 =
    AI.find_word 32
      (Vsa.Test_seam.assume_jump_cond env
         (mk_jmp_to tgt (Bil.BinOp (Bil.LT, Bil.Var ivar, Bil.Int (Cbat_word.to_word (w32 5))))))
      ivar
  in
  check "D4-1: assume (x < 5) refines x to [0,4]"
    (Ws.min_elem c1 = Some (w32 0) && Ws.max_elem c1 = Some (w32 4));
  (* x <= 5 -> [0,5] *)
  let c2 =
    AI.find_word 32
      (Vsa.Test_seam.assume_jump_cond env
         (mk_jmp_to tgt (Bil.BinOp (Bil.LE, Bil.Var ivar, Bil.Int (Cbat_word.to_word (w32 5))))))
      ivar
  in
  check "D4-2: assume (x <= 5) refines x to [0,5]"
    (Ws.min_elem c2 = Some (w32 0) && Ws.max_elem c2 = Some (w32 5));
  (* x == 5 -> {5} *)
  let c3 =
    AI.find_word 32
      (Vsa.Test_seam.assume_jump_cond env
         (mk_jmp_to tgt (Bil.BinOp (Bil.EQ, Bil.Var ivar, Bil.Int (Cbat_word.to_word (w32 5))))))
      ivar
  in
  check "D4-3: assume (x == 5) refines x to {5}"
    (Ws.min_elem c3 = Some (w32 5) && Ws.max_elem c3 = Some (w32 5));
  let c4 = AI.find_word 32 (Vsa.Test_seam.assume_jump_cond env (mk_jmp_to tgt (Bil.Int (Cbat_word.to_word (w32 1))))) ivar in
  check "D4-4: doubt — constant condition keeps the state (top)" (Ws.is_top c4);
  let c5 =
    AI.find_word 32
      (Vsa.Test_seam.assume_jump_cond env (mk_jmp_to tgt (Bil.BinOp (Bil.LT, Bil.Var ivar, Bil.Int (Cbat_word.to_word (w64 5))))))
      ivar
  in
  check "D4-5: doubt — width-mismatched guard keeps the state (top)" (Ws.is_top c5);
  let c6 =
    AI.find_word 32
      (Vsa.Test_seam.assume_jump_cond env (mk_jmp_to tgt (Bil.BinOp (Bil.NEQ, Bil.Var ivar, Bil.Int (Cbat_word.to_word (w32 5))))))
      ivar
  in
  check "D4-6: gate-free (spec §2.1) — the NEQ guard refines to TOP−{5} (5 ∉, 0 ∈, non-top)"
    ((not (Ws.is_top c6)) && (not (Ws.elem (w32 5) c6)) && Ws.elem (w32 0) c6);
  let fv = Var.create ~is_virtual:false ~fresh:false "zf" (Type.Imm 1) in
  let c7 =
    AI.find_word 1
      (Vsa.Test_seam.assume_jump_cond env (mk_jmp_to tgt (Bil.Var fv)))
      fv
  in
  check "D4-7: assume (flag) forces the flag to {1}" (Ws.elem Cbat_word.b1 c7 && not (Ws.elem Cbat_word.b0 c7));
  let c8 =
    AI.find_word 1
      (Vsa.Test_seam.assume_jump_cond env
         (mk_jmp_to tgt (Bil.UnOp (Bil.NOT, Bil.Var fv))))
      fv
  in
  check "D4-8: assume (NOT flag) forces the flag to {0}"
    (Ws.elem Cbat_word.b0 c8 && not (Ws.elem Cbat_word.b1 c8));
  ()

(* Every fixture def is denoted; there is no tag gate. *))
(* BIR-level loop: back-edge refined by "i < 5", exit bounded. *)
;
(  (* Back-edge refined by "i < 5": header converges before widening fires. *)
  let i = Var.create ~is_virtual:false ~fresh:false "i" (Type.Imm 32) in
  let iv = Bil.Var i in
  let lt5 = Bil.BinOp (Bil.LT, iv, Bil.Int (Cbat_word.to_word (w32 5))) in
  let nlt5 = Bil.UnOp (Bil.NOT, lt5) in
  let entry0 = blk_of_defs [ Def.create i (Bil.Int (Cbat_word.to_word (w32 0))) ] in
  let body0 =
    blk_of_defs [ Def.create i (Bil.BinOp (Bil.PLUS, iv, Bil.Int (Cbat_word.to_word (w32 1)))) ]
  in
  let header0 = blk_of_defs [] in
  let exit0 = blk_of_defs [] in
  let body_tid = Term.tid body0 in
  let header_tid = Term.tid header0 in
  let exit_tid = Term.tid exit0 in
  let entry = with_jmps entry0 [ mk_goto body_tid ] in
  let body = with_jmps body0 [ mk_goto header_tid ] in
  let header = with_jmps header0 [ mk_jmp_to exit_tid nlt5; mk_jmp_to body_tid lt5 ] in
  let exit = exit0 in
  let sub_b = Sub.Builder.create ~name:"d4_loop" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  let sol = run_anchored sub in
  (* Per-edge states read from single-predecessor targets' IN-states. *)
  let c_iter = AI.find_word 32 (Graphlib.Std.Solution.get sol body_tid) i in
  let c_exit = AI.find_word 32 (Graphlib.Std.Solution.get sol exit_tid) i in
  check
    "D4-9 (BIR loop): the partition — the iterate view's counter is bounded by the guard (⊆ [0,4]) \
     and the exit view carries the exit-iteration values (min ≥ 5)"
    ((not (Ws.is_top c_iter))
    && (match Ws.max_elem c_iter with Some w -> Cbat_word.(<=) w (w32 4) | None -> false)
    && (not (Ws.is_top c_exit))
    && match Ws.min_elem c_exit with Some w -> Cbat_word.(>=) w (w32 5) | None -> false);
  ())
(* Ite else-arm joins both arms. *)
;
(  (* {0,1}-valued Ite cond must not kill the else value. *)
  let f32 = Var.create ~is_virtual:false ~fresh:false "flag32" (Type.Imm 32) in
  let env = AI.add_word AI.top ~key:f32 ~data:(Ws.of_list ~width:32 [ w32 0; w32 1 ]) in
  let e = Bil.Ite (Bil.Var f32, Bil.Int (Cbat_word.to_word (w32 10)), Bil.Int (Cbat_word.to_word (w32 20))) in
  match Vsa.Test_seam.denote_imm_exp e env with
  | Ok ws ->
      check "E3-1: Ite with a {0,1}-valued flag joins both arms (no bottom)"
        (Ws.elem (w32 10) ws && Ws.elem (w32 20) ws && not (Ws.is_bottom ws))
  | Error _ ->
      check "E3-1: Ite with a {0,1}-valued flag joins both arms (no bottom)" false;
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
  let _, _, sub, exit_tid =
    mk_counter_loop ~exit_defs:(fun i ->
        [ Def.create j (Bil.BinOp (Bil.RSHIFT, Bil.Var i, Bil.Int (Cbat_word.to_word (w64 1)))) ])
  in
  (* Mixed-width rshift computes: no guard fire, j non-top. *)
  let comp = "rshift: mixed-width shift operands (32 and 64 bits)" in
  let fired_r =
    fired comp (fun () -> ignore (run_anchored sub))
  in
  let sol = run_anchored sub in
  let exit_ai = Graphlib.Std.Solution.get sol exit_tid in
  let i = Var.create ~is_virtual:false ~fresh:false "i" (Type.Imm 32) in
  let j_after =
    Vsa.Test_seam.denote_def
      (Def.create j (Bil.BinOp (Bil.RSHIFT, Bil.Var i, Bil.Int (Cbat_word.to_word (w64 1)))))
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
  let d = Def.create iv (Bil.Int (Cbat_word.to_word (w64 7))) in
  let e_den = Vsa.Test_seam.denote_def d AI.top in
  check "T2-1: gate-free — every def is denoted, no tag needed"
    (Ws.equal (AI.find_word 64 e_den iv) (Ws.singleton (w64 7)));
  ()

(* Frozen-flag fixture: f := g/h, stack-access load, unrelated-def control, jmp exit if f. *))
;
(  let x = v64 "t3_x" in
  let tgt = Tid.create () in
  let c_in =
    AI.find_word 64
      (Vsa.Test_seam.assume_jump_cond AI.top
         (mk_jmp_to tgt (Bil.BinOp (Bil.EQ, Bil.Var x, Bil.Int (Cbat_word.to_word (w64 5))))))
      x
  in
  check "T3-1: gate-free — the guard refines x to {5}"
    (Ws.min_elem c_in = Some (w64 5) && Ws.max_elem c_in = Some (w64 5));
  let c_out =
    AI.find_word 64
      (Vsa.Test_seam.assume_jump_cond AI.top
         (mk_jmp_to tgt (Bil.BinOp (Bil.EQ, Bil.Var x, Bil.Int (Cbat_word.to_word (w64 5))))))
      x
  in
  check "T3-2: gate-free (spec §2.1) — the guard refines x to {5}"
    (Ws.min_elem c_out = Some (w64 5) && Ws.max_elem c_out = Some (w64 5));
  ())
;
(  (* G3: gate-free flag-guard refinement (spec §2.1). *)
  let f, ctx, sub, exit_tid, _, _, _ = mk_flag_sub ~mixed:true in
  let sol = run_anchored sub in
  ignore sol;
  (* Exit IN-state is the taken-edge refined state; the fallthrough edge has no target block. *)
  let c = AI.find_word 1 (Graphlib.Std.Solution.get sol exit_tid) f in
  check "T3-7: mixed-def — f IS refined to {1} on the taken edge"
    (Ws.elem Cbat_word.b1 c && not (Ws.elem Cbat_word.b0 c));
  (* Single-def control refines identically. *)
  let f2, _, sub2, exit_tid2, _, _, _ = mk_flag_sub ~mixed:false in
  let sol2 = run_anchored sub2 in
  let c2 = AI.find_word 1 (Graphlib.Std.Solution.get sol2 exit_tid2) f2 in
  check "T3-8: single-def flag — f2 IS refined to {1} on the taken edge"
    (Ws.elem Cbat_word.b1 c2 && not (Ws.elem Cbat_word.b0 c2));
  ()

(* Caller-alias fixture: aliased slot, tracked load, call, post reload. Returns the record. *))
;
(  let fx = mk_caller_alias () in
  let sub = fx.ca_sub in
  (* Pre-call state makes the post-call check non-vacuous. *)
  let entry_blk' =
    match Term.find blk_t sub (Term.tid fx.ca_entry_blk) with Some b -> b | None -> assert false
  in
  let pre = Vsa.Test_seam.denote_defs entry_blk' AI.top in
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
  let sol = run_anchored sub in
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
    let offsets, _ = extract_anchored sub in
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
  let tags, _ = extract_anchored sub in
  check "P22-1: channel 1 — the indexed load at [rdi + idx*8] seeds Range(32,32)"
    (Core.Map.find tags (Term.tid def_load) = Some (Cu.Range (32L, 32L)));
  ()

(* Heap-shaped addresses do not seed; the RSP-direct access does. *))
;
(  let _, _, def_load, def_store_disjoint, def_store_rsp, sub = mk_gpr_rbp_sub () in
  let tags, _ = extract_anchored sub in
  check "P23-1: channel 2 — the load at [rbp + idx*8] (denotes outside the neighborhood) is NOT seeded"
    (Core.Map.find tags (Term.tid def_load) = None);
  check "P23-2: channel 2 — the disjoint store at [rbp + 0x100] is NOT seeded"
    (Core.Map.find tags (Term.tid def_store_disjoint) = None);
  check "P23-3: channel 1 — the RSP-direct store at [RSP - 8] seeds Range(-8,-8)"
    (Core.Map.find tags (Term.tid def_store_rsp) = Some (Cu.Range (-8L, -8L)));
  ())
;
(  let _, def_load, _, def_use, sub = mk_one_path_sub () in
  let tags, _ = extract_anchored sub in
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
(* Crash shape: RAX := high:0[RAX] in the call's return target. Returns (rax, ctx, sub, final tid). *)
(  (* Restriction stays OFF: ON would skip the untagged cast, making the test vacuous. *)
  let rax, _, sub, final_tid = mk_high0_cast_sub () in
  let sol = run_anchored sub in
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
(* BIR loop with counter-shift: [0,N) window survives the shift. *)
(  let i = Var.create ~is_virtual:false ~fresh:false "i" (Type.Imm 32) in
  let x = Var.create ~is_virtual:false ~fresh:false "x" (Type.Imm 64) in
  let y = Var.create ~is_virtual:false ~fresh:false "y" (Type.Imm 64) in
  let iv = Bil.Var i in
  let xv = Bil.Var x in
  let lt5 = Bil.BinOp (Bil.LT, iv, Bil.Int (Cbat_word.to_word (w32 5))) in
  let nlt5 = Bil.UnOp (Bil.NOT, lt5) in
  let entry0 =
    blk_of_defs
      [
        Def.create i (Bil.Int (Cbat_word.to_word (w32 0)));
        Def.create x (Bil.Int (Cbat_word.to_word (w64 16)));
      ]
  in
  (* Body increments first: y = x << (i+1) ∈ {32..512}, in case 1. *)
  let body0 =
    blk_of_defs
      [
        Def.create i (Bil.BinOp (Bil.PLUS, iv, Bil.Int (Cbat_word.to_word (w32 1))));
        Def.create y (Bil.BinOp (Bil.LSHIFT, xv, iv));
      ]
  in
  let header0 = blk_of_defs [] in
  let exit0 = blk_of_defs [] in
  let body_tid = Term.tid body0 in
  let header_tid = Term.tid header0 in
  let exit_tid = Term.tid exit0 in
  let entry = with_jmps entry0 [ mk_goto body_tid ] in
  let body = with_jmps body0 [ mk_goto header_tid ] in
  let header = with_jmps header0 [ mk_jmp_to exit_tid nlt5; mk_jmp_to body_tid lt5 ] in
  let exit = exit0 in
  let sub_b = Sub.Builder.create ~name:"e2ec_loop" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  let sol = run_anchored sub in
  (* Single-predecessor IN-states are the per-edge refined states. *)
  let c_iter = AI.find_word 32 (Graphlib.Std.Solution.get sol body_tid) i in
  let c_exit = AI.find_word 32 (Graphlib.Std.Solution.get sol exit_tid) i in
  check
    "E2eC-13 (BIR loop): the partition — the iterate view's counter is bounded by the guard (⊆ \
     [0,4]) and the exit view carries the exit-iteration values (min ≥ 5)"
    ((not (Ws.is_top c_iter))
    && (match Ws.max_elem c_iter with Some w -> Cbat_word.(<=) w (w32 4) | None -> false)
    && (not (Ws.is_top c_exit))
    && match Ws.min_elem c_exit with Some w -> Cbat_word.(>=) w (w32 5) | None -> false);
  (* Shifted value's window: counter ⊆ [0,4] at the guard. *)
  let c_iter = AI.find_word 32 (Graphlib.Std.Solution.get sol body_tid) i in
  check
    "E2eC-14 (BIR loop): the counter window survives the body shift — the iterate view's counter \
     stays ⊆ [0,4] (y = x << (i+1) ∈ {32..512})"
    ((not (Ws.is_top c_iter))
    && match Ws.max_elem c_iter with Some w -> Cbat_word.(<=) w (w32 4) | None -> false);
  ())
;
(  (* Channel-2 negative (spec §2.2): the heap-indexed store never seeds. *)
  let _, _, _, _, sub, exit_tid = mk_e2ed_heap_sub () in
  (* Gate-free: every def is denoted, so the store's data var reads {99}. *)
  let sol = run_anchored sub in
  let exit_ai = Graphlib.Std.Solution.get sol exit_tid in
  let vv = AI.find_word 64 exit_ai (v64 "e2ed_v") in
  check "E2eD-4: gate-free — the heap store's data var is denoted ({99})"
    (Ws.equal vv (Ws.singleton (w64 99)));
  ()

(* Channel-1 indexed-store pin: same shape seeds without any tagger. *))
;
(  let _, _, def_store, sub, _ = mk_e2ed_rsp_store_sub () in
  let tags, _ = extract_anchored sub in
  check "E2eD-5: channel 1 — the indexed store at [(rbp - 0x30) + i*8] seeds Range(-24,-24)"
    (Core.Map.find tags (Term.tid def_store) = Some (Cu.Range (-24L, -24L)));
  ()

(* E3: top-address stores leave memory unchanged; the slot load reads through. *))
;
(  let m = memv "e2ed_m3" in
  let t = v64 "e2ed_t3" in
  let d1 =
    Def.create m
      (Bil.Store (Bil.Var m, Bil.Int (Cbat_word.to_word (w64 0x100)), Bil.Int (Cbat_word.to_word (w64 42)), LittleEndian, `r64))
  in
  let env1 = Vsa.Test_seam.denote_def d1 AI.top in
  let d2 =
    Def.create m
      (Bil.Store
         (Bil.Var m, Bil.Unknown ("e2ed_top", Type.Imm 64), Bil.Int (Cbat_word.to_word (w64 7)), LittleEndian, `r64))
  in
  let dload = Def.create t (Bil.Load (Bil.Var m, Bil.Int (Cbat_word.to_word (w64 0x100)), LittleEndian, `r64)) in
  let env2 = Vsa.Test_seam.denote_def d2 env1 in
  check "E2eD-7: gate-free — a top-addr store leaves memory unchanged"
    (AI.equal env2 env1);
  let env3 = Vsa.Test_seam.denote_def dload env2 in
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
  let sol = run_anchored sub in
  let st = Graphlib.Std.Solution.get sol (entry_tid_of sub) in
  check
    "P3-1: gate-free — the RSP := 0 anchor is denoted (entry input state \
     carries RSP = {0})"
    (Ws.equal (AI.find_word 64 st rsp_var) (Ws.singleton (w64 0)));
  ())
;
(  let full = Ws.top 1 in
  let full_l = Ws.of_list ~width:1 [ Cbat_word.b0; Cbat_word.b1 ] in
  check
    "L2b-1: the full 1-bit domain {0,1} reads cardn 2 (non-bottom; the FinSet cardinality no \
     longer wraps at the set width)"
    ((not (Ws.is_bottom full))
    && Cbat_word.(=) (Ws.cardinality full) (Cbat_word.of_int ~width:2 2)
    && (not (Ws.is_bottom full_l))
    && Cbat_word.(=) (Ws.cardinality full_l) (Cbat_word.of_int ~width:2 2));
  ()

(* L2b-2: EQ over {0,1} — is_zero guard sees unwrapped cardn. *))
;
(  let zf = v1 "l2b_zf2" in
  let env = AI.add_word AI.top ~key:zf ~data:(Ws.of_list ~width:1 [ Cbat_word.b0; Cbat_word.b1 ]) in
  let e = Bil.BinOp (Bil.EQ, Bil.Var zf, Bil.Int W.b0) in
  match Vsa.Test_seam.denote_imm_exp e env with
  | Ok ws ->
      check
        "L2b-2: EQ over a {0,1} operand is {0,1} (bool_top), not bottom — the is_zero guard sees \
         cardn 2"
        ((not (Ws.is_bottom ws)) && Cbat_word.(=) (Ws.cardinality ws) (Cbat_word.of_int ~width:2 2))
  | Error _ ->
      check
        "L2b-2: EQ over a {0,1} operand is {0,1} (bool_top), not bottom — the is_zero guard sees \
         cardn 2"
        false;
      ()

(* L2b-3: lifted 1-bit flag value via unknown[bits]:u1 def. *))
;
(  let pf = v1 "l2b_pf3" in
  let env_after = Vsa.Test_seam.denote_def (Def.create pf (Bil.Unknown ("l2b_bits", Type.Imm 1))) AI.top in
  let ws = AI.find_word 1 env_after pf in
  check "L2b-3: a lifted 1-bit flag def (val_top (Imm 1)) is {0,1} with cardn 2, not bottom"
    ((not (Ws.is_bottom ws)) && Cbat_word.(=) (Ws.cardinality ws) (Cbat_word.of_int ~width:2 2));
  ()

(* L2b-4: overlap comparisons return bool_top, not bottom. *))
;
(  let x = v64 "l2b_x4" in
  let y = v64 "l2b_y4" in
  let z = v64 "l2b_z4" in
  let ok_lt =
    match Vsa.Test_seam.denote_imm_exp (Bil.BinOp (Bil.LT, Bil.Var x, Bil.Var y)) AI.top with
    | Ok ws -> (not (Ws.is_bottom ws)) && Cbat_word.(=) (Ws.cardinality ws) (Cbat_word.of_int ~width:2 2)
    | Error _ -> false
  in
  let ok_eq =
    match Vsa.Test_seam.denote_imm_exp (Bil.BinOp (Bil.EQ, Bil.Int (Cbat_word.to_word (w64 0)), Bil.Var z)) AI.top with
    | Ok ws -> (not (Ws.is_bottom ws)) && Cbat_word.(=) (Ws.cardinality ws) (Cbat_word.of_int ~width:2 2)
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
    Vsa.Test_seam.denote_def (Def.create zf (Bil.BinOp (Bil.EQ, Bil.Int (Cbat_word.to_word (w64 0)), Bil.Var x))) AI.top
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
  let kept = Vsa.Test_seam.reachable_jumps flag_env (Seq.of_list [ jmp ]) |> Seq.to_list in
  (* (b) loop with flag-gated back-edge. *)
  let cnt = v64 "l2b_cnt5" in
  let entry0 =
    blk_of_defs [ Def.create zf (Bil.BinOp (Bil.EQ, Bil.Int (Cbat_word.to_word (w64 0)), Bil.Var x)) ]
  in
  let body0 =
    blk_of_defs [ Def.create cnt (Bil.BinOp (Bil.PLUS, Bil.Var cnt, Bil.Int (Cbat_word.to_word (w64 1)))) ]
  in
  let header0 = blk_of_defs [] in
  let exit0 = blk_of_defs [] in
  let body_tid = Term.tid body0 in
  let exit_tid = Term.tid exit0 in
  let header_tid = Term.tid header0 in
  let entry = with_jmps entry0 [ mk_goto header_tid ] in
  let body = with_jmps body0 [ mk_goto header_tid ] in
  let header =
    with_jmps header0
      [ mk_jmp_to body_tid (Bil.Var zf); mk_jmp_to exit_tid (Bil.UnOp (Bil.NOT, Bil.Var zf)) ]
  in
  let exit = exit0 in
  let sub_b = Sub.Builder.create ~name:"l2b_flag_loop" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  let sol = run_anchored sub in
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
    && Ws.elem Cbat_word.b1 body_flag);
  ())
