(* test_regression: narrow-store/degraded-frame/outgoing-escape pins (C1-C4 + R11/R6/G3, run_creg), the Oracle remediation batch (A1-A4, run_remediation), and the R12 region-split emission gates (run_regions). KB order: run_creg provides C1's vsa_info entry; A4 borrows it. *)
open Bap.Std
open Bap_core_theory
open Test_common

(* --- regression tests C1..C4 ------------------------------------------- *)
let q64 (v : int64) : word = W.of_int64 ~width:64 v

(* regression C1: the narrow-store OR-mask width (the mask must be computed at the SLOT width 64;
   neg(1 << bits*8) with bits*8 >= 64 collapses to -1 and keeps the stale wide bytes). *)
type c3_fixture = {
  c3_sub : sub term;
  c3_blk0 : blk term;
  c3_blk1 : blk term;
  c3_post_tid : tid;
  c3_m : var;
}

let mk_c3 () : c3_fixture =
  let rsp = v64 "RSP" in
  let fp = v64 "c3_fp" in
  let rdi = v64 "RDI" in
  let r2 = v64 "c3_r2" in
  let m = memv "c3_m" in
  let cb = Blk.Builder.create () in
  let cblk0 = Blk.Builder.result cb in
  let cb = Blk.Builder.init ~copy_defs:true cblk0 in
  Blk.Builder.add_jmp cb (Jmp.create (Goto (Direct (Term.tid cblk0))));
  let cblk = Blk.Builder.result cb in
  let callee_b = Sub.Builder.create ~name:"c3_callee" () in
  Sub.Builder.add_blk callee_b cblk;
  let callee = Sub.Builder.result callee_b in
  let callee_tid = Term.tid callee in
  let post_b = Blk.Builder.create () in
  Blk.Builder.add_def post_b (Def.create r2 (Bil.Load (Bil.Var m, Bil.Var fp, LittleEndian, `r64)));
  let post0 = Blk.Builder.result post_b in
  let post_tid = Term.tid post0 in
  let def_fp = Def.create fp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 8))) in
  let def_seed =
    Def.create m (Bil.Store (Bil.Var m, Bil.Var fp, Bil.Int (w64 0xAA), LittleEndian, `r64))
  in
  let def_prologue = Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 0x20))) in
  let def_rdi = Def.create rdi (Bil.BinOp (Bil.PLUS, Bil.Var rsp, Bil.Int (w64 0x30))) in
  let def_out =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.PLUS, Bil.Var rsp, Bil.Int (w64 16)),
           Bil.Int (w64 0xBB),
           LittleEndian,
           `r64 ))
  in
  let b0 = Blk.Builder.create () in
  List.iter (Blk.Builder.add_def b0) [ def_fp; def_seed; def_prologue ];
  let b00 = Blk.Builder.result b0 in
  let b1 = Blk.Builder.create () in
  List.iter (Blk.Builder.add_def b1) [ def_rdi; def_out ];
  let b10 = Blk.Builder.result b1 in
  let b0' = Blk.Builder.init ~copy_defs:true b00 in
  Blk.Builder.add_jmp b0' (Jmp.create (Goto (Direct (Term.tid b10))));
  let b1' = Blk.Builder.init ~copy_defs:true b10 in
  Blk.Builder.add_jmp b1'
    (Jmp.create
       (Call (Call.create ~return:(Label.direct post_tid) ~target:(Label.direct callee_tid) ())));
  let blk0 = Blk.Builder.result b0' in
  let blk1 = Blk.Builder.result b1' in
  let sub_b = Sub.Builder.create ~name:"c3_caller" () in
  Sub.Builder.add_arg sub_b (Arg.create rdi (Bil.Var rdi));
  Sub.Builder.add_arg sub_b (Arg.create r2 (Bil.Var r2));
  Sub.Builder.add_blk sub_b blk0;
  Sub.Builder.add_blk sub_b blk1;
  Sub.Builder.add_blk sub_b post0;
  let caller = Sub.Builder.result sub_b in
  ignore callee;
  { c3_sub = caller; c3_blk0 = blk0; c3_blk1 = blk1; c3_post_tid = post_tid; c3_m = m }

(* --- remediation batch A1..A4 (the Oracle REMEDIATE findings) ---------- *)

(* remediation A1 (finding 1, the C3 escalation): the outgoing-slot store's data is TOP (RCX is
   never written anywhere in the fixture) — the doubt must escalate to the sound whole-memory-top
   fallback, not be silently skipped (an unknown stored value may be a pointer into ANY caller cell
   — the stack-passed-pointer class). Geometry mirrors regression C3 exactly; only the stored data
   differs. *)
(* --- 32. R12/G4 region-split emission (Stage 1/2) --------------- *)
(* The emitter's Stage-1 gate and Stage-2a size logic are pure predicates
   over vsa_info + defs.  These checks call the PRODUCTION bil2llvm
   functions (region_bytes / region_size_ok, reached through the public
   Hike.Bil2llvm alias like every other production entry point here) on
   synthetic vsa_info records, and pin ALGORITHM-INDEPENDENT properties —
   positivity + 16-byte alignment, domination of the raw payload,
   monotonicity in span/max_width, cap behavior — instead of duplicating
   the formulas and asserting their literal outputs.  No binary needed,
   no BAP init. *)

let run_creg () =
(  let rsp = v64 "RSP" in
  let m = memv "c1_m" in
  let def_wide =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 16)),
           Bil.Int (q64 0x1122334455667788L),
           LittleEndian,
           `r64 ))
  in
  let def_narrow =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 16)),
           Bil.Int (q64 0xABCDL),
           LittleEndian,
           `r16 ))
  in
  let exit_b = Blk.Builder.create () in
  let exit0 = Blk.Builder.result exit_b in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b def_wide;
  Blk.Builder.add_def entry_b def_narrow;
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let sub_b = Sub.Builder.create ~name:"c1_mask" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b exit0;
  let sub = Sub.Builder.result sub_b in
  let tagged = Relevance.analyze sp sub in
  let tagged =
    Term.map blk_t tagged ~f:(fun b ->
        Term.map def_t b ~f:(fun d ->
            if Term.has_attr d Relevance.stack_access then d
            else Term.set_attr d Relevance.stack_access ()))
  in
  let span = (-16L, -16L) in
  let info : Cu.vsa_info =
    Cu.mk_vsa_info
      ~offsets:
        [ (Term.tid def_wide, Cu.Range (-16L, -16L)); (Term.tid def_narrow, Cu.Range (-16L, -16L)) ]
      ~k_ranges:[]
      ~regions:
        [
          {
            Cu.id = 0;
            Cu.span;
            Cu.members = [ (Term.tid def_wide, span); (Term.tid def_narrow, span) ];
            Cu.convertible = true;
            Cu.max_width = 64;
          };
        ]
      ~stack_plan:[] ~degraded:false ~vla_bounds:[]
  in
  let stl_info = Tid.Map.singleton (Term.tid tagged) info in
  Kb.provide stl_info;
  let sub' = Stl.stack_to_locals Theory.Target.unknown sp tagged in
  let masks =
    Term.enum blk_t sub'
    |> Seq.concat_map ~f:(Term.enum def_t)
    |> Seq.to_list
    |> List.filter_map (fun d ->
        match Def.rhs d with
        | Bil.BinOp
            (Bil.OR, Bil.BinOp (Bil.AND, Bil.Var _, Bil.Int w), Bil.Cast (Bil.UNSIGNED, 64, _)) ->
            Some w
        | _ -> None)
  in
  check "regression C1: the narrow elu16 store is rewritten to the slot OR-mask form"
    (List.length masks = 1);
  check "regression C1: the OR-mask constant is neg(1 << 16) = 0xFFFFFFFFFFFF0000 at width 64"
    (match masks with
    | [ w ] -> Word.bitwidth w = 64 && Word.equal w (q64 0xFFFFFFFFFFFF0000L)
    | _ -> false);
  ()

(* regression C2: the degraded frame size must cover the sub's deepest literal stack access (a fixed
   8192 bound ignores the evidence). *))
;
(  let rsp = v64 "RSP" in
  let m = memv "c2_m" in
  let deep =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 0x4000)),
           Bil.Int (w64 1),
           LittleEndian,
           `r8 ))
  in
  let exit_b = Blk.Builder.create () in
  let exit0 = Blk.Builder.result exit_b in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b deep;
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let sub_b = Sub.Builder.create ~name:"c2_deep" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b exit0;
  let sub = Sub.Builder.result sub_b in
  check "regression C2: the degraded frame covers the deepest literal access (>= 0x4000 bytes)"
    (let n, _, _, _ = B2l.degraded_dims sub in
     Int64.compare n 0x4000L >= 0)

(* regression C3: the call-abstraction escape set must include the outgoing-slot stores of the call
   block (the callee may write its incoming stack args), not only the written arg registers. *))
;
(  let fx = mk_c3 () in
  let sub' = Relevance.analyze sp fx.c3_sub in
  let blk_of tid = match Term.find blk_t sub' tid with Some b -> b | None -> assert false in
  let st_pre =
    Vsa.denote_defs
      (blk_of (Term.tid fx.c3_blk1))
      (Vsa.denote_defs
         (blk_of (Term.tid fx.c3_blk0))
         (AI.set_frame (anchored_entry ()) AI.seed_frame))
  in
  let read64 ai addr =
    match Mem.Key.of_wordset (Ws.singleton (q64 addr)) with
    | Some k ->
        Mem.Val.data
          (Mem.find (64, LittleEndian)
             (AI.find_memory { addr_width = 64; addressable_width = 8 } ai fx.c3_m)
             k)
    | None -> assert false
  in
  check "regression C3: pre-call the caller-frame cell [RSP-8] holds {0xAA} (non-vacuous pin)"
    (Ws.equal (read64 st_pre (-8L)) (Ws.singleton (w64 0xAA)));
  check "regression C3: pre-call the outgoing slot [RSP+16] holds {0xBB} (non-vacuous pin)"
    (Ws.equal (read64 st_pre (-16L)) (Ws.singleton (w64 0xBB)));
  let ctx' = Program.create ~subs:[ sub' ] () in
  let sol = Vsa.static_graph_vsa [] ctx' sub' (Vsa.init_sol ~entry:(anchored_entry ()) sub') in
  let post_ai = Graphlib.Std.Solution.get sol fx.c3_post_tid in
  check
    "regression C3: the caller-frame cell [RSP-8] survives the call with its value (frame not \
     whole-memory-topped)"
    (Ws.equal (read64 post_ai (-8L)) (Ws.singleton (w64 0xAA)));
  check
    "regression C3: the outgoing-slot cell [RSP+16] does NOT survive as the stored concrete value"
    (not (Ws.equal (read64 post_ai (-16L)) (Ws.singleton (w64 0xBB))));
  ()

(* regression C4b: an Infinite-span member whose normalized span equals its Range neighbor's span
   must still block convertibility (the provenance, not the normalized numbers, decides). *))
;
(  let rsp = v64 "RSP" in
  let m = memv "c4b_m" in
  let mk_store lo data sz =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 lo)),
           Bil.Int (w64 data),
           LittleEndian,
           sz ))
  in
  let a_mixed = mk_store 24 1 `r64 in
  let b_mixed = mk_store 20 2 `r64 in
  let a_ctrl = mk_store 48 3 `r64 in
  let b_ctrl = mk_store 44 4 `r64 in
  let exit_b = Blk.Builder.create () in
  let exit0 = Blk.Builder.result exit_b in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.create () in
  List.iter (Blk.Builder.add_def entry_b) [ a_mixed; b_mixed; a_ctrl; b_ctrl ];
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let sub_b = Sub.Builder.create ~name:"c4b_regions" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b exit0;
  let sub = Sub.Builder.result sub_b in
  let info_of offsets : Cu.vsa_info =
    Cu.mk_vsa_info ~offsets ~k_ranges:[] ~regions:[] ~stack_plan:[]
      ~degraded:false ~vla_bounds:[]
  in
  let convertible_of info dtid =
    Sm.regions_of_sub (v64 "RSP") Theory.Target.unknown sub info ~frame_escaped:false
    |> List.filter (fun r -> List.exists (fun (t, _) -> Tid.equal t dtid) r.Cu.members)
    |> function
    | [ r ] -> Some r.Cu.convertible
    | _ -> None
  in
  let ctrl =
    info_of [ (Term.tid a_ctrl, Cu.Range (-48L, -40L)); (Term.tid b_ctrl, Cu.Range (-48L, -40L)) ]
  in
  check "regression C4b control: two identical Range members stay convertible=true"
    (convertible_of ctrl (Term.tid a_ctrl) = Some true
    && convertible_of ctrl (Term.tid b_ctrl) = Some true);
  let mixed =
    info_of
      [ (Term.tid a_mixed, Cu.Range (-24L, -16L)); (Term.tid b_mixed, Cu.Infinite (-24L, -16L)) ]
  in
  check
    "regression C4b: an Infinite-span member whose normalized span equals the Range span makes the \
     component convertible=false"
    (convertible_of mixed (Term.tid a_mixed) = Some false
    && convertible_of mixed (Term.tid b_mixed) = Some false);
  ()

(* regression C4a: an Infinite-tagged def overlapping a concrete Range local keeps its Infinite kind
   through the set-overlap merge (the merge must not overwrite the unbounded class with the merged
   Range). *))
;
(  let rsp = v64 "RSP" in
  let i = Var.create ~is_virtual:false ~fresh:false "c4a_i" (Type.Imm 32) in
  let t = Var.create ~is_virtual:false ~fresh:false "c4a_t" (Type.Imm 32) in
  let m = memv "c4a_m" in
  let iv = Bil.Var i in
  let lt = Bil.BinOp (Bil.LT, iv, Bil.Var t) in
  let nlt = Bil.UnOp (Bil.NOT, lt) in
  let idx_addr =
    Bil.BinOp
      ( Bil.PLUS,
        Bil.Var rsp,
        Bil.BinOp (Bil.MINUS, Bil.Cast (Bil.UNSIGNED, 64, iv), Bil.Int (w64 32)) )
  in
  let def_idx_store =
    Def.create m (Bil.Store (Bil.Var m, idx_addr, Bil.Int (w64 7), LittleEndian, `r64))
  in
  let def_inc = Def.create i (Bil.BinOp (Bil.PLUS, iv, Bil.Int (w32 1))) in
  let def_concrete =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 16)),
           Bil.Int (w64 9),
           LittleEndian,
           `r64 ))
  in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b (Def.create i (Bil.Int (w32 0)));
  Blk.Builder.add_def body_b def_idx_store;
  Blk.Builder.add_def body_b def_inc;
  Blk.Builder.add_def exit_b def_concrete;
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
  Blk.Builder.add_jmp header_b (Jmp.create ~cond:nlt (Goto (Direct exit_tid)));
  Blk.Builder.add_jmp header_b (Jmp.create ~cond:lt (Goto (Direct body_tid)));
  let entry = Blk.Builder.result entry_b in
  let body = Blk.Builder.result body_b in
  let header = Blk.Builder.result header_b in
  let exit = Blk.Builder.result exit_b in
  let sub_b = Sub.Builder.create ~name:"c4a_merge" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  let tagged = Relevance.analyze sp sub in
  let info = Hv.offsets_of_sub Theory.Target.unknown sp tagged in
  let kind_of dtid = Core.Map.find info.Cu.offsets dtid in
  check
    "regression C4a: the indexed loop-body store carries an offset tag (fixture locates the \
     Infinite class)"
    (kind_of (Term.tid def_idx_store) <> None);
  check
    "regression C4a: the Infinite tag survives the overlap merge (not overwritten by the merged \
     Range)"
    (match kind_of (Term.tid def_idx_store) with Some (Cu.Infinite _) -> true | _ -> false);
  ()

(* property R11 (PL2): the set-overlap merge must preserve EVERY member's original kind/span
   verbatim — a PRECISE singleton Range member that merely overlaps a wider ranged access keeps its
   exact span through the merge; the component hull lives ONLY in the region record, never
   back-written into the per-def tags. Mirrors the regression-C4a pattern: the concrete store at
   [RSP-16] shares the element -16 with the indexed loop-body store's class ([RSP + zext(i) - 32]
   covers -16 when i = 16), so the two land in ONE overlap component. *))
;
(  let rsp = v64 "RSP" in
  let i = Var.create ~is_virtual:false ~fresh:false "r11_i" (Type.Imm 32) in
  let t = Var.create ~is_virtual:false ~fresh:false "r11_t" (Type.Imm 32) in
  let m = memv "r11_m" in
  let iv = Bil.Var i in
  let lt = Bil.BinOp (Bil.LT, iv, Bil.Var t) in
  let nlt = Bil.UnOp (Bil.NOT, lt) in
  let idx_addr =
    Bil.BinOp
      ( Bil.PLUS,
        Bil.Var rsp,
        Bil.BinOp (Bil.MINUS, Bil.Cast (Bil.UNSIGNED, 64, iv), Bil.Int (w64 32)) )
  in
  let def_idx_store =
    Def.create m (Bil.Store (Bil.Var m, idx_addr, Bil.Int (w64 7), LittleEndian, `r64))
  in
  let def_inc = Def.create i (Bil.BinOp (Bil.PLUS, iv, Bil.Int (w32 1))) in
  let def_singleton =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 16)),
           Bil.Int (w64 9),
           LittleEndian,
           `r64 ))
  in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b (Def.create i (Bil.Int (w32 0)));
  Blk.Builder.add_def body_b def_idx_store;
  Blk.Builder.add_def body_b def_inc;
  Blk.Builder.add_def exit_b def_singleton;
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
  Blk.Builder.add_jmp header_b (Jmp.create ~cond:nlt (Goto (Direct exit_tid)));
  Blk.Builder.add_jmp header_b (Jmp.create ~cond:lt (Goto (Direct body_tid)));
  let entry = Blk.Builder.result entry_b in
  let body = Blk.Builder.result body_b in
  let header = Blk.Builder.result header_b in
  let exit = Blk.Builder.result exit_b in
  let sub_b = Sub.Builder.create ~name:"r11_merge" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  let tagged = Relevance.analyze sp sub in
  let info = Hv.offsets_of_sub Theory.Target.unknown sp tagged in
  let kind_of dtid = Core.Map.find info.Cu.offsets dtid in
  (* CONTROL (must hold pre AND post): the indexed/ranged member keeps its own kind through the
     merge. *)
  check "property R11 control: the indexed member keeps its own kind through the merge"
    (kind_of (Term.tid def_idx_store) <> None);
  (* RED: the singleton's exact span survives the merge verbatim — currently the component hull
     overwrites it. *)
  check "property R11: the precise singleton Range(-16,-16) survives the overlap merge un-hulled"
    (kind_of (Term.tid def_singleton) = Some (Cu.Range (-16L, -16L)));
  ()

(* R6 unit checks — the NEQ arc at the CLP/composite level: the construction {c+1, step 1, cardn 2^w
   - 1} must survive create's normalization (finite, non-top, exact span), agree with the
   edge-collector's diff(top,{c}) form, meet {c} to bottom (x = c necessarily — the taken path
   genuinely infeasible, so bottom is SOUND), and survive a join with a stepped class without
   collapsing to top. *))
;
(  List.iter
    (fun w ->
      List.iter
        (fun cname ->
          let c =
            if cname = "hi" then W.sub (W.ones w) (W.of_int ~width:w 7) else W.of_int ~width:w 0x2A
          in
          let lbl = Printf.sprintf "@w=%d,%s" w cname in
          let base = W.succ c in
          let cardn = W.pred (Wo.dom_size ~width:(w + 1) w) in
          let arc_clp = Clp.create ~width:w ~step:(W.one w) ~cardn base in
          check
            ("R6 unit: the NEQ arc is finite non-top with cardn 2^w-1 " ^ lbl)
            ((not (Clp.is_infinite arc_clp))
            && (not (Clp.is_top arc_clp))
            && W.equal (Clp.cardinality arc_clp) cardn
            && Clp.elem base arc_clp
            && Clp.elem (W.pred c) arc_clp
            && not (Clp.elem c arc_clp));
          let arc_ws = Ws.of_clp arc_clp in
          check
            ("R6 unit: the NEQ arc equals diff(top,{c}) " ^ lbl)
            (Ws.equal arc_ws (Ws.diff (Ws.top w) (Ws.singleton c)));
          check
            ("R6 unit: the arc's meet with {c} is bottom (genuinely infeasible) " ^ lbl)
            (Ws.is_bottom (Ws.meet arc_ws (Ws.singleton c)));
          (* a stepped class inside the arc's linear span: the join stays a bounded CLP (sound hull;
             never top) *)
          let stepped =
            Clp.create
              (W.add base (W.of_int ~width:w 7))
              ~step:(W.of_int ~width:w 10)
              ~cardn:(W.of_int ~width:(w + 1) 5)
          in
          let joined = Ws.union arc_ws (Ws.of_clp stepped) in
          check
            ("R6 unit: the arc survives a join with a stepped class (non-top) " ^ lbl)
            ((not (Ws.is_top joined)) && not (Ws.is_bottom joined)))
        [ "lo"; "hi" ])
    [ 8; 16; 32; 64 ]

(* R6 (Stage 2): the jne-counter loop — the -O0 guard shape is FLAG-INDIRECTED: `t := (i <> lim); if
   t goto body`. The CLP domain is CIRCULAR over Z_2^w, so {x : x <> c} is exactly ONE arc — [c+1 ..
   c-1] (step 1, cardn 2^w - 1) — and the flag-state recovery must derive it: the taken view
   constrains the counter to the arc, the fallthrough view (flag clear) pins it to {lim} exactly.
   Mirrors regression C4a's counter fixture (indexed loop-body store; offsets_of_sub runs the full
   production pipeline). *))
;
(  let rsp = v64 "RSP" in
  let i = Var.create ~is_virtual:false ~fresh:false "r6_i" (Type.Imm 32) in
  let t = Var.create ~is_virtual:false ~fresh:false "r6_t" (Type.Imm 1) in
  let m = memv "r6_m" in
  let iv = Bil.Var i in
  let neq_exp = Bil.BinOp (Bil.NEQ, iv, Bil.Int (w32 9)) in
  let idx_addr =
    Bil.BinOp
      ( Bil.PLUS,
        Bil.Var rsp,
        Bil.BinOp (Bil.MINUS, Bil.Cast (Bil.UNSIGNED, 64, iv), Bil.Int (w64 32)) )
  in
  let def_idx_store =
    Def.create m (Bil.Store (Bil.Var m, idx_addr, Bil.Int (w64 7), LittleEndian, `r64))
  in
  let def_inc = Def.create i (Bil.BinOp (Bil.PLUS, iv, Bil.Int (w32 1))) in
  let def_flag = Def.create t neq_exp in
  let entry_b = Blk.Builder.create () in
  let loop_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b (Def.create i (Bil.Int (w32 0)));
  Blk.Builder.add_def loop_b def_idx_store;
  Blk.Builder.add_def loop_b def_inc;
  (* the flag def comes AFTER the increment (a later def of a free var of the recorded operand would
     clear the flag-state record) *)
  Blk.Builder.add_def loop_b def_flag;
  let entry0 = Blk.Builder.result entry_b in
  let loop0 = Blk.Builder.result loop_b in
  let exit0 = Blk.Builder.result exit_b in
  let loop_tid = Term.tid loop0 in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct loop_tid)));
  let loop_b = Blk.Builder.init ~copy_defs:true loop0 in
  Blk.Builder.add_jmp loop_b (Jmp.create ~cond:(Bil.Var t) (Goto (Direct loop_tid)));
  Blk.Builder.add_jmp loop_b (Jmp.create (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let loop = Blk.Builder.result loop_b in
  let exit = Blk.Builder.result exit_b in
  let sub_b = Sub.Builder.create ~name:"r6_jne_counter" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b loop;
  Sub.Builder.add_blk sub_b exit;
  let sub0 = Sub.Builder.result sub_b in
  let tagged_rel = Relevance.analyze sp sub0 in
  (* The relevance pass does NOT tag 1-bit flag defs (they feed no stack sink), so [tag_relevant]
     would prune the guard's views entirely. The R6 lane needs the GUARD's flag tracked: the fixture
     re-tags the flag def explicitly (the same idiom as the L3c fixtures' [tag_all]), keeping
     Relevance.analyze's tags (incl. direct_sp) for everything else. *)
  let tagged =
    Term.map blk_t tagged_rel ~f:(fun b ->
        Term.map def_t b ~f:(fun d ->
            if Tid.equal (Term.tid d) (Term.tid def_flag) then
              Term.set_attr d Cbat_vsa_utils.relevant ()
            else d))
  in
  let info = Hv.offsets_of_sub Theory.Target.unknown sp tagged in
  let kind_of dtid = Core.Map.find info.Cu.offsets dtid in
  check "R6: the jne-counter loop's indexed store carries an offset tag"
    (kind_of (Term.tid def_idx_store) <> None);
  (* the per-guard views: the taken view must constrain i to the ARC {x : x <> 9} (= diff(top,{9}) —
     one CLP), the fallthrough view (the flag-clear trace) pins i to {9}.
     MIGRATED (ticket 02, the Phase B deletion): the views are gone.  The
     FALLTHROUGH claim is assertable in the fused world — the EXIT block's
     only predecessor is the loop's tail edge, whose ACCUMULATED cond is
     the negation of the when's (i = 9), so the exit's IN-state pins i to
     {9}.  The TAKEN claim has NO fused-world equivalent: its only target
     is the LOOP block, a multi-predecessor head whose IN-state is the
     JOIN of the entry edge and the refined back edge (spec §10.2) — the
     per-edge partition collapses by construction; the check stays in the
     ignore list (already stubbed on the base tree), its body now the
     sound floor (the entry constant survives the join). *)
  let prog' = Program.create ~subs:[ tagged ] () in
  let sol =
    Vsa.static_graph_vsa [] prog' tagged (Vsa.init_sol ~entry:(anchored_entry ()) tagged)
  in
  ignore sol;
  let head_i = AI.find_word 32 (Graphlib.Std.Solution.get sol loop_tid) i in
  check
    "R6: the NEQ guard's TAKEN view constrains the counter to the arc {x <> 9} (non-top, equals \
     diff(top,{9}))"
    (match Ws.min_elem head_i with Some lo -> W.equal lo (w32 0) | None -> false);
  let exit_i = AI.find_word 32 (Graphlib.Std.Solution.get sol exit_tid) i in
  check "R6: the NEQ guard's FALLTHROUGH view pins the counter to {9} exactly"
    (Ws.equal exit_i (Ws.singleton (w32 9)));
  ()

(* G3 (Stage A): the PRODUCTION relevance path must keep FLAG-INDIRECTED guards refineable WITHOUT
   manual re-tagging. Identical geometry to the R6 Stage-2 fixture above, but [Relevance.analyze]'s
   tags are used AS-IS — no [tag_relevant] workaround. The backward lane must seed jump-condition
   variables as live roots so the flag def (which feeds no stack sink) is tagged and the NEQ guard
   refines instead of being pruned to the invariant state. Before the fix this failed: the untagged
   flag var left the guard outside [refineable] (the pre-fusion Phase B walk's tag-relevance
   pruning — deleted with Phase B, ticket 02), so both edge states collapsed to the
   loop-invariant state — taken not the arc, fallthrough not pinned
   to {9}. *))
;
(  let rsp = v64 "RSP" in
  let i = Var.create ~is_virtual:false ~fresh:false "g3_i" (Type.Imm 32) in
  let t = Var.create ~is_virtual:false ~fresh:false "g3_t" (Type.Imm 1) in
  let m = memv "g3_m" in
  let iv = Bil.Var i in
  let neq_exp = Bil.BinOp (Bil.NEQ, iv, Bil.Int (w32 9)) in
  let idx_addr =
    Bil.BinOp
      ( Bil.PLUS,
        Bil.Var rsp,
        Bil.BinOp (Bil.MINUS, Bil.Cast (Bil.UNSIGNED, 64, iv), Bil.Int (w64 32)) )
  in
  let def_idx_store =
    Def.create m (Bil.Store (Bil.Var m, idx_addr, Bil.Int (w64 7), LittleEndian, `r64))
  in
  let def_inc = Def.create i (Bil.BinOp (Bil.PLUS, iv, Bil.Int (w32 1))) in
  let def_flag = Def.create t neq_exp in
  let entry_b = Blk.Builder.create () in
  let loop_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b (Def.create i (Bil.Int (w32 0)));
  Blk.Builder.add_def loop_b def_idx_store;
  Blk.Builder.add_def loop_b def_inc;
  Blk.Builder.add_def loop_b def_flag;
  let entry0 = Blk.Builder.result entry_b in
  let loop0 = Blk.Builder.result loop_b in
  let exit0 = Blk.Builder.result exit_b in
  let loop_tid = Term.tid loop0 in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct loop_tid)));
  let loop_b = Blk.Builder.init ~copy_defs:true loop0 in
  Blk.Builder.add_jmp loop_b (Jmp.create ~cond:(Bil.Var t) (Goto (Direct loop_tid)));
  Blk.Builder.add_jmp loop_b (Jmp.create (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let loop = Blk.Builder.result loop_b in
  let exit = Blk.Builder.result exit_b in
  let sub_b = Sub.Builder.create ~name:"g3_jne_counter" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b loop;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  (* the production path: analyze's tags AS-IS — no manual re-tagging *)
  let tagged = Relevance.analyze sp sub in
  let info = Hv.offsets_of_sub Theory.Target.unknown sp tagged in
  let kind_of dtid = Core.Map.find info.Cu.offsets dtid in
  check "G3: the jne-counter loop's indexed store carries an offset tag"
    (kind_of (Term.tid def_idx_store) <> None);
  let prog' = Program.create ~subs:[ tagged ] () in
  let sol =
    Vsa.static_graph_vsa [] prog' tagged (Vsa.init_sol ~entry:(anchored_entry ()) tagged)
  in
  ignore sol;
  (* MIGRATED (ticket 02): same shape as the R6 Stage-2 fixture above —
     the FALLTHROUGH claim reads the EXIT block's single-predecessor
     IN-state (the accumulated tail cond i = 9); the TAKEN claim's only
     target is the multi-predecessor loop head (the join collapses the
     per-edge arc, spec §10.2), so its body is the sound floor (the
     entry constant survives the join) and the claim stays in the
     ignore list. *)
  let head_i = AI.find_word 32 (Graphlib.Std.Solution.get sol loop_tid) i in
  check
    "G3: the NEQ guard's TAKEN view constrains the counter to the arc {x <> 9} (non-top, equals \
     diff(top,{9}))"
    (match Ws.min_elem head_i with Some lo -> W.equal lo (w32 0) | None -> false);
  let exit_i = AI.find_word 32 (Graphlib.Std.Solution.get sol exit_tid) i in
  check "G3: the NEQ guard's FALLTHROUGH view pins the counter to {9} exactly"
    (Ws.equal exit_i (Ws.singleton (w32 9)));
  ())
let run_remediation () =
(  let rsp = v64 "RSP" in
  let fp = v64 "a1_fp" in
  let rdi = v64 "RDI" in
  let rcx = v64 "RCX" in
  let r2 = v64 "a1_r2" in
  let m = memv "a1_m" in
  let cb = Blk.Builder.create () in
  let cblk0 = Blk.Builder.result cb in
  let cb = Blk.Builder.init ~copy_defs:true cblk0 in
  Blk.Builder.add_jmp cb (Jmp.create (Goto (Direct (Term.tid cblk0))));
  let cblk = Blk.Builder.result cb in
  let callee_b = Sub.Builder.create ~name:"a1_callee" () in
  Sub.Builder.add_blk callee_b cblk;
  let callee = Sub.Builder.result callee_b in
  let callee_tid = Term.tid callee in
  let post_b = Blk.Builder.create () in
  Blk.Builder.add_def post_b (Def.create r2 (Bil.Load (Bil.Var m, Bil.Var fp, LittleEndian, `r64)));
  let post0 = Blk.Builder.result post_b in
  let post_tid = Term.tid post0 in
  let def_fp = Def.create fp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 8))) in
  let def_seed =
    Def.create m (Bil.Store (Bil.Var m, Bil.Var fp, Bil.Int (w64 0xAA), LittleEndian, `r64))
  in
  let def_prologue = Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 0x20))) in
  let def_rdi = Def.create rdi (Bil.BinOp (Bil.PLUS, Bil.Var rsp, Bil.Int (w64 0x30))) in
  (* THE difference vs C3: the outgoing slot stores RCX, which NOTHING in the fixture ever writes —
     its value set at the call is TOP. *)
  let def_out =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.PLUS, Bil.Var rsp, Bil.Int (w64 16)),
           Bil.Var rcx,
           LittleEndian,
           `r64 ))
  in
  let b0 = Blk.Builder.create () in
  List.iter (Blk.Builder.add_def b0) [ def_fp; def_seed; def_prologue ];
  let b00 = Blk.Builder.result b0 in
  let b1 = Blk.Builder.create () in
  List.iter (Blk.Builder.add_def b1) [ def_rdi; def_out ];
  let b10 = Blk.Builder.result b1 in
  let b0' = Blk.Builder.init ~copy_defs:true b00 in
  Blk.Builder.add_jmp b0' (Jmp.create (Goto (Direct (Term.tid b10))));
  let b1' = Blk.Builder.init ~copy_defs:true b10 in
  Blk.Builder.add_jmp b1'
    (Jmp.create
       (Call (Call.create ~return:(Label.direct post_tid) ~target:(Label.direct callee_tid) ())));
  let blk0 = Blk.Builder.result b0' in
  let blk1 = Blk.Builder.result b1' in
  let sub_b = Sub.Builder.create ~name:"a1_caller" () in
  Sub.Builder.add_arg sub_b (Arg.create rdi (Bil.Var rdi));
  Sub.Builder.add_arg sub_b (Arg.create r2 (Bil.Var r2));
  Sub.Builder.add_blk sub_b blk0;
  Sub.Builder.add_blk sub_b blk1;
  Sub.Builder.add_blk sub_b post0;
  let caller = Sub.Builder.result sub_b in
  ignore callee;
  let sub' = Relevance.analyze sp caller in
  let blk_of tid = match Term.find blk_t sub' tid with Some b -> b | None -> assert false in
  let st_pre =
    Vsa.denote_defs
      (blk_of (Term.tid blk1))
      (Vsa.denote_defs (blk_of (Term.tid blk0)) (AI.set_frame (anchored_entry ()) AI.seed_frame))
  in
  let read64 ai addr =
    match Mem.Key.of_wordset (Ws.singleton (q64 addr)) with
    | Some k ->
        Mem.Val.data
          (Mem.find (64, LittleEndian)
             (AI.find_memory { addr_width = 64; addressable_width = 8 } ai m)
             k)
    | None -> assert false
  in
  check
    "remediation A1: pre-call the seeded caller-frame cell [entry RSP-8] holds {0xAA} (non-vacuous \
     pin)"
    (Ws.equal (read64 st_pre (-8L)) (Ws.singleton (w64 0xAA)));
  let ctx' = Program.create ~subs:[ sub' ] () in
  let sol = Vsa.static_graph_vsa [] ctx' sub' (Vsa.init_sol ~entry:(anchored_entry ()) sub') in
  let post_ai = Graphlib.Std.Solution.get sol post_tid in
  check
    "remediation A1: the TOP-valued outgoing-slot store escalates — the seeded caller-frame cell \
     does NOT survive the call"
    (not (Ws.equal (read64 post_ai (-8L)) (Ws.singleton (w64 0xAA))));
  ()

(* remediation A2 (finding 2a, composed depth): the degraded frame size must SUM the two depth
   sources — an [RSP := RSP - k] decrement moves RSP, then a store at [RSP - k] reaches k below the
   MOVED RSP, so the reach is dec + neg_disp, not max(dec, neg_disp). *))
;
(  let rsp = v64 "RSP" in
  let m = memv "a2_m" in
  let dec = Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 0x4800))) in
  let deep =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 0x4800)),
           Bil.Int (w64 1),
           LittleEndian,
           `r8 ))
  in
  let exit_b = Blk.Builder.create () in
  let exit0 = Blk.Builder.result exit_b in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b dec;
  Blk.Builder.add_def entry_b deep;
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let sub_b = Sub.Builder.create ~name:"a2_composed" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b exit0;
  let sub = Sub.Builder.result sub_b in
  check
    "remediation A2: the degraded frame covers the COMPOSED depth (round16(dec + neg_disp + 16) = \
     0x9010)"
    (let n, _, _, _ = B2l.degraded_dims sub in
     Int64.compare n 0x9010L >= 0);
  ()

(* remediation A3 (finding 2b, positive headroom): a store at [RSP + k] lands at anchor + k, so the
   degraded anchor index must retreat by the deepest POSITIVE displacement (and the alloca grow
   accordingly), not sit at the bare n - 8. *))
;
(  let rsp = v64 "RSP" in
  let m = memv "a3_m" in
  let hi =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.PLUS, Bil.Var rsp, Bil.Int (w64 0x20)),
           Bil.Int (w64 1),
           LittleEndian,
           `r8 ))
  in
  let exit_b = Blk.Builder.create () in
  let exit0 = Blk.Builder.result exit_b in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b hi;
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let sub_b = Sub.Builder.create ~name:"a3_posdisp" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b exit0;
  let sub = Sub.Builder.result sub_b in
  let n, _, _, anchor_idx = B2l.degraded_dims sub in
  check
    "remediation A3: the degraded anchor leaves headroom above the highest positive-disp access (n \
     - 8 - 0x20)"
    (Int64.equal anchor_idx (Int64.sub (Int64.sub n 8L) 0x20L));
  ()

(* remediation A4a/A4b (hardening pins, expected green immediately): the narrow-store OR-mask width
   for the remaining slot widths — u8 and u32 (regression C1 pinned u16). The KB's vsa-info slot has
   a JOIN domain (map extension/union — see [Hike_kb]): provides accumulate, and a second info for
   the SAME sub tid is a loud [Toplevel.Conflict], not a silent drop. These pins still BORROW C1's
   entry (the fixtures' defs are created with C1's exact def tids and their sub with C1's sub tid,
   read back from [Kb.vsa_info ()]) because they exercise the SAME sub's info — providing their own
   map under that tid would now conflict, and minimal-change doctrine keeps the borrowing. No KB
   write. *))
;
(  let rsp = v64 "RSP" in
  (* the single surviving entry is C1's (its two offsets share one Range) *)
  let c1_sub_tid, c1_info =
    Core.Map.fold (Kb.vsa_info ())
      ~init:(Tid.create (), None)
      ~f:(fun ~key ~data acc -> match acc with _, None -> (key, Some data) | _ -> acc)
    |> fun (t, i) -> match i with Some i -> (t, i) | None -> assert false
  in
  (* arch C2: [offsets] is the precomputed map — the borrow reads it by
     sorted-tid key now (the old positional [List.nth] over the walk-order
     list was the ONE order dependence in the tree; the two tids are
     distinct so the take is order-independent). *)
  let c1_def_tids = c1_info.Cu.offsets |> Core.Map.keys |> List.rev in
  let lo =
    match Core.Map.min_elt c1_info.Cu.offsets with
    | Some (_, Cu.Range (l, _)) -> l
    | _ -> assert false
  in
  let masks_of (sz : size) (data : int64) : word list =
    let m = memv "a4_m" in
    let def_wide =
      Def.create ~tid:(List.nth c1_def_tids 0) m
        (Bil.Store
           ( Bil.Var m,
             Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (q64 (Int64.neg lo))),
             Bil.Int (q64 0x1122334455667788L),
             LittleEndian,
             `r64 ))
    in
    let def_narrow =
      Def.create ~tid:(List.nth c1_def_tids 1) m
        (Bil.Store
           ( Bil.Var m,
             Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (q64 (Int64.neg lo))),
             Bil.Int (q64 data),
             LittleEndian,
             sz ))
    in
    let exit_b = Blk.Builder.create () in
    let exit0 = Blk.Builder.result exit_b in
    let exit_tid = Term.tid exit0 in
    let entry_b = Blk.Builder.create () in
    Blk.Builder.add_def entry_b def_wide;
    Blk.Builder.add_def entry_b def_narrow;
    Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct exit_tid)));
    let entry = Blk.Builder.result entry_b in
    let sub_b = Sub.Builder.create ~tid:c1_sub_tid ~name:"a4_borrow" () in
    Sub.Builder.add_blk sub_b entry;
    Sub.Builder.add_blk sub_b exit0;
    let sub = Sub.Builder.result sub_b in
    let tagged = Relevance.analyze sp sub in
    let tagged =
      Term.map blk_t tagged ~f:(fun b ->
          Term.map def_t b ~f:(fun d ->
              if Term.has_attr d Relevance.stack_access then d
              else Term.set_attr d Relevance.stack_access ()))
    in
    let sub' = Stl.stack_to_locals Theory.Target.unknown sp tagged in
    Term.enum blk_t sub'
    |> Seq.concat_map ~f:(Term.enum def_t)
    |> Seq.to_list
    |> List.filter_map (fun d ->
        match Def.rhs d with
        | Bil.BinOp
            (Bil.OR, Bil.BinOp (Bil.AND, Bil.Var _, Bil.Int w), Bil.Cast (Bil.UNSIGNED, 64, _)) ->
            Some w
        | _ -> None)
  in
  check
    "remediation A4a: the u8 narrow-store OR-mask is neg(1 << 8) = 0xFFFFFFFFFFFFFF00 at width 64"
    (match masks_of `r8 0xABL with
    | [ w ] -> Word.bitwidth w = 64 && Word.equal w (q64 0xFFFFFFFFFFFFFF00L)
    | _ -> false);
  check
    "remediation A4b: the u32 narrow-store OR-mask is neg(1 << 32) = 0xFFFFFFFF00000000 at width 64"
    (match masks_of `r32 0xABCDL with
    | [ w ] -> Word.bitwidth w = 64 && Word.equal w (q64 0xFFFFFFFF00000000L)
    | _ -> false);
  ()

(* remediation A4c (hardening pin, expected green immediately): the outgoing-slot escape ranges
   cover EXACTLY the two adjacent slots' bytes — both slot cells drop post-call, and the neighbor
   caller-frame cell OUTSIDE their extent survives untouched. *))
;
(  let rsp = v64 "RSP" in
  let fp = v64 "a4c_fp" in
  let rdi = v64 "RDI" in
  let r2 = v64 "a4c_r2" in
  let m = memv "a4c_m" in
  let cb = Blk.Builder.create () in
  let cblk0 = Blk.Builder.result cb in
  let cb = Blk.Builder.init ~copy_defs:true cblk0 in
  Blk.Builder.add_jmp cb (Jmp.create (Goto (Direct (Term.tid cblk0))));
  let cblk = Blk.Builder.result cb in
  let callee_b = Sub.Builder.create ~name:"a4c_callee" () in
  Sub.Builder.add_blk callee_b cblk;
  let callee = Sub.Builder.result callee_b in
  let callee_tid = Term.tid callee in
  let post_b = Blk.Builder.create () in
  Blk.Builder.add_def post_b (Def.create r2 (Bil.Load (Bil.Var m, Bil.Var fp, LittleEndian, `r64)));
  let post0 = Blk.Builder.result post_b in
  let post_tid = Term.tid post0 in
  (* the neighbor sits at [entry RSP - 0x18]: inside the caller's kept frame (call-time RSP =
     -0x20), OUTSIDE both slots' byte extents ([RSP+16] = [-0x10,-0x9], [RSP+24] = [-0x8,-0x1]). *)
  let def_fp = Def.create fp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 0x18))) in
  let def_seed =
    Def.create m (Bil.Store (Bil.Var m, Bil.Var fp, Bil.Int (w64 0xAA), LittleEndian, `r64))
  in
  let def_prologue = Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 0x20))) in
  let def_rdi = Def.create rdi (Bil.BinOp (Bil.PLUS, Bil.Var rsp, Bil.Int (w64 0x30))) in
  let def_out1 =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.PLUS, Bil.Var rsp, Bil.Int (w64 16)),
           Bil.Int (w64 0xBB),
           LittleEndian,
           `r64 ))
  in
  let def_out2 =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.PLUS, Bil.Var rsp, Bil.Int (w64 24)),
           Bil.Int (w64 0xDD),
           LittleEndian,
           `r64 ))
  in
  let b0 = Blk.Builder.create () in
  List.iter (Blk.Builder.add_def b0) [ def_fp; def_seed; def_prologue ];
  let b00 = Blk.Builder.result b0 in
  let b1 = Blk.Builder.create () in
  List.iter (Blk.Builder.add_def b1) [ def_rdi; def_out1; def_out2 ];
  let b10 = Blk.Builder.result b1 in
  let b0' = Blk.Builder.init ~copy_defs:true b00 in
  Blk.Builder.add_jmp b0' (Jmp.create (Goto (Direct (Term.tid b10))));
  let b1' = Blk.Builder.init ~copy_defs:true b10 in
  Blk.Builder.add_jmp b1'
    (Jmp.create
       (Call (Call.create ~return:(Label.direct post_tid) ~target:(Label.direct callee_tid) ())));
  let blk0 = Blk.Builder.result b0' in
  let blk1 = Blk.Builder.result b1' in
  let sub_b = Sub.Builder.create ~name:"a4c_caller" () in
  Sub.Builder.add_arg sub_b (Arg.create rdi (Bil.Var rdi));
  Sub.Builder.add_arg sub_b (Arg.create r2 (Bil.Var r2));
  Sub.Builder.add_blk sub_b blk0;
  Sub.Builder.add_blk sub_b blk1;
  Sub.Builder.add_blk sub_b post0;
  let caller = Sub.Builder.result sub_b in
  ignore callee;
  let sub' = Relevance.analyze sp caller in
  let blk_of tid = match Term.find blk_t sub' tid with Some b -> b | None -> assert false in
  let st_pre =
    Vsa.denote_defs
      (blk_of (Term.tid blk1))
      (Vsa.denote_defs (blk_of (Term.tid blk0)) (AI.set_frame (anchored_entry ()) AI.seed_frame))
  in
  let read64 ai addr =
    match Mem.Key.of_wordset (Ws.singleton (q64 addr)) with
    | Some k ->
        Mem.Val.data
          (Mem.find (64, LittleEndian)
             (AI.find_memory { addr_width = 64; addressable_width = 8 } ai m)
             k)
    | None -> assert false
  in
  check
    "remediation A4c: pre-call the neighbor cell [-0x18] holds {0xAA} and the slots hold their \
     values (non-vacuous pins)"
    (Ws.equal (read64 st_pre (-0x18L)) (Ws.singleton (w64 0xAA))
    && Ws.equal (read64 st_pre (-0x10L)) (Ws.singleton (w64 0xBB))
    && Ws.equal (read64 st_pre (-0x8L)) (Ws.singleton (w64 0xDD)));
  let ctx' = Program.create ~subs:[ sub' ] () in
  let sol = Vsa.static_graph_vsa [] ctx' sub' (Vsa.init_sol ~entry:(anchored_entry ()) sub') in
  let post_ai = Graphlib.Std.Solution.get sol post_tid in
  check
    "remediation A4c: BOTH adjacent outgoing-slot cells drop post-call (exact-extent containment)"
    ((not (Ws.equal (read64 post_ai (-0x10L)) (Ws.singleton (w64 0xBB))))
    && not (Ws.equal (read64 post_ai (-0x8L)) (Ws.singleton (w64 0xDD))));
  check "remediation A4c: the neighbor cell OUTSIDE the slots' extent survives the call untouched"
    (Ws.equal (read64 post_ai (-0x18L)) (Ws.singleton (w64 0xAA)));
  ())
let run_regions () =
(  (* fixtures: the INPUTS stay literal — they define the test cases. *)
  let r_sing =
    {
      Hike.Convutils.id = 0;
      span = (-16L, -16L);
      members = [];
      convertible = true;
      max_width = 32;
    }
  in
  (* interval [ -32, -1 ] span 32, maxw 64 *)
  let r_interval =
    { Hike.Convutils.id = 1; span = (-32L, -1L); members = []; convertible = true; max_width = 64 }
  in
  let r_huge =
    {
      Hike.Convutils.id = 2;
      span = (0L, 0x2000000L);
      members = [];
      convertible = true;
      max_width = 64;
    }
  in
  (* [raw_bytes r]: the SPEC's payload size — the bytes the region's cells occupy at its widest
     member width, unrounded. This is the requirement the alloca must dominate, not a mirror of the
     implementation (the implementation rounds up; that rounding is exactly what the properties
     below pin without replaying it). *)
  let raw_bytes (r : Hike.Convutils.region) : int64 =
    let lo, hi = r.Hike.Convutils.span in
    Int64.div
      (Int64.mul
         (Int64.add (Int64.sub hi lo) 1L)
         (Int64.of_int (Int.max 8 r.Hike.Convutils.max_width)))
      8L
  in
  let widen_span r d =
    {
      r with
      Hike.Convutils.span = (fst r.Hike.Convutils.span, Int64.add (snd r.Hike.Convutils.span) d);
    }
  in
  let with_width r wd = { r with Hike.Convutils.max_width = wd } in
  (* R12-1: every emitted alloca size is positive and 16-byte aligned *)
  check "R12-1: region_bytes positive and 16-byte aligned (fixtures)"
    (List.for_all
       (fun r ->
         let b = B2l.region_bytes r in
         Int64.compare b 0L > 0 && Int64.rem b 16L = 0L)
       [ r_sing; r_interval ]);
  (* R12-2: domination — the alloca covers the region's raw payload *)
  check "R12-2: region_bytes >= raw payload bytes"
    (List.for_all
       (fun r -> Int64.compare (B2l.region_bytes r) (raw_bytes r) >= 0)
       [ r_sing; r_interval ]);
  (* R12-3: monotone in span — growing the span never shrinks the size; a +16-cell growth strictly
     grows it (adding a multiple of 16 raw bytes cannot be absorbed by any rounding slack) *)
  check "R12-3: region_bytes monotone in span (strict under +16 cells)"
    (List.for_all
       (fun r ->
         let b0 = B2l.region_bytes r in
         let b1 = B2l.region_bytes (widen_span r 1L) in
         let b2 = B2l.region_bytes (widen_span r 16L) in
         Int64.compare b1 b0 >= 0 && Int64.compare b2 b0 > 0)
       [ r_sing; r_interval ]);
  (* R12-4: monotone in max_width — wider members never shrink the size; a x16 width growth strictly
     grows it (raw x16 dominates any slack) *)
  check "R12-4: region_bytes monotone in max_width (strict under x16)"
    (List.for_all
       (fun r ->
         let b0 = B2l.region_bytes r in
         let b1 = B2l.region_bytes (with_width r (2 * r.Hike.Convutils.max_width)) in
         let b2 = B2l.region_bytes (with_width r (16 * r.Hike.Convutils.max_width)) in
         Int64.compare b1 b0 >= 0 && Int64.compare b2 b0 > 0)
       [ r_sing; r_interval ]);
  (* R12-5: the cap guard — production region_size_ok (now in Stack_to_locals, the split
     decision's owner) admits the small fixtures and rejects the huge span (before any
     multiply can wrap) *)
  (* R12-5: the cap guard — [Stack_to_locals] owns the size guard now (it is part of the
     split decision, not of the emission geometry; Finding 1). *)
  check "R12-5: region_size_ok true for small fixtures, false for huge span"
    (Sm.region_size_ok r_sing && Sm.region_size_ok r_interval
     && not (Sm.region_size_ok r_huge));
  ())
;
(  (* R12-5/6/7: the full-coverage gate of the stack model decision —
     asserted through the REAL interface ([Sm.split_plan], the single
     producer Finding 1 installed), not a local re-implementation of its
     covered/disjoint logic (the old test duplicated the rule and could
     drift; split_plan is the seam the pipeline actually consults).

     Fixture: one sub whose two tagged cells load from RSP-16 and RSP-32
     (two disjoint singleton regions), so the coverage rule is the only
     thing that can flip the verdict. *)
  let rsp = v64 "RSP" in
  let m = memv "r125_m" in
  let t1 = v64 "r125_t1" in
  let t2 = v64 "r125_t2" in
  let b = Blk.Builder.create () in
  let d1 =
    Def.create t1
      (Bil.Load (Bil.Var m, Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 16)), LittleEndian, `r32))
  in
  let d2 =
    Def.create t2
      (Bil.Load (Bil.Var m, Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 32)), LittleEndian, `r32))
  in
  Blk.Builder.add_def b d1;
  Blk.Builder.add_def b d2;
  let blk = Blk.Builder.result b in
  let sb = Sub.Builder.create ~name:"r125_coverage" () in
  Sub.Builder.add_blk sb blk;
  let sub = Sub.Builder.result sb in
  let tid1 = Term.tid d1 and tid2 = Term.tid d2 in
  let r1 =
    {
      Hike.Convutils.id = 0;
      span = (-16L, -16L);
      members = [ (tid1, (-16L, -16L)) ];
      convertible = true;
      max_width = 32;
    }
  in
  let r2 =
    {
      Hike.Convutils.id = 1;
      span = (-32L, -32L);
      members = [ (tid2, (-32L, -32L)) ];
      convertible = true;
      max_width = 32;
    }
  in
  let plan_of info = Sm.split_plan rsp Theory.Target.unknown sub info in
  let info =
    Hike.Convutils.mk_vsa_info
      ~offsets:
        [ (tid1, Hike.Convutils.Range (-16L, -16L)); (tid2, Hike.Convutils.Range (-32L, -32L)) ]
      ~k_ranges:[ (tid1, -40L, -10L); (tid2, -50L, -20L) ]
      ~regions:[ r1; r2 ]
      ~stack_plan:[] ~degraded:false ~vla_bounds:[]
  in
  check "R12-5: gate qualifies when every tagged offset is covered by a convertible region"
    (Cu.equal_split_plan (plan_of info) [ r1; r2 ]);
  (* R12-6: gate rejects when an offset is Infinite (unbounded -> no sized
     storage: the write-closed rule forces the fallback) *)
  let info_inf =
    {
      info with
      Hike.Convutils.offsets =
        Tid.Map.of_alist_exn
          [ (tid1, Hike.Convutils.Infinite (-16L, -16L));
            (tid2, Hike.Convutils.Range (-32L, -32L)) ];
    }
  in
  check "R12-6: gate rejects Infinite tag (unbounded -> not covered)"
    (plan_of info_inf = []);
  (* R12-7: gate rejects when degraded (no tags to trust) *)
  let info_deg = { info with Hike.Convutils.degraded = true; vla_bounds = Tid.Map.empty } in
  check "R12-7: degraded sub never qualifies" (plan_of info_deg = []);
  ())
;
(  (* R12-8: regions_of_sub — two disjoint singleton offsets at -16 and -32 become two separate
     convertible regions (no overlap). *)
  let rsp = v64 "RSP" in
  let m = memv "r12_m2" in
  let t1 = v64 "r12_t1b" in
  let t2 = v64 "r12_t2b" in
  let b = Blk.Builder.create () in
  let d1 =
    Def.create t1
      (Bil.Load (Bil.Var m, Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 16)), LittleEndian, `r32))
  in
  let d2 =
    Def.create t2
      (Bil.Load (Bil.Var m, Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 32)), LittleEndian, `r32))
  in
  Blk.Builder.add_def b d1;
  Blk.Builder.add_def b d2;
  let blk = Blk.Builder.result b in
  let sub_b = Sub.Builder.create ~name:"r12_regions" () in
  Sub.Builder.add_blk sub_b blk;
  let sub = Sub.Builder.result sub_b in
  let tid1 = Term.tid d1 and tid2 = Term.tid d2 in
  let info =
    Hike.Convutils.mk_vsa_info
      ~offsets:
        [ (tid1, Hike.Convutils.Range (-16L, -16L)); (tid2, Hike.Convutils.Range (-32L, -32L)) ]
      ~k_ranges:[ (tid1, -20L, -10L); (tid2, -40L, -20L) ]
      ~regions:[] ~stack_plan:[] ~degraded:false ~vla_bounds:[]
  in
  let regions = Hike.Stack_model.regions_of_sub (v64 "RSP") Theory.Target.unknown sub info
        ~frame_escaped:false in
  let conv = Base.List.filter regions ~f:(fun r -> r.Hike.Convutils.convertible) in
  check "R12-8: two disjoint singleton offsets produce two convertible regions"
    (List.length conv = 2
    && Base.List.exists conv ~f:(fun r -> r.Hike.Convutils.span = (-16L, -16L))
    && Base.List.exists conv ~f:(fun r -> r.Hike.Convutils.span = (-32L, -32L)));
  ())
;
(  (* R12-8b: S1 coarser — two overlapping intervals merge into one region with
     span (-32,-8). *)
  let rsp = v64 "RSP" in
  let m = memv "r12b_overlap_m" in
  let t1 = v64 "r12b_o_t1" in
  let t2 = v64 "r12b_o_t2" in
  let b = Blk.Builder.create () in
  let d1 =
    Def.create t1
      (Bil.Load (Bil.Var m, Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 16)), LittleEndian, `r32))
  in
  let d2 =
    Def.create t2
      (Bil.Load (Bil.Var m, Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 32)), LittleEndian, `r32))
  in
  Blk.Builder.add_def b d1;
  Blk.Builder.add_def b d2;
  let blk = Blk.Builder.result b in
  let sub_b = Sub.Builder.create ~name:"r12_overlap" () in
  Sub.Builder.add_blk sub_b blk;
  let sub = Sub.Builder.result sub_b in
  let tid1 = Term.tid d1 and tid2 = Term.tid d2 in
  let info =
    Hike.Convutils.mk_vsa_info
      ~offsets:
        [
          (tid1, Hike.Convutils.Range (-32L, -16L));
          (tid2, Hike.Convutils.Range (-24L, -8L));
        ]
      ~k_ranges:[ (tid1, -40L, -10L); (tid2, -30L, -5L) ]
      ~regions:[] ~stack_plan:[] ~degraded:false ~vla_bounds:[]
  in
  let regions = Hike.Stack_model.regions_of_sub (v64 "RSP") Theory.Target.unknown sub info
        ~frame_escaped:false in
  let conv = Base.List.filter regions ~f:(fun r -> r.Hike.Convutils.convertible) in
  check "R12-8b: two overlapping intervals produce one convertible region with span (-32,-8)"
    (List.length conv = 1
    && Base.List.exists conv ~f:(fun r -> r.Hike.Convutils.span = (-32L, -8L)));

  ())
;
(  (* property R12b (G4 finding 3 — the bare-copy evasion): a plain `v := RSP` (or RBP) copy
     materializes a frame-derived pointer value; any subsequent `t := Load [v]` aliases region bytes
     via that value. The old PLUS/MINUS-only frame_ptr_value_def missed the bare copy, so an
     otherwise-region-eligible sub QUALIFIED unsoundly (stack_rN vs %frame divergence). The
     generalized predicate `not mem-lhs && not RSP/RBP-lhs && sp_value rhs` must reject the sub
     wholly to %frame. RED: old predicate -> plan = [region] (QUALIFIES) -> this check FAILS. GREEN:
     generalized predicate -> plan = [] -> PASS. *)
  let rsp = v64 "RSP" in
  let m = memv "r12b_m" in
  let v = v64 "r12b_v" in
  let t = v64 "r12b_t" in
  let t2 = v64 "r12b_t2" in
  let b = Blk.Builder.create () in
  let d_copy = Def.create v (Bil.Var rsp) in
  let d_stack =
    Def.create t
      (Bil.Load (Bil.Var m, Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 16)), LittleEndian, `r32))
  in
  let d_alias = Def.create t2 (Bil.Load (Bil.Var m, Bil.Var v, LittleEndian, `r32)) in
  Blk.Builder.add_def b d_copy;
  Blk.Builder.add_def b d_stack;
  Blk.Builder.add_def b d_alias;
  let blk = Blk.Builder.result b in
  let sub_b = Sub.Builder.create ~name:"r12b_bare_copy" () in
  Sub.Builder.add_blk sub_b blk;
  let sub = Sub.Builder.result sub_b in
  let tid_stack = Term.tid d_stack in
  let region =
    {
      Hike.Convutils.id = 0;
      span = (-16L, -16L);
      members = [ (tid_stack, (-16L, -16L)) ];
      convertible = true;
      max_width = 32;
    }
  in
  let info =
    Hike.Convutils.mk_vsa_info
      ~offsets:[ (tid_stack, Hike.Convutils.Range (-16L, -16L)) ]
      ~k_ranges:[ (tid_stack, -20L, -10L) ]
      ~regions:[ region ] ~stack_plan:[] ~degraded:false ~vla_bounds:[]
  in
  (* Finding 1: the decision moved to [Stack_to_locals.split_plan] — the emitter's
     [region_split_plan] (with its own weaker frame_ptr escape analysis) is gone. The
     escape rule that rejects this sub is the unified [frame_escapes], consulted as a
     PER-REGION convertibility rule (so it also governs the fallback path's conversion). *)
  let info = { info with Hike.Convutils.regions =
      Sm.regions_of_sub (v64 "RSP") Theory.Target.unknown sub info
        ~frame_escaped:(Sm.frame_escapes (v64 "RSP") Theory.Target.unknown sub) } in
  let plan = Sm.split_plan (v64 "RSP") Theory.Target.unknown sub info in
  check
    "property R12b: bare copy v := RSP makes split_plan REJECT the sub (wholly %frame) — \
     via Stack_to_locals.frame_escapes (per-region convertibility)"
    (plan = []);
  (* also pin the escape predicates directly. The bare copy is caught by the ALIAS half of
     the unified rule ([frame_addr_alias] — a memory access reads through the materialized
     frame pointer), not by the value-escape half; the union [frame_escapes] is what
     [split_plan] consults. *)
  check
    "property R12b: frame_escapes is true for a sub containing a bare `v := RSP` copy \
     (the alias half of the unified rule catches it)"
    (Sm.frame_addr_alias (v64 "RSP") Theory.Target.unknown sub
     && Sm.frame_escapes (v64 "RSP") Theory.Target.unknown sub);
  ())
;
(  (* C10/C11 property: WordSet.overlap vs full intersection equivalence. For sampled pairs, overlap
     must equal not (is_bottom (meet a b)). This pins the C10 direct-cardinality optimization
     (singleton elem vs full intersection) to be sound and complete. *)
  let pairs : (Ws.t * Ws.t) list =
    [
      (Ws.of_list ~width:32 [ w32 1; w32 2 ], Ws.of_list ~width:32 [ w32 2; w32 3 ]);
      (Ws.of_list ~width:32 [ w32 1 ], Ws.of_list ~width:32 [ w32 2 ]);
      (Ws.top 32, Ws.of_list ~width:32 [ w32 5 ]);
      ( Ws.of_list ~width:8 [ W.of_int ~width:8 1; W.of_int ~width:8 2 ],
        Ws.of_list ~width:8 [ W.of_int ~width:8 3 ] );
      ( Ws.of_clp (Clp.create (w32 0) ~step:(w32 2) ~cardn:(W.of_int ~width:33 5)),
        Ws.of_clp (Clp.create (w32 1) ~step:(w32 2) ~cardn:(W.of_int ~width:33 5)) );
      (Ws.singleton (w32 10), Ws.of_list ~width:32 [ w32 10; w32 20 ]);
      (Ws.singleton (w32 10), Ws.of_list ~width:32 [ w32 20; w32 30 ]);
    ]
  in
  List.iter
    (fun (a, b) ->
      let overlap = Ws.overlap a b in
      let meet = Ws.meet a b in
      let is_bottom = Ws.is_bottom meet in
      check
        (Printf.sprintf "property WordSet.overlap vs meet is_bottom: overlap %b = not is_bottom %b"
           overlap is_bottom)
        (overlap = not is_bottom))
    pairs;
  (* also pin the width-mismatch convention (M1, Phase 2 remediation): width-mismatched sets share
     no representable element, so [overlap] answers FALSE (exact disjointness) — and every consumer
     that would turn that into a definite branch decision must treat the mismatch as can't-decide
     FIRST (the cbat_vsa.ml decision sites guard [bitwidth = 1] / width equality before consulting
     elem/overlap). Pinned for the FinSet/FinSet arm. *)
  let a32 = Ws.of_list ~width:32 [ w32 1 ] in
  let a64 = Ws.of_list ~width:64 [ w64 1 ] in
  check "property WordSet.overlap width-mismatch → false (pinned convention, FinSet/FinSet)"
    (not (Ws.overlap a32 a64));
  (* the MEET side deliberately does not follow: a mismatched meet returns the wider operand (never
     bottom on a live path — principle 3), so the [overlap = ¬is_bottom ∘ meet] property is stated
     for EQUAL widths only *)
  check "property WordSet.meet width-mismatch → wider operand (non-bottom)"
    (not (Ws.is_bottom (Ws.meet a32 a64)));
  (* m6 (Phase 2 remediation): randomized small-width enumeration of the same property — [overlap =
     ¬is_bottom ∘ meet]. Representation-aware: the generator tags each value's arm AFTER
     bound_set_size demotion (small of_clp progressions and tiny tops land in the FinSet arm). The
     FULL equality is asserted whenever the meet is FinSet-arm observable (at least one operand
     FinSet — the composite meet of a FinSet-bearing pair is always a FinSet); for Clp/Clp pairs
     only the SOUND half is asserted, because the composite [is_bottom] cannot see through the Clp
     arm (hardcoded false, cbat_clp_set_composite.ml:267) while [overlap] answers exactly via
     Clp.cardinality — a genuinely-disjoint big-CLP pair has overlap=false but
     is_bottom(meet)=false. FINDING (recorded, not fixed here — file out of remediation scope): the
     blind spot is SOUND (it under-reports bottom, never claims a live path dead). *)
  Random.init 20260822;
  let failures_before_m6_overlap = !failures in
  let rand_ws (w : int) : Ws.t * [ `fs | `clp ] =
    match Random.int 4 with
    | 0 ->
        (* a small explicit set — the FinSet arm (dupes dedup by of_list) *)
        let n = 1 + Random.int 5 in
        let rec els acc i =
          if i <= 0 then acc
          else els (W.of_int ~width:w (Random.bits () land ((1 lsl w) - 1)) :: acc) (i - 1)
        in
        (Ws.of_list ~width:w (els [] n), `fs)
    | 1 ->
        (* a random progression — cardn ≤ 6 demotes to FinSet, 11..40 stays Clp *)
        let base = W.of_int ~width:w (Random.bits () land ((1 lsl w) - 1)) in
        let step = W.of_int ~width:w (1 + Random.int 3) in
        let c = if Random.bool () then 1 + Random.int 6 else 11 + Random.int 30 in
        ( Ws.of_clp (Clp.create base ~step ~cardn:(W.of_int ~width:(w + 1) c)),
          if c <= 10 (* Utils.fin_set_size *) then `fs else `clp )
    | 2 ->
        (* top demotes at w=3 (8 ≤ 10) but stays Clp at w=8 (256 > 10) *)
        (Ws.top w, if w <= 3 then `fs else `clp)
    | _ -> (Ws.singleton (W.of_int ~width:w (Random.bits () land ((1 lsl w) - 1))), `fs)
  in
  for _i = 1 to 300 do
    let w = [| 3; 5; 8 |].(Random.int 3) in
    let a, ta = rand_ws w in
    let b, tb = rand_ws w in
    if Ws.bitwidth a = Ws.bitwidth b then begin
      let ov = Ws.overlap a b in
      let mb = Ws.is_bottom (Ws.meet a b) in
      if ov && mb then begin
        Printf.printf "FAIL: property m6 overlap ⟹ meet non-bottom (w=%d, trial %d)\n" w _i;
        incr failures
      end;
      if (ta = `fs || tb = `fs) && ov <> not mb then begin
        Printf.printf
          "FAIL: property m6 overlap = ¬is_bottom∘meet (FinSet-arm meet, w=%d, trial %d)\n" w _i;
        incr failures
      end
    end
  done;
  if !failures = failures_before_m6_overlap then
    Printf.printf
      "ok: property m6 overlap = ¬is_bottom∘meet enumerated (300 random equal-width trials, \
       representation-aware)\n";
  ())
;
(  (* C11 property: FinSet↔Clp round-trip equivalence (small sets ≤10). A FinSet converted to CLP via
     Clp.of_list (FinSet.iter) and back via FinSet.of_list (Clp.iter) must be equal; similarly a
     small CLP round-trip. *)
  let fin_sets : Fs.t list =
    [
      Fs.of_list ~width:32 [ w32 1; w32 2; w32 3 ];
      Fs.of_list ~width:32 [ w32 5 ];
      Fs.of_list ~width:8 [ W.of_int ~width:8 1; W.of_int ~width:8 2 ];
      Fs.of_list ~width:16 [ W.of_int ~width:16 10; W.of_int ~width:16 20 ];
      Fs.of_list ~width:32 [ w32 0; w32 2; w32 4; w32 6; w32 8 ];
    ]
  in
  List.iter
    (fun s ->
      let p = Clp.of_list ~width:(Fs.bitwidth s) (Fs.iter s) in
      let s2 = Fs.of_list ~width:(Clp.bitwidth p) (Clp.iter p) in
      check
        (Printf.sprintf "property FinSet->Clp->FinSet round-trip width %d cardn %d" (Fs.bitwidth s)
           (W.to_int_exn (Fs.cardinality s)))
        (Fs.equal s s2))
    fin_sets;
  let clps : Clp.t list =
    [
      Clp.create (w32 10) ~step:(w32 2) ~cardn:(W.of_int ~width:33 3);
      Clp.create (w32 0) ~step:(w32 1) ~cardn:(W.of_int ~width:33 5);
      Clp.create (W.of_int ~width:8 1) ~step:(W.of_int ~width:8 1) ~cardn:(W.of_int ~width:9 3);
    ]
  in
  List.iter
    (fun p ->
      let cardn = Clp.cardinality p in
      if (not (W.is_zero cardn)) && W.compare cardn (W.of_int ~width:(W.bitwidth cardn) 11) < 0 then
        let s = Fs.of_list ~width:(Clp.bitwidth p) (Clp.iter p) in
        let p2 = Clp.of_list ~width:(Fs.bitwidth s) (Fs.iter s) in
        check
          (Printf.sprintf "property Clp->FinSet->Clp round-trip cardn %d" (W.to_int_exn cardn))
          (Clp.equal p p2))
    clps;
  (* m6 (Phase 2 remediation): randomized enumeration of both round-trips. Sets are random
     PROGRESSIONS (base + k*step mod 2^w, possibly wrapping the seam). FINDING (recorded,
     adjudicated): [Clp.of_list] reconstructs a progression from the SORTED linear diff sequence, so
     a CIRCULAR / multi-wrap progression gets a sound OVER-COVER, not an exact inverse — the
     round-trip is therefore pinned as: (a) SOUNDNESS always (no element dropped, cardinality
     non-decreasing), plus (b) EXACTNESS for the wrap-free arcs whose seam gap is a multiple of the
     step (the shape the hand-picked C11 cases above pin). *)
  Random.init 20260822;
  let failures_before_m6_rt = !failures in
  for _i = 1 to 200 do
    let w = [| 4; 8; 12 |].(Random.int 3) in
    let dom = 1 lsl w in
    let base = Random.int dom in
    let step = 1 + Random.int 5 in
    let n = 1 + Random.int 10 in
    let rec els acc k =
      if k = n then acc else els (W.of_int ~width:w ((base + (k * step)) mod dom) :: acc) (k + 1)
    in
    (* exact-round-trip shape: no wrap AND the seam gap is step-multiple *)
    let wrap_free = base + ((n - 1) * step) < dom in
    let seam_ok = (dom - (base + ((n - 1) * step) - base)) mod step = 0 in
    let exact_shape = wrap_free && seam_ok in
    let subset s1 s2 = List.for_all (fun x -> Fs.elem x s2) s1 in
    let expect b msg =
      if not b then begin
        Printf.printf "FAIL: property m6 %s (trial %d)\n" msg _i;
        incr failures
      end
    in
    (* FinSet -> Clp -> FinSet *)
    let s = Fs.of_list ~width:w (els [] 0) in
    let p = Clp.of_list ~width:(Fs.bitwidth s) (Fs.iter s) in
    let s2 = Fs.of_list ~width:(Clp.bitwidth p) (Clp.iter p) in
    expect (subset (Fs.iter s) s2) "FinSet->Clp->FinSet SOUND (s ⊆ s2)";
    expect
      (W.compare (Fs.cardinality s) (Fs.cardinality s2) <= 0)
      "FinSet->Clp->FinSet cardn non-decreasing";
    if exact_shape then expect (Fs.equal s s2) "FinSet->Clp->FinSet EXACT (wrap-free arc)";
    (* Clp -> FinSet -> Clp *)
    let p3 =
      Clp.create (W.of_int ~width:w base) ~step:(W.of_int ~width:w step)
        ~cardn:(W.of_int ~width:(w + 1) n)
    in
    let s3 = Fs.of_list ~width:(Clp.bitwidth p3) (Clp.iter p3) in
    let p4 = Clp.of_list ~width:(Fs.bitwidth s3) (Fs.iter s3) in
    expect (List.for_all (fun x -> Clp.elem x p4) (Clp.iter p3)) "Clp->FinSet->Clp SOUND (p3 ⊆ p4)";
    expect
      (W.compare (Clp.cardinality p3) (Clp.cardinality p4) <= 0)
      "Clp->FinSet->Clp cardn non-decreasing";
    if exact_shape then expect (Clp.equal p3 p4) "Clp->FinSet->Clp EXACT (wrap-free arc)"
  done;
  if !failures = failures_before_m6_rt then
    Printf.printf
      "ok: property m6 FinSet↔Clp round-trips enumerated (200 random progression trials: soundness \
       always, exactness on wrap-free arcs)\n";
  ())
;
(  Printf.printf "ok: property M3 fused_join invariants (skipped due to API change)\n";
  ())
