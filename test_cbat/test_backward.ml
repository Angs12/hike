(* test_backward: the backward-refinement rows — L3a, L3c tiers 1-3, lane shifts, interrupt, coalesce, the jcc decoder, wide-bound, RSP restore, the RBP blocker, and the inverse_denote refactor pins. *)
open Bap.Std
open Bap_core_theory
open Test_common

(* --- 30. L3a (ora-2-approved): backward guard refinement pins -------- The L3a-A machinery
   (src/cbat_vsa/cbat_vsa.ml:419-663) walks BACKWARD through the compared operand's def chain on the
   taken edge of a conditional jump, refining producers and the memory CELL at any Load:
   [refine_backward]/[refine_chain]/[refine_cell]/[refine_row] (PLUS, MINUS, LSHIFT-const rows),
   [defs_of_sub], wired via [assume_jump_cond ?defs] (threaded through denote_jump/denote_block;
   static_graph_vsa computes and passes it, so full fixpoint calls have the walk ON). Sound-stop:
   missing row / doubt / wrap / disjoint / depth cap 6 / non-refineable gate keep the unrefined
   state.

   Fixture shape (the ONLY shape in which the cell refinement is observable in the fixpoint
   SOLUTION): ENTRY ([RSP := RSP] — the prologue def, see below) -> HEADER; HEADER: if (v cmp c)
   goto BODY else EXIT — the COMPARISON is the jump cond (a flag-indirected guard would hit the
   bare-flag arm and never reach the walk); BODY: t := Load [m, RSP-8]; v := <rhs>; jmp HEADER.
   BODY's ONLY predecessor is the HEADER's taken edge, so BODY's solution input state carries the
   backward-refined cell — a join with an unrefined path (e.g. a direct ENTRY->BODY edge) would
   re-absorb the refinement. The load cell is read back the way the vendored load denotation reads
   it (denote_imm_exp of the Load, cbat_vsa.ml:241-248: addr set -> Key -> Mem.find (resSize,
   endian)).

   TAG-ONLY DESIGN (2026-08-10): [denote_def] skips untagged defs unconditionally (the per-def
   [relevant] tag presence IS the restriction — no switch; see the fixture comment). The memory
   starts as AI.top (MemEnv.top — every cell reads top), so the walk's meet narrows the cell from
   top to its constraint window with no seed store, and the top readback is the UNREFINED state (the
   L3a-4/L3a-5 pins).

   NOTE (adaptations): the fixtures use the UNSIGNED LT (and one EQ) guards —
   [constraint_of_compare] (cbat_vsa.ml:395-416) returns None for signed comparisons (SLT/SLE) and
   NEQ by design (doubt -> no walk); L3a-6 pins that doubt path with NEQ. The PLUS pin uses EQ(v,
   5): for a "+1 with LT(v, 10)" chain the row's lo - b_max underflows the width (the true
   constraint {-1} ∪ [0,8] is not a single interval) — the row soundly stops on the wrap, so the pin
   uses the wrap-free instance EQ(v, 5) -> t' = {4}. *)

(* The L3a loop fixture: returns (sub, body tid). The jump cond is the COMPARISON itself (if (v cmp
   c) goto BODY else EXIT) — the backward walk fires on comparison guards; a flag-indirected guard
   (CF := cmp(v, c); if CF goto ...) hits the bare-flag arm and never reaches the walk.

   Tag-only design (2026-08-10): [denote_def] skips untagged defs UNCONDITIONALLY (the per-def
   [relevant] tag presence IS the restriction — no switch), so the fixture adds (a) the -O0 prologue
   def [RSP := RSP] (identity — keeps the RSP anchor value; gives RSP a def so it lands in the
   refineable set, the [refine_cell] addr- gate prerequisite) and (b) [tag_all] (every def tagged ->
   tracked). The memory starts as AI.top (MemEnv.top — every cell reads top), so the walk's meet
   narrows the cell from top to its constraint window with no seed store; the body-input readback
   observes the narrowed cell.

   MIGRATED (ticket 02, the Phase B deletion): the load/chain defs moved
   from the BODY into the HEADER — the -O0-canonical shape (the guard
   reads operands defined in its own block, exactly the L3c1/L3c3
   fixtures' geometry).  The reason is observable-mechanics, not a
   semantic change of the pinned rows: the old L3a geometry pinned the
   rows through Phase B's POST-PASS views (the walk over the CONVERGED
   solution, where the body's defs are always available), while the
   fused engine walks over the CURRENT iterate — on the body's first
   visit the body's snapshot is BOTTOM, the walk dies before reaching
   the producer, and the unrefined edge joins in; the fused fixpoint
   can never observe the row there.  With the defs in the header, the
   walk fires on the FIRST header visit and the body-IN cell carries
   the exact window (probe-verified: BODY-IN cell = {4} for L3a-1).
   The pinned ROWS (PLUS/MINUS/LSHIFT/TIMES/NEQ backward rows) and
   the asserted windows are UNCHANGED — only the block the defs live
   in moved. *)
let mk_l3a_loop ~(cmp : Bil.binop) ~(c : word) ~(rhs : exp) : sub term * tid =
  let m = memv "l3a_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let t = Var.create ~is_virtual:false ~fresh:false "l3a_t" (Type.Imm 32) in
  let v = Var.create ~is_virtual:false ~fresh:false "l3a_v" (Type.Imm 32) in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  let cond = Bil.BinOp (cmp, Bil.Var v, Bil.Int c) in
  let ncond = Bil.UnOp (Bil.NOT, cond) in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  (* the -O0 prologue shape (identity): RSP gets a (tagged) def, so RSP lands in the refineable set
     and the cell gate passes. *)
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
  let sub = tag_all (Sub.Builder.result sub_b) in
  (sub, body_tid)

(* [l3a_cell_of st]: the value of the cell at RBP-8 in [st], read back exactly as the vendored load
   denotation reads it (denote_imm_exp of the load expression). *)
let l3a_cell_of (st : AI.t) : Ws.t =
  let m = memv "l3a_m" in
  let rbp = v64 "RBP" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  match Vsa.denote_imm_exp (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)) st with
  | Ok ws -> ws
  | Error _ -> Ws.top 32

(* [l3a_bounded ws maxv]: [ws] is a finite non-top, non-bottom set bounded above by [maxv] (the
   cell-refinement assertions). *)
let l3a_bounded (ws : Ws.t) (maxv : word) : bool =
  (not (Ws.is_top ws))
  && (not (Ws.is_bottom ws))
  && match Ws.max_elem ws with Some w -> Word.( <= ) w maxv | None -> false

(* [l3a_run_analyzed sub body_tid]: the tagged-sub fixpoint —
   [Relevance.analyze] tags the defs (the per-def [relevant] tag
   presence IS the restriction — [denote_def] skips untagged defs
   unconditionally), the fixture's [RSP := RSP] prologue def puts RSP
   in the refineable set, and the walk's cell meet is observable at
   the BODY input. *)
(* M4 (MIGRATED, ticket 02 — the Phase B deletion): the former iter-view
   re-pointing helper.  The fused fixpoint refines the per-edge states
   INLINE at every jump (docs/trace-partitioning-plan.md §2/§4.3), so the
   ITERATE state of the conditional edge toward [target_tid] IS the
   single-predecessor target's IN-state read directly from the converged
   solution (§10.2: every fixture passing a target here has exactly ONE
   predecessor — the guard block's taken edge — so the IN-state read is
   faithful to the per-edge view the old post-pass computed). *)
let iter_state_of (_sub : sub term) (sol : Vsa.vsa_sol) (target_tid : tid) : AI.t =
  Graphlib.Std.Solution.get sol target_tid

let iter_cell_of (sub : sub term) (sol : Vsa.vsa_sol) (target_tid : tid) (cell_of : AI.t -> Ws.t) :
    Ws.t =
  cell_of (iter_state_of sub sol target_tid)

let l3a_run_analyzed (sub : sub term) (body_tid : tid) : Ws.t =
  let sub' = Relevance.analyze sp sub in
  let prog' = Program.create ~subs:[ sub' ] () in
  let sol = Vsa.static_graph_vsa [] prog' sub' (Vsa.init_sol ~entry:(anchored_entry ()) sub') in
  iter_cell_of sub' sol body_tid l3a_cell_of

(* --- 31. L3c-1 (ora-approved): flag-state mechanism + single-def gate
   ---------------------------------------------------------------------- The -O0 lifted guards are
   FLAG-INDIRECTED: `CF := cmp(v, c); if CF goto …` — the jump cond is the bare flag, so the
   comparison constraint dies with the flag and the L3a walk never fires. L3c-1 adds
   (src/cbat_vsa/cbat_vsa.ml): [flag_state_of_block] — the per-block record (flag, op, e, c) of the
   LAST in-scope 1-bit def whose rhs is an understood comparison (LT/LE/EQ vs constant), with the
   BLP "forgot flag" invalidation (a later def of a free var of [e], or a non-comparison
   redefinition of the flag, clears it) — and the bare-flag arm of [assume_jump_cond] recovers the
   constraint on [e] (operand meet + backward walk), gated on ?defs. Also the L3c-1 SINGLE-DEF GATE:
   [defs_of_sub] flags multi-def bases and the walk stops (sound) through them.

   Fixtures mirror section 30 (same cell readback + observability shape: the loop body's only
   predecessor is the taken edge). For the flag-state pins the comparison is a def in the HEADER and
   the guard is `if CF goto BODY` (the -O0 pattern). *)

(* [mk_l3c1_loop extra_header_defs]: ENTRY ([RSP := RSP] — the prologue def: gives RSP a (tagged)
   def so it lands in the refineable set, the [refine_cell] addr-gate prerequisite) -> HEADER;
   HEADER: t := Load [m, RSP-8]; CF := LT(t, 10); <extra defs>; if CF goto BODY else EXIT; BODY: jmp
   HEADER. Returns (sub, body tid, the flag-gated back-edge jump). The sub is [tag_all]'d (the tag
   presence IS the restriction — [denote_def] skips untagged defs unconditionally). *)
let mk_l3c1_loop ~(extra_header_defs : def term list) : sub term * tid * jmp term =
  let m = memv "l3c1_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let t = Var.create ~is_virtual:false ~fresh:false "l3c1_t" (Type.Imm 32) in
  let cf = v1 "l3c1_cf" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  (* the -O0 prologue shape (identity): RSP gets a (tagged) def, so RSP lands in the refineable set
     and the cell gate passes. *)
  Blk.Builder.add_def entry_b (Def.create rbp (Bil.Var rsp));
  Blk.Builder.add_def header_b (Def.create t (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  Blk.Builder.add_def header_b (Def.create cf (Bil.BinOp (Bil.LT, Bil.Var t, Bil.Int (w32 10))));
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
  let sub = tag_all (Sub.Builder.result sub_b) in
  let jmp =
    match Term.enum jmp_t header |> Seq.to_list with [ j1; _ ] -> j1 | _ -> assert false
  in
  (sub, body_tid, jmp)

(* [l3c1_cell_of m st]: the value of the cell at RBP-8 in [st], read back exactly as the vendored
   load denotation reads it (section-30 idiom, mem-var parameterized). *)
let l3c1_cell_of (m : var) (st : AI.t) : Ws.t =
  let rbp = v64 "RBP" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  match Vsa.denote_imm_exp (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)) st with
  | Ok ws -> ws
  | Error _ -> Ws.top 32

(* [l3c1_bounded ws maxv]: finite non-top, non-bottom, max <= maxv. *)
let l3c1_bounded (ws : Ws.t) (maxv : word) : bool =
  (not (Ws.is_top ws))
  && (not (Ws.is_bottom ws))
  && match Ws.max_elem ws with Some w -> Word.( <= ) w maxv | None -> false

(* --- 32. L3c-2 (ora-approved): signed comparison rows (SLT/SLE) ------ The -O0 loop-bound guards
   are `CF := SLT(v, 10); if CF goto …` (gcc `i < N` with int -> icmp slt) — constraint_of_compare
   only handled the UNSIGNED LT/LE/EQ, so the flag-state record (L3c-1) recovered the constraint and
   the walk still returned None for the actual counter loops. L3c-2 adds the SLT/SLE rows with the
   non-negativity soundness gate (src/cbat_vsa/cbat_vsa.ml): for a NEGATIVE constant (MSB set) the
   true constraint is ONE interval [2^(w-1), w(c)) in unsigned words (no gate); for c >= 0 the true
   constraint is TWO pieces [0,c) ∪ [2^(w-1), 2^w), so the row fires only when the operand's current
   value set is provably non-negative (max_elem < 2^(w-1) — loop counters qualify; [cur] is threaded
   from the call sites). BIL LT/LE ARE the unsigned comparisons — their rows are untouched
   (byte-identical).

   Fixtures: an incrementing/decrementing counter loop whose cell is seeded by a store and mutated
   by the body — the walk's meet on the cell is what caps it, so the pins FAIL without the signed
   rows (the cell grows unboundedly and the fixpoint stops at the step cap). *)

(* [mk_l3c2_loop ~prologue ~seed ~cmp ~c ~body_op ~body_k ~flag]: ENTRY: [m := mem[RSP-8] <- seed];
   [RSP := RSP (the -O0 prologue shape — gives RSP a (tagged) def so it lands in the refineable set,
   the [refine_cell] addr-gate prerequisite)]; jmp HEADER. HEADER: t := Load [m, RSP-8]; [CF := t
   cmp c;] if (t cmp c) [or CF] goto BODY else EXIT. BODY: u := t <body_op> k; m := mem[RSP-8] <- u;
   jmp HEADER. [flag] selects the -O0 flag-indirected guard shape; [prologue] drops the prologue def
   (the L3c2-5 cell-gate pin: RSP then has no def -> not refineable -> the walk stops at the cell).
   The sub is [tag_all]'d (the tag presence IS the restriction). Returns (sub, body tid). *)
let mk_l3c2_loop ~(prologue : bool) ~(seed : word option) ~(cmp : Bil.binop) ~(c : word)
    ~(body_op : Bil.binop) ~(body_k : word) ~(flag : bool) : sub term * tid =
  let m = memv "l3c2_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let t = Var.create ~is_virtual:false ~fresh:false "l3c2_t" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "l3c2_u" (Type.Imm 32) in
  let cf = v1 "l3c2_cf" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  let cond = Bil.BinOp (cmp, Bil.Var t, Bil.Int c) in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  (match seed with
  | Some v ->
      Blk.Builder.add_def entry_b
        (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int v, LittleEndian, `r32)))
  | None -> ());
  if prologue then Blk.Builder.add_def entry_b (Def.create rbp (Bil.Var rsp));
  Blk.Builder.add_def header_b (Def.create t (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  if flag then Blk.Builder.add_def header_b (Def.create cf (Bil.BinOp (cmp, Bil.Var t, Bil.Int c)));
  Blk.Builder.add_def body_b (Def.create u (Bil.BinOp (body_op, Bil.Var t, Bil.Int body_k)));
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
  let sub = tag_all (Sub.Builder.result sub_b) in
  (sub, body_tid)

(* [l3c2_cell_of st]: the value of the cell at RBP-8 in [st] (the section-31 readback idiom, this
   section's mem var). *)
let l3c2_cell_of (st : AI.t) : Ws.t =
  let m = memv "l3c2_m" in
  let rbp = v64 "RBP" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  match Vsa.denote_imm_exp (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)) st with
  | Ok ws -> ws
  | Error _ -> Ws.top 32

(* [l3c2_bounded ws maxv]: finite, non-top, non-bottom, max <= maxv. *)
let l3c2_bounded (ws : Ws.t) (maxv : word) : bool =
  (not (Ws.is_top ws))
  && (not (Ws.is_bottom ws))
  && match Ws.max_elem ws with Some w -> Word.( <= ) w maxv | None -> false

(* [l3c2_in_high ws lo hi]: finite, non-top, non-bottom, all values in [lo, hi] (the c < 0
   single-piece constraint). *)
let l3c2_in_high (ws : Ws.t) (lo : word) (hi : word) : bool =
  (not (Ws.is_top ws))
  && (not (Ws.is_bottom ws))
  &&
  match (Ws.min_elem ws, Ws.max_elem ws) with
  | Some mn, Some mx -> Word.( >= ) mn lo && Word.( <= ) mx hi
  | _ -> false

(* --- 33. L3c-3 (ora-approved Tier-1 rows 3-5): PLUS-hull, TIMES-const, RSHIFT/ARSHIFT-const
   ------------------------------------------------- The remaining Tier-1 backward rows for the
   arithmetic chains between load and compare (src/cbat_vsa/cbat_vsa.ml refine_row): - PLUS-HULL:
   the canonical `v := t + 1; if v < N` chain — the PLUS row's bounds wrap (lo - b_max underflows
   0); instead of the sound stop the row now returns the WRAPPED HULL as a CIRCULAR CLP (hull ⊇ the
   true {−1} ∪ [0, N−1) — the CLP domain represents circular intervals natively; a full-domain hull
   is a no-op None). - TIMES-const: v = a * k, k a literal: a' = [ceil(lo/k), floor(hi/k)] gated on
   the operand's range being unable to wrap (a wrapped solution a*k mod 2^w ∈ [lo,hi] would sit
   outside the linear interval); the EQ-singleton case falls out (non-divisible -> empty -> None); k
   = 0 and negative k -> None. - RSHIFT/ARSHIFT-const: v = a >> k / a arshift k: a' = [lo<<k,
   (hi+1)<<k − 1] (the INVERSE of the def-side LSHIFT row), sound only when (hi+1)*2^k <= 2^w;
   ARSHIFT additionally gated on the operand provably non-negative. Fixtures mirror section 32
   (mk_l3c3_loop: seed store, the chain def v := <chain> in the HEADER between the load and the
   direct guard, incrementing body with body_k = 4 so the meet-capped fixed point stabilizes before
   the i>10 widening). *)

(* [mk_l3c3_loop ~seed ~chain ~cmp ~c ~body_k]: ENTRY: [seed store]; jmp HEADER. HEADER: t := Load
   [m, RSP-8]; v := <chain>; if (v cmp c) goto BODY else EXIT. BODY: u := t + <body_k>; m :=
   mem[RSP-8] <- u; jmp HEADER. Returns (sub, body tid). *)
let mk_l3c3_loop ~(seed : word option) ~(chain : exp) ~(cmp : Bil.binop) ~(c : word)
    ~(body_k : word) : sub term * tid =
  let m = memv "l3c3_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let t = Var.create ~is_virtual:false ~fresh:false "l3c3_t" (Type.Imm 32) in
  let v = Var.create ~is_virtual:false ~fresh:false "l3c3_v" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "l3c3_u" (Type.Imm 32) in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  let cond = Bil.BinOp (cmp, Bil.Var v, Bil.Int c) in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  (match seed with
  | Some sv ->
      Blk.Builder.add_def entry_b
        (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int sv, LittleEndian, `r32)))
  | None -> ());
  (* the -O0 prologue shape (identity): RSP gets a (tagged) def, so RSP lands in the refineable set
     and the cell gate passes. *)
  Blk.Builder.add_def entry_b (Def.create rbp (Bil.Var rsp));
  Blk.Builder.add_def header_b (Def.create t (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  Blk.Builder.add_def header_b (Def.create v chain);
  Blk.Builder.add_def body_b (Def.create u (Bil.BinOp (Bil.PLUS, Bil.Var t, Bil.Int body_k)));
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
  let sub = tag_all (Sub.Builder.result sub_b) in
  (sub, body_tid)

(* [l3c3_cell_of st]: the value of the cell at RBP-8 in [st] (this section's mem var). *)
let l3c3_cell_of (st : AI.t) : Ws.t =
  let m = memv "l3c3_m" in
  let rbp = v64 "RBP" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  match Vsa.denote_imm_exp (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)) st with
  | Ok ws -> ws
  | Error _ -> Ws.top 32

(* [l3c3_run sub body_tid]: the plain fixpoint returning the BODY input state's cell at RBP-8. *)
let l3c3_run (sub : sub term) (body_tid : tid) : Ws.t =
  let ctx = Program.create ~subs:[ sub ] () in
  let sol = Vsa.static_graph_vsa [] ctx sub (Vsa.init_sol ~entry:(anchored_entry ()) sub) in
  iter_cell_of sub sol body_tid l3c3_cell_of

(* --- 34. L3c-4 (ora-approved Tier-2): Var-vs-Var interval-overlap, DIVIDE-const, HIGH-extract
   producer ---------------------------------- The last closed-form backward rows
   (src/cbat_vsa/cbat_vsa.ml): - Var-vs-Var guard arm in assume_jump_cond (`i < len`-style chains):
   LT/LE tighten both sides from the other's bounds (x' = x ∩ [0, mx−1]; y' = y ∩ [mn+1, 2^w−1]
   etc.); EQ meets the overlap; SLT/SLE use the signed min/max with the sound single- interval cases
   only (a signed-negative mx gives the high half [2^(w-1), mx−1]; a signed-non-negative mx requires
   x provably non-negative; the y-side requires mn_signed >= 0). A FULL-RANGE operand makes the
   refinement vacuous — the `_start` argc class (counter vs unknown bound) is SEMANTIC-TOP,
   unfixable by any guard row. - DIVIDE-const row (refine_row): v = a / k -> a' = [lo*k, (hi+1)*k −
   1] with the (hi+1)*k <= 2^w soundness guard. - HIGH-extract producer (refine_backward's Cast case
   + refine_cast_high): v := cast HIGH a -> a' = [lo << (w−N), (hi+1) << (w−N) − 1] (only the HIGH
   cast has a row; the mask guard (hi+1) <= 2^N). Fixtures mirror section 33 (mk_l3c4_loop with the
   chain def and a parameterized compared-var width; mk_l3c4_vv_loop for the two-load Var-vs-Var
   shape). *)

(* [mk_l3c4_loop ~seed ~chain ~v_w ~cmp ~c ~body_k]: ENTRY: [seed store]; jmp HEADER. HEADER: t :=
   Load [m, RSP-8]; v := <chain> (v's width v_w); if (v cmp c) goto BODY else EXIT. BODY: u := t +
   <body_k>; m := mem[RSP-8] <- u; jmp HEADER. Returns (sub, body tid). *)
let mk_l3c4_loop ~(seed : word option) ~(chain : exp) ~(v_w : int) ~(cmp : Bil.binop) ~(c : word)
    ~(body_k : word) : sub term * tid =
  let m = memv "l3c4_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let t = Var.create ~is_virtual:false ~fresh:false "l3c4_t" (Type.Imm 32) in
  let v = Var.create ~is_virtual:false ~fresh:false "l3c4_v" (Type.Imm v_w) in
  let u = Var.create ~is_virtual:false ~fresh:false "l3c4_u" (Type.Imm 32) in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  let cond = Bil.BinOp (cmp, Bil.Var v, Bil.Int c) in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  (match seed with
  | Some sv ->
      Blk.Builder.add_def entry_b
        (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int sv, LittleEndian, `r32)))
  | None -> ());
  (* the -O0 prologue shape (identity): RSP gets a (tagged) def, so RSP lands in the refineable set
     and the cell gate passes. *)
  Blk.Builder.add_def entry_b (Def.create rbp (Bil.Var rsp));
  Blk.Builder.add_def header_b (Def.create t (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  Blk.Builder.add_def header_b (Def.create v chain);
  Blk.Builder.add_def body_b (Def.create u (Bil.BinOp (Bil.PLUS, Bil.Var t, Bil.Int body_k)));
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
  let sub = tag_all (Sub.Builder.result sub_b) in
  (sub, body_tid)

(* [mk_l3c4_vv_loop ~seed ~seed2 ~cmp ~body_k]: the two-load Var-vs-Var shape: ENTRY: [seed store @
   RSP-8]; [seed2 store @ RSP-16]; jmp HEADER. HEADER: t := Load [RSP-8]; u := Load [RSP-16]; if (t
   cmp u) goto BODY else EXIT. BODY: w := t + <body_k>; mem[RSP-8] <- w; jmp HEADER. Returns (sub,
   body tid). *)
let mk_l3c4_vv_loop ~(seed : word option) ~(seed2 : word option) ~(cmp : Bil.binop) ~(body_k : word)
    : sub term * tid =
  let m = memv "l3c4_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let t = Var.create ~is_virtual:false ~fresh:false "l3c4_t" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "l3c4_u" (Type.Imm 32) in
  let w = Var.create ~is_virtual:false ~fresh:false "l3c4_w" (Type.Imm 32) in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  let addr2 = Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 16)) in
  let cond = Bil.BinOp (cmp, Bil.Var t, Bil.Var u) in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  (match seed with
  | Some sv ->
      Blk.Builder.add_def entry_b
        (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int sv, LittleEndian, `r32)))
  | None -> ());
  (match seed2 with
  | Some sv ->
      Blk.Builder.add_def entry_b
        (Def.create m (Bil.Store (Bil.Var m, addr2, Bil.Int sv, LittleEndian, `r32)))
  | None -> ());
  (* the -O0 prologue shape (identity): RSP gets a (tagged) def, so RSP lands in the refineable set
     and the cell gate passes. *)
  Blk.Builder.add_def entry_b (Def.create rbp (Bil.Var rsp));
  Blk.Builder.add_def header_b (Def.create t (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  Blk.Builder.add_def header_b (Def.create u (Bil.Load (Bil.Var m, addr2, LittleEndian, `r32)));
  Blk.Builder.add_def body_b (Def.create w (Bil.BinOp (Bil.PLUS, Bil.Var t, Bil.Int body_k)));
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
  let sub = tag_all (Sub.Builder.result sub_b) in
  (sub, body_tid)

(* [l3c4_cell_of st]: the value of the cell at RBP-8 in [st] (this section's mem var). *)
let l3c4_cell_of (st : AI.t) : Ws.t =
  let m = memv "l3c4_m" in
  let rbp = v64 "RBP" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  match Vsa.denote_imm_exp (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)) st with
  | Ok ws -> ws
  | Error _ -> Ws.top 32

(* [l3c4_run sub body_tid]: the plain fixpoint returning the BODY input state's cell at RBP-8. *)
let l3c4_run (sub : sub term) (body_tid : tid) : Ws.t =
  let ctx = Program.create ~subs:[ sub ] () in
  let sol = Vsa.static_graph_vsa [] ctx sub (Vsa.init_sol ~entry:(anchored_entry ()) sub) in
  iter_cell_of sub sol body_tid l3c4_cell_of

(* --- 35. L3c-5 (ora-approved Tier-3 + directive 2): the structural closure — explicit None-rows,
   identity rows, the const-first guard arm, the shrunk catch-all
   ------------------------------------------- Every remaining BIL operator gets an explicit row (an
   exact identity where cheap, otherwise a documented None-returning sound stop with the "no
   closed-form on CLPs" comment + the ASE'21 inverse-semantics reference); the CONST-FIRST guard arm
   (`10 = i` lift shapes) normalizes EQ to the const-second form; and the final `_ -> env` catch-all
   is shrunk to the genuinely-unhandled non-binop condition shapes (Bil.Unknown, Ite-as-condition,
   exotic exps) — keep env, never assert (the D1/D6b totality history: an assert crashes the
   analysis on legal input). NOTE: the BIL binop set has NO GT/GE/SGT/SGE constructors
   (bap_bil.ml:22-42), so the only const-first comparisons are the commutative EQ/NEQ. *)

(* [mk_l3c5_loop ~seed ~chain ~cond ~body_k]: ENTRY: [seed store]; jmp HEADER. HEADER: t := Load [m,
   RSP-8]; [v := <chain>]; if (<cond>) goto BODY else EXIT. BODY: u := t + <body_k>; m := mem[RSP-8]
   <- u; jmp HEADER. Returns (sub, body tid). *)
let mk_l3c5_loop ~(seed : word option) ~(chain : exp option) ~(cond : exp) ~(body_k : word) :
    sub term * tid =
  let m = memv "l3c5_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let t = Var.create ~is_virtual:false ~fresh:false "l3c5_t" (Type.Imm 32) in
  let v = Var.create ~is_virtual:false ~fresh:false "l3c5_v" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "l3c5_u" (Type.Imm 32) in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  (match seed with
  | Some sv ->
      Blk.Builder.add_def entry_b
        (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int sv, LittleEndian, `r32)))
  | None -> ());
  (* the -O0 prologue shape (identity): RSP gets a (tagged) def, so RSP lands in the refineable set
     and the cell gate passes. *)
  Blk.Builder.add_def entry_b (Def.create rbp (Bil.Var rsp));
  Blk.Builder.add_def header_b (Def.create t (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  (match chain with Some ch -> Blk.Builder.add_def header_b (Def.create v ch) | None -> ());
  Blk.Builder.add_def body_b (Def.create u (Bil.BinOp (Bil.PLUS, Bil.Var t, Bil.Int body_k)));
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
  let sub = tag_all (Sub.Builder.result sub_b) in
  (sub, body_tid)

(* [l3c5_cell_of st]: the value of the cell at RBP-8 in [st] (this section's mem var). *)
let l3c5_cell_of (st : AI.t) : Ws.t =
  let m = memv "l3c5_m" in
  let rbp = v64 "RBP" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  match Vsa.denote_imm_exp (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)) st with
  | Ok ws -> ws
  | Error _ -> Ws.top 32

(* [l3c5_run sub body_tid]: the plain fixpoint returning the BODY input state's cell at RBP-8. *)
let l3c5_run (sub : sub term) (body_tid : tid) : Ws.t =
  let ctx = Program.create ~subs:[ sub ] () in
  let sol = Vsa.static_graph_vsa [] ctx sub (Vsa.init_sol ~entry:(anchored_entry ()) sub) in
  iter_cell_of sub sol body_tid l3c5_cell_of

(* --- 37. Lane B (ora-2): the interrupt denotation --------------------- The interrupt arm
   (cbat_vsa.ml denote_jump's `Int _` case) returned [not_implemented ~top:AI.top "interrupt
   denotation"] — the interrupt edge's state (joined into the block's outgoing state) was AI.top,
   destroying the RSP anchor AND everything else on the continuation. The replacement abstracts the
   interrupt as an unknown EXTERNAL callee via [AI.call_abstraction ~preserved] (caller-saved
   destroyed, callee-saved preserved, memory topped) — sound and strictly more precise (the RSP
   anchor survives). The fixture: ENTRY -> BLK; BLK: rdi := 42; [intr jmp] + [jmp CONT]; CONT:
   empty. The two per-jmp states join into CONT: the interrupt edge's abstraction (rdi topped, RSP =
   {0} preserved) JOIN the Goto edge (env). *)
(* --- 38. L-3b (ora-3): the coalesce equal-lower merge arm — the restored-fix pins (S-1..S-4)
   ------------------------------------------ L-3a restored the equal-lower merge arm of [coalesce]
   (src/cbat_vsa/cbat_ai_memmap.ml:635-672): inline top-drop -> EQUAL- LOWER hull union with
   Val.join_poly -> +1-adjacent equal-value hull union -> flush. The arm is LIVE because IT.add at
   an equal lower KEEPS the old binding (bap_interval_tree.ml:128-135: bal map key data None — the
   new binding becomes the ROOT, the OLD tree its left child; Key. compare is lower-only), so
   equal-lower duplicates ACCUMULATE in the tree (the measured soup: point-key piles 16-17 deep on
   the traverse shape, ~200-300 per frame-slot point key on fizzBuzz) and find' folds them ALL
   (cbat_ai_memmap.ml:519-535) — merging them is read-equivalent (identical hulls: the merged read =
   the fold's join exactly; different uppers: a sound over-approximation at the difference region).
   S-1 (fixture F — the seeded RMW counter, the traverse shape): the 16-17 pile collapses to 1 and
   the surviving cell carries the joined value (⊇ {0..8}, not top, not {0}). S-2 (revert-proof,
   out-of-band): neutralizing the equal-lower arm makes S-1a fail with the 16-17 count; restoring
   makes it green. S-3: D4-9 (section 12b) stays green UNMODIFIED — the byte-identity guard; no new
   check here (it runs as-is above). S-4 (NEW): pins the +1-adjacent arm so the equal-lower arm does
   NOT shadow it — two +1-adjacent equal-value cells ([RSP-8] and [RSP-7], both {7}) through one
   merge -> the single union hull [RSP-8, RSP-7]; fails without the +1 arm (the two cells stay
   separate). *)

(* [mk_l3b1_loop]: the S-1 fixture F — the TRAVERSE SHAPE, a memory- carried counter with an RMW
   store, seeded in the entry, guard on the loaded value: ENTRY: m := mem[RSP-8] <- 0; jmp HEADER.
   HEADER: t := Load [m, RSP-8]; if (t < 8) goto BODY else EXIT. BODY: u := t + 1; m := mem[RSP-8]
   <- u; jmp HEADER. Returns (sub, body tid, header tid). *)
let mk_l3b1_loop () : sub term * tid * tid =
  let m = memv "l3b1_m" in
  let rsp = v64 "RSP" in
  let t = Var.create ~is_virtual:false ~fresh:false "l3b1_t" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "l3b1_u" (Type.Imm 32) in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 8)) in
  let cond = Bil.BinOp (Bil.LT, Bil.Var t, Bil.Int (w32 8)) in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b
    (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int (w32 0), LittleEndian, `r32)));
  Blk.Builder.add_def header_b (Def.create t (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  Blk.Builder.add_def body_b (Def.create u (Bil.BinOp (Bil.PLUS, Bil.Var t, Bil.Int (w32 1))));
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
  let sub = tag_all (Sub.Builder.result sub_b) in
  (sub, body_tid, header_tid)

(* [mk_l3b4_diamond]: the S-4 fixture — two +1-adjacent equal-value stores of {7} at [RSP-8] and
   [RSP-7] (0x…F8 / 0x…F9, succ-adjacent point keys), repeated identically in TWO branches that join
   at a merge block. The merge input is exactly ONE [join'] whose coalesce sees the +1-adjacent
   equal-value pair ([RSP-8] then [RSP-7], both {7}) and unions them into the single hull [RSP-8,
   RSP-7]. Shape rationale: (1) both join sides must carry the SAME aligned cells — join' folds the
   single-sided segments to top and the coalesce's inline top-drop loses them, so a join of
   disjoint-keyed memories can never fire the +1 arm; (2) no back-edge — a loop's next join
   re-splits the hull into point stores and the top-drop eats it (the find' alignment gate,
   cbat_ai_memmap.ml:528-534: a query whose start is not cell-start-aligned reads top); (3) the
   entry guard must be UNRESOLVABLE — a provably-true guard prunes the false branch
   (reachable_jumps, cbat_vsa.ml:373-380), and two plain unconditional Gotos from the entry do not
   both reach their targets through the fixpoint (B stayed bottom) — an unconstrained flag (i = top
   -> the LT evaluates {0,1}) keeps both edges live. ENTRY: if (i < 1) goto A else goto B (i
   unconstrained = top -> both edges live). A: m := mem[RSP-8] <- 7; m := mem[RSP-7] <- 7; jmp
   MERGE. B: same; jmp MERGE. MERGE: empty. Returns (sub, merge tid). *)
let mk_l3b4_diamond () : sub term * tid =
  let m = memv "l3b4_m" in
  let rsp = v64 "RSP" in
  let i = Var.create ~is_virtual:false ~fresh:false "l3b4_i" (Type.Imm 32) in
  let addr8 = Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 8)) in
  let addr7 = Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 7)) in
  let cond = Bil.BinOp (Bil.LT, Bil.Var i, Bil.Int (w32 1)) in
  let entry_b = Blk.Builder.create () in
  let a_b = Blk.Builder.create () in
  let b_b = Blk.Builder.create () in
  let merge_b = Blk.Builder.create () in
  Blk.Builder.add_def a_b
    (Def.create m (Bil.Store (Bil.Var m, addr8, Bil.Int (w32 7), LittleEndian, `r32)));
  Blk.Builder.add_def a_b
    (Def.create m (Bil.Store (Bil.Var m, addr7, Bil.Int (w32 7), LittleEndian, `r32)));
  Blk.Builder.add_def b_b
    (Def.create m (Bil.Store (Bil.Var m, addr8, Bil.Int (w32 7), LittleEndian, `r32)));
  Blk.Builder.add_def b_b
    (Def.create m (Bil.Store (Bil.Var m, addr7, Bil.Int (w32 7), LittleEndian, `r32)));
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
  let sub = tag_all (Sub.Builder.result sub_b) in
  (sub, merge_tid)

(* [l3b_cells_of mv st]: the number of cells (AVL nodes, duplicates included) in [st]'s memory for
   [mv] — the sexp-marker accessor: Mem.sexp_of_t prints one "(height " marker per node (the L-2
   probe idiom, zz_scratch_probe/probe.ml:26-35). *)
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

(* [l3b1_cell_of st]: the cell at RBP-8 in [st] (this section's mem var, the section-31 readback
   idiom). *)
let l3b1_cell_of (st : AI.t) : Ws.t =
  let m = memv "l3b1_m" in
  let rsp = v64 "RSP" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 8)) in
  match Vsa.denote_imm_exp (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)) st with
  | Ok ws -> ws
  | Error _ -> Ws.top 32

(* --- 39. L-B (ora-6): the jcc-decoder pins — the exact -O0 corpus block fixture
   ----------------------------------------------------------- The L-A1/L-A2 decoder
   (src/cbat_vsa/cbat_vsa.ml) recognizes the compound -O0 loop guards (jle = `ZF | (SF|OF) &
   ~(SF&OF)`, jl = `(SF|OF) & ~(SF&OF)`, ja = `~(CF | ZF)`) and recovers the loop-counter constraint
   from the flag-state record (CF, LT, e, c) + the same-comparison group gate. These pins build the
   EXACT corpus block (the oracle's Q4 fixture, ora-6 Q2): the canonical per-cmp emission `#t := e -
   c; CF := e < c; OF := high:1[(e ^ c) & (e ^ #t)]; SF := high:1[#t]; ZF := 0 = #t` with e = the
   Load expression itself, the seeded RSP-8 store (the L-3b fixture-F seed pattern), and the RMW
   body — so the decoder's Load-case walk reaches the memory cell directly. The flag defs use the
   file's BIL constructors (Bil.Load/Bil.Store, Bil.BinOp with the actual binop names —
   Bil.MINUS/PLUS, Bil.XOR/AND/OR — Bil.Cast (Bil.HIGH, 1, …) for the high:1[...] casts per the
   L3c4-4 idiom, and `Bil.BinOp (Bil.EQ, Bil.Int 0, …)` for the const-first `0 = #t`); the t := e -
   c def is a FULL-WIDTH (32-bit) temp, not a 1-bit flag (the flag_group `cmp` field adaptation).
   Flag vars are named exactly CF/OF/SF/ZF — the decoder matches on Var.name. Cell readback = the
   section-31 idiom (denote_imm_exp of the RSP-8 load on the solution state; BODY input carries the
   refined taken-edge state). *)

(* [l39_jle zf sf ofv]: `ZF | (SF|OF) & ~(SF&OF)` — the jle guard (signed e <= c; includes
   equality). [l39_jl sf ofv]: the XOR core alone — the jl guard (signed e < c). [l39_ja cf zf]:
   `~(CF | ZF)` — the ja guard (unsigned e > c). The exact BIR-verified nestings the decoder matcher
   accepts (cbat_vsa.ml:435-465). *)
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

(* [mk_l39_loop ~seed ~c ~body_op ~body_k ~mk_cond ~extra_header_defs]: the EXACT corpus block
   fixture (ora-6 Q2/Q4): ENTRY: m := mem[RSP-8] <- seed; jmp HEADER. HEADER: t := Load[RSP-8] - c;
   CF := Load[RSP-8] < c; OF := high:1[(Load ^ c) & (Load ^ t)]; SF := high:1[t]; ZF := 0 = t;
   <extra defs>; when <mk_cond ~cf ~ofv ~sf ~zf> goto BODY else EXIT. BODY: u := Load[RSP-8]; m :=
   mem[RSP-8] <- (u <body_op> <body_k>); jmp HEADER. [mk_cond] receives the fixture's OWN flag vars
   (the gate needs the cond's flag vars to BE the defs' lhs); the extra defs receive the fixture's
   mem var (the L-B4 second-cmp group). Returns (sub, body tid). *)
let mk_l39_loop ~(seed : word) ~(c : word) ~(body_op : Bil.binop) ~(body_k : word)
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
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  let load_e = Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32) in
  let cond = mk_cond ~cf ~ofv ~sf ~zf in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b
    (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int seed, LittleEndian, `r32)));
  (* the -O0 prologue shape (identity): RSP gets a (tagged) def, so RSP lands in the refineable set
     and the cell gate passes. *)
  Blk.Builder.add_def entry_b (Def.create rbp (Bil.Var rsp));
  (* the canonical -O0 cmp emission, fixed order: the full-width subtraction temp first, then CF,
     OF, SF, ZF (ora-6 Q2) *)
  Blk.Builder.add_def header_b (Def.create t (Bil.BinOp (Bil.MINUS, load_e, Bil.Int c)));
  Blk.Builder.add_def header_b (Def.create cf (Bil.BinOp (Bil.LT, load_e, Bil.Int c)));
  Blk.Builder.add_def header_b
    (Def.create ofv
       (Bil.Cast
          ( Bil.HIGH,
            1,
            Bil.BinOp
              ( Bil.AND,
                Bil.BinOp (Bil.XOR, load_e, Bil.Int c),
                Bil.BinOp (Bil.XOR, load_e, Bil.Var t) ) )));
  Blk.Builder.add_def header_b (Def.create sf (Bil.Cast (Bil.HIGH, 1, Bil.Var t)));
  Blk.Builder.add_def header_b
    (Def.create zf (Bil.BinOp (Bil.EQ, Bil.Int (Word.zero (Word.bitwidth c)), Bil.Var t)));
  List.iter (Blk.Builder.add_def header_b) (extra_header_defs m);
  Blk.Builder.add_def body_b (Def.create u (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  Blk.Builder.add_def body_b
    (Def.create m
       (Bil.Store
          (Bil.Var m, addr_e, Bil.BinOp (body_op, Bil.Var u, Bil.Int body_k), LittleEndian, `r32)));
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
  let sub = tag_all (Sub.Builder.result sub_b) in
  (sub, body_tid)

(* [mk_l39b5_loop]: the L-B5 fixture — the RECORD path (the bare-flag guard; minimal per the
   oracle): ENTRY: m := mem[RBP-8] <- 0; jmp HEADER. HEADER: v := Load[m, RBP-8]; CF := v < 3; when
   CF goto BODY else EXIT. BODY: u := Load[m, RBP-8]; m := mem[RBP-8] <- (u + 1); jmp HEADER. v's
   def is UNIQUE (the single-def gate passes), so the L3c-1 flag-state arm's walk goes through v :=
   Load to the cell. Returns (sub, body tid). *)
let mk_l39b5_loop () : sub term * tid =
  let m = memv "l39_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let v = Var.create ~is_virtual:false ~fresh:false "l39b5_v" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "l39b5_u" (Type.Imm 32) in
  let cf = v1 "CF" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b
    (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int (w32 0), LittleEndian, `r32)));
  (* the -O0 prologue shape (identity): RSP gets a (tagged) def, so RSP lands in the refineable set
     and the cell gate passes. *)
  Blk.Builder.add_def entry_b (Def.create rbp (Bil.Var rsp));
  Blk.Builder.add_def header_b (Def.create v (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  Blk.Builder.add_def header_b (Def.create cf (Bil.BinOp (Bil.LT, Bil.Var v, Bil.Int (w32 3))));
  Blk.Builder.add_def body_b (Def.create u (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  Blk.Builder.add_def body_b
    (Def.create m
       (Bil.Store
          (Bil.Var m, addr_e, Bil.BinOp (Bil.PLUS, Bil.Var u, Bil.Int (w32 1)), LittleEndian, `r32)));
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
  let sub = tag_all (Sub.Builder.result sub_b) in
  (sub, body_tid)

(* [l39_cell_of st]: the value of the cell at RBP-8 in [st] (the section-31 readback idiom, this
   section's mem var). *)
let l39_cell_of (st : AI.t) : Ws.t =
  let m = memv "l39_m" in
  let rbp = v64 "RBP" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  match Vsa.denote_imm_exp (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)) st with
  | Ok ws -> ws
  | Error _ -> Ws.top 32

(* [l39_run sub body_tid]: the plain fixpoint returning the BODY input state's cell at RBP-8 (BODY's
   only predecessor is the header's taken edge, so its input state carries the taken-edge
   refinement). *)
let l39_run (sub : sub term) (body_tid : tid) : Ws.t =
  let ctx = Program.create ~subs:[ sub ] () in
  let sol = Vsa.static_graph_vsa [] ctx sub (Vsa.init_sol ~entry:(anchored_entry ()) sub) in
  iter_cell_of sub sol body_tid l39_cell_of

(* [l39_bounded ws maxv]: finite, non-top, non-bottom, max <= maxv. *)
let l39_bounded (ws : Ws.t) (maxv : word) : bool =
  (not (Ws.is_top ws))
  && (not (Ws.is_bottom ws))
  && match Ws.max_elem ws with Some w -> Word.( <= ) w maxv | None -> false

(* --- 41. L-E1 (ora-9 Item 2): the ON-path matched-pair RSP restoration
   ---------------------------------------------------------- The ON-path call abstraction
   ([inspect_call], restriction ON) preserves RSP at the POST-PUSH value — the caller models the
   push as defs (RSP := RSP − 8; mem[RSP] := retaddr; call) and the callee's ret, the pop (t :=
   mem[RSP]; RSP := RSP + 8; the noreturn call IS the Ret), is NEVER modeled when the callee is
   abstracted — so the continuation RSP is truth − 8 after every call. In a straight line this is a
   benign constant shift; in a CALL-CONTAINING LOOP the header RSP joins {−8k} per iteration and the
   i>10 widening turns it into an infinite DESCENDING CLP (wide RSP/RSP-relative windows + a fresh
   retaddr cell per iteration). The L-E1 fix (cbat_vsa.ml inspect_call, ON-path only): after
   [AI.call_abstraction], restore RSP := RSP + 8 on the return edge — the matched-pair restoration
   (the callee's ret pops exactly the retaddr the caller pushed). Under L-E1b the +8 is CONDITIONAL
   on the call block writing RSP (the FP-intrinsic calls — BIR Calls with no stack push — must NOT
   get it, or RSP drifts +8 per intrinsic call); a push-modeled call always writes RSP, so these
   fixtures take the restoring arm and the continuation gets the TRUE pre-call RSP. Pins: - E1-1:
   the call-in-loop class — the header RSP stays EXACTLY at the pre-push {0x1000} (bounded, no
   drift). FAILS pre-L-E1 (the header joins {−8k}/iteration and the widening makes the infinite
   descending CLP — min_elem 0 / max_elem 2^64−8, the wbig signature). - E1-2: the straight-line
   call — the continuation RSP is EXACTLY the pre-call singleton {0x2000} (truth, not truth − 8 =
   {0x1ff8}). FAILS pre-L-E1. Both run the ON-path fixpoint (the restriction armed via
   [Relevance.analyze]; the call has an INDIRECT target, so the abstraction fires without a callee
   sub — [static_graph_vsa] on the single tagged sub). Revert-proof: removing the +8 (a temporary
   src edit) fails both pins. *)

(* [mk_e1_loop_sub]: the call-in-loop fixture (the ora-9 class): ENTRY: rsp := 0x1000; jmp HEADER.
   HEADER: jmp BODY. BODY: rsp := RSP − 8 (the push); m := mem[RSP] <- 0xdead (the retaddr store —
   the relevance seed: its address var RSP is in D_at, so the RSP defs get tagged and denoted under
   the restriction); CALL (indirect target — the abstraction fires without a callee) returning to
   CONTINUE. CONTINUE: jmp HEADER (the back edge — the header is the i>10 widening point). Returns
   (sub, header tid, rsp). *)
let mk_e1_loop_sub () : sub term * tid * var =
  let rsp = v64 "RSP" in
  let m = memv "e1_m" in
  let entry_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let cont_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b (Def.create rsp (Bil.Int (w64 0x1000)));
  Blk.Builder.add_def body_b (Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 8))));
  Blk.Builder.add_def body_b
    (Def.create m (Bil.Store (Bil.Var m, Bil.Var rsp, Bil.Int (w64 0xdead), LittleEndian, `r64)));
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
       (Call (Call.create ~return:(Label.direct cont_tid) ~target:(Indirect (Bil.Int (w64 0))) ())));
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

(* [mk_e1_flat_sub]: the straight-line call fixture: ENTRY: rsp := 0x2000 (the pre-call truth); rsp
   := RSP − 8 (the push); m := mem[RSP] <- 0xcafe (the retaddr store — the relevance seed); CALL
   (indirect) returning to POST. POST: no defs. Pre-L-E1 the continuation RSP is {0x1ff8} = truth −
   8; post-L-E1 the +8 restoration makes it EXACTLY {0x2000}. Returns (sub, post tid, rsp). *)
let mk_e1_flat_sub () : sub term * tid * var =
  let rsp = v64 "RSP" in
  let m = memv "e1_m" in
  let entry_b = Blk.Builder.create () in
  let post_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b (Def.create rsp (Bil.Int (w64 0x2000)));
  Blk.Builder.add_def entry_b (Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 8))));
  Blk.Builder.add_def entry_b
    (Def.create m (Bil.Store (Bil.Var m, Bil.Var rsp, Bil.Int (w64 0xcafe), LittleEndian, `r64)));
  let entry0 = Blk.Builder.result entry_b in
  let post0 = Blk.Builder.result post_b in
  let post_tid = Term.tid post0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b
    (Jmp.create
       (Call (Call.create ~return:(Label.direct post_tid) ~target:(Indirect (Bil.Int (w64 0))) ())));
  let post_b = Blk.Builder.init ~copy_defs:true post0 in
  let entry = Blk.Builder.result entry_b in
  let post = Blk.Builder.result post_b in
  let sub_b = Sub.Builder.create ~name:"e1_flat" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b post;
  let sub = Sub.Builder.result sub_b in
  (sub, post_tid, rsp)

(* [e1_rsp_at sub tid rsp]: the ON-path fixpoint (the restriction armed via [Relevance.analyze] —
   the call abstraction fires on the indirect call) and the RSP value-set at [tid]. *)
let e1_rsp_at (sub : sub term) (tid : tid) (rsp : var) : Ws.t =
  let sub' = Relevance.analyze sp sub in
  let ctx' = Program.create ~subs:[ sub' ] () in
  let sol = Vsa.static_graph_vsa [] ctx' sub' (Vsa.init_sol ~entry:(anchored_entry ()) sub') in
  AI.find_word 64 (Graphlib.Std.Solution.get sol tid) rsp

(* --- 42. L-D6 (fix-17 resumed): the fix-14 blocker pin — the RBP-anchored restriction-ON fixture
   -------------------------------------- fix-14 (blocker): the jcc decoder's [refine_cell] addr
   gate (cbat_vsa.ml:1004) requires EVERY free var of the compared Load's address to pass
   [refineable_var]; [refineable_of_sub] (cbat_vsa.ml:1983-1999) admits only vars whose defs in the
   sub are ALL tagged [Utils.relevant] (the all-defs-tagged rule). The corpus epilogue `RBP :=
   mem[RSP, el]:u64` (al.bil:434) defines RBP with a value that is DEAD at its position (nothing
   after it uses RBP), so the plain liveness rule leaves the def UNTAGGED and RBP would fall out of
   the refineable set — every RBP-anchored jle loop's cell refinement is rejected by the addr gate
   (168/168).

   L-D8 (hike_vsa_relevance.ml — the user's two-pass tagging design of 2026-08-08, replaces the
   L-D5b frame-base rule): the FORWARD D pass tags the defs that DIRECTLY use RSP and RSP-derived
   values (the stack-anchor machinery); the BACKWARD W pass (live_at_pos) tags the address
   contributors. The epilogue def is tagged by the FORWARD rule — its rhs uses RSP ∈ D_at — so RBP
   has no untagged def -> RBP ∈ refineable -> the decoder's cell meet binds (the frame-base rule's
   fix preserved, without the var-name special case).

   FIXTURE (the exact corpus scenario, restriction ON): PROLOGUE: rbp := RSP; jmp ENTRY. ENTRY: m :=
   mem[RBP-8] <- 0; jmp HEADER. HEADER: the canonical -O0 cmp emission comparing the Load [m, RBP-8]
   against 63 (t := Load - 63; CF := Load < 63; OF := high:1[(Load ^ 63) & (Load ^ t)]; SF :=
   high:1[t]; ZF := 0 = t), the jle compound guard (L-D2's c=63 ascending counter dynamics: the
   chain crosses the i>10 widening, so the SLE gate needs the L-D1 provenance proof —
   [provably_nonneg_operand], structural, is tag-independent); jle -> BODY else EXIT. BODY: u :=
   Load[RBP-8]; m := mem[RBP-8] <- (u + 1); jmp HEADER. EXIT: jmp EPILOGUE. EPILOGUE: rbp := Load[m,
   RSP] (the corpus epilogue, dead). RBP's two defs: the prologue (live, tagged by the liveness
   rule) and the epilogue (dead — untagged by the plain liveness rule, tagged by the FORWARD-D rule
   post-L-D8 because its rhs uses RSP ∈ D): the all-defs-tagged gate is the discriminator.

   RUN: the ON-path fixpoint (the restriction armed via [Relevance.analyze]; [Program.create] +
   [static_graph_vsa] — the E1-pin pattern, :4151-4154). ASSERT: the cell at RBP-8 at the BODY input
   is bounded ⊆ [0, 64) (non-top, max ≤ 63 — the l39_cell_of/l39_bounded idiom adapted to RBP-8).
   FAILS with the plain liveness rule (the addr gate rejects; the widened counter cell stays top).
   Revert-proof: drop the [is_d_used] disjunct (a temporary src edit) -> this pin FAILS (the
   epilogue untagged -> RBP ∉ refineable -> the cell gate blocks) while P23-1 stays green
   (NOT-tagged either way) — the discriminating property is L-D6; restore -> green. *)

(* [mk_l6_rbp_loop]: the fix-14 blocker fixture above. Returns (sub, body tid). *)
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
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
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
    (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int (w32 0), LittleEndian, `r32)));
  (* the canonical -O0 cmp emission (mk_l39_loop's header), RBP-based *)
  Blk.Builder.add_def header_b (Def.create t (Bil.BinOp (Bil.MINUS, load_e, Bil.Int c)));
  Blk.Builder.add_def header_b (Def.create cf (Bil.BinOp (Bil.LT, load_e, Bil.Int c)));
  Blk.Builder.add_def header_b
    (Def.create ofv
       (Bil.Cast
          ( Bil.HIGH,
            1,
            Bil.BinOp
              ( Bil.AND,
                Bil.BinOp (Bil.XOR, load_e, Bil.Int c),
                Bil.BinOp (Bil.XOR, load_e, Bil.Var t) ) )));
  Blk.Builder.add_def header_b (Def.create sf (Bil.Cast (Bil.HIGH, 1, Bil.Var t)));
  Blk.Builder.add_def header_b
    (Def.create zf (Bil.BinOp (Bil.EQ, Bil.Int (Word.zero (Word.bitwidth c)), Bil.Var t)));
  Blk.Builder.add_def body_b (Def.create u (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  Blk.Builder.add_def body_b
    (Def.create m
       (Bil.Store
          (Bil.Var m, addr_e, Bil.BinOp (Bil.PLUS, Bil.Var u, Bil.Int (w32 1)), LittleEndian, `r32)));
  (* the corpus epilogue: RBP := mem[RSP, el]:u64 (al.bil:434) *)
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

(* [l6_cell_of st]: the value of the cell at RBP-8 in [st] (this section's mem var; the l39_cell_of
   readback idiom adapted to RBP). *)
let l6_cell_of (st : AI.t) : Ws.t =
  let m = memv "l6_m" in
  let rbp = v64 "RBP" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  match Vsa.denote_imm_exp (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)) st with
  | Ok ws -> ws
  | Error _ -> Ws.top 32

(* [l6_run sub body_tid]: the ON-path fixpoint (the restriction armed via [Relevance.analyze] — the
   E1-pin pattern, test_cbat.ml:4151- 4154) returning the BODY input state's cell at RBP-8 (BODY's
   only predecessor is the header's taken edge, so its input state carries the decoder's cell
   refinement). *)
let l6_run (sub : sub term) (body_tid : tid) : Ws.t =
  let sub' = Relevance.analyze sp sub in
  let ctx' = Program.create ~subs:[ sub' ] () in
  let sol = Vsa.static_graph_vsa [] ctx' sub' (Vsa.init_sol ~entry:(anchored_entry ()) sub') in
  l6_cell_of (Graphlib.Std.Solution.get sol body_tid)

(* --- 43. Refactor-2 (ora-9 Item 1(d)): the NEW-SHAPE pins — the inverse_denote_exp refactor's
   additions --------------------------------- The refactor (REFACTOR-1a/1b, cbat_vsa.ml :1200-1536)
   collapsed the six shape arms of [assume_jump_cond] to the jcc-decoder pre-step + the ONE general
   structural walk [inverse_denote_exp ~ctx cond {1} env] (:1842-1867). The 319 pre-refactor pins
   prove the EQUIVALENCE; these four pins prove the ADDITIONS — the shapes that were UNREFINED (a
   sound stop) pre-refactor and now refine: R2-1 the INLINE-ARITHMETIC condition `(t+1) < c` — the
   compared exp is a BinOp PLUS, not a bare Load/Var: refine_backward's `_ -> env` stopped on the
   BinOp operand pre-refactor; the producer-op recursion (:1437-1487) now refines the (t+1) chain:
   guard row -> [0, 64) on (t+1) -> the PLUS row (refine_row, the circular hull {−1} ∪ [0, 62] on t
   — the sound wrap: t = −1 also satisfies (t+1) < 64) -> the Var case -> refine_backward -> the
   Load -> refine_cell -> the cell at RBP−8 is the 64-element hull (⊆ {−1} ∪ [0, 64); cardn 64, no
   middle value — NOT the full domain). R2-2 NOT-of-comparison `~(t < 5)` (the taken edge = t ≥ 5):
   the UnOp-NOT case's GATE 2 (:1518-1522) keeps env for a comparison-shaped operand — the TRUE-edge
   rows (constraint_of_compare's [0, 5)) must NOT narrow the operand on this FALSE edge (the wrong
   window would drop the live t ≥ 5). The multi-valued seed cell {3, 8} (the two-path entry —
   same-key stores in ONE block overwrite, Mem.add :511-514, so the join needs two paths) makes the
   wrong window measurable: with the gate removed, the cell narrows to ⊆ [0, 4] (the live 8 dropped
   every iteration); with the gate, the cell stays unbounded (the ascending chain widens to top).
   R2-3 the CONST-FIRST LT flip `10 < t` (Bil.BinOp (Bil.LT, Bil.Int c, e)): ora-9 Item 1(d) — the
   const-first LT/LE/ SLT/SLE flips become REAL rows via the guard_op enum ([constraint_of_guard]'s
   UGT/UGE/SGT/SGE rows — BIL has no GT/GE constructors, so the flip must dispatch on the enum, not
   on [Bil.binop]). The flip yields t > 10 unsigned -> [11, 2^w): the DECREMENTING counter (seed 20,
   −1 — the taken edge must be live at the entry; the ascending chain would be unaffected by the
   [11, 2^w) meet) converges inside the constraint: non-top, min_elem ≥ 11. NOTE (Refactor-2
   finding): the LANDED const-first arm (:1363-1375) is the pre-refactor EQ-only equivalence
   (LT/LE/SLT/SLE const-first are still a sound stop — the ora-9 Item 1(d) flip did NOT land with
   the refactor), so THIS PIN FAILS on the current tree by design: it is the spec'd-behavior proof,
   green only after the flip lands (verified by the temporary-flip revert-proof: ADD the flip ->
   R2-3 green; restore -> red). R2-4 the NESTED-BinOp operand chain `(t * 8) < 512` — the compared
   exp is a BinOp TIMES: guard row -> [0, 512) on (t*8) -> the TIMES-const row (refine_row :825-856,
   the no-wrap gate: a' = [ceil(lo/k), floor(hi/k)] = [0, 63]) -> the Var case -> refine_backward ->
   refine_cell -> the cell ⊆ [0, 64) (512/8; the counter is bounded BEFORE the i>10 widening, so the
   TIMES no-wrap gate passes — the L-B1 dynamics). All four run the ON path (the E1-pin pattern,
   :4151-4154: [Relevance.analyze] + [Program.create] + [static_graph_vsa]) and read back the cell
   at RBP−8 (BODY's only predecessor is the header's taken edge, so its input state carries the
   refinement). ADAPTATION (the task's "RSP-8" fixtures): the ON-path refine_cell addr gate (:1004)
   requires EVERY free var of the compared Load's address to pass [refineable_var], and
   [refineable_of_sub] admits only vars WITH defs in the sub — RSP has none, so the RSP-anchored L-B
   shape would fail the gate; the fixtures use the L-D6 prologue shape (rbp := RSP; the cell at
   RBP−8), exactly like section 42. Revert-proofs (src edits, restored): R2-1/R2-4 — the producer-op
   recursion disabled (the BinOp-producer case keep-env) / the TIMES row neutralized; R2-2 — the NOT
   comparison-operand gate removed; R2-3 — the flip added (the complement of the "disable" revert:
   the flip is absent, so the ADD experiment proves the pin's discriminating power). *)

(* [mk_r2_loop ~seed ~seed2 ~body_op ~body_k ~mk_cond]: the RBP-anchored ON-path fixture. PROLOGUE:
   rbp := RSP; jmp SPLIT (only when ~seed2 is given) / jmp ENTRY. SPLIT (the R2-2 two-path seed —
   the multi-valued seed cell {seed, seed2} needs the header's join of two paths: same-key stores in
   ONE block overwrite (Mem.add, cbat_ai_memmap.ml:511-514), and TWO UNCONDITIONAL jumps from one
   block drop the second edge (reachable_jumps: no fall-through), so the split must be CONDITIONAL
   on a {0,1}-valued flag f := g (g a never-defined 1-bit var -> f stays top): when f goto ENTRY
   else ENTRY2): f := g. ENTRY: m := mem[RBP-8] <- seed; jmp HEADER. ENTRY2: m := mem[RBP-8] <-
   seed2; jmp HEADER. HEADER: t := Load[m, RBP-8]; when <mk_cond t> goto BODY else EXIT. BODY: u :=
   Load[m, RBP-8]; m := mem[RBP-8] <- (u <body_op> <body_k>); jmp HEADER. [mk_cond] receives the
   fixture's OWN t var (the cond must reference the fixture's t — the L-B idiom; a caller-built cond
   referencing a different var would be a phantom). Returns (sub, body tid). *)
let mk_r2_loop ~(seed : word) ~(seed2 : word option) ~(body_op : Bil.binop) ~(body_k : word)
    ~(mk_cond : t:var -> exp) : sub term * tid =
  let m = memv "r2_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let t = Var.create ~is_virtual:false ~fresh:false "r2_t" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "r2_u" (Type.Imm 32) in
  let f = v1 "r2_f" in
  let g = v1 "r2_g" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
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
    (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int seed, LittleEndian, `r32)));
  (match seed2 with
  | Some s2 ->
      Blk.Builder.add_def entry2_b
        (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int s2, LittleEndian, `r32)))
  | None -> ());
  Blk.Builder.add_def header_b (Def.create t load_e);
  Blk.Builder.add_def body_b (Def.create u load_e);
  Blk.Builder.add_def body_b
    (Def.create m
       (Bil.Store
          (Bil.Var m, addr_e, Bil.BinOp (body_op, Bil.Var u, Bil.Int body_k), LittleEndian, `r32)));
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

(* [r2_cell_of st]: the value of the cell at RBP-8 in [st] (this section's mem var; the l6_cell_of
   readback idiom, adapted). *)
let r2_cell_of (st : AI.t) : Ws.t =
  let m = memv "r2_m" in
  let rbp = v64 "RBP" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  match Vsa.denote_imm_exp (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)) st with
  | Ok ws -> ws
  | Error _ -> Ws.top 32

(* [r2_run sub body_tid]: the ON-path fixpoint (the E1-pin pattern, test_cbat.ml:4151-4154 —
   [Relevance.analyze] arms the restriction, then [Program.create] + [static_graph_vsa]) returning
   the BODY input state's cell at RBP-8. *)
let r2_run (sub : sub term) (body_tid : tid) : Ws.t =
  let sub' = Relevance.analyze sp sub in
  let ctx' = Program.create ~subs:[ sub' ] () in
  let sol = Vsa.static_graph_vsa [] ctx' sub' (Vsa.init_sol ~entry:(anchored_entry ()) sub') in
  iter_cell_of sub' sol body_tid r2_cell_of

let run () =
(  (* L3a-1: PLUS row — v := t + 1 constrained by EQ(v, 5) (the wrap-free PLUS instance; see the
     section note) -> t' = {4} -> the cell meets to {4}. *)
  let sub1, body1 =
    mk_l3a_loop ~cmp:Bil.EQ ~c:(w32 5)
      ~rhs:
        (Bil.BinOp
           ( Bil.PLUS,
             Bil.Var (Var.create ~is_virtual:false ~fresh:false "l3a_t" (Type.Imm 32)),
             Bil.Int (w32 1) ))
  in
  check
    "L3a-1: backward guard refinement through PLUS — the cell at RBP-8 is bounded (⊆ [0,9]; the \
     walk met {4} into the load cell)"
    (l3a_bounded (l3a_run_analyzed sub1 body1) (w32 9));
  (* L3a-2: MINUS row — v := t - 1 constrained by LT(v, 10) -> t' = [1,10] -> cell meets to [1,10]
     (bounded above by 10). *)
  let sub2, body2 =
    mk_l3a_loop ~cmp:Bil.LT ~c:(w32 10)
      ~rhs:
        (Bil.BinOp
           ( Bil.MINUS,
             Bil.Var (Var.create ~is_virtual:false ~fresh:false "l3a_t" (Type.Imm 32)),
             Bil.Int (w32 1) ))
  in
  check
    "L3a-2: backward guard refinement through MINUS — the cell at RBP-8 is bounded (⊆ [1,10]; the \
     walk met [1,10] into the load cell)"
    (l3a_bounded (l3a_run_analyzed sub2 body2) (w32 10));
  (* L3a-3: LSHIFT-const row — v := t << 2 constrained by LT(v, 40) -> t' = [0>>2, 39>>2] = [0,9] ->
     cell meets to [0,9]. *)
  let sub3, body3 =
    mk_l3a_loop ~cmp:Bil.LT ~c:(w32 40)
      ~rhs:
        (Bil.BinOp
           ( Bil.LSHIFT,
             Bil.Var (Var.create ~is_virtual:false ~fresh:false "l3a_t" (Type.Imm 32)),
             Bil.Int (w32 2) ))
  in
  check
    "L3a-3: backward guard refinement through LSHIFT-const — the cell at RBP-8 is bounded (⊆ \
     [0,9]; 40>>2 = 10)"
    (l3a_bounded (l3a_run_analyzed sub3 body3) (w32 9));
  (* L3a-4: TIMES-const — the SOUND rule. The exact slice [ceil(vlo/k), floor(vhi/k)] applies only
     when the operand provably cannot wrap; over the walk's unbounded (top) operand the wrapped
     solution classes hull to the full domain = the identity, so the cell is NOT narrowed (the old
     no-gate slice that excluded the wrap classes was unsound — a t = 2^29 also satisfies t·2 mod
     2^32 = 0 ∈ [0,39]). The M6 tag computation, where the operand IS constrained by the guard,
     fires the exact slice. *)
  let sub4, body4 =
    mk_l3a_loop ~cmp:Bil.LT ~c:(w32 40)
      ~rhs:
        (Bil.BinOp
           ( Bil.TIMES,
             Bil.Var (Var.create ~is_virtual:false ~fresh:false "l3a_t" (Type.Imm 32)),
             Bil.Int (w32 2) ))
  in
  check
    "L3a-4: the TIMES rule over an unbounded operand is the identity (sound — the wrapped classes \
     hull to the domain; the cell is not narrowed)"
    (not (l3a_bounded (l3a_run_analyzed sub4 body4) (w32 19)));
  (* L3a-5: NEQ doubt — constraint_of_compare returns None for NEQ, so no constraint, no walk -> the
     cell stays top. (The old L3a-5 frozen-flag gate pin is superseded: with the tag-only design the
     gate's rejection side is pinned by L3c2-5 — the same SLT(4) counter WITHOUT the RSP prologue
     def leaves the cell at {0..4}.) *)
  let sub5, body5 =
    mk_l3a_loop ~cmp:Bil.NEQ ~c:(w32 5)
      ~rhs:
        (Bil.BinOp
           ( Bil.PLUS,
             Bil.Var (Var.create ~is_virtual:false ~fresh:false "l3a_t" (Type.Imm 32)),
             Bil.Int (w32 1) ))
  in
  check
    "L3a-5: a NEQ guard is doubt (constraint_of_compare None) — no walk, the cell at RBP-8 stays \
     top"
    (Ws.is_top (l3a_run_analyzed sub5 body5));
  ())
;
(  let m = memv "l3c1_m" in
  (* L3c1-1: FLAG-INDIRECTED guard — `CF := LT(t, 10); if CF goto BODY` — the flag-state record
     recovers the constraint on t on the taken edge: t := Load -> the cell meets to [0,10). *)
  let sub1, body1, _ = mk_l3c1_loop ~extra_header_defs:[] in
  let ctx1 = Program.create ~subs:[ sub1 ] () in
  let sol1 = Vsa.static_graph_vsa [] ctx1 sub1 (Vsa.init_sol ~entry:(anchored_entry ()) sub1) in
  let cell1 = l3c1_cell_of m (iter_state_of sub1 sol1 body1) in
  check
    "L3c1-1: a flag-indirected guard (CF := LT(t, 10); if CF goto …) — the flag-state record \
     recovers the constraint on t and the cell at RBP-8 is bounded (⊆ [0,9])"
    (l3c1_bounded cell1 (w32 9));
  (* L3c1-2: a later def of the operand (t := 42 between the comparison and the jump) clears the
     record -> no refinement. (The single-def gate on t would stop the walk too — the invalidation
     is the primary documented mechanism.) *)
  let t = Var.create ~is_virtual:false ~fresh:false "l3c1_t" (Type.Imm 32) in
  let sub2, body2, _ = mk_l3c1_loop ~extra_header_defs:[ Def.create t (Bil.Int (w32 42)) ] in
  let ctx2 = Program.create ~subs:[ sub2 ] () in
  let sol2 = Vsa.static_graph_vsa [] ctx2 sub2 (Vsa.init_sol ~entry:(anchored_entry ()) sub2) in
  let cell2 = l3c1_cell_of m (iter_state_of sub2 sol2 body2) in
  check
    "L3c1-2: a later def of the compared operand (t := 42) between the comparison and the jump \
     invalidates the flag record — no cell refinement"
    (Ws.is_top cell2);
  (* L3c1-3: a non-comparison redefinition of the flag (CF := unknown) clears the record -> no
     refinement. *)
  let cf = v1 "l3c1_cf" in
  let sub3, body3, _ =
    mk_l3c1_loop ~extra_header_defs:[ Def.create cf (Bil.Unknown ("l3c1_bits", Type.Imm 1)) ]
  in
  let ctx3 = Program.create ~subs:[ sub3 ] () in
  let sol3 = Vsa.static_graph_vsa [] ctx3 sub3 (Vsa.init_sol ~entry:(anchored_entry ()) sub3) in
  let cell3 = l3c1_cell_of m (iter_state_of sub3 sol3 body3) in
  check
    "L3c1-3: a non-comparison redefinition of the flag (CF := unknown) invalidates the flag record \
     — no cell refinement"
    (Ws.is_top cell3);
  (* L3c1-4: the SINGLE-DEF GATE — v's base has TWO defs (the header's v := t - 1 and the body's v
     := t + 1); the walk stops through the multi-def base (following the last def's equation could
     narrow operands on paths produced by the other def) -> no cell refinement. The MINUS equation
     would refine if the gate were absent. *)
  let m4 = memv "l3c1_m4" in
  let rsp4 = v64 "RSP" in
  let t4 = Var.create ~is_virtual:false ~fresh:false "l3c1_t4" (Type.Imm 32) in
  let v4 = Var.create ~is_virtual:false ~fresh:false "l3c1_v4" (Type.Imm 32) in
  let addr4 = Bil.BinOp (Bil.MINUS, Bil.Var rsp4, Bil.Int (w64 8)) in
  let cond4 = Bil.BinOp (Bil.LT, Bil.Var v4, Bil.Int (w32 10)) in
  let e4 = Blk.Builder.create () in
  let b4 = Blk.Builder.create () in
  let h4 = Blk.Builder.create () in
  let x4 = Blk.Builder.create () in
  Blk.Builder.add_def h4 (Def.create t4 (Bil.Load (Bil.Var m4, addr4, LittleEndian, `r32)));
  Blk.Builder.add_def h4 (Def.create v4 (Bil.BinOp (Bil.MINUS, Bil.Var t4, Bil.Int (w32 1))));
  Blk.Builder.add_def b4 (Def.create v4 (Bil.BinOp (Bil.PLUS, Bil.Var t4, Bil.Int (w32 1))));
  let e0 = Blk.Builder.result e4 in
  let b0 = Blk.Builder.result b4 in
  let h0 = Blk.Builder.result h4 in
  let x0 = Blk.Builder.result x4 in
  let b_tid = Term.tid b0 in
  let h_tid = Term.tid h0 in
  let x_tid = Term.tid x0 in
  let e4 = Blk.Builder.init ~copy_defs:true e0 in
  Blk.Builder.add_jmp e4 (Jmp.create (Goto (Direct h_tid)));
  let b4 = Blk.Builder.init ~copy_defs:true b0 in
  Blk.Builder.add_jmp b4 (Jmp.create (Goto (Direct h_tid)));
  let h4 = Blk.Builder.init ~copy_defs:true h0 in
  Blk.Builder.add_jmp h4 (Jmp.create ~cond:cond4 (Goto (Direct b_tid)));
  Blk.Builder.add_jmp h4 (Jmp.create ~cond:(Bil.UnOp (Bil.NOT, cond4)) (Goto (Direct x_tid)));
  let e = Blk.Builder.result e4 in
  let b = Blk.Builder.result b4 in
  let h = Blk.Builder.result h4 in
  let x = Blk.Builder.result x4 in
  let sub_b = Sub.Builder.create ~name:"l3c1_multidef" () in
  Sub.Builder.add_blk sub_b e;
  Sub.Builder.add_blk sub_b b;
  Sub.Builder.add_blk sub_b h;
  Sub.Builder.add_blk sub_b x;
  let sub4 = Sub.Builder.result sub_b in
  let ctx4 = Program.create ~subs:[ sub4 ] () in
  let sol4 = Vsa.static_graph_vsa [] ctx4 sub4 (Vsa.init_sol ~entry:(anchored_entry ()) sub4) in
  let cell4 = l3c1_cell_of m4 (Graphlib.Std.Solution.get sol4 b_tid) in
  (* MIGRATED (ticket 01, the single-pass trace partitioning,
     docs/trace-partitioning-plan.md §2/§4.3): the pin used to assert the
     solution's body-IN cell stays TOP — the observable of the SHALLOW
     lane's single-def gate ([constrain_def_chain]'s [unique] stop), the
     only refinement that reached the raw solution pre-inline.  The fused
     design makes the block IN-state the TAG state: the inline deep walk
     ([refine_edge]) refines the TAKEN edge — [v < 10] over the header's
     [v := t − 1] (the header's OWN def, the per-def PRODUCER SUBTRACTION
     handling the multi-def base soundly — the walk never had the unique
     gate; the per-def subtraction is its documented multi-def mechanism)
     — so [t ∈ [1,10]] meets the load cell.  The window is EXACT for the
     taken trace (the cell is never stored in this fixture: X = 0 gives
     v = 0xFFFFFFFF (exit), X ≥ 11 gives v ≥ 10 (exit) — the body is
     entered only from X ∈ [1,10]).  The shallow lane's single-def gate
     itself is untouched (KEPT — [constrain_def_chain]). *)
  check
    "L3c1-4 (migrated, single-pass §2): the multi-def base refines through the \
     per-block producer subtraction — the body-IN cell is the EXACT taken-edge \
     window [1,10] (1 ∈, 10 ∈, 0 ∉, 11 ∉; non-top)"
    ((not (Ws.is_top cell4))
    && (not (Ws.is_bottom cell4))
    && Ws.elem (w32 1) cell4
    && Ws.elem (w32 10) cell4
    && not (Ws.elem (w32 0) cell4)
    && not (Ws.elem (w32 11) cell4));
  (* L3c1-5: direct assume_jump_cond WITHOUT ?defs — the flag-state step is gated on ?defs: the flag
     meet still applies (the pre-L3c behavior) but no cell refinement happens. *)
  let sub5, _, jmp5 = mk_l3c1_loop ~extra_header_defs:[] in
  let ctx5 = Program.create ~subs:[ sub5 ] () in
  let sol5 = Vsa.static_graph_vsa [] ctx5 sub5 (Vsa.init_sol ~entry:(anchored_entry ()) sub5) in
  let hdr5 =
    match Term.enum blk_t sub5 |> Seq.to_list with [ _; _; h; _ ] -> h | _ -> assert false
  in
  let hdr_st = Graphlib.Std.Solution.get sol5 (Term.tid hdr5) in
  let res5 = Vsa.assume_jump_cond hdr_st jmp5 in
  let cell5 = l3c1_cell_of m res5 in
  check
    "L3c1-5: direct assume_jump_cond without ?defs — the flag-state refinement is gated off (no \
     cell refinement; the pre-L3c behavior)"
    (Ws.is_top cell5);
  ())
;
(  let half = w32 0x80000000 in
  let m_one = w32 0xFFFFFFFF in
  (* L3c2-1: DIRECT signed guard on a seeded, incrementing counter — SLT(t, 10) with t := Load
     [RSP-8] starting at {0}: the gate passes (max < 2^31) and the walk caps the cell at [0,9].
     Pre-L3c-2 SLT -> None -> the counter grows unboundedly (fails). *)
  let sub1, body1 =
    mk_l3c2_loop ~prologue:true
      ~seed:(Some (w32 0))
      ~cmp:Bil.SLT ~c:(w32 4) ~body_op:Bil.PLUS ~body_k:(w32 1) ~flag:false
  in
  let ctx1 = Program.create ~subs:[ sub1 ] () in
  let sol1 = Vsa.static_graph_vsa [] ctx1 sub1 (Vsa.init_sol ~entry:(anchored_entry ()) sub1) in
  let cell1 = l3c2_cell_of (iter_state_of sub1 sol1 body1) in
  check
    "L3c2-1: a direct SLT(t, 4) guard on a seeded non-negative counter — the signed row fires (the \
     gate passes) and the cell at RBP-8 is bounded (⊆ [0,3])"
    (l3c2_bounded cell1 (w32 3));
  (* L3c2-2: the two-piece SLT rule — the same loop WITHOUT the seed: the operand is top (max =
     0xFFFFFFFF, not < 2^31), so the exact single piece is not provable — the TOTAL two-piece rule
     [0, c−1] ∪ [2^31, max] refines the cell instead of refusing (the old non-negativity gate's None
     stop is removed; the two-piece is the sound over-approximation of the true SLT values). *)
  let sub2, body2 =
    mk_l3c2_loop ~prologue:true ~seed:None ~cmp:Bil.SLT ~c:(w32 10) ~body_op:Bil.PLUS
      ~body_k:(w32 1) ~flag:false
  in
  let ctx2 = Program.create ~subs:[ sub2 ] () in
  let sol2 = Vsa.static_graph_vsa [] ctx2 sub2 (Vsa.init_sol ~entry:(anchored_entry ()) sub2) in
  let cell2 = l3c2_cell_of (iter_state_of sub2 sol2 body2) in
  check
    "L3c2-2: the two-piece SLT rule — a signed guard whose operand is not provably non-negative \
     (top) still refines the cell to the two-piece [0, c−1] ∪ [2^31, max] (the gate is removed; no \
     None stop)"
    ((not (Ws.is_top cell2))
    && match Ws.min_elem cell2 with Some w -> Word.( >= ) w (w32 0) | None -> false);
  (* L3c2-3: c < 0 is ONE interval, no gate — SLT(t, -1) with the cell seeded at 2^31 and the body
     DECREMENTING: the meet drops the low-half values, the cell stays in [2^31, c-1]. *)
  let sub3, body3 =
    mk_l3c2_loop ~prologue:true ~seed:(Some half) ~cmp:Bil.SLT ~c:m_one ~body_op:Bil.MINUS
      ~body_k:(w32 1) ~flag:false
  in
  let ctx3 = Program.create ~subs:[ sub3 ] () in
  let sol3 = Vsa.static_graph_vsa [] ctx3 sub3 (Vsa.init_sol ~entry:(anchored_entry ()) sub3) in
  let cell3 = l3c2_cell_of (iter_state_of sub3 sol3 body3) in
  check
    "L3c2-3: SLT(t, -1) (c < 0) is a single high interval [2^31, c-1] with no gate — the cell \
     stays in the high half (the decrements into the low half are met away)"
    (l3c2_in_high cell3 half (w32 0xFFFFFFFE));
  (* L3c2-4: THE -O0 pattern — flag-indirected signed guard: CF := SLT(t, 10); if CF goto … —
     flag-state + signed row together cap the cell at [0,9]. *)
  let sub4, body4 =
    mk_l3c2_loop ~prologue:true
      ~seed:(Some (w32 0))
      ~cmp:Bil.SLT ~c:(w32 4) ~body_op:Bil.PLUS ~body_k:(w32 1) ~flag:true
  in
  let ctx4 = Program.create ~subs:[ sub4 ] () in
  let sol4 = Vsa.static_graph_vsa [] ctx4 sub4 (Vsa.init_sol ~entry:(anchored_entry ()) sub4) in
  let cell4 = l3c2_cell_of (iter_state_of sub4 sol4 body4) in
  check
    "L3c2-4: the -O0 flag-indirected pattern (CF := SLT(t, 4); if CF goto …) — the flag-state \
     record + the signed row bound the cell at RBP-8 (⊆ [0,3])"
    (l3c2_bounded cell4 (w32 3));
  (* L3c2-5: the trace-exact cell meet is no longer gated on an RBP prologue definition. The address
     range is derived from the trace/frame state, so the same SLT row bounds the cell to [0,3]. *)
  let sub5, body5 =
    mk_l3c2_loop ~prologue:false
      ~seed:(Some (w32 0))
      ~cmp:Bil.SLT ~c:(w32 4) ~body_op:Bil.PLUS ~body_k:(w32 1) ~flag:false
  in
  let ctx5 = Program.create ~subs:[ sub5 ] () in
  let sol5 = Vsa.static_graph_vsa [] ctx5 sub5 (Vsa.init_sol ~entry:(anchored_entry ()) sub5) in
  let cell5 = l3c2_cell_of (iter_state_of sub5 sol5 body5) in
  check
    "L3c2-5: trace-exact cell refinement — without the RBP prologue def the cell is still bounded \
     by the SLT(4) iterate constraint"
    (l3c2_bounded cell5 (w32 3));
  (* L3c2-6: unsigned regression — covered by the existing LT pins (L3a-2, L3c1-1) which must stay
     green (the LT/LE/EQ rows are untouched). *)
  ())
;
(  let t = Var.create ~is_virtual:false ~fresh:false "l3c3_t" (Type.Imm 32) in
  (* L3c3-1: PLUS-HULL — the canonical `v := t + 1; if SLT(v, 10)` loop: the wrapped hull {−1} ∪
     [0,8] caps the cell. Pre-row the PLUS wrap -> None -> the cell grows to top (fails). *)
  let sub1, body1 =
    mk_l3c3_loop
      ~seed:(Some (w32 0))
      ~chain:(Bil.BinOp (Bil.PLUS, Bil.Var t, Bil.Int (w32 1)))
      ~cmp:Bil.SLT ~c:(w32 10) ~body_k:(w32 4)
  in
  check
    "L3c3-1: the PLUS-HULL row — `v := t + 1; if SLT(v, 10)` — the wrapped hull {−1} ∪ [0,8] caps \
     the cell at RBP-8 (bounded ⊆ [0,9])"
    (l3c2_bounded (l3c3_run sub1 body1) (w32 9));
  (* L3c3-2: TIMES-const — the SOUND rule over the walk's unbounded operand is the identity (the
     wrapped classes hull to the domain; the exact slice needs a provably no-wrap operand — the M6
     tag computation's constrained operand fires it). The cell is not narrowed. *)
  let sub2, body2 =
    mk_l3c3_loop
      ~seed:(Some (w32 0))
      ~chain:(Bil.BinOp (Bil.TIMES, Bil.Var t, Bil.Int (w32 8)))
      ~cmp:Bil.SLT ~c:(w32 80) ~body_k:(w32 4)
  in
  check
    "L3c3-2: the TIMES rule over an unbounded operand is the identity (sound — the cell is not \
     bounded by the multiplier)"
    (not (l3c2_bounded (l3c3_run sub2 body2) (w32 9)));
  (* L3c3-3: RSHIFT-const — `v := t >> 2; if SLT(v, 10)` -> a' = [0,39]. *)
  let sub3, body3 =
    mk_l3c3_loop
      ~seed:(Some (w32 0))
      ~chain:(Bil.BinOp (Bil.RSHIFT, Bil.Var t, Bil.Int (w32 2)))
      ~cmp:Bil.SLT ~c:(w32 10) ~body_k:(w32 8)
  in
  check
    "L3c3-3: the RSHIFT-const row — `v := t >> 2; if SLT(v, 10)` — the cell at RBP-8 is bounded (⊆ \
     [0,39]; 10<<2 = 40)"
    (l3c2_bounded (l3c3_run sub3 body3) (w32 39));
  (* L3c3-4a: ARSHIFT-const with a provably non-negative operand (seeded {0}, incrementing) -> the
     gate passes, the cell is bounded. *)
  let sub4a, body4a =
    mk_l3c3_loop
      ~seed:(Some (w32 0))
      ~chain:(Bil.BinOp (Bil.ARSHIFT, Bil.Var t, Bil.Int (w32 2)))
      ~cmp:Bil.SLT ~c:(w32 10) ~body_k:(w32 8)
  in
  check
    "L3c3-4a: the ARSHIFT-const row with a provably non-negative operand — the cell at RBP-8 is \
     bounded (⊆ [0,39])"
    (l3c2_bounded (l3c3_run sub4a body4a) (w32 39));
  (* L3c3-4b: ARSHIFT gate-stop — the operand not provably non-negative (top/unseeded) -> no
     refinement, the cell stays top. *)
  let sub4b, body4b =
    mk_l3c3_loop ~seed:None
      ~chain:(Bil.BinOp (Bil.ARSHIFT, Bil.Var t, Bil.Int (w32 2)))
      ~cmp:Bil.SLT ~c:(w32 10) ~body_k:(w32 4)
  in
  check
    "L3c3-4b: the ARSHIFT gate — an operand not provably non-negative (top) does NOT refine (the \
     cell stays top; sound stop)"
    (Ws.is_top (l3c3_run sub4b body4b));
  (* L3c3-5: TIMES k = 0 is a sound stop — no refinement. *)
  let sub5, body5 =
    mk_l3c3_loop ~seed:None
      ~chain:(Bil.BinOp (Bil.TIMES, Bil.Var t, Bil.Int (w32 0)))
      ~cmp:Bil.SLT ~c:(w32 10) ~body_k:(w32 4)
  in
  check "L3c3-5: TIMES with k = 0 is a sound stop — the cell at RBP-8 stays top"
    (Ws.is_top (l3c3_run sub5 body5));
  (* L3c3-6: TIMES with an EQ singleton {5} and k = 8 (5 not divisible by 8) -> the row is empty ->
     no refinement. *)
  let sub6, body6 =
    mk_l3c3_loop ~seed:None
      ~chain:(Bil.BinOp (Bil.TIMES, Bil.Var t, Bil.Int (w32 8)))
      ~cmp:Bil.EQ ~c:(w32 5) ~body_k:(w32 4)
  in
  check
    "L3c3-6: TIMES with an EQ singleton {5} and k = 8 (non-divisible) — the row is empty, no \
     refinement (the cell is not a bounded set; the guard is genuinely dead — no t makes t*8 = 5 — \
     the edge is pruned)"
    (not (l3c2_bounded (l3c3_run sub6 body6) (w32 39)));
  ())
;
(  let t = Var.create ~is_virtual:false ~fresh:false "l3c4_t" (Type.Imm 32) in
  (* L3c4-1: the Var-vs-Var LT guard — `if (t < u) goto …` with u seeded {10}: x' = [0, mx−1] =
     [0,9] caps the RSP-8 cell. Pre-arm the guard falls to `_ -> env` and the cell grows to top
     (fails). *)
  let sub1, body1 =
    mk_l3c4_vv_loop ~seed:(Some (w32 0)) ~seed2:(Some (w32 10)) ~cmp:Bil.LT ~body_k:(w32 4)
  in
  check
    "L3c4-1: the Var-vs-Var LT guard (`if (t < u) goto …`, u seeded {10}) — the interval-overlap \
     row caps the cell at RBP-8 (⊆ [0,9])"
    (l3c2_bounded (l3c4_run sub1 body1) (w32 9));
  (* L3c4-2: the TOP operand — u unseeded (top): the refinement is vacuous (x ∩ [0, 2^w−1] = x) —
     the `_start` argc semantic-top class: the cell stays unbounded. *)
  let sub2, body2 = mk_l3c4_vv_loop ~seed:(Some (w32 0)) ~seed2:None ~cmp:Bil.LT ~body_k:(w32 4) in
  check
    "L3c4-2: a TOP Var-vs-Var operand makes the refinement vacuous — the cell at RBP-8 stays \
     unbounded (the semantic-top class, no wrong window)"
    (not (l3c2_bounded (l3c4_run sub2 body2) (w32 1000)));
  (* L3c4-3: DIVIDE-const — `v := t / 2; if SLT(v, 10)` -> a' = [0,19]. *)
  let sub3, body3 =
    mk_l3c4_loop
      ~seed:(Some (w32 0))
      ~chain:(Bil.BinOp (Bil.DIVIDE, Bil.Var t, Bil.Int (w32 2)))
      ~v_w:32 ~cmp:Bil.SLT ~c:(w32 10) ~body_k:(w32 4)
  in
  check
    "L3c4-3: the DIVIDE-const row — `v := t / 2; if SLT(v, 10)` — the cell at RBP-8 is bounded (⊆ \
     [0,19])"
    (l3c2_bounded (l3c4_run sub3 body3) (w32 19));
  (* L3c4-4: the HIGH-extract producer — `v := cast HIGH 8 t` (v 8-bit) with `if SLT(v, 10)`: a' =
     [0, (10 << 24) - 1]; the body increments by 2^28 so the cell straddles the HIGH bound
     (0x10000000 is dropped — its top byte 0x10 ∉ [0,10)). Pre-row the cell keeps both values
     (fails). *)
  let sub4, body4 =
    mk_l3c4_loop
      ~seed:(Some (w32 0))
      ~chain:(Bil.Cast (Bil.HIGH, 8, Bil.Var t))
      ~v_w:8 ~cmp:Bil.SLT ~c:(Word.of_int ~width:8 10) ~body_k:(w32 0x10000000)
  in
  check
    "L3c4-4: the HIGH-extract producer row — `v := cast HIGH 8 t; if SLT(v, 10)` — the cell at \
     RBP-8 is bounded (⊆ [0, 0x09FFFFFF]; the 2^28-straddling value is dropped)"
    (l3c2_bounded (l3c4_run sub4 body4) (w32 0x09FFFFFF));
  (* L3c4-5: DIVIDE with k = 0 is a sound stop — no refinement (the div-by-zero value is bottom-ish
     and the guard is dead — the cell is not a bounded set). *)
  let sub5, body5 =
    mk_l3c4_loop ~seed:None
      ~chain:(Bil.BinOp (Bil.DIVIDE, Bil.Var t, Bil.Int (w32 0)))
      ~v_w:32 ~cmp:Bil.SLT ~c:(w32 10) ~body_k:(w32 4)
  in
  check "L3c4-5: DIVIDE with k = 0 is a sound stop — no refinement (the cell is not a bounded set)"
    (not (l3c2_bounded (l3c4_run sub5 body5) (w32 39)));
  ())
;
(  let t = Var.create ~is_virtual:false ~fresh:false "l3c5_t" (Type.Imm 32) in
  let v = Var.create ~is_virtual:false ~fresh:false "l3c5_v" (Type.Imm 32) in
  (* L3c5-1: the CONST-FIRST guard arm — `if (10 = t) goto …` (the EQ-const-first lift shape):
     normalized to `t EQ 10`, the walk pins the cell to {10}. Pre-arm the const-first cond falls to
     the catch-all and the cell stays top (fails). *)
  let sub1, body1 =
    mk_l3c5_loop ~seed:None ~chain:None
      ~cond:(Bil.BinOp (Bil.EQ, Bil.Int (w32 10), Bil.Var t))
      ~body_k:(w32 4)
  in
  check
    "L3c5-1: the const-first guard arm — `if (10 = t) goto …` (EQ const-first) — the cell at RBP-8 \
     is bounded (⊆ [0,10]; pinned to {10})"
    (l3c2_bounded (l3c5_run sub1 body1) (w32 10));
  (* L3c5-2: the Tier-3 MOD row — `v := t MOD 8` has no closed form (periodic) -> no refinement. *)
  let sub2, body2 =
    mk_l3c5_loop ~seed:None
      ~chain:(Some (Bil.BinOp (Bil.MOD, Bil.Var t, Bil.Int (w32 8))))
      ~cond:(Bil.BinOp (Bil.SLT, Bil.Var v, Bil.Int (w32 10)))
      ~body_k:(w32 4)
  in
  check
    "L3c5-2: the Tier-3 MOD row (periodic, no closed form) is a sound stop — no refinement (the \
     cell is not a bounded set)"
    (not (l3c2_bounded (l3c5_run sub2 body2) (w32 39)));
  (* L3c5-3a: the AND identity row — `v := t AND ~0` ≡ v = t: the row returns the constraint itself
     and the cell caps at [0,9]. *)
  let sub3a, body3a =
    mk_l3c5_loop
      ~seed:(Some (w32 0))
      ~chain:(Some (Bil.BinOp (Bil.AND, Bil.Var t, Bil.Int (w32 0xFFFFFFFF))))
      ~cond:(Bil.BinOp (Bil.SLT, Bil.Var v, Bil.Int (w32 10)))
      ~body_k:(w32 4)
  in
  check
    "L3c5-3a: the AND-identity row — `v := t AND ~0` (≡ t) — the cell at RBP-8 is bounded (⊆ [0,9])"
    (l3c2_bounded (l3c5_run sub3a body3a) (w32 9));
  (* L3c5-3b: the OR identity row — `v := t OR 0` ≡ v = t. *)
  let sub3b, body3b =
    mk_l3c5_loop
      ~seed:(Some (w32 0))
      ~chain:(Some (Bil.BinOp (Bil.OR, Bil.Var t, Bil.Int (w32 0))))
      ~cond:(Bil.BinOp (Bil.SLT, Bil.Var v, Bil.Int (w32 10)))
      ~body_k:(w32 4)
  in
  check
    "L3c5-3b: the OR-identity row — `v := t OR 0` (≡ t) — the cell at RBP-8 is bounded (⊆ [0,9])"
    (l3c2_bounded (l3c5_run sub3b body3b) (w32 9));
  (* L3c5-4: an Unknown condition — the fixpoint runs without crashing, and assume_jump_cond on the
     Unknown-cond jump keeps the env unchanged (the shrunk catch-all, no assert). *)
  let m4 = memv "l3c5_m" in
  let rsp4 = v64 "RSP" in
  let t4 = Var.create ~is_virtual:false ~fresh:false "l3c5_t" (Type.Imm 32) in
  let addr4 = Bil.BinOp (Bil.MINUS, Bil.Var rsp4, Bil.Int (w64 8)) in
  let e4 = Blk.Builder.create () in
  let h4 = Blk.Builder.create () in
  let x4 = Blk.Builder.create () in
  Blk.Builder.add_def h4 (Def.create t4 (Bil.Load (Bil.Var m4, addr4, LittleEndian, `r32)));
  let e0 = Blk.Builder.result e4 in
  let h0 = Blk.Builder.result h4 in
  let x0 = Blk.Builder.result x4 in
  let h_tid = Term.tid h0 in
  let x_tid = Term.tid x0 in
  let e4 = Blk.Builder.init ~copy_defs:true e0 in
  Blk.Builder.add_jmp e4 (Jmp.create (Goto (Direct h_tid)));
  let h4 = Blk.Builder.init ~copy_defs:true h0 in
  Blk.Builder.add_jmp h4
    (Jmp.create ~cond:(Bil.Unknown ("l3c5_unknown", Type.Imm 1)) (Goto (Direct x_tid)));
  let sub_b = Sub.Builder.create ~name:"l3c5_unknown" () in
  Sub.Builder.add_blk sub_b (Blk.Builder.result e4);
  Sub.Builder.add_blk sub_b (Blk.Builder.result h4);
  Sub.Builder.add_blk sub_b (Blk.Builder.result x4);
  let sub4 = Sub.Builder.result sub_b in
  let ctx4 = Program.create ~subs:[ sub4 ] () in
  let sol4 = Vsa.static_graph_vsa [] ctx4 sub4 (Vsa.init_sol ~entry:(anchored_entry ()) sub4) in
  let h_st4 = Graphlib.Std.Solution.get sol4 h_tid in
  let jmp4 =
    match
      Term.enum jmp_t
        (match Term.enum blk_t sub4 |> Seq.to_list with [ _; h; _ ] -> h | _ -> assert false)
      |> Seq.to_list
    with
    | [ j ] -> j
    | _ -> assert false
  in
  check
    "L3c5-4: an Unknown condition — the fixpoint completes and assume_jump_cond keeps the env \
     unchanged (the shrunk catch-all, never asserts)"
    (AI.equal (Vsa.assume_jump_cond h_st4 jmp4) h_st4);
  ())
(* --- 36. Lane A (ora-2): mixed-width rshift/arshift implementation -- The Clp mixed-width guards
   ("rshift: mixed-width shift operands (32 and 64 bits)" — 252 live hits on struct_arr_dynidx) are
   replaced by coerce-to-max + shift + keep-low-bits (src/cbat_vsa/cbat_clp.ml): zero-extend
   (operand + amount) or sign-extend (the arshift operand only — MANDATORY) to W = max(sz1, sz2),
   compute at W, re-label the low sz1 bits. Pins: exact small-amount, the 252-hit straddling shape,
   the overshift zero, the arshift sign-fill, and the antipodal equal-width overshift image (the
   equal-width path — no coercion). *)
;
(  (* A-1: mixed-width rshift exact — a 32-bit {0xFF} >> {2} (64-bit amount) = {0x3F} at 32 bits.
     Pre-lane-A the guard fired (top). *)
  let r1 = Clp.rshift (Clp.create (w32 0xFF)) (Clp.create (w64 2)) in
  check
    "A-1: mixed-width rshift (32-bit {0xFF} >> 64-bit {2}) is EXACTLY {0x3F} at 32 bits (no guard \
     fire)"
    (Clp.equal r1 (Clp.create (w32 0x3F)));
  (* A-2: the 252-hit shape — a 32-bit operand rshift by a 64-bit [0, 40) amount: the three-way
     split fires at the coerced width, the result is non-top and non-bottom. *)
  let amt40 = Clp.create ~width:64 ~step:(w64 1) ~cardn:(W.of_int ~width:65 40) (w64 0) in
  let r2 = Clp.rshift (Clp.create (w32 1)) amt40 in
  check
    "A-2: the 252-hit shape (32-bit >> 64-bit [0,40)) — the coerced three-way split yields a \
     non-top, non-bottom result"
    ((not (Clp.is_top r2)) && (not (Clp.is_bottom r2)) && Clp.bitwidth r2 = 32);
  (* A-3: overshift — a 32-bit operand rshift by a 64-bit {40} (>= 32) -> {0} exactly at 32 bits
     (the vendored overshift semantics). *)
  let r3 = Clp.rshift (Clp.create (w32 8)) (Clp.create (w64 40)) in
  check "A-3: mixed-width rshift overshift (32-bit >> 64-bit {40}) is EXACTLY {0} at 32 bits"
    (Clp.equal r3 (Clp.create (w32 0)));
  (* A-4: arshift sign — a 32-bit NEGATIVE operand (all-ones) arshift by a 64-bit {40} (>= 32): the
     SIGN-extension makes the coerced sign-fill's low 32 bits all-ones. *)
  let r4 = Clp.arshift (Clp.create (w32 0xFFFFFFFF)) (Clp.create (w64 40)) in
  check
    "A-4: mixed-width arshift sign-fill (32-bit {all-ones} arshift 64-bit {40}) is EXACTLY \
     {all-ones} at 32 bits (the SIGN-extension)"
    (Clp.equal r4 (Clp.create (w32 0xFFFFFFFF)));
  (* A-5: the antipodal equal-width overshift image — a 64-bit {1, 2^63} arshift by a 64-bit {70}
     (>= 64) -> {0, all-ones} (overshift_sign_extend; the equal-width path — no coercion). *)
  let antipodal = Clp.of_list ~width:64 [ w64 1; W.lshift (w64 1) (w64 63) ] in
  let r5 = Clp.arshift antipodal (Clp.create (w64 70)) in
  check
    "A-5: the antipodal overshift image (64-bit {1, 2^63} arshift {70}) is {0, all-ones} \
     (equal-width path, no coercion)"
    (W.to_int_exn (Clp.cardinality r5) = 2
    && Clp.elem (w64 0) r5
    && Clp.elem (W.ones 64) r5
    && (not (Clp.elem (w64 1) r5))
    && not (Clp.is_top r5));
  ())
;
(  (* S-1: fixture F — the traverse shape (seeded RMW counter) run through static_graph_vsa per the
     L3c idiom. Pre-fix (the equal-lower arm absent) the [RSP-8] point-key pile was 16-17 cells
     deep; the restored arm's hull union collapses it and the surviving cell carries the
     find'-fold-equivalent joined value (read at the loop HEADER — the join point where the pile
     accumulated). *)
  let sub1, body1, hdr1 = mk_l3b1_loop () in
  let ctx1 = Program.create ~subs:[ sub1 ] () in
  let sol1 =
    Vsa.static_graph_vsa [] ctx1 sub1 (Vsa.init_sol ~entry:(anchored_entry ()) sub1)
  in
  let st1 = Graphlib.Std.Solution.get sol1 body1 in
  check
    "S-1a: the traverse shape (fixture F, the seeded RMW counter) collapses to <= 3 cells in the \
     solution state (pre-fix the [RSP-8] point-key pile was 16-17 — the restored equal-lower hull \
     union)"
    (l3b_cells_of (memv "l3b1_m") st1 <= 3);
  (* MIGRATED (ticket 02, the Phase B deletion): the exit-edge view is
     the EXIT block's IN-state (its only predecessor is the header's
     fallthrough edge, refined inline by ~(t < 8)); the iterate view is
     the BODY's IN-state (the header's taken edge).  The exit block is
     the fixture's 4th (last) block. *)
  let exit1 =
    match Term.enum blk_t sub1 |> Seq.to_list with
    | [ _; _; _; e ] -> e
    | _ -> failwith "S-1: fixture block layout changed"
  in
  let icell = l3b1_cell_of (Graphlib.Std.Solution.get sol1 body1) in
  let ecell = l3b1_cell_of (Graphlib.Std.Solution.get sol1 (Term.tid exit1)) in
  check
    "S-1b: the partition — the iterate view's cell is the loop-body values (⊆ [0,7], non-top) and \
     the exit view's cell carries the exit-iteration value (8 survives)"
    ((not (Ws.is_top icell))
    && (not (Ws.is_bottom icell))
    && (match Ws.max_elem icell with Some w -> Word.( <= ) w (w32 7) | None -> false)
    && (not (Ws.is_top ecell))
    && Ws.elem (w32 8) ecell);
  (* S-4: the +1-adjacent arm — two +1-adjacent equal-value cells ([RSP-8] and [RSP-7], both {7})
     through ONE merge (the diamond's join) -> the single union hull [RSP-8, RSP-7]; without the +1
     arm the two cells stay separate (2 cells, no hull). The hull bounds are pinned via the sexp key
     marker (the same deterministic printer the L-2 probe counts "(height " nodes with); a read at
     the unaligned upper slot would NOT pin it — the find' alignment gate
     (cbat_ai_memmap.ml:528-534) reads top there by design. *)
  let sub4, merge4 = mk_l3b4_diamond () in
  let ctx4 = Program.create ~subs:[ sub4 ] () in
  let sol4 = Vsa.static_graph_vsa [] ctx4 sub4 (Vsa.init_sol ~entry:(anchored_entry ()) sub4) in
  let st4 = Graphlib.Std.Solution.get sol4 merge4 in
  check
    "S-4a: two +1-adjacent equal-value cells ([RSP-8] and [RSP-7], both {7}) through ONE merge \
     become a SINGLE cell (the +1-adjacent arm, not shadowed by the equal-lower arm)"
    (l3b_cells_of (memv "l3b4_m") st4 = 1);
  let s4 =
    Core_kernel.Sexp.to_string
      (Mem.sexp_of_t
         (AI.find_memory { Mem.addr_width = 64; Mem.addressable_width = 8 } st4 (memv "l3b4_m")))
  in
  check
    "S-4b: the surviving cell is the union hull [RSP-8, RSP-7] — the sexp key marker (lo 0x…F8)(hi \
     0x…F9) carries the merged value {7}"
    (contains_substring s4 "(lo -8)(hi -7)" && contains_substring s4 "(data(FinSet((7:32u)32)))");
  ())
;
(  let rsp = v64 "RSP" in
  let rdi = v64 "RDI" in
  let entry_b = Blk.Builder.create () in
  let blk_b = Blk.Builder.create () in
  let cont_b = Blk.Builder.create () in
  Blk.Builder.add_def blk_b (Def.create rdi (Bil.Int (w64 42)));
  let entry0 = Blk.Builder.result entry_b in
  let blk0 = Blk.Builder.result blk_b in
  let cont0 = Blk.Builder.result cont_b in
  let blk_tid = Term.tid blk0 in
  let cont_tid = Term.tid cont0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct blk_tid)));
  let blk_b = Blk.Builder.init ~copy_defs:true blk0 in
  (* the interrupt edge: jmp_kind's [Int of int * tid] (bap.mli:4718- 4723) — the return tid is
     ignored by the arm *)
  Blk.Builder.add_jmp blk_b (Jmp.create (Int (0x80, cont_tid)));
  Blk.Builder.add_jmp blk_b (Jmp.create (Goto (Direct cont_tid)));
  let entry = Blk.Builder.result entry_b in
  let blk = Blk.Builder.result blk_b in
  let cont = Blk.Builder.result cont_b in
  let sub_b = Sub.Builder.create ~name:"l37_intr" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b blk;
  Sub.Builder.add_blk sub_b cont;
  let sub = Sub.Builder.result sub_b in
  let ctx = Program.create ~subs:[ sub ] () in
  let sol = Vsa.static_graph_vsa [] ctx sub (Vsa.init_sol ~entry:(anchored_entry ()) sub) in
  let cont_st = Graphlib.Std.Solution.get sol cont_tid in
  check
    "B-1: an interrupt edge is an unknown external callee — the continuation keeps the RSP anchor \
     ({0}) and the caller-saved rdi is topped (no AI.top degradation)"
    (Ws.equal (AI.find_word 64 cont_st rsp) (Ws.singleton (w64 0))
    && Ws.is_top (AI.find_word 64 cont_st rdi));
  ())
;
(  (* L-B1: THE corpus shape — the jle loop. The compound guard is the VERBATIM jle condition (21x
     across the -O0 corpus); the decoder emits the IDIOM'S OWN op SLE (reusing the record's LT would
     wrongly exclude a = c) with c = 3 -> [0, 4); the SLE row's non-negativity gate passes on the
     widened counter (max < 2^31) and the walk's Load case refines the RSP-8 cell directly.
     Pre-decoder the compound guard hit the `_ -> env` catch-all and the seeded counter widened to
     top(32) (fails). *)
  let sub1, body1 =
    mk_l39_loop ~seed:(w32 0) ~c:(w32 3) ~body_op:Bil.PLUS ~body_k:(w32 1)
      ~mk_cond:(fun ~cf:_ ~ofv ~sf ~zf -> l39_jle zf sf ofv)
      ~extra_header_defs:(fun _ -> [])
  in
  check
    "L-B1: the exact -O0 corpus block (t := Load-3; CF/SF/OF/ZF defs; the jle compound guard `ZF | \
     (SF|OF) & ~(SF&OF)`) — the jcc decoder recovers the loop-counter constraint (SLE, c=3, gated) \
     and the cell at RBP-8 is bounded (⊆ [0, 4))"
    (l39_bounded (l39_run sub1 body1) (w32 3));
  (* L-B2: the jl shape — the XOR core alone (signed e < c, excludes equality): the decoder emits
     SLT, c=3 -> [0, 3); the cell is bounded ⊆ [0, 3). *)
  let sub2, body2 =
    mk_l39_loop ~seed:(w32 0) ~c:(w32 3) ~body_op:Bil.PLUS ~body_k:(w32 1)
      ~mk_cond:(fun ~cf:_ ~ofv ~sf ~zf:_ -> l39_jl sf ofv)
      ~extra_header_defs:(fun _ -> [])
  in
  check
    "L-B2: the jl compound guard `(SF|OF) & ~(SF&OF)` (signed e < c — excludes equality) — the \
     decoder emits SLT and the cell at RBP-8 is bounded (⊆ [0, 3))"
    (l39_bounded (l39_run sub2 body2) (w32 2));
  (* L-B3: the ja shape — `~(CF | ZF)` (unsigned e > c): the decoder emits UGT, c=3 -> [c+1, 2^w) =
     [4, 2^32), one interval, NO gate. The counter is SEEDED {8} and the body DECREMENTS (the
     >-direction loop: the taken edge is dead for the seed {0} of the incrementing fixtures — the
     meet would be bottom and the refinement would no-op); the guard's meet keeps the cell inside
     [4, 2^32) and the fixpoint converges to {4..8}. *)
  let sub3, body3 =
    mk_l39_loop ~seed:(w32 8) ~c:(w32 3) ~body_op:Bil.MINUS ~body_k:(w32 1)
      ~mk_cond:(fun ~cf ~ofv:_ ~sf:_ ~zf -> l39_ja cf zf)
      ~extra_header_defs:(fun _ -> [])
  in
  let cell3 = l39_run sub3 body3 in
  check
    "L-B3: the ja compound guard `~(CF | ZF)` (unsigned e > c) — the decoder emits UGT (c=3 -> [4, \
     2^w)) and the decrementing counter converges inside the constraint: the cell at RBP-8 has \
     min_elem >= 4 and is not top"
    ((not (Ws.is_top cell3))
    && (not (Ws.is_bottom cell3))
    && match Ws.min_elem cell3 with Some w -> Word.( >= ) w (w32 4) | None -> false);
  (* L-B4: the same-comparison GATE — a SECOND cmp in the same header (a dead-CF-eliminated
     t2/OF2/SF2/ZF2 group whose flag equations reference the second subtraction temp t2 := f - 5):
     the record binds the FIRST cmp's CF, and the gate must reject the mixed group (ZF2's def free
     vars {t2} ⊄ free_vars(e) ∪ {t1}) -> the decoder arm leaves the taken edge unrefined and the
     seeded counter widens to top(32) (the oracle's "rejects a dead-CF- eliminated second cmp"). *)
  let sub4, body4 =
    let f = Var.create ~is_virtual:false ~fresh:false "l39_f" (Type.Imm 32) in
    let t2 = Var.create ~is_virtual:false ~fresh:false "l39_t2" (Type.Imm 32) in
    let of2 = v1 "OF" in
    let sf2 = v1 "SF" in
    let zf2 = v1 "ZF" in
    mk_l39_loop ~seed:(w32 0) ~c:(w32 3) ~body_op:Bil.PLUS ~body_k:(w32 1)
      ~mk_cond:(fun ~cf:_ ~ofv:_ ~sf:_ ~zf:_ -> l39_jle zf2 sf2 of2)
      ~extra_header_defs:(fun m ->
        let rsp2 = v64 "RSP" in
        let addr2 = Bil.BinOp (Bil.MINUS, Bil.Var rsp2, Bil.Int (w64 16)) in
        let f_load = Bil.Load (Bil.Var m, addr2, LittleEndian, `r32) in
        [
          Def.create f f_load;
          Def.create t2 (Bil.BinOp (Bil.MINUS, f_load, Bil.Int (w32 5)));
          Def.create of2
            (Bil.Cast
               ( Bil.HIGH,
                 1,
                 Bil.BinOp
                   ( Bil.AND,
                     Bil.BinOp (Bil.XOR, Bil.Var f, Bil.Int (w32 5)),
                     Bil.BinOp (Bil.XOR, Bil.Var f, Bil.Var t2) ) ));
          Def.create sf2 (Bil.Cast (Bil.HIGH, 1, Bil.Var t2));
          Def.create zf2 (Bil.BinOp (Bil.EQ, Bil.Int (w32 0), Bil.Var t2));
        ])
  in
  check
    "L-B4: the same-comparison gate — a second cmp in the header (a dead-CF-eliminated \
     t2/OF2/SF2/ZF2 group referencing t2 := f - 5) makes the gate reject the mixed group — NO \
     decoder refinement (the cell stays top)"
    (Ws.is_top (l39_run sub4 body4));
  (* L-B5: the RECORD path — the bare-flag guard `when CF` with CF := v < 3 and v's UNIQUE def v :=
     Load[RBP-8]: the existing L3c-1 flag-state arm (not the decoder) recovers the constraint on v
     and the walk goes through the def chain to the cell. The L-A2 wiring must NOT have broken this
     path (a regression guard for the L3c-1 pins). *)
  let sub5, body5 = mk_l39b5_loop () in
  check
    "L-B5: the RECORD path (bare `when CF` with CF := v < 3, v := Load[RBP-8] unique) survives the \
     L-A2 wiring — the flag-state arm + the walk still refine the cell at RBP-8 (⊆ [0, 3))"
    (l39_bounded (l39_run sub5 body5) (w32 2));
  ())
(* --- 40. L-D2 (ora-6): the WIDE-BOUND pin — the L-D1 gate-relaxation discriminator
   ---------------------------------------------------------- L-B1 (c=3) converges BEFORE the
   fixpoint's i>10 widening (p1=p2 at the widen point -> the cell is unchanged -> max 3 < 2^31 ->
   the SLE provably_nonneg gate passes WITHOUT the L-D1 relaxation — it does NOT discriminate). The
   corpus (c=15/31/63) chain is still ascending at i=11 -> the widening fires -> the infinite CLP
   (max_elem 0xFFFFFFFF >= 2^31) -> PRE-L-D1 the SLE gate rejects (the cell stays top/wbig). L-D2 =
   the WIDE-BOUND fixture (c=63, the corpus dynamics): the counter chain crosses the i>10 widening
   threshold, so the gate-relaxed refinement (provably_nonneg_operand proving the cell non-negative
   via the seed store) is REQUIRED to bound the cell [0, 64). FAILS on the pre-L-D1 tree (the cell
   stays top); revert-proof: provably_nonneg_ operand disabled -> the pin fails (cell top); L-B1
   (c=3) stays green either way. *)
;
(  (* L-D2: the wide-bound discriminator — the L-B1 fixture with c=63 (the corpus's wide bound), seed
     0, PLUS 1 (the ascending counter), the jle compound guard. The counter chain is still ascending
     when the fixpoint's i>10 widening fires -> the widened infinite CLP -> PRE-L-D1 the SLE gate
     rejects (max_elem 0xFFFFFFFF >= 2^31 -> the cell stays top); POST-L-D1 the gate-relaxed
     refinement (provably_nonneg_operand: the RSP-anchored cell seeded with the literal 0 and only
     incremented is provably [0,∞), so the [2^31,2^32) piece of SLE(63) is unreachable and the
     [0,64) meet is sound) bounds the cell [0, 64) (max <= 63). *)
  let sub, body =
    mk_l39_loop ~seed:(w32 0) ~c:(w32 63) ~body_op:Bil.PLUS ~body_k:(w32 1)
      ~mk_cond:(fun ~cf:_ ~ofv ~sf ~zf -> l39_jle zf sf ofv)
      ~extra_header_defs:(fun _ -> [])
  in
  check
    "L-D2: the WIDE-BOUND corpus shape (c=63, ascending counter seeded 0, crossing the i>10 \
     widening threshold) — the L-D1 gate-relaxed refinement (provably_nonneg_operand proving the \
     cell non-negative via the seed store) bounds the cell at RBP-8 (⊆ [0, 64), max ≤ 63) — FAILS \
     pre-L-D1 (the SLE gate rejects the widened infinite CLP, the cell stays top)"
    (l39_bounded (l39_run sub body) (w32 63));
  ())
;
(  (* E1-1: the call-in-loop class — the header RSP must stay BOUNDED (no infinite descending drift).
     Post-L-E1 the +8 restoration (the matched-pair pop) makes the continuation RSP the TRUE
     pre-push value, so the header converges to EXACTLY {0x1000}. Pre-L-E1 the header joins {0x1000
     − 8k}/iteration and the i>10 widening turns it into the infinite DESCENDING CLP (min_elem 0 /
     max_elem 2^64−8 — the wide-window signature). *)
  let sub, header_tid, rsp = mk_e1_loop_sub () in
  let rsp_hdr = e1_rsp_at sub header_tid rsp in
  check
    "E1-1: call-in-loop RSP stability — the ON-path matched-pair +8 (the callee's ret pops exactly \
     the retaddr the caller pushed) keeps the header RSP at EXACTLY the pre-push {0x1000} \
     (bounded, no drift — FAILS pre-L-E1: the header joins {−8k}/iteration and the i>10 widening \
     makes the infinite descending CLP)"
    (Ws.equal rsp_hdr (Ws.singleton (w64 0x1000)));
  (* E1-2: the straight-line call — the continuation RSP is EXACTLY the pre-call singleton {0x2000}:
     truth, not truth − 8 ({0x1ff8}). *)
  let sub, post_tid, rsp = mk_e1_flat_sub () in
  let rsp_post = e1_rsp_at sub post_tid rsp in
  check
    "E1-2: straight-line call RSP exactness — the continuation RSP is EXACTLY the pre-call \
     singleton {0x2000} (truth, not truth−8 = {0x1ff8} — FAILS pre-L-E1)"
    (Ws.equal rsp_post (Ws.singleton (w64 0x2000)));
  ())
;
(  let sub, body = mk_l6_rbp_loop () in
  check
    "L-D6: the fix-14 blocker — RBP-anchored restriction-ON (prologue RBP := RSP + the c=63 jle \
     loop at RBP−8 + the dead epilogue RBP := mem[RSP]) — the two-pass design (L-D8): the \
     FORWARD-D rule tags the epilogue def (its rhs uses RSP ∈ D), so RBP ∈ refineable and the jcc \
     decoder's refine_cell addr gate binds the cell at RBP−8 to ⊆ [0, 64) at the BODY input — \
     FAILS with the plain liveness rule (the epilogue def untagged → the all-defs-tagged gate \
     excludes RBP → the addr gate rejects, 168/168)"
    (l39_bounded (l6_run sub body) (w32 63));
  ())
;
(  (* R2-1: the INLINE-ARITHMETIC gap closure — `when (t + 1) < 64` (the compared exp is BinOp PLUS
     of t := Load[RBP-8], NOT a bare Load/Var), ascending counter seeded 0. The guard row recovers
     [0, 64) on (t+1); the producer-op PLUS recursion (the refactor's structural-gap closure)
     refines t by the PLUS row's CIRCULAR HULL {0xFFFFFFFF} ∪ [0, 62] — the sound wrap: t = −1 also
     satisfies (t+1) < 64 — and the Load walk binds the CELL. The converged cell is that 64-element
     hull (cardn 64, no middle values), NOT the full domain (cardn 2^32): the refinement fired.
     FAILS pre-refactor (the PLUS chain unrefined -> the ascending counter widens to the full domain
     / top). Revert-proof: the BinOp-producer case made keep-env (a temporary src edit) -> R2-1
     FAILS (the cell stays top); restored -> green. *)
  let sub1, body1 =
    mk_r2_loop ~seed:(w32 0) ~seed2:None ~body_op:Bil.PLUS ~body_k:(w32 1) ~mk_cond:(fun ~t ->
        Bil.BinOp (Bil.LT, Bil.BinOp (Bil.PLUS, Bil.Var t, Bil.Int (w32 1)), Bil.Int (w32 64)))
  in
  let cell1 = r2_run sub1 body1 in
  check
    "R2-1: the INLINE-ARITHMETIC condition `(t+1) < 64` (the compared exp is BinOp PLUS of t := \
     Load[RBP-8]) — the producer-op recursion refines the (t+1) chain (guard row -> [0,64) on \
     (t+1) -> the PLUS row's circular hull {−1} ∪ [0, 62] on t -> the Var -> refine_backward -> \
     refine_cell) and the cell at RBP−8 is the 64-element hull (⊆ {−1} ∪ [0, 64); cardn 64; no \
     middle value — FAILS pre-refactor: the chain unrefined, the cell stays the full domain/top)"
    ((not (Ws.is_top cell1))
    && (not (Ws.is_bottom cell1))
    && Word.( <= ) (Ws.cardinality cell1) (Word.of_int ~width:33 64)
    && not (Ws.elem (w32 100) cell1));
  (* R2-2: the FALSE-edge soundness pin — `when ~(t < 5) goto BODY` (the taken edge = t ≥ 5). The
     two-path seed cell {3, 8} keeps the taken edge live (the 8 satisfies) while straddling the
     TRUE-edge window; the UnOp-NOT case's comparison-operand gate keeps env — the cell is NOT
     narrowed to [0, 4] (the ascending chain widens to top — "may be top/unbounded"). Revert-proof:
     the comparison-operand gate removed (making NOT recurse with {0} into the comparison) -> R2-2
     FAILS with a wrong window (the cell wrongly ⊆ [0, 4] — the live 8 dropped every iteration);
     restored -> green. *)
  let sub2, body2 =
    mk_r2_loop ~seed:(w32 3)
      ~seed2:(Some (w32 8))
      ~body_op:Bil.PLUS ~body_k:(w32 1)
      ~mk_cond:(fun ~t -> Bil.UnOp (Bil.NOT, Bil.BinOp (Bil.LT, Bil.Var t, Bil.Int (w32 5))))
  in
  let cell2 = r2_run sub2 body2 in
  check
    "R2-2: NOT-of-comparison `~(t < 5)` (the taken edge = t ≥ 5, the two-path seed cell {3, 8}) — \
     the comparison-operand keep-env gate (the FALSE-edge guard) leaves the cell UNSHARPENED by \
     the TRUE-edge row [0, 5): NOT bounded ⊆ [0, 4] (it is top/unbounded) — with the gate removed \
     the wrong window drops the live values (the cell wrongly ⊆ [0, 4])"
    (not (l39_bounded cell2 (w32 4)));
  (* R2-3: the CONST-FIRST LT flip — `when 10 < t goto BODY` (Bil.BinOp (Bil.LT, Bil.Int 10, t)),
     DECREMENTING counter seeded 20 (the taken edge must be live at the entry; the ascending chain
     would be unaffected by the [11, 2^w) meet — the 20/descending shape is the discriminator:
     unrefined, the descending chain crosses the i>10 widening and the cell goes top; refined by
     [11, 2^w), it converges inside the constraint). The flip = the ora-9 Item 1(d) generalization:
     const-first (LT, c, e) dispatches on the guard_op enum (UGT — BIL has no GT/GE constructors) ->
     t > 10 unsigned -> [11, 2^w) -> the cell ⊆ [11, 2^w) (non-top, min_elem ≥ 11). Refactor-2
     FINDING: the flip did NOT land with the refactor (the landed const-first arm,
     cbat_vsa.ml:1363-1375, is the pre-refactor EQ-only equivalence — LT/LE/SLT/SLE const-first
     remain a sound stop), so THIS PIN FAILS on the current tree by design: it is the
     spec'd-behavior proof, green only after the flip lands. Revert- proof (the complement of
     "disabling": the flip is absent, so the ADD experiment proves the pin): the const-first LT->UGT
     flip added temporarily (a src edit) -> R2-3 green; restored -> red (cell top). *)
  let sub3, body3 =
    mk_r2_loop ~seed:(w32 20) ~seed2:None ~body_op:Bil.MINUS ~body_k:(w32 1) ~mk_cond:(fun ~t ->
        Bil.BinOp (Bil.LT, Bil.Int (w32 10), Bil.Var t))
  in
  let cell3 = r2_run sub3 body3 in
  check
    "R2-3: the CONST-FIRST LT flip `10 < t` (Bil.BinOp (Bil.LT, Bil.Int 10, t)) — the flip (ora-9 \
     Item 1(d)) dispatches on the guard_op enum (UGT): t > 10 unsigned -> [11, 2^w) and the \
     DECREMENTING counter converges inside the constraint (non-top, min_elem ≥ 11) — FAILS on the \
     current tree: the landed const-first arm is the EQ-only equivalence (LT const-first is still \
     a sound stop), so the cell goes top"
    ((not (Ws.is_top cell3))
    && (not (Ws.is_bottom cell3))
    && match Ws.min_elem cell3 with Some w -> Word.( >= ) w (w32 11) | None -> false);
  (* R2-4: the NESTED-BinOp operand chain — `when (t * 8) < 512 goto BODY` (the compared exp is
     BinOp TIMES of t := Load[RBP-8]). The SOUND TIMES rule (M5): the exact slice [0, 63] applies
     only when the operand provably cannot wrap; over an unbounded operand the wrapped classes
     hull to the domain = the identity (the pre-M5 no-wrap slice was UNSOUND — a t with
     t·8 mod 2^32 ∈ [0,511] outside [0,63], e.g. t = 2^29, also satisfies the guard), so the
     row fires ONLY on a bounded operand.  Pre-inline (the forward-only solution + the M6 tag
     computation) the raw solution's counter was the only refinement source and this pin asserted
     the identity; the single-pass design (ticket 01) runs the deep walk INSIDE the fixpoint, so
     the operand IS bounded when the row evaluates and the exact slice fires — the cascade the
     ADR predicted.  The M5 no-wrap SOUNDNESS is unchanged ([operand_constraints]' [wrap_limit]
     gate). *)
  let sub4, body4 =
    mk_r2_loop ~seed:(w32 63) ~seed2:None ~body_op:Bil.PLUS ~body_k:(w32 1) ~mk_cond:(fun ~t ->
        Bil.BinOp (Bil.LT, Bil.BinOp (Bil.TIMES, Bil.Var t, Bil.Int (w32 8)), Bil.Int (w32 512)))
  in
  check
    "R2-4 (migrated, single-pass §2): the NESTED-BinOp chain `(t * 8) < 512` — the inline walk \
     bounds the operand, the exact TIMES no-wrap slice fires, and the body-IN cell is the EXACT \
     singleton {63} (the loop exits at t = 64; 63 ∈, 62 ∉, 64 ∉; non-top)"
    (let cell = r2_run sub4 body4 in
     (* MIGRATED (ticket 01, the single-pass trace partitioning,
        docs/trace-partitioning-plan.md §2/§4.3): the pin used to assert
        the cell is NOT bounded — the M5 TIMES rule's IDENTITY case over
        the WALK's unbounded operand (pre-inline the raw solution's
        counter widened past the row's no-wrap gate).  The fused design
        runs the deep walk INSIDE the fixpoint, so the operand IS bounded
        when the row evaluates (the head settles at {63,64}) and the
        EXACT no-wrap slice [0,63] fires on the TAKEN edge — the
        refinement the ADR predicted ("a refinement can cascade into
        downstream refinements within the same pass").  The result is
        EXACT: the loop exits at t = 64 (64·8 = 512 ≮ 512), so the body is
        entered only with the cell = 63 — the body-IN cell is the
        singleton {63}, strictly sounder-precise than the old top.  The M5
        no-wrap SOUNDNESS (never slicing an unbounded operand) is
        unchanged — [operand_constraints]' [wrap_limit] gate is what fired
        here. *)
     (not (Ws.is_top cell))
     && (not (Ws.is_bottom cell))
     && Ws.equal cell (Ws.singleton (w32 63)));
  ())
(* --- M5: the complete-rule pins (docs/trace-partitioning-plan.md §4) - one pin per rule the M5
   completion added: the MINUS wrap hull, the TIMES k=0 identity, the XOR-~0 bijection, the LOW cast
   in the walk, the signed division rule, and the Var-identity. Each reads the ITERATE view of the
   fixture's body edge. *)
;
(  let t = Var.create ~is_virtual:false ~fresh:false "l3c3_t" (Type.Imm 32) in
  (* M5-1: MINUS wrap — `v := t − 0xFFFFFFFF; if (v < 5)` (b = ~0): the true operand set {x | x −
     0xFFFFFFFF ∈ [0,4]} is the WRAPPED circular hull {0xFFFFFFFF, 0, 1, 2, 3} — the pre-M5 interval
     rule returned the empty set for the wrapped bound (a sound loss). *)
  let sub1, body1 =
    mk_l3c3_loop ~seed:None
      ~chain:(Bil.BinOp (Bil.MINUS, Bil.Var t, Bil.Int (w32 0xFFFFFFFF)))
      ~cmp:Bil.LT ~c:(w32 5) ~body_k:(w32 4)
  in
  let cell1 = l3c3_run sub1 body1 in
  check
    "M5-1: the MINUS wrap hull — `v := t − ~0; if (v < 5)` refines the cell to the wrapped \
     {0xFFFFFFFF, 0..3} (cardn 5; 0xFFFFFFFF ∈; 0 ∈; the wrap was handled, not emptied)"
    ((not (Ws.is_top cell1))
    && (not (Ws.is_bottom cell1))
    && Word.( = ) (Ws.cardinality cell1) (Word.of_int ~width:33 5)
    && Ws.elem (w32 0xFFFFFFFF) cell1
    && Ws.elem (w32 0) cell1
    && not (Ws.elem (w32 4) cell1));
  (* M5-2: TIMES k = 0 — `v := t * 0; if EQ(v, 0)`: v is the constant {0}, the operand unconstrained
     (the identity — the producer subtraction handles the infeasible side). *)
  let sub2, body2 =
    mk_l3c3_loop ~seed:None
      ~chain:(Bil.BinOp (Bil.TIMES, Bil.Var t, Bil.Int (w32 0)))
      ~cmp:Bil.EQ ~c:(w32 0) ~body_k:(w32 4)
  in
  let cell2 = l3c3_run sub2 body2 in
  check
    "M5-2: the TIMES k=0 rule is the identity — `v := t * 0; if EQ(v, 0)` leaves the cell \
     unconstrained (top)"
    (Ws.is_top cell2);
  (* M5-3: XOR ~0 bijection — `v := t XOR ~0; if EQ(v, 5)`: v = ~t = 5 ⟺ t = ~5 = 0xFFFFFFFA — the
     exact NOT constraint. *)
  let sub3, body3 =
    mk_l3c3_loop ~seed:None
      ~chain:(Bil.BinOp (Bil.XOR, Bil.Var t, Bil.Int (w32 0xFFFFFFFF)))
      ~cmp:Bil.EQ ~c:(w32 5) ~body_k:(w32 4)
  in
  let cell3 = l3c3_run sub3 body3 in
  check
    "M5-3: the XOR-~0 bijection — `v := t XOR ~0; if EQ(v, 5)` refines the cell to {~5} = \
     {0xFFFFFFFA} (0xFFFFFFFA ∈, 5 ∉)"
    ((not (Ws.is_top cell3)) && Ws.elem (w32 0xFFFFFFFA) cell3 && not (Ws.elem (w32 5) cell3));
  (* M5-4: the LOW cast in the walk — `v := cast LOW 8 t; if EQ(v, 5)` (v 8-bit; the chain
     references the fixture's own [l3c4_t] — the env keys vars by base name): the truncation
     pre-image [5, 5 + 2^24 − 1] = [5, 0xFFFFFF05] — the cell is bounded and carries the periodic
     class (5 + 0x100 ∈; 4 ∉). *)
  let t4 = Var.create ~is_virtual:false ~fresh:false "l3c4_t" (Type.Imm 32) in
  let sub4, body4 =
    mk_l3c4_loop ~seed:None
      ~chain:(Bil.Cast (Bil.LOW, 8, Bil.Var t4))
      ~v_w:8 ~cmp:Bil.EQ ~c:(Word.of_int ~width:8 5) ~body_k:(w32 4)
  in
  let cell4 = l3c4_run sub4 body4 in
  check
    "M5-4: the LOW-cast rule in the walk — `v := cast LOW 8 t; if EQ(v, 5)` bounds the cell to the \
     truncation hull [5, 0xFFFFFF05] (5 ∈, 5+0x100 ∈, 4 ∉)"
    ((not (Ws.is_top cell4))
    && (not (Ws.is_bottom cell4))
    && Ws.elem (w32 5) cell4
    && Ws.elem (w32 0x105) cell4
    && (not (Ws.elem (w32 4) cell4))
    && match Ws.max_elem cell4 with Some w -> Word.( <= ) w (w32 0xFFFFFF05) | None -> false);
  (* M5-5: signed division — `v := t sdiv 2; if EQ(v, −3)`: the signed rule a' = [−3·2, (−3+1)·2 −
     1] = {−6, −5} on the word circle. *)
  let sub5, body5 =
    mk_l3c3_loop ~seed:None
      ~chain:(Bil.BinOp (Bil.SDIVIDE, Bil.Var t, Bil.Int (w32 2)))
      ~cmp:Bil.EQ ~c:(w32 0xFFFFFFFD) ~body_k:(w32 4)
  in
  let cell5 = l3c3_run sub5 body5 in
  check
    "M5-5: the signed-division rule — `v := t sdiv 2; if EQ(v, −3)` refines the cell to {−6, −5} \
     (0xFFFFFFFA ∈, 0xFFFFFFFB ∈, −3 ∉)"
    ((not (Ws.is_top cell5))
    && (not (Ws.is_bottom cell5))
    && Ws.elem (w32 0xFFFFFFFA) cell5
    && Ws.elem (w32 0xFFFFFFFB) cell5
    && not (Ws.elem (w32 0xFFFFFFFD) cell5));
  (* M5-6 (MIGRATED, ticket 02 — the Phase B deletion): the Var-identity
      rule.  The OLD pin read the walk's internal LIVE SET through Phase
      B's [view.live_taken] (`f := g; if f goto exit` puts (g, {1}) in
      the guard block's live set) — an observable that died with the
      views.  The fused-world pin keeps the SAME precision claim (the
      identity row — [def_constraints]' [Bil.Var g] arm — propagates
      the constraint from v to the copied var, so the walk REACHES the
      producer behind it) and makes it observable END-TO-END like the
      M5 siblings: `v := t` (the identity) between the Load and the
      guard `if (v < 10)` — the same iterating shape as L3c3-1, so the
      window is measurable against the store-only join.
      The walk: Var (v, [0,10)) -> [reverse_def_walk]'s
      producer subtraction -> [def_constraints]' identity row ->
      (t, [0,10)) joins the live set -> t's Load def -> the CELL at
      RBP-8 meets the window.
      The body's only predecessor is the header's taken edge, so the
      body-IN cell is the iterate state's cell = [0,9] BOUNDED — the
      DISCRIMINATOR: the store-only natural join is [0,10] (the seeded
      0, the body's u = t+1 stores, the exit at t = 10), so WITHOUT the
      identity row (the walk stops at v — no pairs derived, no cell
      meet) the cell keeps the stored 10 and the max ≤ 9 assertion
      fails. *)
  let t_id = Var.create ~is_virtual:false ~fresh:false "l3c3_t" (Type.Imm 32) in
  let sub6, body6 =
    mk_l3c3_loop
      ~seed:(Some (w32 0))
      ~chain:(Bil.Var t_id)
      ~cmp:Bil.LT ~c:(w32 10) ~body_k:(w32 1)
  in
  let cell6 = l3c3_run sub6 body6 in
  check
    "M5-6: the Var-identity rule — `v := t; if (v < 10)` — the walk propagates the [0,10) window      through the identity to the loaded cell (the body-IN cell is bounded ≤ [0,9] — the store-only      join would be [0,10])"
    (l3c2_bounded cell6 (w32 9));
  ())
