(* Backward-refinement rows: L3a, L3c tiers, jcc decoder, RSP restore, RBP blocker. *)
open Bap.Std
open Bap_core_theory
open Test_common
open Test_fixtures

(* L3a: backward guard refinement. Walk fires on comparison guards; body input carries the cell. *)

(* Loop fixture: comparison guard in header, defs in header (fused walk fires first visit).
   Returns (sub, body tid). *)


let run () =
(  (* L3a-1: PLUS row — EQ(v,5) gives t' = {4}. *)
  let sub1, body1 =
    mk_l3a_loop ~cmp:Bil.EQ ~c:(w32 5)
      ~rhs:
        (Bil.BinOp
           ( Bil.PLUS,
             Bil.Var (Var.create ~is_virtual:false ~fresh:false "l3a_t" (Type.Imm 32)),
             Bil.Int (Cbat_word.to_word (w32 1)) ))
  in
  check
    "L3a-1: backward guard refinement through PLUS — the cell at RBP-8 is bounded (⊆ [0,9]; the \
     walk met {4} into the load cell)"
    (bounded_above (l3a_run_analyzed sub1 body1) (w32 9));
  (* L3a-2: MINUS row — LT(v,10) gives t' = [1,10]. *)
  let sub2, body2 =
    mk_l3a_loop ~cmp:Bil.LT ~c:(w32 10)
      ~rhs:
        (Bil.BinOp
           ( Bil.MINUS,
             Bil.Var (Var.create ~is_virtual:false ~fresh:false "l3a_t" (Type.Imm 32)),
             Bil.Int (Cbat_word.to_word (w32 1)) ))
  in
  check
    "L3a-2: backward guard refinement through MINUS — the cell at RBP-8 is bounded (⊆ [1,10]; the \
     walk met [1,10] into the load cell)"
    (bounded_above (l3a_run_analyzed sub2 body2) (w32 10));
  (* L3a-3: LSHIFT-const row — t' = [0,9]. *)
  let sub3, body3 =
    mk_l3a_loop ~cmp:Bil.LT ~c:(w32 40)
      ~rhs:
        (Bil.BinOp
           ( Bil.LSHIFT,
             Bil.Var (Var.create ~is_virtual:false ~fresh:false "l3a_t" (Type.Imm 32)),
             Bil.Int (Cbat_word.to_word (w32 2)) ))
  in
  check
    "L3a-3: backward guard refinement through LSHIFT-const — the cell at RBP-8 is bounded (⊆ \
     [0,9]; 40>>2 = 10)"
    (bounded_above (l3a_run_analyzed sub3 body3) (w32 9));
  (* L3a-4: TIMES over unbounded operand is the identity (sound). *)
  let sub4, body4 =
    mk_l3a_loop ~cmp:Bil.LT ~c:(w32 40)
      ~rhs:
        (Bil.BinOp
           ( Bil.TIMES,
             Bil.Var (Var.create ~is_virtual:false ~fresh:false "l3a_t" (Type.Imm 32)),
             Bil.Int (Cbat_word.to_word (w32 2)) ))
  in
  check
    "L3a-4: the TIMES rule over an unbounded operand is the identity (sound — the wrapped classes \
     hull to the domain; the cell is not narrowed)"
    (not (bounded_above (l3a_run_analyzed sub4 body4) (w32 19)));
  (* L3a-5: NEQ doubt — no walk, cell stays top. *)
  let sub5, body5 =
    mk_l3a_loop ~cmp:Bil.NEQ ~c:(w32 5)
      ~rhs:
        (Bil.BinOp
           ( Bil.PLUS,
             Bil.Var (Var.create ~is_virtual:false ~fresh:false "l3a_t" (Type.Imm 32)),
             Bil.Int (Cbat_word.to_word (w32 1)) ))
  in
  check
    "L3a-5: a NEQ guard is doubt (constraint_of_compare None) — no walk, the cell at RBP-8 stays \
     top"
    (Ws.is_top (l3a_run_analyzed sub5 body5));
  ())
;
(  let m = memv "l3c1_m" in
  (* L3c1-1: flag-indirected guard recovers the constraint. *)
  let sub1, body1, _ = mk_l3c1_loop ~extra_header_defs:[] in
  let sol1 = run_anchored sub1 in
  let cell1 = cell_at m (v64 "RBP") (iter_state_of sub1 sol1 body1) in
  check
    "L3c1-1: a flag-indirected guard (CF := LT(t, 10); if CF goto …) — the flag-state record \
     recovers the constraint on t and the cell at RBP-8 is bounded (⊆ [0,9])"
    (bounded_above cell1 (w32 9));
  (* L3c1-2: later def of the operand clears the record. *)
  let t = Var.create ~is_virtual:false ~fresh:false "l3c1_t" (Type.Imm 32) in
  let sub2, body2, _ = mk_l3c1_loop ~extra_header_defs:[ Def.create t (Bil.Int (Cbat_word.to_word (w32 42))) ] in
  let sol2 = run_anchored sub2 in
  let cell2 = cell_at m (v64 "RBP") (iter_state_of sub2 sol2 body2) in
  check
    "L3c1-2: a later def of the compared operand (t := 42) between the comparison and the jump \
     invalidates the flag record — no cell refinement"
    (Ws.is_top cell2);
  (* L3c1-3: non-comparison flag redefinition clears the record. *)
  let cf = v1 "l3c1_cf" in
  let sub3, body3, _ =
    mk_l3c1_loop ~extra_header_defs:[ Def.create cf (Bil.Unknown ("l3c1_bits", Type.Imm 1)) ]
  in
  let sol3 = run_anchored sub3 in
  let cell3 = cell_at m (v64 "RBP") (iter_state_of sub3 sol3 body3) in
  check
    "L3c1-3: a non-comparison redefinition of the flag (CF := unknown) invalidates the flag record \
     — no cell refinement"
    (Ws.is_top cell3);
  (* L3c1-4: multi-def base refines through the producer subtraction. *)
  let m4 = memv "l3c1_m4" in
  let rsp4 = v64 "RSP" in
  let t4 = Var.create ~is_virtual:false ~fresh:false "l3c1_t4" (Type.Imm 32) in
  let v4 = Var.create ~is_virtual:false ~fresh:false "l3c1_v4" (Type.Imm 32) in
  let addr4 = Bil.BinOp (Bil.MINUS, Bil.Var rsp4, Bil.Int (Cbat_word.to_word (w64 8))) in
  let cond4 = Bil.BinOp (Bil.LT, Bil.Var v4, Bil.Int (Cbat_word.to_word (w32 10))) in
  let e0 = blk_of_defs [] in
  let b0 =
    blk_of_defs
      [ Def.create v4 (Bil.BinOp (Bil.PLUS, Bil.Var t4, Bil.Int (Cbat_word.to_word (w32 1)))) ]
  in
  let h0 =
    blk_of_defs
      [
        Def.create t4 (Bil.Load (Bil.Var m4, addr4, LittleEndian, `r32));
        Def.create v4 (Bil.BinOp (Bil.MINUS, Bil.Var t4, Bil.Int (Cbat_word.to_word (w32 1))));
      ]
  in
  let x0 = blk_of_defs [] in
  let b_tid = Term.tid b0 in
  let h_tid = Term.tid h0 in
  let x_tid = Term.tid x0 in
  let e = with_jmps e0 [ mk_goto h_tid ] in
  let b = with_jmps b0 [ mk_goto h_tid ] in
  let h = with_jmps h0 [ mk_jmp_to b_tid cond4; mk_jmp_to x_tid (Bil.UnOp (Bil.NOT, cond4)) ] in
  let sub_b = Sub.Builder.create ~name:"l3c1_multidef" () in
  Sub.Builder.add_blk sub_b e;
  Sub.Builder.add_blk sub_b b;
  Sub.Builder.add_blk sub_b h;
  Sub.Builder.add_blk sub_b x0;
  let sub4 = Sub.Builder.result sub_b in
  let sol4 = run_anchored sub4 in
  let cell4 = cell_at m4 (v64 "RBP") (Graphlib.Std.Solution.get sol4 b_tid) in
  (* Body-IN cell is the exact taken-edge window [1,10]. *)
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
  (* L3c1-5: without ?defs the flag-state step is gated off. *)
  let sub5, _, jmp5 = mk_l3c1_loop ~extra_header_defs:[] in
  let sol5 = run_anchored sub5 in
  let hdr5 =
    match Term.enum blk_t sub5 |> Seq.to_list with [ _; _; h; _ ] -> h | _ -> assert false
  in
  let hdr_st = Graphlib.Std.Solution.get sol5 (Term.tid hdr5) in
  let res5 = Vsa.assume_jump_cond hdr_st jmp5 in
  let cell5 = cell_at m (v64 "RBP") res5 in
  check
    "L3c1-5: direct assume_jump_cond without ?defs — the flag-state refinement is gated off (no \
     cell refinement; the pre-L3c behavior)"
    (Ws.is_top cell5);
  ())
;
(  let half = w32 0x80000000 in
  let m_one = w32 0xFFFFFFFF in
  (* L3c2-1: direct SLT on seeded non-negative counter caps the cell. *)
  let sub1, body1 =
    mk_l3c2_loop ~prologue:true
      ~seed:(Some (w32 0))
      ~cmp:Bil.SLT ~c:(w32 4) ~body_op:Bil.PLUS ~body_k:(w32 1) ~flag:false
  in
  let sol1 = run_anchored sub1 in
  let cell1 = cell_at (memv "l3c2_m") (v64 "RBP") (iter_state_of sub1 sol1 body1) in
  check
    "L3c2-1: a direct SLT(t, 4) guard on a seeded non-negative counter — the signed row fires (the \
     gate passes) and the cell at RBP-8 is bounded (⊆ [0,3])"
    (bounded_above cell1 (w32 3));
  (* L3c2-2: unseeded operand refines to the two-piece rule. *)
  let sub2, body2 =
    mk_l3c2_loop ~prologue:true ~seed:None ~cmp:Bil.SLT ~c:(w32 10) ~body_op:Bil.PLUS
      ~body_k:(w32 1) ~flag:false
  in
  let sol2 = run_anchored sub2 in
  let cell2 = cell_at (memv "l3c2_m") (v64 "RBP") (iter_state_of sub2 sol2 body2) in
  check
    "L3c2-2: the two-piece SLT rule — a signed guard whose operand is not provably non-negative \
     (top) still refines the cell to the two-piece [0, c−1] ∪ [2^31, max] (the gate is removed; no \
     None stop)"
    ((not (Ws.is_top cell2))
    && match Ws.min_elem cell2 with Some w -> Cbat_word.(>=) w (w32 0) | None -> false);
  (* L3c2-3: c < 0 is one interval, no gate. *)
  let sub3, body3 =
    mk_l3c2_loop ~prologue:true ~seed:(Some half) ~cmp:Bil.SLT ~c:m_one ~body_op:Bil.MINUS
      ~body_k:(w32 1) ~flag:false
  in
  let sol3 = run_anchored sub3 in
  let cell3 = cell_at (memv "l3c2_m") (v64 "RBP") (iter_state_of sub3 sol3 body3) in
  check
    "L3c2-3: SLT(t, -1) (c < 0) is a single high interval [2^31, c-1] with no gate — the cell \
     stays in the high half (the decrements into the low half are met away)"
    (l3c2_in_high cell3 half (w32 0xFFFFFFFE));
  (* L3c2-4: flag-indirected signed guard caps the cell. *)
  let sub4, body4 =
    mk_l3c2_loop ~prologue:true
      ~seed:(Some (w32 0))
      ~cmp:Bil.SLT ~c:(w32 4) ~body_op:Bil.PLUS ~body_k:(w32 1) ~flag:true
  in
  let sol4 = run_anchored sub4 in
  let cell4 = cell_at (memv "l3c2_m") (v64 "RBP") (iter_state_of sub4 sol4 body4) in
  check
    "L3c2-4: the -O0 flag-indirected pattern (CF := SLT(t, 4); if CF goto …) — the flag-state \
     record + the signed row bound the cell at RBP-8 (⊆ [0,3])"
    (bounded_above cell4 (w32 3));
  (* L3c2-5: no prologue def needed; trace/frame derives the range. *)
  let sub5, body5 =
    mk_l3c2_loop ~prologue:false
      ~seed:(Some (w32 0))
      ~cmp:Bil.SLT ~c:(w32 4) ~body_op:Bil.PLUS ~body_k:(w32 1) ~flag:false
  in
  let sol5 = run_anchored sub5 in
  let cell5 = cell_at (memv "l3c2_m") (v64 "RBP") (iter_state_of sub5 sol5 body5) in
  check
    "L3c2-5: trace-exact cell refinement — without the RBP prologue def the cell is still bounded \
     by the SLT(4) iterate constraint"
    (bounded_above cell5 (w32 3));
  (* L3c2-6: unsigned regression covered by the LT pins. *)
  ())
;
(  let t = Var.create ~is_virtual:false ~fresh:false "l3c3_t" (Type.Imm 32) in
  (* L3c3-1: PLUS-HULL caps the cell. *)
  let sub1, body1 =
    mk_l3c3_loop
      ~seed:(Some (w32 0))
      ~chain:(Bil.BinOp (Bil.PLUS, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 1))))
      ~cmp:Bil.SLT ~c:(w32 10) ~body_k:(w32 4)
  in
  check
    "L3c3-1: the PLUS-HULL row — `v := t + 1; if SLT(v, 10)` — the wrapped hull {−1} ∪ [0,8] caps \
     the cell at RBP-8 (bounded ⊆ [0,9])"
    (bounded_above (l3c3_run sub1 body1) (w32 9));
  (* L3c3-2: TIMES over unbounded operand is the identity. *)
  let sub2, body2 =
    mk_l3c3_loop
      ~seed:(Some (w32 0))
      ~chain:(Bil.BinOp (Bil.TIMES, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 8))))
      ~cmp:Bil.SLT ~c:(w32 80) ~body_k:(w32 4)
  in
  check
    "L3c3-2: the TIMES rule over an unbounded operand is the identity (sound — the cell is not \
     bounded by the multiplier)"
    (not (bounded_above (l3c3_run sub2 body2) (w32 9)));
  (* L3c3-3: RSHIFT-const row. *)
  let sub3, body3 =
    mk_l3c3_loop
      ~seed:(Some (w32 0))
      ~chain:(Bil.BinOp (Bil.RSHIFT, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 2))))
      ~cmp:Bil.SLT ~c:(w32 10) ~body_k:(w32 8)
  in
  check
    "L3c3-3: the RSHIFT-const row — `v := t >> 2; if SLT(v, 10)` — the cell at RBP-8 is bounded (⊆ \
     [0,39]; 10<<2 = 40)"
    (bounded_above (l3c3_run sub3 body3) (w32 39));
  (* L3c3-4a: ARSHIFT with provably non-negative operand bounds the cell. *)
  let sub4a, body4a =
    mk_l3c3_loop
      ~seed:(Some (w32 0))
      ~chain:(Bil.BinOp (Bil.ARSHIFT, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 2))))
      ~cmp:Bil.SLT ~c:(w32 10) ~body_k:(w32 8)
  in
  check
    "L3c3-4a: the ARSHIFT-const row with a provably non-negative operand — the cell at RBP-8 is \
     bounded (⊆ [0,39])"
    (bounded_above (l3c3_run sub4a body4a) (w32 39));
  (* L3c3-4b: ARSHIFT on top operand is a sound stop. *)
  let sub4b, body4b =
    mk_l3c3_loop ~seed:None
      ~chain:(Bil.BinOp (Bil.ARSHIFT, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 2))))
      ~cmp:Bil.SLT ~c:(w32 10) ~body_k:(w32 4)
  in
  check
    "L3c3-4b: the ARSHIFT gate — an operand not provably non-negative (top) does NOT refine (the \
     cell stays top; sound stop)"
    (Ws.is_top (l3c3_run sub4b body4b));
  (* L3c3-5: TIMES k = 0 is a sound stop. *)
  let sub5, body5 =
    mk_l3c3_loop ~seed:None
      ~chain:(Bil.BinOp (Bil.TIMES, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 0))))
      ~cmp:Bil.SLT ~c:(w32 10) ~body_k:(w32 4)
  in
  check "L3c3-5: TIMES with k = 0 is a sound stop — the cell at RBP-8 stays top"
    (Ws.is_top (l3c3_run sub5 body5));
  (* L3c3-6: TIMES non-divisible EQ singleton is empty — no refinement. *)
  let sub6, body6 =
    mk_l3c3_loop ~seed:None
      ~chain:(Bil.BinOp (Bil.TIMES, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 8))))
      ~cmp:Bil.EQ ~c:(w32 5) ~body_k:(w32 4)
  in
  check
    "L3c3-6: TIMES with an EQ singleton {5} and k = 8 (non-divisible) — the row is empty, no \
     refinement (the cell is not a bounded set; the guard is genuinely dead — no t makes t*8 = 5 — \
     the edge is pruned)"
    (not (bounded_above (l3c3_run sub6 body6) (w32 39)));
  ())
;
(  let t = Var.create ~is_virtual:false ~fresh:false "l3c4_t" (Type.Imm 32) in
  (* L3c4-1: Var-vs-Var LT guard caps the cell. *)
  let sub1, body1 =
    mk_l3c4_vv_loop ~seed:(Some (w32 0)) ~seed2:(Some (w32 10)) ~cmp:Bil.LT ~body_k:(w32 4)
  in
  check
    "L3c4-1: the Var-vs-Var LT guard (`if (t < u) goto …`, u seeded {10}) — the interval-overlap \
     row caps the cell at RBP-8 (⊆ [0,9])"
    (bounded_above (l3c4_run sub1 body1) (w32 9));
  (* L3c4-2: TOP operand makes refinement vacuous. *)
  let sub2, body2 = mk_l3c4_vv_loop ~seed:(Some (w32 0)) ~seed2:None ~cmp:Bil.LT ~body_k:(w32 4) in
  check
    "L3c4-2: a TOP Var-vs-Var operand makes the refinement vacuous — the cell at RBP-8 stays \
     unbounded (the semantic-top class, no wrong window)"
    (not (bounded_above (l3c4_run sub2 body2) (w32 1000)));
  (* L3c4-3: DIVIDE-const row. *)
  let sub3, body3 =
    mk_l3c4_loop
      ~seed:(Some (w32 0))
      ~chain:(Bil.BinOp (Bil.DIVIDE, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 2))))
      ~v_w:32 ~cmp:Bil.SLT ~c:(w32 10) ~body_k:(w32 4)
  in
  check
    "L3c4-3: the DIVIDE-const row — `v := t / 2; if SLT(v, 10)` — the cell at RBP-8 is bounded (⊆ \
     [0,19])"
    (bounded_above (l3c4_run sub3 body3) (w32 19));
  (* L3c4-4: HIGH-extract producer row. *)
  let sub4, body4 =
    mk_l3c4_loop
      ~seed:(Some (w32 0))
      ~chain:(Bil.Cast (Bil.HIGH, 8, Bil.Var t))
      ~v_w:8 ~cmp:Bil.SLT ~c:(Cbat_word.of_int ~width:8 10) ~body_k:(w32 0x10000000)
  in
  check
    "L3c4-4: the HIGH-extract producer row — `v := cast HIGH 8 t; if SLT(v, 10)` — the cell at \
     RBP-8 is bounded (⊆ [0, 0x09FFFFFF]; the 2^28-straddling value is dropped)"
    (bounded_above (l3c4_run sub4 body4) (w32 0x09FFFFFF));
  (* L3c4-5: DIVIDE k = 0 is a sound stop. *)
  let sub5, body5 =
    mk_l3c4_loop ~seed:None
      ~chain:(Bil.BinOp (Bil.DIVIDE, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 0))))
      ~v_w:32 ~cmp:Bil.SLT ~c:(w32 10) ~body_k:(w32 4)
  in
  check "L3c4-5: DIVIDE with k = 0 is a sound stop — no refinement (the cell is not a bounded set)"
    (not (bounded_above (l3c4_run sub5 body5) (w32 39)));
  ())
;
(  let t = Var.create ~is_virtual:false ~fresh:false "l3c5_t" (Type.Imm 32) in
  let v = Var.create ~is_virtual:false ~fresh:false "l3c5_v" (Type.Imm 32) in
  (* L3c5-1: const-first guard arm normalizes to const-second. *)
  let sub1, body1 =
    mk_l3c5_loop ~seed:None ~chain:None
      ~cond:(Bil.BinOp (Bil.EQ, Bil.Int (Cbat_word.to_word (w32 10)), Bil.Var t))
      ~body_k:(w32 4)
  in
  check
    "L3c5-1: the const-first guard arm — `if (10 = t) goto …` (EQ const-first) — the cell at RBP-8 \
     is bounded (⊆ [0,10]; pinned to {10})"
    (bounded_above (l3c5_run sub1 body1) (w32 10));
  (* L3c5-2: MOD has no closed form — sound stop. *)
  let sub2, body2 =
    mk_l3c5_loop ~seed:None
      ~chain:(Some (Bil.BinOp (Bil.MOD, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 8)))))
      ~cond:(Bil.BinOp (Bil.SLT, Bil.Var v, Bil.Int (Cbat_word.to_word (w32 10))))
      ~body_k:(w32 4)
  in
  check
    "L3c5-2: the Tier-3 MOD row (periodic, no closed form) is a sound stop — no refinement (the \
     cell is not a bounded set)"
    (not (bounded_above (l3c5_run sub2 body2) (w32 39)));
  (* L3c5-3a: AND-identity row. *)
  let sub3a, body3a =
    mk_l3c5_loop
      ~seed:(Some (w32 0))
      ~chain:(Some (Bil.BinOp (Bil.AND, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 0xFFFFFFFF)))))
      ~cond:(Bil.BinOp (Bil.SLT, Bil.Var v, Bil.Int (Cbat_word.to_word (w32 10))))
      ~body_k:(w32 4)
  in
  check
    "L3c5-3a: the AND-identity row — `v := t AND ~0` (≡ t) — the cell at RBP-8 is bounded (⊆ [0,9])"
    (bounded_above (l3c5_run sub3a body3a) (w32 9));
  (* L3c5-3b: OR-identity row. *)
  let sub3b, body3b =
    mk_l3c5_loop
      ~seed:(Some (w32 0))
      ~chain:(Some (Bil.BinOp (Bil.OR, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 0)))))
      ~cond:(Bil.BinOp (Bil.SLT, Bil.Var v, Bil.Int (Cbat_word.to_word (w32 10))))
      ~body_k:(w32 4)
  in
  check
    "L3c5-3b: the OR-identity row — `v := t OR 0` (≡ t) — the cell at RBP-8 is bounded (⊆ [0,9])"
    (bounded_above (l3c5_run sub3b body3b) (w32 9));
  (* L3c5-4: Unknown cond keeps env unchanged, never asserts. *)
  let m4 = memv "l3c5_m" in
  let rsp4 = v64 "RSP" in
  let t4 = Var.create ~is_virtual:false ~fresh:false "l3c5_t" (Type.Imm 32) in
  let addr4 = Bil.BinOp (Bil.MINUS, Bil.Var rsp4, Bil.Int (Cbat_word.to_word (w64 8))) in
  let e0 = blk_of_defs [] in
  let h0 =
    blk_of_defs [ Def.create t4 (Bil.Load (Bil.Var m4, addr4, LittleEndian, `r32)) ]
  in
  let x0 = blk_of_defs [] in
  let h_tid = Term.tid h0 in
  let x_tid = Term.tid x0 in
  let sub_b = Sub.Builder.create ~name:"l3c5_unknown" () in
  Sub.Builder.add_blk sub_b (with_jmps e0 [ mk_goto h_tid ]);
  Sub.Builder.add_blk sub_b
    (with_jmps h0 [ mk_jmp_to x_tid (Bil.Unknown ("l3c5_unknown", Type.Imm 1)) ]);
  Sub.Builder.add_blk sub_b x0;
  let sub4 = Sub.Builder.result sub_b in
  let sol4 = run_anchored sub4 in
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
;
(  (* S-1: traverse shape collapses to ≤ 3 cells. *)
  let sub1, body1, hdr1 = mk_l3b1_loop () in
  let sol1 = run_anchored sub1 in
  let st1 = Graphlib.Std.Solution.get sol1 body1 in
  check
    "S-1a: the traverse shape (fixture F, the seeded RMW counter) collapses to <= 3 cells in the \
     solution state (pre-fix the [RSP-8] point-key pile was 16-17 — the restored equal-lower hull \
     union)"
    (l3b_cells_of (memv "l3b1_m") st1 <= 3);
  (* Exit IN-state is the fallthrough view; body IN-state the iterate view. *)
  let exit1 =
    match Term.enum blk_t sub1 |> Seq.to_list with
    | [ _; _; _; e ] -> e
    | _ -> failwith "S-1: fixture block layout changed"
  in
  let icell = cell_at (memv "l3b1_m") (v64 "RSP") (Graphlib.Std.Solution.get sol1 body1) in
  let ecell = cell_at (memv "l3b1_m") (v64 "RSP") (Graphlib.Std.Solution.get sol1 (Term.tid exit1)) in
  check
    "S-1b: the partition — the iterate view's cell is the loop-body values (⊆ [0,7], non-top) and \
     the exit view's cell carries the exit-iteration value (8 survives)"
    ((not (Ws.is_top icell))
    && (not (Ws.is_bottom icell))
    && (match Ws.max_elem icell with Some w -> Cbat_word.(<=) w (w32 7) | None -> false)
    && (not (Ws.is_top ecell))
    && Ws.elem (w32 8) ecell);
  (* S-4: +1-adjacent equal-value cells merge to one hull. *)
  let sub4, merge4 = mk_l3b4_diamond () in
  let sol4 = run_anchored sub4 in
  let st4 = Graphlib.Std.Solution.get sol4 merge4 in
  check
    "S-4a: two +1-adjacent equal-value cells ([RSP-8] and [RSP-7], both {7}) through ONE merge \
     become a SINGLE cell (the +1-adjacent arm, not shadowed by the equal-lower arm)"
    (l3b_cells_of (memv "l3b4_m") st4 = 1);
  ())
;
(  let rsp = v64 "RSP" in
  let rdi = v64 "RDI" in
  let entry0 = blk_of_defs [] in
  let blk0 = blk_of_defs [ Def.create rdi (Bil.Int (Cbat_word.to_word (w64 42))) ] in
  let cont0 = blk_of_defs [] in
  let blk_tid = Term.tid blk0 in
  let cont_tid = Term.tid cont0 in
  (* Interrupt edge: return tid ignored by the arm. *)
  let entry = with_jmps entry0 [ mk_goto blk_tid ] in
  let blk =
    with_jmps blk0 [ Jmp.create (Int (0x80, cont_tid)); mk_goto cont_tid ]
  in
  let sub_b = Sub.Builder.create ~name:"l37_intr" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b blk;
  Sub.Builder.add_blk sub_b cont0;
  let sub = Sub.Builder.result sub_b in
  let sol = run_anchored sub in
  let cont_st = Graphlib.Std.Solution.get sol cont_tid in
  check
    "B-1: an interrupt edge is an unknown external callee — the continuation keeps the RSP anchor \
     ({0}) and the caller-saved rdi is topped (no AI.top degradation)"
    (Ws.equal (AI.find_word 64 cont_st rsp) (Ws.singleton (w64 0))
    && Ws.is_top (AI.find_word 64 cont_st rdi));
  ())
;
(  (* L-B1: jle corpus shape — decoder emits SLE. *)
  let sub1, body1 =
    mk_l39_loop ~seed:(w32 0) ~c:(w32 3) ~body_op:Bil.PLUS ~body_k:(w32 1)
      ~mk_cond:(fun ~cf:_ ~ofv ~sf ~zf -> l39_jle zf sf ofv)
      ~extra_header_defs:(fun _ -> [])
  in
  check
    "L-B1: the exact -O0 corpus block (t := Load-3; CF/SF/OF/ZF defs; the jle compound guard `ZF | \
     (SF|OF) & ~(SF&OF)`) — the jcc decoder recovers the loop-counter constraint (SLE, c=3, gated) \
     and the cell at RBP-8 is bounded (⊆ [0, 4))"
    (bounded_above (l39_run sub1 body1) (w32 3));
  (* L-B2: jl shape — decoder emits SLT. *)
  let sub2, body2 =
    mk_l39_loop ~seed:(w32 0) ~c:(w32 3) ~body_op:Bil.PLUS ~body_k:(w32 1)
      ~mk_cond:(fun ~cf:_ ~ofv ~sf ~zf:_ -> l39_jl sf ofv)
      ~extra_header_defs:(fun _ -> [])
  in
  check
    "L-B2: the jl compound guard `(SF|OF) & ~(SF&OF)` (signed e < c — excludes equality) — the \
     decoder emits SLT and the cell at RBP-8 is bounded (⊆ [0, 3))"
    (bounded_above (l39_run sub2 body2) (w32 2));
  (* L-B3: ja shape — decoder emits UGT; decrementing counter converges. *)
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
    && match Ws.min_elem cell3 with Some w -> Cbat_word.(>=) w (w32 4) | None -> false);
  (* L-B4: second cmp makes the gate reject the mixed group. *)
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
        let addr2 = Bil.BinOp (Bil.MINUS, Bil.Var rsp2, Bil.Int (Cbat_word.to_word (w64 16))) in
        let f_load = Bil.Load (Bil.Var m, addr2, LittleEndian, `r32) in
        [
          Def.create f f_load;
          Def.create t2 (Bil.BinOp (Bil.MINUS, f_load, Bil.Int (Cbat_word.to_word (w32 5))));
          Def.create of2
            (Bil.Cast
               ( Bil.HIGH,
                 1,
                 Bil.BinOp
                   ( Bil.AND,
                     Bil.BinOp (Bil.XOR, Bil.Var f, Bil.Int (Cbat_word.to_word (w32 5))),
                     Bil.BinOp (Bil.XOR, Bil.Var f, Bil.Var t2) ) ));
          Def.create sf2 (Bil.Cast (Bil.HIGH, 1, Bil.Var t2));
          Def.create zf2 (Bil.BinOp (Bil.EQ, Bil.Int (Cbat_word.to_word (w32 0)), Bil.Var t2));
        ])
  in
  check
    "L-B4: the same-comparison gate — a second cmp in the header (a dead-CF-eliminated \
     t2/OF2/SF2/ZF2 group referencing t2 := f - 5) makes the gate reject the mixed group — NO \
     decoder refinement (the cell stays top)"
    (Ws.is_top (l39_run sub4 body4));
  (* L-B5: record path survives (flag-state arm regression guard). *)
  let sub5, body5 = mk_l39b5_loop () in
  check
    "L-B5: the RECORD path (bare `when CF` with CF := v < 3, v := Load[RBP-8] unique) survives the \
     L-A2 wiring — the flag-state arm + the walk still refine the cell at RBP-8 (⊆ [0, 3))"
    (bounded_above (l39_run sub5 body5) (w32 2));
  ())
(* L-D2: wide-bound pin — counter crosses widening before converging. *)
;
(  (* L-D2: c=63 ascending counter needs the relaxed gate. *)
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
    (bounded_above (l39_run sub body) (w32 63));
  ())
;
(  (* E1-1: call-in-loop header RSP stays exactly {0x1000}. *)
  let sub, header_tid, rsp = mk_e1_loop_sub () in
  let rsp_hdr = e1_rsp_at sub header_tid rsp in
  check
    "E1-1: call-in-loop RSP stability — the ON-path matched-pair +8 (the callee's ret pops exactly \
     the retaddr the caller pushed) keeps the header RSP at EXACTLY the pre-push {0x1000} \
     (bounded, no drift — FAILS pre-L-E1: the header joins {−8k}/iteration and the i>10 widening \
     makes the infinite descending CLP)"
    (Ws.equal rsp_hdr (Ws.singleton (w64 0x1000)));
  (* E1-2: straight-line continuation RSP is exactly {0x2000}. *)
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
    "L-D6 (gate-free, spec §2.1): the RBP-anchored loop (prologue RBP := RSP + the c=63 jle \
     loop at RBP−8 + the dead epilogue RBP := mem[RSP]) — every def is denoted, so the jcc \
     decoder's cell meet binds the cell at RBP−8 to ⊆ [0, 64) at the BODY input"
    (bounded_above (l6_run sub body) (w32 63));
  ())
;
(  (* R2-1: inline-arithmetic chain refines to the 64-element hull. *)
  let sub1, body1 =
    mk_r2_loop ~seed:(w32 0) ~seed2:None ~body_op:Bil.PLUS ~body_k:(w32 1) ~mk_cond:(fun ~t ->
        Bil.BinOp (Bil.LT, Bil.BinOp (Bil.PLUS, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 1))), Bil.Int (Cbat_word.to_word (w32 64))))
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
    && Cbat_word.(<=) (Ws.cardinality cell1) (Cbat_word.of_int ~width:33 64)
    && not (Ws.elem (w32 100) cell1));
  (* R2-2: NOT-edge keeps env — cell not narrowed to TRUE-edge window. *)
  let sub2, body2 =
    mk_r2_loop ~seed:(w32 3)
      ~seed2:(Some (w32 8))
      ~body_op:Bil.PLUS ~body_k:(w32 1)
      ~mk_cond:(fun ~t -> Bil.UnOp (Bil.NOT, Bil.BinOp (Bil.LT, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 5)))))
  in
  let cell2 = r2_run sub2 body2 in
  check
    "R2-2: NOT-of-comparison `~(t < 5)` (the taken edge = t ≥ 5, the two-path seed cell {3, 8}) — \
     the comparison-operand keep-env gate (the FALSE-edge guard) leaves the cell UNSHARPENED by \
     the TRUE-edge row [0, 5): NOT bounded ⊆ [0, 4] (it is top/unbounded) — with the gate removed \
     the wrong window drops the live values (the cell wrongly ⊆ [0, 4])"
    (not (bounded_above cell2 (w32 4)));
  (* R2-3: const-first LT flip — decrementing counter converges in [11, 2^w). *)
  let sub3, body3 =
    mk_r2_loop ~seed:(w32 20) ~seed2:None ~body_op:Bil.MINUS ~body_k:(w32 1) ~mk_cond:(fun ~t ->
        Bil.BinOp (Bil.LT, Bil.Int (Cbat_word.to_word (w32 10)), Bil.Var t))
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
    && match Ws.min_elem cell3 with Some w -> Cbat_word.(>=) w (w32 11) | None -> false);
  (* R2-4: nested TIMES chain — inline walk bounds the operand, exact slice fires. *)
  let sub4, body4 =
    mk_r2_loop ~seed:(w32 63) ~seed2:None ~body_op:Bil.PLUS ~body_k:(w32 1) ~mk_cond:(fun ~t ->
        Bil.BinOp (Bil.LT, Bil.BinOp (Bil.TIMES, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 8))), Bil.Int (Cbat_word.to_word (w32 512))))
  in
  check
    "R2-4 (migrated, single-pass §2): the NESTED-BinOp chain `(t * 8) < 512` — the inline walk \
     bounds the operand, the exact TIMES no-wrap slice fires, and the body-IN cell is the EXACT \
     singleton {63} (the loop exits at t = 64; 63 ∈, 62 ∉, 64 ∉; non-top)"
    (let cell = r2_run sub4 body4 in
     (* Body-IN cell is the exact singleton {63}. *)
     (not (Ws.is_top cell))
     && (not (Ws.is_bottom cell))
     && Ws.equal cell (Ws.singleton (w32 63)));
  ())
(* M5: complete-rule pins — one per rule. *)
;
(  let t = Var.create ~is_virtual:false ~fresh:false "l3c3_t" (Type.Imm 32) in
  (* M5-1: MINUS wrap hull. *)
  let sub1, body1 =
    mk_l3c3_loop ~seed:None
      ~chain:(Bil.BinOp (Bil.MINUS, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 0xFFFFFFFF))))
      ~cmp:Bil.LT ~c:(w32 5) ~body_k:(w32 4)
  in
  let cell1 = l3c3_run sub1 body1 in
  check
    "M5-1: the MINUS wrap hull — `v := t − ~0; if (v < 5)` refines the cell to the wrapped \
     {0xFFFFFFFF, 0..3} (cardn 5; 0xFFFFFFFF ∈; 0 ∈; the wrap was handled, not emptied)"
    ((not (Ws.is_top cell1))
    && (not (Ws.is_bottom cell1))
    && Cbat_word.(=) (Ws.cardinality cell1) (Cbat_word.of_int ~width:33 5)
    && Ws.elem (w32 0xFFFFFFFF) cell1
    && Ws.elem (w32 0) cell1
    && not (Ws.elem (w32 4) cell1));
  (* M5-2: TIMES k = 0 is the identity. *)
  let sub2, body2 =
    mk_l3c3_loop ~seed:None
      ~chain:(Bil.BinOp (Bil.TIMES, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 0))))
      ~cmp:Bil.EQ ~c:(w32 0) ~body_k:(w32 4)
  in
  let cell2 = l3c3_run sub2 body2 in
  check
    "M5-2: the TIMES k=0 rule is the identity — `v := t * 0; if EQ(v, 0)` leaves the cell \
     unconstrained (top)"
    (Ws.is_top cell2);
  (* M5-3: XOR-~0 bijection. *)
  let sub3, body3 =
    mk_l3c3_loop ~seed:None
      ~chain:(Bil.BinOp (Bil.XOR, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 0xFFFFFFFF))))
      ~cmp:Bil.EQ ~c:(w32 5) ~body_k:(w32 4)
  in
  let cell3 = l3c3_run sub3 body3 in
  check
    "M5-3: the XOR-~0 bijection — `v := t XOR ~0; if EQ(v, 5)` refines the cell to {~5} = \
     {0xFFFFFFFA} (0xFFFFFFFA ∈, 5 ∉)"
    ((not (Ws.is_top cell3)) && Ws.elem (w32 0xFFFFFFFA) cell3 && not (Ws.elem (w32 5) cell3));
  (* M5-4: LOW cast in the walk — truncation hull. *)
  let t4 = Var.create ~is_virtual:false ~fresh:false "l3c4_t" (Type.Imm 32) in
  let sub4, body4 =
    mk_l3c4_loop ~seed:None
      ~chain:(Bil.Cast (Bil.LOW, 8, Bil.Var t4))
      ~v_w:8 ~cmp:Bil.EQ ~c:(Cbat_word.of_int ~width:8 5) ~body_k:(w32 4)
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
    && match Ws.max_elem cell4 with Some w -> Cbat_word.(<=) w (w32 0xFFFFFF05) | None -> false);
  (* M5-5: signed-division rule. *)
  let sub5, body5 =
    mk_l3c3_loop ~seed:None
      ~chain:(Bil.BinOp (Bil.SDIVIDE, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 2))))
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
  (* M5-6: Var-identity row propagates through the copy. *)
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
    (bounded_above cell6 (w32 9));
  ())
