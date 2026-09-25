(* Backward-refinement and inverse-denotation pins.  One Alcotest group per
   pin; each pin builds its own fixture, so no state crosses pins.  The first
   block of pins is the backward lane (the guard/flag/row walks); the second
   is the inverse denote's leaf facts (the load cell meet and the guard
   operand windows). *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

(* The inverse-denote fixtures' interval builders (64-bit and 32-bit). *)
let bk_iv64 ~lo ~hi =
  Ws.of_clp
    (Clp.create ~width:64 ~step:(w64 1)
       ~cardn:(Cbat_word.of_int ~width:65 (hi - lo + 1)) (w64 lo))

let s_r32 = Cbat_word.of_int ~width:32

let bk_iv32 ~lo ~hi =
  Ws.of_clp
    (Clp.create ~width:32 ~step:(s_r32 1)
       ~cardn:(Cbat_word.of_int ~width:33 (hi - lo + 1)) (s_r32 lo))

(* The load-cell fixture: one memory var keyed by absolute offset words. *)
let t_rsp = Var.create ~is_virtual:false ~fresh:false "RSP" (Type.Imm 64)
let t_rbp = Var.create ~is_virtual:false ~fresh:false "RBP" (Type.Imm 64)
let t_idx = Var.create ~is_virtual:true ~fresh:false "t_idx" (Type.Imm 64)
let t_m = Var.create ~is_virtual:false ~fresh:false "t_m" (Type.Mem (`r64, `r8))

let t_mem_idx = { Mem.addr_width = 64; Mem.addressable_width = 8 }

let t_key_of (ws : Ws.t) =
  match Mem.Key.of_wordset ws with Some k -> k | None -> failwith "key_of"

let t_add_cell st addr_ws data =
  let mv = AI.find_memory t_mem_idx st t_m in
  let mv' =
    Mem.add mv ~key:(t_key_of addr_ws) ~data:(Mem.Val.create data LittleEndian)
  in
  AI.add_memory st ~key:t_m ~data:mv'

let t_cell_at st addr_ws =
  let mv = AI.find_memory t_mem_idx st t_m in
  Mem.Val.data (Mem.find (64, LittleEndian) mv (t_key_of addr_ws))

let t_load_exp addr = Bil.Load (Bil.Var t_m, addr, LittleEndian, `r64)

(* The guard-window fixture: the virtual compared vars and the mem var. *)
let s_t = Var.create ~is_virtual:true ~fresh:false "s_t" (Type.Imm 32)
let s_u = Var.create ~is_virtual:true ~fresh:false "s_u" (Type.Imm 32)
let s_m = Var.create ~is_virtual:false ~fresh:false "s_m" (Type.Mem (`r32, `r8))

let s_w32_of_env env v = AI.find_word 32 env (Var.base v)

let s_window_of env cond v =
  AI.find_word 32
    (Vsa.Test_seam.constrain_operands ~landmarks:(Cbat_landmarks.create ()) ~env cond
       (Ws.singleton (Cbat_word.of_word Word.b1)))
    (Var.base v)

let tests : unit Alcotest.test list =
  [
    (* L3a: backward guard refinement through the producer rows. *)
    pin "BK-01"
      "backward guard refinement through PLUS — the cell at RBP-8 is bounded \
       (⊆ [0,9]; the walk met {4} into the load cell)"
      (fun () ->
        let sub1, body1 =
          mk_l3a_loop ~cmp:Bil.EQ ~c:(w32 5)
            ~rhs:
              (Bil.BinOp
                 ( Bil.PLUS,
                   Bil.Var (Var.create ~is_virtual:false ~fresh:false "l3a_t" (Type.Imm 32)),
                   Bil.Int (Cbat_word.to_word (w32 1)) ))
        in
        check "BK-01" (bounded_above (l3a_run_analyzed sub1 body1) (w32 9)));

    pin "BK-02"
      "backward guard refinement through MINUS — the cell at RBP-8 is bounded \
       (⊆ [1,10]; the walk met [1,10] into the load cell)"
      (fun () ->
        let sub2, body2 =
          mk_l3a_loop ~cmp:Bil.LT ~c:(w32 10)
            ~rhs:
              (Bil.BinOp
                 ( Bil.MINUS,
                   Bil.Var (Var.create ~is_virtual:false ~fresh:false "l3a_t" (Type.Imm 32)),
                   Bil.Int (Cbat_word.to_word (w32 1)) ))
        in
        check "BK-02"
          (let v = l3a_run_analyzed sub2 body2 in
           bounded_above v (w32 10)));

    pin "BK-03"
      "backward guard refinement through LSHIFT-const — the cell at RBP-8 is \
       bounded (⊆ [0,9]; 40>>2 = 10)"
      (fun () ->
        let sub3, body3 =
          mk_l3a_loop ~cmp:Bil.LT ~c:(w32 40)
            ~rhs:
              (Bil.BinOp
                 ( Bil.LSHIFT,
                   Bil.Var (Var.create ~is_virtual:false ~fresh:false "l3a_t" (Type.Imm 32)),
                   Bil.Int (Cbat_word.to_word (w32 2)) ))
        in
        check "BK-03" (bounded_above (l3a_run_analyzed sub3 body3) (w32 9)));

    pin "BK-04"
      "the TIMES rule over an unbounded operand is the identity (sound — the \
       wrapped classes hull to the domain; the cell is not narrowed)"
      (fun () ->
        let sub4, body4 =
          mk_l3a_loop ~cmp:Bil.LT ~c:(w32 40)
            ~rhs:
              (Bil.BinOp
                 ( Bil.TIMES,
                   Bil.Var (Var.create ~is_virtual:false ~fresh:false "l3a_t" (Type.Imm 32)),
                   Bil.Int (Cbat_word.to_word (w32 2)) ))
        in
        check "BK-04" (not (bounded_above (l3a_run_analyzed sub4 body4) (w32 19))));

    pin "BK-05"
      "a NEQ guard is doubt (constraint_of_compare None) — no walk, the cell \
       at RBP-8 stays top"
      (fun () ->
        let sub5, body5 =
          mk_l3a_loop ~cmp:Bil.NEQ ~c:(w32 5)
            ~rhs:
              (Bil.BinOp
                 ( Bil.PLUS,
                   Bil.Var (Var.create ~is_virtual:false ~fresh:false "l3a_t" (Type.Imm 32)),
                   Bil.Int (Cbat_word.to_word (w32 1)) ))
        in
        check "BK-05" (Ws.is_top (l3a_run_analyzed sub5 body5)));

    (* L3c1: the flag-state mechanism. *)
    pin "BK-06"
      "a flag-indirected guard (CF := LT(t, 10); if CF goto …) — the flag-state \
       record recovers the constraint on t and the cell at RBP-8 is bounded \
       (⊆ [0,9])"
      (fun () ->
        let m = memv "l3c1_m" in
        let sub1, body1, _ = mk_l3c1_loop ~extra_header_defs:[] ~pre_cf_defs:[] in
        let sol1 = run_anchored sub1 in
        let cell1 = cell_at m (v64 "RBP") (iter_state_of sub1 sol1 body1) in
        check "BK-06" (bounded_above cell1 (w32 9)));

    pin "BK-07"
      "a redefinition of the compared operand (t := 42) between the load and \
       the comparison makes the guard constant-false — the taken edge is dead \
       and the body's state is empty (the cell reads bottom; no refinement of a \
       dead path)"
      (fun () ->
        let m = memv "l3c1_m" in
        let t = Var.create ~is_virtual:false ~fresh:false "l3c1_t" (Type.Imm 32) in
        let sub2, body2, _ =
          mk_l3c1_loop ~extra_header_defs:[]
            ~pre_cf_defs:[ Def.create t (Bil.Int (Cbat_word.to_word (w32 42))) ]
        in
        let sol2 = run_anchored sub2 in
        let cell2 = cell_at m (v64 "RBP") (iter_state_of sub2 sol2 body2) in
        check "BK-07" (Ws.is_bottom cell2));

    pin "BK-08"
      "a non-comparison redefinition of the flag (CF := unknown) invalidates \
       the flag record — no cell refinement"
      (fun () ->
        let m = memv "l3c1_m" in
        let cf = v1 "l3c1_cf" in
        let sub3, body3, _ =
          mk_l3c1_loop
            ~extra_header_defs:[ Def.create cf (Bil.Unknown ("l3c1_bits", Type.Imm 1)) ]
            ~pre_cf_defs:[]
        in
        let sol3 = run_anchored sub3 in
        let cell3 = cell_at m (v64 "RBP") (iter_state_of sub3 sol3 body3) in
        check "BK-08" (Ws.is_top cell3));

    pin "BK-09"
      "the multi-def base refines through the per-block producer subtraction — \
       the body-IN cell is the EXACT taken-edge window [1,10] (1 ∈, 10 ∈, 0 ∉, \
       11 ∉; non-top)"
      (fun () ->
        let m4 = memv "l3c1_m4" in
        let rsp4 = v64 "RSP" in
        let t4 = Var.create ~is_virtual:false ~fresh:false "l3c1_t4" (Type.Imm 32) in
        let v4 = Var.create ~is_virtual:false ~fresh:false "l3c1_v4" (Type.Imm 32) in
        let addr4 =
          Bil.BinOp (Bil.MINUS, Bil.Var rsp4, Bil.Int (Cbat_word.to_word (w64 8)))
        in
        let cond4 =
          Bil.BinOp (Bil.LT, Bil.Var v4, Bil.Int (Cbat_word.to_word (w32 10)))
        in
        let sub4, tids4 =
          sub_of "l3c1_multidef"
            [ [], [ (2, mk_goto) ];
              [ Def.create v4 (Bil.BinOp (Bil.PLUS, Bil.Var t4, Bil.Int (Cbat_word.to_word (w32 1)))) ],
              [ (2, mk_goto) ];
              [ Def.create t4 (Bil.Load (Bil.Var m4, addr4, LittleEndian, `r32));
                Def.create v4 (Bil.BinOp (Bil.MINUS, Bil.Var t4, Bil.Int (Cbat_word.to_word (w32 1)))) ],
              [ (1, fun t -> mk_jmp_to t cond4);
                (3, fun t -> mk_jmp_to t (Bil.UnOp (Bil.NOT, cond4))) ];
              [], [] ]
        in
        let b_tid = tids4.(1) in
        let sol4 = run_anchored sub4 in
        let cell4 =
          cell_at m4 (v64 "RBP") (Graphlib.Std.Solution.get sol4 b_tid)
        in
        check "BK-09"
          ((not (Ws.is_top cell4))
          && (not (Ws.is_bottom cell4))
          && Ws.elem (w32 1) cell4
          && Ws.elem (w32 10) cell4
          && not (Ws.elem (w32 0) cell4)
          && not (Ws.elem (w32 11) cell4)));

    pin "BK-10"
      "direct constrain_edge — the flag-state refinement is gated off (no cell \
       refinement)"
      (fun () ->
        let m = memv "l3c1_m" in
        let sub5, _, jmp5 = mk_l3c1_loop ~extra_header_defs:[] ~pre_cf_defs:[] in
        let sol5 = run_anchored sub5 in
        let hdr5 =
          match Term.enum blk_t sub5 |> Seq.to_list with
          | [ _; _; h; _ ] -> h
          | _ -> assert false
        in
        let hdr_st = Graphlib.Std.Solution.get sol5 (Term.tid hdr5) in
        let res5 = Vsa.Test_seam.constrain_edge ~landmarks:(Cbat_landmarks.create ()) ~env:hdr_st (Jmp.cond jmp5) in
        let cell5 = cell_at m (v64 "RBP") res5 in
        check "BK-10" (Ws.is_top cell5));

    (* L3c2: the signed comparison rows. *)
    pin "BK-11"
      "a direct SLT(t, 4) guard on a seeded non-negative counter — the signed \
       row fires (the gate passes) and the cell at RBP-8 is bounded (⊆ [0,3])"
      (fun () ->
        let sub1, body1 =
          mk_l3c2_loop ~prologue:true ~seed:(Some (w32 0)) ~cmp:Bil.SLT
            ~c:(w32 4) ~body_op:Bil.PLUS ~body_k:(w32 1) ~flag:false
        in
        let sol1 = run_anchored sub1 in
        let cell1 =
          cell_at (memv "l3c2_m") (v64 "RBP") (iter_state_of sub1 sol1 body1)
        in
        check "BK-11" (bounded_above cell1 (w32 3)));

    pin "BK-12"
      "the two-piece SLT rule — a signed guard whose operand is not provably \
       non-negative (top) still refines the cell to the two-piece [0, c−1] ∪ \
       [2^31, max]"
      (fun () ->
        let sub2, body2 =
          mk_l3c2_loop ~prologue:true ~seed:None ~cmp:Bil.SLT ~c:(w32 10)
            ~body_op:Bil.PLUS ~body_k:(w32 1) ~flag:false
        in
        let sol2 = run_anchored sub2 in
        let cell2 =
          cell_at (memv "l3c2_m") (v64 "RBP") (iter_state_of sub2 sol2 body2)
        in
        check "BK-12"
          ((not (Ws.is_top cell2))
          && Base.Option.filter (Ws.min_elem cell2)
               ~f:(fun w -> Cbat_word.(>=) w (w32 0))
             |> Option.is_some));

    pin "BK-13"
      "SLT(t, -1) (c < 0) is a single high interval [2^31, c-1] with no gate — \
       the cell stays in the high half (the decrements into the low half are \
       met away)"
      (fun () ->
        let half = w32 0x80000000 in
        let m_one = w32 0xFFFFFFFF in
        let sub3, body3 =
          mk_l3c2_loop ~prologue:true ~seed:(Some half) ~cmp:Bil.SLT ~c:m_one
            ~body_op:Bil.MINUS ~body_k:(w32 1) ~flag:false
        in
        let sol3 = run_anchored sub3 in
        let cell3 =
          cell_at (memv "l3c2_m") (v64 "RBP") (iter_state_of sub3 sol3 body3)
        in
        check "BK-13" (l3c2_in_high cell3 half (w32 0xFFFFFFFE)));

    pin "BK-14"
      "the -O0 flag-indirected pattern (CF := SLT(t, 4); if CF goto …) — the \
       flag-state record + the signed row bound the cell at RBP-8 (⊆ [0,3])"
      (fun () ->
        let sub4, body4 =
          mk_l3c2_loop ~prologue:true ~seed:(Some (w32 0)) ~cmp:Bil.SLT
            ~c:(w32 4) ~body_op:Bil.PLUS ~body_k:(w32 1) ~flag:true
        in
        let sol4 = run_anchored sub4 in
        let cell4 =
          cell_at (memv "l3c2_m") (v64 "RBP") (iter_state_of sub4 sol4 body4)
        in
        check "BK-14" (bounded_above cell4 (w32 3)));

    pin "BK-15"
      "trace-exact cell refinement — without the RBP prologue def the cell is \
       still bounded by the SLT(4) iterate constraint"
      (fun () ->
        let sub5, body5 =
          mk_l3c2_loop ~prologue:false ~seed:(Some (w32 0)) ~cmp:Bil.SLT
            ~c:(w32 4) ~body_op:Bil.PLUS ~body_k:(w32 1) ~flag:false
        in
        let sol5 = run_anchored sub5 in
        let cell5 =
          cell_at (memv "l3c2_m") (v64 "RBP") (iter_state_of sub5 sol5 body5)
        in
        check "BK-15" (bounded_above cell5 (w32 3)));

    (* L3c3: the PLUS-hull, TIMES-const, RSHIFT/ARSHIFT-const rows. *)
    pin "BK-16"
      "the PLUS-HULL row — `v := t + 1; if SLT(v, 10)` — the wrapped hull \
       {−1} ∪ [0,8] caps the cell at RBP-8 (bounded ⊆ [0,9])"
      (fun () ->
        let t = Var.create ~is_virtual:false ~fresh:false "l3c3_t" (Type.Imm 32) in
        let sub1, body1 =
          mk_l3c3_loop ~seed:(Some (w32 0))
            ~chain:(Bil.BinOp (Bil.PLUS, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 1))))
            ~cmp:Bil.SLT ~c:(w32 10) ~body_k:(w32 4)
        in
        check "BK-16"
          (let v = l3c3_run sub1 body1 in
           bounded_above v (w32 9)));

    pin "BK-17"
      "the TIMES rule over an unbounded operand is the identity (sound — the \
       cell is not bounded by the multiplier)"
      (fun () ->
        let t = Var.create ~is_virtual:false ~fresh:false "l3c3_t" (Type.Imm 32) in
        let sub2, body2 =
          mk_l3c3_loop ~seed:None
            ~chain:(Bil.BinOp (Bil.TIMES, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 8))))
            ~cmp:Bil.SLT ~c:(w32 80) ~body_k:(w32 4)
        in
        check "BK-17" (not (bounded_above (l3c3_run sub2 body2) (w32 9))));

    pin "BK-18"
      "the seeded operand is bounded by the guard's signed row, so the TIMES \
       pre-image applies: the cell at RBP-8 is [0..9] (8t <s 80 over t ∈ [0..9])"
      (fun () ->
        let t = Var.create ~is_virtual:false ~fresh:false "l3c3_t" (Type.Imm 32) in
        let sub2b, body2b =
          mk_l3c3_loop ~seed:(Some (w32 0))
            ~chain:(Bil.BinOp (Bil.TIMES, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 8))))
            ~cmp:Bil.SLT ~c:(w32 80) ~body_k:(w32 4)
        in
        check "BK-18"
          (let ws = l3c3_run sub2b body2b in
           bounded_above ws (w32 9)
           && Option.is_some
                (Base.Option.filter (Ws.min_elem ws)
                   ~f:(fun lo -> Cbat_word.equal lo (w32 0)))));

    pin "BK-19"
      "the RSHIFT-const row — `v := t >> 2; if SLT(v, 10)` — the cell at RBP-8 \
       is bounded (⊆ [0,39]; 10<<2 = 40)"
      (fun () ->
        let t = Var.create ~is_virtual:false ~fresh:false "l3c3_t" (Type.Imm 32) in
        let sub3, body3 =
          mk_l3c3_loop ~seed:(Some (w32 0))
            ~chain:(Bil.BinOp (Bil.RSHIFT, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 2))))
            ~cmp:Bil.SLT ~c:(w32 10) ~body_k:(w32 8)
        in
        check "BK-19" (bounded_above (l3c3_run sub3 body3) (w32 39)));

    pin "BK-20"
      "the ARSHIFT-const row with a provably non-negative operand — the cell at \
       RBP-8 is bounded (⊆ [0,39])"
      (fun () ->
        let t = Var.create ~is_virtual:false ~fresh:false "l3c3_t" (Type.Imm 32) in
        let sub4a, body4a =
          mk_l3c3_loop ~seed:(Some (w32 0))
            ~chain:(Bil.BinOp (Bil.ARSHIFT, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 2))))
            ~cmp:Bil.SLT ~c:(w32 10) ~body_k:(w32 8)
        in
        check "BK-20" (bounded_above (l3c3_run sub4a body4a) (w32 39)));

    pin "BK-21"
      "the ARSHIFT gate — an operand not provably non-negative (top) does NOT \
       refine (the cell stays top; sound stop)"
      (fun () ->
        let t = Var.create ~is_virtual:false ~fresh:false "l3c3_t" (Type.Imm 32) in
        let sub4b, body4b =
          mk_l3c3_loop ~seed:None
            ~chain:(Bil.BinOp (Bil.ARSHIFT, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 2))))
            ~cmp:Bil.SLT ~c:(w32 10) ~body_k:(w32 4)
        in
        check "BK-21" (Ws.is_top (l3c3_run sub4b body4b)));

    pin "BK-22" "TIMES with k = 0 is a sound stop — the cell at RBP-8 stays top"
      (fun () ->
        let t = Var.create ~is_virtual:false ~fresh:false "l3c3_t" (Type.Imm 32) in
        let sub5, body5 =
          mk_l3c3_loop ~seed:None
            ~chain:(Bil.BinOp (Bil.TIMES, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 0))))
            ~cmp:Bil.SLT ~c:(w32 10) ~body_k:(w32 4)
        in
        check "BK-22" (Ws.is_top (l3c3_run sub5 body5)));

    pin "BK-23"
      "TIMES with an EQ singleton {5} and k = 8 (non-divisible) — the row is \
       empty, no refinement (the cell is not a bounded set; the guard is \
       genuinely dead — no t makes t*8 = 5 — the edge is pruned)"
      (fun () ->
        let t = Var.create ~is_virtual:false ~fresh:false "l3c3_t" (Type.Imm 32) in
        let sub6, body6 =
          mk_l3c3_loop ~seed:None
            ~chain:(Bil.BinOp (Bil.TIMES, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 8))))
            ~cmp:Bil.EQ ~c:(w32 5) ~body_k:(w32 4)
        in
        check "BK-23" (not (bounded_above (l3c3_run sub6 body6) (w32 39))));

    (* L3c4: Var-vs-Var overlap, DIVIDE-const, HIGH-extract rows. *)
    pin "BK-24"
      "the Var-vs-Var LT guard (`if (t < u) goto …`, u seeded {10}) — the \
       interval-overlap row caps the cell at RBP-8 (⊆ [0,9])"
      (fun () ->
        let sub1, body1 =
          mk_l3c4_vv_loop ~seed:(Some (w32 0)) ~seed2:(Some (w32 10))
            ~cmp:Bil.LT ~body_k:(w32 4)
        in
        check "BK-24" (bounded_above (l3c4_run sub1 body1) (w32 9)));

    pin "BK-25"
      "a TOP Var-vs-Var operand makes the refinement vacuous — the cell at \
       RBP-8 stays unbounded (the semantic-top class, no wrong window)"
      (fun () ->
        let sub2, body2 =
          mk_l3c4_vv_loop ~seed:(Some (w32 0)) ~seed2:None ~cmp:Bil.LT
            ~body_k:(w32 4)
        in
        check "BK-25" (not (bounded_above (l3c4_run sub2 body2) (w32 1000))));

    pin "BK-26"
      "the DIVIDE-const row — `v := t / 2; if SLT(v, 10)` — the cell at RBP-8 \
       is bounded (⊆ [0,19])"
      (fun () ->
        let t = Var.create ~is_virtual:false ~fresh:false "l3c4_t" (Type.Imm 32) in
        let sub3, body3 =
          mk_l3c4_loop ~seed:(Some (w32 0))
            ~chain:(Bil.BinOp (Bil.DIVIDE, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 2))))
            ~v_w:32 ~cmp:Bil.SLT ~c:(w32 10) ~body_k:(w32 4)
        in
        check "BK-26" (bounded_above (l3c4_run sub3 body3) (w32 19)));

    pin "BK-27"
      "the HIGH-extract producer row — `v := cast HIGH 8 t; if SLT(v, 10)` — the \
       cell at RBP-8 is bounded (⊆ [0, 0x09FFFFFF]; the 2^28-straddling value \
       is dropped)"
      (fun () ->
        let t = Var.create ~is_virtual:false ~fresh:false "l3c4_t" (Type.Imm 32) in
        let sub4, body4 =
          mk_l3c4_loop ~seed:(Some (w32 0))
            ~chain:(Bil.Cast (Bil.HIGH, 8, Bil.Var t))
            ~v_w:8 ~cmp:Bil.SLT ~c:(Cbat_word.of_int ~width:8 10)
            ~body_k:(w32 0x10000000)
        in
        check "BK-27" (bounded_above (l3c4_run sub4 body4) (w32 0x09FFFFFF)));

    pin "BK-28"
      "DIVIDE with k = 0 is a sound stop — no refinement (the cell is not a \
       bounded set)"
      (fun () ->
        let t = Var.create ~is_virtual:false ~fresh:false "l3c4_t" (Type.Imm 32) in
        let sub5, body5 =
          mk_l3c4_loop ~seed:None
            ~chain:(Bil.BinOp (Bil.DIVIDE, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 0))))
            ~v_w:32 ~cmp:Bil.SLT ~c:(w32 10) ~body_k:(w32 4)
        in
        check "BK-28" (not (bounded_above (l3c4_run sub5 body5) (w32 39))));

    (* L3c5: structural closure — identity rows, const-first arm, catch-all. *)
    pin "BK-29"
      "the const-first guard arm — `if (10 = t) goto …` (EQ const-first) — the \
       cell at RBP-8 is bounded (⊆ [0,10]; pinned to {10})"
      (fun () ->
        let t = Var.create ~is_virtual:false ~fresh:false "l3c5_t" (Type.Imm 32) in
        let sub1, body1 =
          mk_l3c5_loop ~seed:None ~chain:None
            ~cond:(Bil.BinOp (Bil.EQ, Bil.Int (Cbat_word.to_word (w32 10)), Bil.Var t))
            ~body_k:(w32 4)
        in
        check "BK-29" (bounded_above (l3c5_run sub1 body1) (w32 10)));

    pin "BK-30"
      "the Tier-3 MOD row (periodic, no closed form) is a sound stop — no \
       refinement (the cell is not a bounded set)"
      (fun () ->
        let t = Var.create ~is_virtual:false ~fresh:false "l3c5_t" (Type.Imm 32) in
        let v = Var.create ~is_virtual:false ~fresh:false "l3c5_v" (Type.Imm 32) in
        let sub2, body2 =
          mk_l3c5_loop ~seed:None
            ~chain:(Some (Bil.BinOp (Bil.MOD, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 8)))))
            ~cond:(Bil.BinOp (Bil.SLT, Bil.Var v, Bil.Int (Cbat_word.to_word (w32 10))))
            ~body_k:(w32 4)
        in
        check "BK-30" (not (bounded_above (l3c5_run sub2 body2) (w32 39))));

    pin "BK-31"
      "the AND-identity row — `v := t AND ~0` (≡ t) — the cell at RBP-8 is \
       bounded (⊆ [0,9])"
      (fun () ->
        let t = Var.create ~is_virtual:false ~fresh:false "l3c5_t" (Type.Imm 32) in
        let v = Var.create ~is_virtual:false ~fresh:false "l3c5_v" (Type.Imm 32) in
        let sub3a, body3a =
          mk_l3c5_loop ~seed:(Some (w32 0))
            ~chain:(Some (Bil.BinOp (Bil.AND, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 0xFFFFFFFF)))))
            ~cond:(Bil.BinOp (Bil.SLT, Bil.Var v, Bil.Int (Cbat_word.to_word (w32 10))))
            ~body_k:(w32 4)
        in
        check "BK-31"
          (let v = l3c5_run sub3a body3a in
           bounded_above v (w32 9)));

    pin "BK-32"
      "the OR-identity row — `v := t OR 0` (≡ t) — the cell at RBP-8 is bounded \
       (⊆ [0,9])"
      (fun () ->
        let t = Var.create ~is_virtual:false ~fresh:false "l3c5_t" (Type.Imm 32) in
        let v = Var.create ~is_virtual:false ~fresh:false "l3c5_v" (Type.Imm 32) in
        let sub3b, body3b =
          mk_l3c5_loop ~seed:(Some (w32 0))
            ~chain:(Some (Bil.BinOp (Bil.OR, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 0)))))
            ~cond:(Bil.BinOp (Bil.SLT, Bil.Var v, Bil.Int (Cbat_word.to_word (w32 10))))
            ~body_k:(w32 4)
        in
        check "BK-32"
          (let v = l3c5_run sub3b body3b in
           bounded_above v (w32 9)));

    pin "BK-33"
      "an Unknown condition — the fixpoint completes and constrain_edge keeps \
       the env unchanged (the shrunk catch-all, never asserts)"
      (fun () ->
        let m4 = memv "l3c5_m" in
        let rsp4 = v64 "RSP" in
        let t4 = Var.create ~is_virtual:false ~fresh:false "l3c5_t" (Type.Imm 32) in
        let addr4 =
          Bil.BinOp (Bil.MINUS, Bil.Var rsp4, Bil.Int (Cbat_word.to_word (w64 8)))
        in
        let sub4, tids4 =
          sub_of "l3c5_unknown"
            [ [], [ (1, mk_goto) ];
              [ Def.create t4 (Bil.Load (Bil.Var m4, addr4, LittleEndian, `r32)) ],
              [ (2, fun t -> mk_jmp_to t (Bil.Unknown ("l3c5_unknown", Type.Imm 1))) ];
              [], [] ]
        in
        let h_tid = tids4.(1) in
        let sol4 = run_anchored sub4 in
        let h_st4 = Graphlib.Std.Solution.get sol4 h_tid in
        let jmp4 =
          match
            Term.enum jmp_t
              (match Term.enum blk_t sub4 |> Seq.to_list with
              | [ _; h; _ ] -> h
              | _ -> assert false)
            |> Seq.to_list
          with
          | [ j ] -> j
          | _ -> assert false
        in
        check "BK-33"
          (AI.equal (Vsa.Test_seam.constrain_edge ~landmarks:(Cbat_landmarks.create ()) ~env:h_st4 (Jmp.cond jmp4)) h_st4));

    (* L-3b: the equal-lower merge arm and the partition views. *)
    pin "BK-34"
      "the traverse shape (the seeded RMW counter) collapses to <= 3 cells in \
       the solution state (the equal-lower hull union keeps the cell count bounded)"
      (fun () ->
        let sub1, body1, _ = mk_l3b1_loop () in
        let sol1 = run_anchored sub1 in
        let st1 = Graphlib.Std.Solution.get sol1 body1 in
        check "BK-34" (l3b_cells_of (memv "l3b1_m") st1 <= 3));

    pin "BK-35"
      "the partition — the iterate view's cell is the loop-body values (⊆ [0,7], \
       non-top) and the exit view's cell carries the exit-iteration value (8 \
       survives)"
      (fun () ->
        let sub1, body1, _ = mk_l3b1_loop () in
        let sol1 = run_anchored sub1 in
        let exit1 =
          match Term.enum blk_t sub1 |> Seq.to_list with
          | [ _; _; _; e ] -> e
          | _ -> failwith "BK-35: fixture block layout changed"
        in
        let icell =
          cell_at (memv "l3b1_m") (v64 "RSP")
            (Graphlib.Std.Solution.get sol1 body1)
        in
        let ecell =
          cell_at (memv "l3b1_m") (v64 "RSP")
            (Graphlib.Std.Solution.get sol1 (Term.tid exit1))
        in
        check "BK-35"
          ((not (Ws.is_top icell))
          && (not (Ws.is_bottom icell))
          && Base.Option.filter (Ws.max_elem icell)
               ~f:(fun w -> Cbat_word.(<=) w (w32 7))
             |> Option.is_some
          && (not (Ws.is_top ecell))
          && Ws.elem (w32 8) ecell));

    pin "BK-36"
      "two +1-adjacent equal-value cells ([RSP-8] and [RSP-7], both {7}) through \
       ONE merge become a SINGLE cell (the +1-adjacent arm, not shadowed by the \
       equal-lower arm)"
      (fun () ->
        let sub4, merge4 = mk_l3b4_diamond () in
        let sol4 = run_anchored sub4 in
        let st4 = Graphlib.Std.Solution.get sol4 merge4 in
        check "BK-36" (l3b_cells_of (memv "l3b4_m") st4 = 1));

    (* B-1: interrupt edges. *)
    pin "BK-37"
      "an interrupt edge is an unknown external callee — the continuation keeps \
       the RSP anchor (the symbolic segment base at offset 0) and the \
       caller-saved rdi is topped (no AI.top degradation)"
      (fun () ->
        let rsp = v64 "RSP" in
        let rdi = v64 "RDI" in
        let sub, tids =
          sub_of "l37_intr"
            [ [], [ (1, mk_goto) ];
              [ Def.create rdi (Bil.Int (Cbat_word.to_word (w64 42))) ],
              [ (2, fun t -> Jmp.create (Int (0x80, t))); (2, mk_goto) ];
              [], [] ]
        in
        let cont_tid = tids.(2) in
        let sol = run_anchored sub in
        let cont_st = Graphlib.Std.Solution.get sol cont_tid in
        check "BK-37"
          (Ws.equal (AI.find_word 64 cont_st rsp) (Ws.stack_word_i64 0L)
          && Ws.is_top (AI.find_word 64 cont_st rdi)));

    (* L-B: the jcc decoder. *)
    pin "BK-38"
      "the exact -O0 corpus block (t := Load-3; CF/SF/OF/ZF defs; the jle \
       compound guard `ZF | (SF|OF) & ~(SF&OF)`) — the jcc decoder recovers the \
       loop-counter constraint (SLE, c=3, gated) and the cell at RBP-8 is \
       bounded (⊆ [0, 4))"
      (fun () ->
        let sub1, body1 =
          mk_l39_loop ~seed:(w32 0) ~c:(w32 3) ~body_op:Bil.PLUS ~body_k:(w32 1)
            ~mk_cond:(fun ~cf:_ ~ofv ~sf ~zf -> l39_jle zf sf ofv)
            ~extra_header_defs:(fun _ -> [])
        in
        check "BK-38" (bounded_above (l39_run sub1 body1) (w32 3)));

    pin "BK-39"
      "the jl compound guard `(SF|OF) & ~(SF&OF)` (signed e < c — excludes \
       equality) — the decoder emits SLT and the cell at RBP-8 is bounded \
       (⊆ [0, 3))"
      (fun () ->
        let sub2, body2 =
          mk_l39_loop ~seed:(w32 0) ~c:(w32 3) ~body_op:Bil.PLUS ~body_k:(w32 1)
            ~mk_cond:(fun ~cf:_ ~ofv ~sf ~zf:_ -> l39_jl sf ofv)
            ~extra_header_defs:(fun _ -> [])
        in
        check "BK-39" (bounded_above (l39_run sub2 body2) (w32 2)));

    pin "BK-40"
      "the ja compound guard `~(CF | ZF)` (unsigned e > c) — the decoder emits \
       UGT (c=3 -> [4, 2^w)) and the decrementing counter converges inside the \
       constraint: the cell at RBP-8 has min_elem >= 4 and is not top"
      (fun () ->
        let sub3, body3 =
          mk_l39_loop ~seed:(w32 8) ~c:(w32 3) ~body_op:Bil.MINUS ~body_k:(w32 1)
            ~mk_cond:(fun ~cf ~ofv:_ ~sf:_ ~zf -> l39_ja cf zf)
            ~extra_header_defs:(fun _ -> [])
        in
        let cell3 = l39_run sub3 body3 in
        check "BK-40"
          ((not (Ws.is_top cell3))
          && (not (Ws.is_bottom cell3))
          && Base.Option.filter (Ws.min_elem cell3)
               ~f:(fun w -> Cbat_word.(>=) w (w32 4))
             |> Option.is_some));

    pin "BK-41"
      "the same-comparison gate — a second cmp in the header (a \
       dead-CF-eliminated t2/OF2/SF2/ZF2 group referencing t2 := f - 5) makes \
       the gate reject the mixed group — NO decoder refinement (the cell stays \
       top)"
      (fun () ->
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
              let addr2 =
                Bil.BinOp (Bil.MINUS, Bil.Var rsp2, Bil.Int (Cbat_word.to_word (w64 16)))
              in
              let f_load = Bil.Load (Bil.Var m, addr2, LittleEndian, `r32) in
              [
                Def.create f f_load;
                Def.create t2
                  (Bil.BinOp (Bil.MINUS, f_load, Bil.Int (Cbat_word.to_word (w32 5))));
                Def.create of2
                  (Bil.Cast
                     ( Bil.HIGH,
                       1,
                       Bil.BinOp
                         ( Bil.AND,
                           Bil.BinOp (Bil.XOR, Bil.Var f, Bil.Int (Cbat_word.to_word (w32 5))),
                           Bil.BinOp (Bil.XOR, Bil.Var f, Bil.Var t2) ) ));
                Def.create sf2 (Bil.Cast (Bil.HIGH, 1, Bil.Var t2));
                Def.create zf2
                  (Bil.BinOp (Bil.EQ, Bil.Int (Cbat_word.to_word (w32 0)), Bil.Var t2));
              ])
        in
        check "BK-41" (Ws.is_top (l39_run sub4 body4)));

    pin "BK-42"
      "the RECORD path (bare `when CF` with CF := v < 3, v := Load[RBP-8] \
       unique) survives the wiring — the flag-state arm + the walk still refine \
       the cell at RBP-8 (⊆ [0, 3))"
      (fun () ->
        let sub5, body5 = mk_l39b5_loop () in
        check "BK-42" (bounded_above (l39_run sub5 body5) (w32 2)));

    (* L-D2: the wide-bound shape. *)
    pin "BK-43"
      "the WIDE-BOUND corpus shape (c=63, ascending counter seeded 0, crossing \
       the i>10 widening threshold) — the cell's proven non-negativity (via the \
       seed store) survives the widened state and bounds the cell at RBP-8 \
       (⊆ [0, 64), max ≤ 63)"
      (fun () ->
        let sub, body =
          mk_l39_loop ~seed:(w32 0) ~c:(w32 63) ~body_op:Bil.PLUS ~body_k:(w32 1)
            ~mk_cond:(fun ~cf:_ ~ofv ~sf ~zf -> l39_jle zf sf ofv)
            ~extra_header_defs:(fun _ -> [])
        in
        check "BK-43"
          (let v = l39_run sub body in
           bounded_above v (w32 63)));

    (* L-E1: the ON-path matched-pair RSP restore. *)
    pin "BK-44"
      "call-in-loop RSP stability — the ON-path matched-pair +8 (the callee's \
       ret pops exactly the retaddr the caller pushed) keeps the header RSP at \
       EXACTLY the pre-push {0x1000} (bounded, no drift)"
      (fun () ->
        let sub, header_tid, rsp = mk_e1_loop_sub () in
        let rsp_hdr = e1_rsp_at sub header_tid rsp in
        check "BK-44" (Ws.equal rsp_hdr (Ws.singleton (w64 0x1000))));

    pin "BK-45"
      "straight-line call RSP exactness — the continuation RSP is EXACTLY the \
       pre-call singleton {0x2000} (the exact truth, not truth−8 = {0x1ff8})"
      (fun () ->
        let sub, post_tid, rsp = mk_e1_flat_sub () in
        let rsp_post = e1_rsp_at sub post_tid rsp in
        check "BK-45" (Ws.equal rsp_post (Ws.singleton (w64 0x2000))));

    (* L-D6: the RBP-anchored gate-free loop. *)
    pin "BK-46"
      "the RBP-anchored loop (prologue RBP := RSP + the c=63 jle loop at RBP−8 + \
       the dead epilogue RBP := mem[RSP]) — every def is denoted, so the jcc \
       decoder's cell meet binds the cell at RBP−8 to ⊆ [0, 64) at the BODY \
       input"
      (fun () ->
        let sub, body = mk_l6_rbp_loop () in
        check "BK-46"
          (let v = l6_run sub body in
           bounded_above v (w32 63)));

    (* R2: the secondary guarded-refinement shapes. *)
    pin "BK-47"
      "the INLINE-ARITHMETIC condition `(t+1) < 64` (the compared exp is BinOp \
       PLUS of t := Load[RBP-8]) — the producer-op recursion refines the (t+1) \
       chain (guard row -> [0,64) on (t+1) -> the PLUS row's circular hull \
       {−1} ∪ [0, 62] on t -> the Var -> refine_backward -> refine_cell) and \
       the cell at RBP−8 is the 64-element hull (⊆ {−1} ∪ [0, 64); cardn 64; no \
       middle value)"
      (fun () ->
        let sub1, body1 =
          mk_r2_loop ~seed:(w32 0) ~seed2:None ~body_op:Bil.PLUS ~body_k:(w32 1)
            ~mk_cond:(fun ~t ->
              Bil.BinOp
                ( Bil.LT,
                  Bil.BinOp (Bil.PLUS, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 1))),
                  Bil.Int (Cbat_word.to_word (w32 64)) ))
        in
        let cell1 = r2_run sub1 body1 in
        check "BK-47"
          ((not (Ws.is_top cell1))
          && (not (Ws.is_bottom cell1))
          && Cbat_word.(<=) (Ws.cardinality cell1) (Cbat_word.of_int ~width:33 64)
          && not (Ws.elem (w32 100) cell1)));

    pin "BK-48"
      "NOT-of-comparison `~(t < 5)` (the taken edge = t ≥ 5, the two-path seed \
       cell {3, 8}) — the NOT-edge keeps its env: the false-edge row [0, 5) \
       never confines the taken edge, so the cell keeps its live values (not \
       bounded ⊆ [0, 4])"
      (fun () ->
        let sub2, body2 =
          mk_r2_loop ~seed:(w32 3) ~seed2:(Some (w32 8)) ~body_op:Bil.PLUS
            ~body_k:(w32 1)
            ~mk_cond:(fun ~t ->
              Bil.UnOp
                ( Bil.NOT,
                  Bil.BinOp (Bil.LT, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 5))) ))
        in
        let cell2 = r2_run sub2 body2 in
        check "BK-48" (not (bounded_above cell2 (w32 4))));

    pin "BK-49"
      "the CONST-FIRST LT flip `10 < t` (Bil.BinOp (Bil.LT, Bil.Int 10, t)) — \
       the flip dispatches on the guard_op enum (UGT): t > 10 unsigned -> \
       [11, 2^w) and the DECREMENTING counter converges inside the constraint \
       (non-top, min_elem ≥ 11)"
      (fun () ->
        let sub3, body3 =
          mk_r2_loop ~seed:(w32 20) ~seed2:None ~body_op:Bil.MINUS ~body_k:(w32 1)
            ~mk_cond:(fun ~t ->
              Bil.BinOp (Bil.LT, Bil.Int (Cbat_word.to_word (w32 10)), Bil.Var t))
        in
        let cell3 = r2_run sub3 body3 in
        check "BK-49"
          ((not (Ws.is_top cell3))
          && (not (Ws.is_bottom cell3))
          && Base.Option.filter (Ws.min_elem cell3)
               ~f:(fun w -> Cbat_word.(>=) w (w32 11))
             |> Option.is_some));

    pin "BK-50"
      "the NESTED-BinOp chain `(t * 8) < 512` — the inline walk bounds the \
       operand, the exact TIMES no-wrap slice fires, and the body-IN cell is \
       the EXACT singleton {63} (the loop exits at t = 64; 63 ∈, 62 ∉, 64 ∉; \
       non-top)"
      (fun () ->
        let sub4, body4 =
          mk_r2_loop ~seed:(w32 63) ~seed2:None ~body_op:Bil.PLUS ~body_k:(w32 1)
            ~mk_cond:(fun ~t ->
              Bil.BinOp
                ( Bil.LT,
                  Bil.BinOp (Bil.TIMES, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 8))),
                  Bil.Int (Cbat_word.to_word (w32 512)) ))
        in
        let cell = r2_run sub4 body4 in
        check "BK-50"
          ((not (Ws.is_top cell))
          && (not (Ws.is_bottom cell))
          && Ws.equal cell (Ws.singleton (w32 63))));

    (* M5: complete-rule pins — one per rule. *)
    pin "BK-51"
      "the MINUS wrap hull — `v := t − ~0; if (v < 5)` refines the cell to the \
       wrapped {0xFFFFFFFF, 0..3} (cardn 5; 0xFFFFFFFF ∈; 0 ∈; the wrap was \
       handled, not emptied)"
      (fun () ->
        let t = Var.create ~is_virtual:false ~fresh:false "l3c3_t" (Type.Imm 32) in
        let sub1, body1 =
          mk_l3c3_loop ~seed:None
            ~chain:(Bil.BinOp (Bil.MINUS, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 0xFFFFFFFF))))
            ~cmp:Bil.LT ~c:(w32 5) ~body_k:(w32 4)
        in
        let cell1 = l3c3_run sub1 body1 in
        check "BK-51"
          ((not (Ws.is_top cell1))
          && (not (Ws.is_bottom cell1))
          && Cbat_word.(=) (Ws.cardinality cell1) (Cbat_word.of_int ~width:33 5)
          && Ws.elem (w32 0xFFFFFFFF) cell1
          && Ws.elem (w32 0) cell1
          && not (Ws.elem (w32 4) cell1)));

    pin "BK-52"
      "the TIMES k=0 rule is the identity — `v := t * 0; if EQ(v, 0)` leaves the \
       cell unconstrained (top)"
      (fun () ->
        let t = Var.create ~is_virtual:false ~fresh:false "l3c3_t" (Type.Imm 32) in
        let sub2, body2 =
          mk_l3c3_loop ~seed:None
            ~chain:(Bil.BinOp (Bil.TIMES, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 0))))
            ~cmp:Bil.EQ ~c:(w32 0) ~body_k:(w32 4)
        in
        let cell2 = l3c3_run sub2 body2 in
        check "BK-52" (Ws.is_top cell2));

    pin "BK-53"
      "the XOR-~0 bijection — `v := t XOR ~0; if EQ(v, 5)` refines the cell to \
       {~5} = {0xFFFFFFFA} (0xFFFFFFFA ∈, 5 ∉)"
      (fun () ->
        let t = Var.create ~is_virtual:false ~fresh:false "l3c3_t" (Type.Imm 32) in
        let sub3, body3 =
          mk_l3c3_loop ~seed:None
            ~chain:(Bil.BinOp (Bil.XOR, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 0xFFFFFFFF))))
            ~cmp:Bil.EQ ~c:(w32 5) ~body_k:(w32 4)
        in
        let cell3 = l3c3_run sub3 body3 in
        check "BK-53"
          ((not (Ws.is_top cell3))
          && Ws.elem (w32 0xFFFFFFFA) cell3
          && not (Ws.elem (w32 5) cell3)));

    pin "BK-54"
      "the LOW-cast rule in the walk — `v := cast LOW 8 t; if EQ(v, 5)` bounds \
       the cell to the truncation hull [5, 0xFFFFFF05] (5 ∈, 5+0x100 ∈, 4 ∉)"
      (fun () ->
        let t4 = Var.create ~is_virtual:false ~fresh:false "l3c4_t" (Type.Imm 32) in
        let sub4, body4 =
          mk_l3c4_loop ~seed:None ~chain:(Bil.Cast (Bil.LOW, 8, Bil.Var t4))
            ~v_w:8 ~cmp:Bil.EQ ~c:(Cbat_word.of_int ~width:8 5) ~body_k:(w32 4)
        in
        let cell4 = l3c4_run sub4 body4 in
        check "BK-54"
          ((not (Ws.is_top cell4))
          && (not (Ws.is_bottom cell4))
          && Ws.elem (w32 5) cell4
          && Ws.elem (w32 0x105) cell4
          && (not (Ws.elem (w32 4) cell4))
          && Base.Option.filter (Ws.max_elem cell4)
               ~f:(fun w -> Cbat_word.(<=) w (w32 0xFFFFFF05))
             |> Option.is_some));

    pin "BK-55"
      "the signed-division rule — `v := t sdiv 2; if EQ(v, −3)` refines the cell \
       to {−6, −5} (0xFFFFFFFA ∈, 0xFFFFFFFB ∈, −3 ∉)"
      (fun () ->
        let t = Var.create ~is_virtual:false ~fresh:false "l3c3_t" (Type.Imm 32) in
        let sub5, body5 =
          mk_l3c3_loop ~seed:None
            ~chain:(Bil.BinOp (Bil.SDIVIDE, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 2))))
            ~cmp:Bil.EQ ~c:(w32 0xFFFFFFFD) ~body_k:(w32 4)
        in
        let cell5 = l3c3_run sub5 body5 in
        check "BK-55"
          ((not (Ws.is_top cell5))
          && (not (Ws.is_bottom cell5))
          && Ws.elem (w32 0xFFFFFFFA) cell5
          && Ws.elem (w32 0xFFFFFFFB) cell5
          && not (Ws.elem (w32 0xFFFFFFFD) cell5)));

    pin "BK-56"
      "the Var-identity rule — `v := t; if (v < 10)` — the walk propagates the \
       [0,10) window through the identity to the loaded cell (the body-IN cell \
       is bounded ≤ [0,9] — the store-only join would be [0,10])"
      (fun () ->
        let t_id = Var.create ~is_virtual:false ~fresh:false "l3c3_t" (Type.Imm 32) in
        let sub6, body6 =
          mk_l3c3_loop ~seed:(Some (w32 0)) ~chain:(Bil.Var t_id) ~cmp:Bil.LT
            ~c:(w32 10) ~body_k:(w32 1)
        in
        let cell6 = l3c3_run sub6 body6 in
        check "BK-56" (bounded_above cell6 (w32 9)));

    (* The inverse denote's leaf facts: the load's cell meet. *)
    pin "BK-57"
      "the RSP-based same-block cell meet — [RSP-8] meets the cell at the offset \
       key (the frame's RSP offset 0)"
      (fun () ->
        let st1 =
          t_add_cell (mk_seed_state t_rsp t_rbp ()) (Ws.singleton (w64 (-8)))
            (bk_iv64 ~lo:0 ~hi:20)
        in
        let env1 =
          Vsa.Test_seam.constrain_operands ~landmarks:(Cbat_landmarks.create ()) ~env:st1
            (t_load_exp
               (Bil.BinOp (Bil.MINUS, Bil.Var t_rsp, Bil.Int (Cbat_word.to_word (w64 8)))))
            (bk_iv64 ~lo:0 ~hi:9)
        in
        check "BK-57"
          (let v = t_cell_at env1 (Ws.singleton (w64 (-8))) in
           Ws.elem (w64 9) v && not (Ws.elem (w64 15) v)));

    pin "BK-58"
      "the dynamic-index meet — the index's iterate constraint [0,4] confines the \
       meet to the cells {0..32}; the cell at 40 (the exit-side) is untouched"
      (fun () ->
        let st2 =
          let s =
            t_add_cell (mk_seed_state t_rsp t_rbp ()) (Ws.singleton (w64 0))
              (bk_iv64 ~lo:0 ~hi:20)
          in
          t_add_cell s (Ws.singleton (w64 40)) (bk_iv64 ~lo:0 ~hi:20)
        in
        let st2 = AI.add_word st2 ~key:t_idx ~data:(bk_iv64 ~lo:0 ~hi:4) in
        let env2 =
          Vsa.Test_seam.constrain_operands ~landmarks:(Cbat_landmarks.create ()) ~env:st2
            (t_load_exp
               (Bil.BinOp
                  ( Bil.PLUS,
                    Bil.Var t_rbp,
                    Bil.BinOp (Bil.TIMES, Bil.Var t_idx, Bil.Int (Cbat_word.to_word (w64 8))) )))
            (bk_iv64 ~lo:0 ~hi:9)
        in
        check "BK-58"
          (let v0 = t_cell_at env2 (Ws.singleton (w64 0)) in
           let v40 = t_cell_at env2 (Ws.singleton (w64 40)) in
           Ws.elem (w64 9) v0 && (not (Ws.elem (w64 15) v0)) && Ws.elem (w64 15) v40));

    pin "BK-59"
      "the ranged meet's overlap boundary — the stored [0,64] cell splits: the \
       overlapping part [8,24] meets; the parts [0,8) and (24,64] keep the \
       original (the reads at the split's aligned points — the find' alignment \
       semantics: an unaligned sub-region read returns top)"
      (fun () ->
        let st3 =
          t_add_cell (mk_seed_state t_rsp t_rbp ()) (bk_iv64 ~lo:0 ~hi:64)
            (bk_iv64 ~lo:0 ~hi:20)
        in
        let st3 = AI.add_word st3 ~key:t_idx ~data:(bk_iv64 ~lo:8 ~hi:24) in
        let env3 =
          Vsa.Test_seam.constrain_operands ~landmarks:(Cbat_landmarks.create ()) ~env:st3
            (t_load_exp (Bil.BinOp (Bil.PLUS, Bil.Var t_rbp, Bil.Var t_idx)))
            (bk_iv64 ~lo:0 ~hi:9)
        in
        check "BK-59"
          (let v8 = t_cell_at env3 (Ws.singleton (w64 8)) in
           let v0 = t_cell_at env3 (Ws.singleton (w64 0)) in
           let v24 = t_cell_at env3 (Ws.singleton (w64 24)) in
           Ws.elem (w64 9) v8
           && (not (Ws.elem (w64 15) v8))
           && Ws.elem (w64 15) v0
           && Ws.elem (w64 15) v24));

    pin "BK-60"
      "the exit-side cells survive — the iterate range [0,32] meets; the \
       exit-side offsets 40 and 80 (the ¬iterate values) are untouched"
      (fun () ->
        let st4 =
          let s =
            t_add_cell (mk_seed_state t_rsp t_rbp ()) (Ws.singleton (w64 0))
              (bk_iv64 ~lo:0 ~hi:20)
          in
          let s = t_add_cell s (Ws.singleton (w64 40)) (bk_iv64 ~lo:0 ~hi:20) in
          t_add_cell s (Ws.singleton (w64 80)) (bk_iv64 ~lo:0 ~hi:20)
        in
        let st4 = AI.add_word st4 ~key:t_idx ~data:(bk_iv64 ~lo:0 ~hi:4) in
        let env4 =
          Vsa.Test_seam.constrain_operands ~landmarks:(Cbat_landmarks.create ()) ~env:st4
            (t_load_exp
               (Bil.BinOp
                  ( Bil.PLUS,
                    Bil.Var t_rbp,
                    Bil.BinOp (Bil.TIMES, Bil.Var t_idx, Bil.Int (Cbat_word.to_word (w64 8))) )))
            (bk_iv64 ~lo:0 ~hi:9)
        in
        check "BK-60"
          (let v0 = t_cell_at env4 (Ws.singleton (w64 0)) in
           let v40 = t_cell_at env4 (Ws.singleton (w64 40)) in
           let v80 = t_cell_at env4 (Ws.singleton (w64 80)) in
           Ws.elem (w64 9) v0
           && (not (Ws.elem (w64 15) v0))
           && Ws.elem (w64 15) v40
           && Ws.elem (w64 15) v80));

    (* The guard's operand windows observed through the inverse denote: on a
       TOP env the leaf meet preserves the raw row. *)
    pin "BK-61" "EQ const-second -> the Var seed {10}"
      (fun () ->
        let c =
          s_window_of (mk_env [])
            (Bil.BinOp (Bil.EQ, Bil.Var s_t, Bil.Int (Cbat_word.to_word (s_r32 10))))
            s_t
        in
        check "BK-61" (Ws.elem (s_r32 10) c && not (Ws.elem (s_r32 11) c)));

    pin "BK-62" "NEQ const-second -> the wrapped complement (10 ∉; 11, 9 ∈)"
      (fun () ->
        let c =
          s_window_of (mk_env [])
            (Bil.BinOp (Bil.NEQ, Bil.Var s_t, Bil.Int (Cbat_word.to_word (s_r32 10))))
            s_t
        in
        check "BK-62"
          ((not (Ws.elem (s_r32 10) c)) && Ws.elem (s_r32 11) c && Ws.elem (s_r32 9) c));

    pin "BK-63" "SLT const-second -> the two-piece [0,3] ∪ [2^31, max] (no gate)"
      (fun () ->
        let c =
          s_window_of (mk_env [])
            (Bil.BinOp (Bil.SLT, Bil.Var s_t, Bil.Int (Cbat_word.to_word (s_r32 4))))
            s_t
        in
        check "BK-63"
          (Ws.elem (s_r32 3) c
          && (not (Ws.elem (s_r32 4) c))
          && Ws.elem (s_r32 0x80000000) c));

    pin "BK-64" "const-first LT -> the UGT flip [11, max] (10 ∉; 11 ∈)"
      (fun () ->
        let c =
          s_window_of (mk_env [])
            (Bil.BinOp (Bil.LT, Bil.Int (Cbat_word.to_word (s_r32 10)), Bil.Var s_t))
            s_t
        in
        check "BK-64" (Ws.elem (s_r32 11) c && not (Ws.elem (s_r32 10) c)));

    pin "BK-65" "the var-vs-var LT overlap — t ∈ [0,9] (the u's max 10)"
      (fun () ->
        let env5 =
          mk_env [ (s_t, bk_iv32 ~lo:0 ~hi:10); (s_u, Ws.singleton (s_r32 10)) ]
        in
        let c5 = s_window_of env5 (Bil.BinOp (Bil.LT, Bil.Var s_t, Bil.Var s_u)) s_t in
        check "BK-65" (Ws.elem (s_r32 9) c5 && not (Ws.elem (s_r32 10) c5)));

    pin "BK-66"
      "the var-vs-var NEQ — the t seed = the complement of the {5} overlap (the \
       interior: the identity — sound)"
      (fun () ->
        let env6 =
          mk_env [ (s_t, bk_iv32 ~lo:0 ~hi:10); (s_u, Ws.singleton (s_r32 5)) ]
        in
        let c6 = s_window_of env6 (Bil.BinOp (Bil.NEQ, Bil.Var s_t, Bil.Var s_u)) s_t in
        check "BK-66" (Ws.elem (s_r32 0) c6 && Ws.elem (s_r32 10) c6));

    pin "BK-67"
      "the generic comparison — the t row from the (u+1) value-set [1,4] \
       (t ⊆ [0,3]) + the u producer seed"
      (fun () ->
        let env7 = mk_env [ (s_t, bk_iv32 ~lo:0 ~hi:10); (s_u, bk_iv32 ~lo:0 ~hi:3) ] in
        let env7' =
          Vsa.Test_seam.constrain_operands ~landmarks:(Cbat_landmarks.create ()) ~env:env7
            (Bil.BinOp
               ( Bil.LT,
                 Bil.Var s_t,
                 Bil.BinOp (Bil.PLUS, Bil.Var s_u, Bil.Int (Cbat_word.to_word (s_r32 1))) ))
            (Ws.singleton (Cbat_word.of_word Word.b1))
        in
        let ct7 = s_w32_of_env env7' s_t and cu7 = s_w32_of_env env7' s_u in
        check "BK-67"
          (Ws.elem (s_r32 3) ct7
          && (not (Ws.elem (s_r32 4) ct7))
          && Ws.elem (s_r32 1) cu7));

    pin "BK-68" "the producer PLUS hull — the circular hull {0xFFFFFFFF} ∪ [0,8] on t"
      (fun () ->
        let c8 =
          s_window_of (mk_env [])
            (Bil.BinOp
               ( Bil.LT,
                 Bil.BinOp (Bil.PLUS, Bil.Var s_t, Bil.Int (Cbat_word.to_word (s_r32 1))),
                 Bil.Int (Cbat_word.to_word (s_r32 10)) ))
            s_t
        in
        check "BK-68"
          (Ws.elem (s_r32 8) c8
          && (not (Ws.elem (s_r32 9) c8))
          && Ws.elem (s_r32 0xFFFFFFFF) c8));

    pin "BK-69"
      "the load operand -> the cell fact meets the env's memory ([0,9] on the \
       cell)"
      (fun () ->
        let rsp64 = Var.create ~is_virtual:false ~fresh:false "RSP" (Type.Imm 64) in
        let st9 = mk_seed_state rsp64 rsp64 () in
        let k9 = { Mem.addr_width = 32; Mem.addressable_width = 8 } in
        let mem9 =
          let mv = Mem.top k9 in
          AI.add_memory st9 ~key:s_m
            ~data:
              (Mem.add mv ~key:(key_of (Ws.singleton (w64 0)))
                 ~data:(Mem.Val.create (bk_iv32 ~lo:0 ~hi:40) LittleEndian))
        in
        let env9 =
          Vsa.Test_seam.constrain_operands ~landmarks:(Cbat_landmarks.create ()) ~env:mem9
            (Bil.BinOp
               ( Bil.LT,
                 Bil.Load
                   ( Bil.Var s_m,
                     Bil.BinOp (Bil.MINUS, Bil.Var rsp64, Bil.Int (Cbat_word.to_word (w64 8))),
                     LittleEndian,
                     `r32 ),
                 Bil.Int (Cbat_word.to_word (s_r32 10)) ))
            (Ws.singleton (Cbat_word.of_word Word.b1))
        in
        check "BK-69"
          (let mv = AI.find_memory k9 env9 s_m in
           let v =
             Mem.Val.data (Mem.find (32, LittleEndian) mv (key_of (Ws.singleton (w64 (-8)))))
           in
           Ws.elem (s_r32 9) v && not (Ws.elem (s_r32 10) v)));

    pin "BK-70"
      "the completed fallthrough of (t <u 10) seeds the UGE side [10, max] \
       (10 ∈; 9 ∉)"
      (fun () ->
        let s10 =
          Vsa.Test_seam.constrain_operands ~landmarks:(Cbat_landmarks.create ()) ~env:(mk_env [])
            (Cbat_vsa_utils.complete_cond
               (Bil.UnOp (Bil.NOT, Bil.BinOp (Bil.LT, Bil.Var s_t, Bil.Int (Cbat_word.to_word (s_r32 10))))))
            (Ws.singleton (Cbat_word.of_word Word.b1))
        in
        let c10 = s_w32_of_env s10 s_t in
        check "BK-70" (Ws.elem (s_r32 10) c10 && not (Ws.elem (s_r32 9) c10)));

    pin "BK-71" "the NEG row — the neg'd [0,9]: 0 ∈, −1 ∈"
      (fun () ->
        let s11 =
          Vsa.Test_seam.constrain_operands ~landmarks:(Cbat_landmarks.create ()) ~env:(mk_env [])
            (Bil.BinOp (Bil.LT, Bil.UnOp (Bil.NEG, Bil.Var s_t), Bil.Int (Cbat_word.to_word (s_r32 10))))
            (Ws.singleton (Cbat_word.of_word Word.b1))
        in
        let c11 = s_w32_of_env s11 s_t in
        check "BK-71" (Ws.elem (s_r32 0) c11 && Ws.elem (s_r32 0xFFFFFFFF) c11));

    pin "BK-72" "the completed dual — NOT (t EQ 10) -> the NEQ complement (10 ∉; 11 ∈)"
      (fun () ->
        let s13 =
          Vsa.Test_seam.constrain_operands ~landmarks:(Cbat_landmarks.create ()) ~env:(mk_env [])
            (Cbat_vsa_utils.complete_cond
               (Bil.UnOp (Bil.NOT, Bil.BinOp (Bil.EQ, Bil.Var s_t, Bil.Int (Cbat_word.to_word (s_r32 10))))))
            (Ws.singleton (Cbat_word.of_word Word.b1))
        in
        let c13 = s_w32_of_env s13 s_t in
        check "BK-72" (not (Ws.elem (s_r32 10) c13) && Ws.elem (s_r32 11) c13));

    pin "BK-73"
      "the LOW cast row — the truncation hull [5, 5 + 2^32 − 2^8] (5 ∈; 5+0x100 \
       ∈; 4 ∉)"
      (fun () ->
        let env15 =
          mk_env
            [ ( s_t,
                Ws.of_clp
                  (Clp.create ~width:32 ~step:(s_r32 1)
                     ~cardn:(Cbat_word.of_int ~width:33 0x10000) (s_r32 0)) ) ]
        in
        let env15' =
          Vsa.Test_seam.constrain_operands ~landmarks:(Cbat_landmarks.create ()) ~env:env15
            (Bil.BinOp
               ( Bil.EQ,
                 Bil.Cast (Bil.LOW, 8, Bil.Var s_t),
                 Bil.Int (Cbat_word.to_word (Cbat_word.of_int ~width:8 5)) ))
            (Ws.singleton (Cbat_word.of_word Word.b1))
        in
        let c15 = s_w32_of_env env15' s_t in
        check "BK-73"
          (Ws.elem (s_r32 5) c15
          && Ws.elem (s_r32 0x105) c15
          && not (Ws.elem (s_r32 4) c15)));

    pin "BK-74"
      "the SIGNED ext row — the pre-image [0, 0xFF] on a top env; the meet with \
       {0x100} is empty, so the env keeps its value (identity, observed)"
      (fun () ->
        let env15b = mk_env [ (s_t, Ws.singleton (s_r32 0x100)) ] in
        let env15b' =
          Vsa.Test_seam.constrain_operands ~landmarks:(Cbat_landmarks.create ()) ~env:env15b
            (Bil.BinOp
               ( Bil.LT,
                 Bil.Cast (Bil.SIGNED, 64, Bil.Var s_t),
                 Bil.Int (Cbat_word.to_word (Cbat_word.of_int ~width:64 0x100)) ))
            (Ws.singleton (Cbat_word.of_word Word.b1))
        in
        let c15b = s_w32_of_env env15b' s_t in
        let row15b =
          s_w32_of_env
            (Vsa.Test_seam.constrain_operands ~landmarks:(Cbat_landmarks.create ()) ~env:(mk_env [])
               (Bil.BinOp
                  ( Bil.LT,
                    Bil.Cast (Bil.SIGNED, 64, Bil.Var s_t),
                    Bil.Int (Cbat_word.to_word (Cbat_word.of_int ~width:64 0x100)) ))
               (Ws.singleton (Cbat_word.of_word Word.b1)))
            s_t
        in
        check "BK-74"
          (Ws.elem (s_r32 0xFF) row15b
          && not (Ws.elem (s_r32 0x100) row15b)
          && Ws.equal c15b (Ws.singleton (s_r32 0x100))));

    pin "BK-75"
      "the completion is the negation — NOT over each of the six comparisons \
       (both operand orders, const and var sides) completes structurally to the \
       negated comparison"
      (fun () ->
        let x16 = Var.create ~is_virtual:true ~fresh:false "s16_x" (Type.Imm 32) in
        let y16 = Var.create ~is_virtual:true ~fresh:false "s16_y" (Type.Imm 32) in
        let completes_to op op' swap =
          List.for_all
            (fun (a, b) ->
              Exp.equal
                (Cbat_vsa_utils.complete_cond (Bil.UnOp (Bil.NOT, Bil.BinOp (op, a, b))))
                (if swap then Bil.BinOp (op', b, a) else Bil.BinOp (op', a, b)))
            [ (Bil.Var x16, Bil.Var y16); (Bil.Var y16, Bil.Var x16);
              (Bil.Var x16, Bil.Int (Cbat_word.to_word (s_r32 7)));
              (Bil.Int (Cbat_word.to_word (s_r32 7)), Bil.Var x16) ]
        in
        check "BK-75"
          (List.for_all
             (fun (o, o', s) -> completes_to o o' s)
             [ (Bil.LT, Bil.LE, true); (Bil.LE, Bil.LT, true);
               (Bil.SLT, Bil.SLE, true); (Bil.SLE, Bil.SLT, true);
               (Bil.EQ, Bil.NEQ, false); (Bil.NEQ, Bil.EQ, false) ]));

    pin "BK-76"
      "the completed fallthrough of (x <u y) with x = [0,3], y = top seeds \
       y ⊆ [0,3] (0, 3 ∈; 4 ∉)"
      (fun () ->
        let x16 = Var.create ~is_virtual:true ~fresh:false "s16_x" (Type.Imm 32) in
        let y16 = Var.create ~is_virtual:true ~fresh:false "s16_y" (Type.Imm 32) in
        let env16 = mk_env [ (x16, bk_iv32 ~lo:0 ~hi:3); (y16, bk_iv32 ~lo:0 ~hi:0xFFFFFFFF) ] in
        let b1 = Ws.singleton (Cbat_word.of_word Word.b1) in
        let y16_read =
          s_w32_of_env
            (Vsa.Test_seam.constrain_operands ~landmarks:(Cbat_landmarks.create ()) ~env:env16
               (Cbat_vsa_utils.complete_cond
                  (Bil.UnOp (Bil.NOT, Bil.BinOp (Bil.LT, Bil.Var x16, Bil.Var y16))))
               b1)
            y16
        in
        check "BK-76"
          (Ws.elem (s_r32 0) y16_read
          && Ws.elem (s_r32 3) y16_read
          && not (Ws.elem (s_r32 4) y16_read)));

    pin "BK-77"
      "the 3-comparison AND chain narrows by the meet — a is cut to [0,6] (the \
       y-max row); y and c keep their values (their rows do not narrow what the \
       env already knows)"
      (fun () ->
        let a16 = Var.create ~is_virtual:true ~fresh:false "s16_a" (Type.Imm 32) in
        let y16 = Var.create ~is_virtual:true ~fresh:false "s16_y" (Type.Imm 32) in
        let c16v = Var.create ~is_virtual:true ~fresh:false "s16_c" (Type.Imm 32) in
        let env16c =
          mk_env
            [ (a16, bk_iv32 ~lo:0 ~hi:9); (y16, bk_iv32 ~lo:3 ~hi:7);
              (c16v, bk_iv32 ~lo:5 ~hi:9) ]
        in
        let b1 = Ws.singleton (Cbat_word.of_word Word.b1) in
        let env16c' =
          Vsa.Test_seam.constrain_operands ~landmarks:(Cbat_landmarks.create ()) ~env:env16c
            (Bil.BinOp
               ( Bil.AND,
                 Bil.BinOp (Bil.LT, Bil.Var a16, Bil.Var y16),
                 Bil.BinOp (Bil.LT, Bil.Var y16, Bil.Var c16v) ))
            b1
        in
        check "BK-77"
          (let a' = s_w32_of_env env16c' a16 in
           Ws.elem (s_r32 6) a'
           && not (Ws.elem (s_r32 7) a')
           && Ws.equal (s_w32_of_env env16c' y16) (AI.find_word 32 env16c (Var.base y16))
           && Ws.equal (s_w32_of_env env16c' c16v) (AI.find_word 32 env16c (Var.base c16v))));

    pin "BK-78"
      "the infeasible constant — (Int 5) with {7} -> the empty state; with {5} \
       -> the identity"
      (fun () ->
        check "BK-78"
          (AI.equal
             (Vsa.Test_seam.constrain_operands ~landmarks:(Cbat_landmarks.create ()) ~env:(mk_env [])
                (Bil.Int (Cbat_word.to_word (s_r32 5)))
                (Ws.singleton (s_r32 7)))
             AI.bottom
          && AI.equal
               (Vsa.Test_seam.constrain_operands ~landmarks:(Cbat_landmarks.create ()) ~env:(mk_env [])
                  (Bil.Int (Cbat_word.to_word (s_r32 5)))
                  (Ws.singleton (s_r32 5)))
               (mk_env [])));
  ]

let () = run "backward" tests
