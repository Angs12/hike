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
let t_rsp = sp
let t_rbp = frame_ptr
let t_idx = Var.create ~is_virtual:true ~fresh:false "t_idx" (Type.Imm 64)
let t_m = Var.create ~is_virtual:false ~fresh:false "t_m" (Type.Mem (`r64, `r8))

let t_mem_idx = { Mem.addr_width = 64; Mem.addressable_width = 8 }

let t_key_of (ws : Ws.t) =
  match Mem.Key.of_wordset ws with [ k ] -> k | _ -> failwith "key_of"

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

(* The frame cell at the [RSP-8] slot, read straight from a state's
   memory map: a state that holds no frame pointer cannot denote the
   address, but the cell itself is in the map. *)
let frame_cell ~(width : int) (m : var) (st : AI.t) : Ws.t =
  let mv = AI.find_memory t_mem_idx st m in
  Mem.Val.data
    (Mem.find (width, LittleEndian) mv (t_key_of (Ws.stack_word_i64 (-8L))))

(* The guard-window fixture: the virtual compared vars and the mem var. *)
let s_t = Var.create ~is_virtual:true ~fresh:false "s_t" (Type.Imm 32)
let s_u = Var.create ~is_virtual:true ~fresh:false "s_u" (Type.Imm 32)

let s_w32_of_env env v = AI.find_word 32 env (Var.base v)

(* T07 / A4: the four-way soundness table.  {syntactic, range} x
   {cast UNSIGNED, extract-hull}.  A 32-bit counter cell at RBP-8 is
   seeded 0 and incremented by 1; the guard admits [0, c-1], so the
   value c is reachable at the head and the guard must still be able to
   be false there.  "syntactic" places the cast/extract in the compared
   var's def; "range" places it in the guard operand itself. *)
let a4_t = Var.create ~is_virtual:false ~fresh:false "a4_t" (Type.Imm 32)
let a4_v (w : int) = Var.create ~is_virtual:false ~fresh:false "a4_v" (Type.Imm w)
let a4_w16 = Cbat_word.of_int ~width:16

(* One cell of the table.  Returns (guard-can-be-false,
   head-cell-keeps-the-exit-value, body-cell-excludes-it). *)
let a4_cell ~(op : exp) ~(v_w : int) ~(c : Cbat_word.t) ~(exit : Cbat_word.t)
    ~(seed : Cbat_word.t) ~(body_k : Cbat_word.t) ~(inline : bool) :
    bool * bool * bool =
  let chain, operand =
    if inline then (None, op) else (Some op, Bil.Var (a4_v v_w)) in
  let cond = Bil.BinOp (Bil.LT, operand, Bil.Int (Cbat_word.to_word c)) in
  let sub, body_tid =
    mk_l3_chain_loop ~name:"a4" ~seed:(Some seed) ~v_w ~chain ~cond ~body_k
  in
  let sol = run_anchored sub in
  let head = List.nth (Term.enum blk_t sub |> Seq.to_list) 2 in
  let head_in = Graphlib.Std.Solution.get sol (Term.tid head) in
  let head_post = Vsa.Test_seam.denote_defs ~synth:Hike.Synth.empty head head_in in
  let cond_ws =
    match Vsa.Test_seam.denote_imm_exp ~synth:Hike.Synth.empty cond head_post with
    | Ok ws -> ws
    | Error _ -> failwith "a4: the guard does not denote"
  in
  (* The cell at RBP-8, read in the state of the block that holds it:
     each block carries its own frame-pointer version. *)
  let cell_in tid st =
    cell_at (memv "a4_m") (version_at sub tid frame_ptr) st in
  ( Ws.elem Cbat_word.b0 cond_ws,
    Ws.elem exit (cell_in (Term.tid head) head_in),
    not (Ws.elem exit (cell_in body_tid (Graphlib.Std.Solution.get sol body_tid))) )

(* The guard-edge walk on one block after an [RBP := RSP] entry: [defs]
   end in [zf]'s guard, the edge takes zf = {1}, and the refined edge
   state is returned.  [m] is the block's memory, top at entry. *)
(* The refined edge state of a block's guard, with the SSA form the
   versions come from and the block's tid. *)
let wr_refine (name : string) (m : var) (zf : var) (defs : def term list) :
    AI.t * sub term * tid =
  let rsp = sp in
  let rbp = frame_ptr in
  let sub, tids =
    sub_of name
      [ [ Def.create rbp (Bil.Var rsp) ], [ (1, mk_goto) ];
        defs, [ (2, mk_goto) ];
        [], [] ]
  in
  let ssa = sub in
  let entry =
    AI.add_memory (anchored_entry ()) ~key:m
      ~data:(Mem.top { Mem.addr_width = 64; Mem.addressable_width = 8 })
  in
  let sol =
    static_graph_vsa ~synth:Hike.Synth.empty ~abi:Hike_abi.x86_64_sysv ssa
      (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv ~entry ssa)
  in
  let rctx = mk_rctx ~synth:Hike.Synth.empty ~abi:Hike_abi.x86_64_sysv ssa in
  let blk =
    Term.enum blk_t ssa |> Seq.to_list
    |> List.find (fun b -> Tid.equal (Term.tid b) tids.(1))
  in
  let post = Vsa.Test_seam.denote_defs ~synth:Hike.Synth.empty blk (Graphlib.Std.Solution.get sol tids.(1)) in
  let zf = version_at ssa tids.(1) zf in
  let edge = AI.add_word post ~key:zf ~data:(Ws.singleton Cbat_word.b1) in
  let out, _, _ =
    Vsa.Test_seam.refine_edge_count_writes ~sol ~rctx
      ~seeds:(Var.Set.singleton zf) edge blk
  in
  out, ssa, tids.(1)

(* The value of the base variable [v] in a hand-built environment. *)
let plain_value (env : AI.t) (v : var) : Ws.t =
  let width = match Var.typ v with Type.Imm w -> w | _ -> 64 in
  AI.find_word width env (Var.base v)

(* The value of the base variable [v] in a refined edge state. *)
let wr_value (ssa : sub term) (tid : tid) (out : AI.t) (v : var) : Ws.t =
  let version = version_at ssa tid v in
  let width = match Var.typ v with Type.Imm w -> w | _ -> 64 in
  AI.find_word width out version

(* The [RBP - 8] cell address the write-site pins store and load. *)
let wr_addr =
  Bil.BinOp (Bil.MINUS, Bil.Var frame_ptr, Bil.Int (Cbat_word.to_word (w64 8)))

let wr_v32 (n : string) = Var.create ~is_virtual:false ~fresh:false n (Type.Imm 32)

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
      "LSHIFT pre-images preserve every wrapped input class and exclude low bits outside the guard"
      (fun () ->
        let sub3, body3 =
          mk_l3a_loop ~cmp:Bil.LT ~c:(w32 40)
            ~rhs:
              (Bil.BinOp
                 ( Bil.LSHIFT,
                   Bil.Var (Var.create ~is_virtual:false ~fresh:false "l3a_t" (Type.Imm 32)),
                   Bil.Int (Cbat_word.to_word (w32 2)) ))
        in
        let cell = l3a_run_analyzed sub3 body3 in
        check "BK-03" (Ws.elem (w32 0) cell && Ws.elem (w32 9) cell
          && Ws.elem (w32 0x40000000) cell && Ws.elem (w32 0xC0000009) cell
          && not (Ws.elem (w32 10) cell)));

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
        check "BK-04" (Ws.is_top (l3a_run_analyzed sub4 body4)));

    pin "BK-05"
      "a NEQ guard refines: the loop counter's fixpoint excludes the \
       guard's own value (the two-piece interior exclusion)"
      (fun () ->
        let sub5, body5 =
          mk_l3c2_loop ~prologue:true ~seed:(Some (w32 0)) ~cmp:Bil.NEQ
            ~c:(w32 10) ~body_op:Bil.PLUS ~body_k:(w32 1) ~flag:false
        in
        let sol5 = run_anchored sub5 in
        let cell5 =
          cell_at (memv "l3c2_m") (version_at sub5 body5 frame_ptr) (iter_state_of sub5 sol5 body5)
        in
        check "BK-05"
          (not (Ws.is_top cell5) && not (Ws.elem (w32 10) cell5)));

    (* L3c1: the flag-state mechanism. *)
    pin "BK-06"
      "a flag-indirected guard (CF := LT(t, 10); if CF goto …) — the flag-state \
       record recovers the constraint on t and the cell at RBP-8 is bounded \
       (⊆ [0,9])"
      (fun () ->
        let m = memv "l3c1_m" in
        let sub1, body1, _ = mk_l3c1_loop ~extra_header_defs:[] ~pre_cf_defs:[] in
        let sol1 = run_anchored sub1 in
        let cell1 = cell_at m (version_at sub1 body1 frame_ptr) (iter_state_of sub1 sol1 body1) in
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
        let cell2 = cell_at m (version_at sub2 body2 frame_ptr) (iter_state_of sub2 sol2 body2) in
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
        let cell3 = cell_at m (version_at sub3 body3 frame_ptr) (iter_state_of sub3 sol3 body3) in
        check "BK-08" (Ws.is_top cell3));

    pin "BK-09"
      "the multi-def base refines through the per-block producer subtraction — \
       the body-IN cell at RSP-8 is the EXACT taken-edge window [1,10] (1 ∈, \
       10 ∈, 0 ∉, 11 ∉; non-top)"
      (fun () ->
        let m4 = memv "l3c1_m4" in
        let rsp4 = sp in
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
        (* The cell lives at RSP-8, so it is read through the frame
           pointer's own version: the body holds that version. *)
        let cell4 =
          cell_at m4 (version_at sub4 b_tid sp)
            (Graphlib.Std.Solution.get sol4 b_tid)
        in
        check "BK-09"
          ((not (Ws.is_top cell4))
          && (not (Ws.is_bottom cell4))
          && Ws.elem (w32 1) cell4
          && Ws.elem (w32 10) cell4
          && not (Ws.elem (w32 0) cell4)
          && not (Ws.elem (w32 11) cell4)));



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
          cell_at (memv "l3c2_m") (version_at sub1 body1 frame_ptr) (iter_state_of sub1 sol1 body1)
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
          cell_at (memv "l3c2_m") (version_at sub2 body2 frame_ptr) (iter_state_of sub2 sol2 body2)
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
          cell_at (memv "l3c2_m") (version_at sub3 body3 frame_ptr) (iter_state_of sub3 sol3 body3)
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
          cell_at (memv "l3c2_m") (version_at sub4 body4 frame_ptr) (iter_state_of sub4 sol4 body4)
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
          cell_at (memv "l3c2_m") (version_at sub5 body5 frame_ptr) (iter_state_of sub5 sol5 body5)
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
      "the ARSHIFT inverse preserves negative inputs and bounds the positive half"
      (fun () ->
        let t = Var.create ~is_virtual:false ~fresh:false "l3c3_t" (Type.Imm 32) in
        let sub4b, body4b =
          mk_l3c3_loop ~seed:None
            ~chain:(Bil.BinOp (Bil.ARSHIFT, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 2))))
            ~cmp:Bil.SLT ~c:(w32 10) ~body_k:(w32 4)
        in
        let cell = l3c3_run sub4b body4b in
        check "BK-21" (Ws.elem (w32 0x80000000) cell
          && Ws.elem (w32 0xFFFFFFFF) cell && Ws.elem (w32 39) cell
          && not (Ws.elem (w32 40) cell)));



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
        check "BK-23" (Ws.is_bottom (l3c3_run sub6 body6)));

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
        check "BK-25" (let c = l3c4_run sub2 body2 in not (Ws.is_bottom c) && not (bounded_above c (w32 1000))));

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
        check "BK-28" (Ws.is_top (l3c4_run sub5 body5)));

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
        check "BK-30" (Ws.is_top (l3c5_run sub2 body2)));

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



    pin "BK-33"
      "an Unknown condition — the fixpoint completes and constrain_edge keeps \
       the env unchanged (the shrunk catch-all, never asserts)"
      (fun () ->
        let m4 = memv "l3c5_m" in
        let rsp4 = sp in
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
          (AI.equal (Vsa.Test_seam.constrain_edge ~synth:Hike.Synth.empty ~landmarks:(Cbat_landmarks.create ()) ~env:h_st4 (Jmp.cond jmp4)) h_st4));

    (* L-3b: the equal-lower merge arm and the partition views. *)


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
        (* The iterate view: the body holds the frame pointer's version, so
           the cell denotes through the load. *)
        let icell =
          cell_at (memv "l3b1_m") (version_at sub1 body1 sp)
            (Graphlib.Std.Solution.get sol1 body1)
        in
        (* The exit view holds no frame pointer: its cell is read from the
           memory map itself. *)
        let ecell =
          frame_cell ~width:32 (memv "l3b1_m")
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



    (* B-1: interrupt edges. *)
    pin "BK-37"
      "an interrupt edge is an unknown external callee — the continuation \
       receives the RSP anchor (the symbolic segment base at offset 0), and \
       the caller's SSA version survives the unknown callee (a version is \
       never redefined)"
      (fun () ->
        let rsp = sp in
        let rdi = int_param 0 in
        let keep = v64 "l37_keep" in
        let arg = v64 "l37_arg" in
        let sub, tids =
          sub_of "l37_intr"
            [ [], [ (1, mk_goto) ];
              [ Def.create rdi (Bil.Int (Cbat_word.to_word (w64 42))) ],
              [ (2, fun t -> Jmp.create (Int (0x80, t))); (2, mk_goto) ];
              [ Def.create keep (Bil.Var rsp); Def.create arg (Bil.Var rdi) ], [] ]
        in
        let cont_tid = tids.(2) in
        let sol = run_anchored sub in
        let cont_st = Graphlib.Std.Solution.get sol cont_tid in
        (* The continuation reads both values, so they are the versions
           it receives; the state holds versions, not ABI lanes. *)
        check "BK-37.frame-anchor"
          (Ws.equal (value_at sub sol cont_tid sp) (Ws.stack_word_i64 0L));
        check "BK-37.caller-value"
          (Ws.equal (value_at sub sol cont_tid rdi) (Ws.singleton (w64 42)));
        check "BK-37.lane-not-delivered"
          (Ws.is_top (AI.find_word 64 cont_st rdi)));

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
          let of2 = abi_of in
          let sf2 = abi_sf in
          let zf2 = abi_zf in
          mk_l39_loop ~seed:(w32 0) ~c:(w32 3) ~body_op:Bil.PLUS ~body_k:(w32 1)
            ~mk_cond:(fun ~cf:_ ~ofv:_ ~sf:_ ~zf:_ -> l39_jle zf2 sf2 of2)
            ~extra_header_defs:(fun m ->
              let rsp2 = sp in
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
       ret pops exactly the retaddr the caller pushed, the program's restore def) keeps the header RSP at \
       EXACTLY the pre-push {0x1000} (bounded, no drift)"
      (fun () ->
        let sub, header_tid, _ = mk_e1_loop_sub () in
        let rsp_hdr = sp_after_block sub (run_ssa_anchored sub) header_tid in
        check "BK-44" (Ws.equal rsp_hdr (Ws.singleton (w64 0x1000))));

    pin "BK-45"
      "straight-line call RSP exactness — the continuation RSP is EXACTLY the \
       pre-call singleton {0x2000} (the exact truth, not truth−8 = {0x1ff8})"
      (fun () ->
        let sub, post_tid, _ = mk_e1_flat_sub () in
        let rsp_post = sp_after_block sub (run_ssa_anchored sub) post_tid in
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
          && Cbat_word.leq_int (Ws.cardinality cell1) 64
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
        check "BK-48" (Ws.elem (w32 8) cell2 && not (bounded_above cell2 (w32 4))));

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
          && Cbat_word.to_int_exn (Ws.cardinality cell1) = 5
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
       to {−7, −6} (0xFFFFFFF9 ∈, 0xFFFFFFFA ∈, −5 ∉)"
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
          && Ws.elem (w32 0xFFFFFFF9) cell5
          && not (Ws.elem (w32 0xFFFFFFFB) cell5)
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
          t_add_cell (mk_seed_state t_rsp t_rbp ()) (Ws.stack_word_i64 (-8L))
            (bk_iv64 ~lo:0 ~hi:20)
        in
        let env1 =
          Vsa.Test_seam.constrain_operands ~synth:Hike.Synth.empty ~landmarks:(Cbat_landmarks.create ()) ~env:st1
            (t_load_exp
               (Bil.BinOp (Bil.MINUS, Bil.Var t_rsp, Bil.Int (Cbat_word.to_word (w64 8)))))
            (bk_iv64 ~lo:0 ~hi:9)
        in
        check "BK-57"
          (let v = t_cell_at env1 (Ws.stack_word_i64 (-8L)) in
           Ws.elem (w64 9) v && not (Ws.elem (w64 15) v)));

    pin "BK-58"
      "S6: a dynamic-index read spans several cells, so the read's value \
       constraint is not met into each — the cells keep their stored values"
      (fun () ->
        let st2 =
          let s =
            t_add_cell (mk_seed_state t_rsp t_rbp ()) (Ws.stack_word_i64 0L)
              (bk_iv64 ~lo:0 ~hi:20)
          in
          t_add_cell s (Ws.stack_word_i64 40L) (bk_iv64 ~lo:0 ~hi:20)
        in
        let st2 = AI.add_word st2 ~key:t_idx ~data:(bk_iv64 ~lo:0 ~hi:4) in
        let env2 =
          Vsa.Test_seam.constrain_operands ~synth:Hike.Synth.empty ~landmarks:(Cbat_landmarks.create ()) ~env:st2
            (t_load_exp
               (Bil.BinOp
                  ( Bil.PLUS,
                    Bil.Var t_rbp,
                    Bil.BinOp (Bil.TIMES, Bil.Var t_idx, Bil.Int (Cbat_word.to_word (w64 8))) )))
            (bk_iv64 ~lo:0 ~hi:9)
        in
        check "BK-58"
          (let v0 = t_cell_at env2 (Ws.stack_word_i64 0L) in
           let v40 = t_cell_at env2 (Ws.stack_word_i64 40L) in
           Ws.elem (w64 15) v0 && Ws.elem (w64 15) v40));

    pin "BK-59"
      "S6: a ranged read that only partly overlaps the stored cell is not met \
       into it — the cell keeps its stored value"
      (fun () ->
        let st3 =
          t_add_cell (mk_seed_state t_rsp t_rbp ()) (Ws.stack_word_i64 0L)
            (bk_iv64 ~lo:0 ~hi:20)
        in
        let st3 = AI.add_word st3 ~key:t_idx ~data:(bk_iv64 ~lo:4 ~hi:12) in
        let env3 =
          Vsa.Test_seam.constrain_operands ~synth:Hike.Synth.empty ~landmarks:(Cbat_landmarks.create ()) ~env:st3
            (t_load_exp (Bil.BinOp (Bil.PLUS, Bil.Var t_rbp, Bil.Var t_idx)))
            (bk_iv64 ~lo:0 ~hi:9)
        in
        check "BK-59"
          (let v0 = t_cell_at env3 (Ws.stack_word_i64 0L) in
           Ws.elem (w64 15) v0));

    pin "BK-60"
      "S6: the dynamic-index read meets no cell — the cells at 0, 40 and 80 all \
       keep their stored values"
      (fun () ->
        let st4 =
          let s =
            t_add_cell (mk_seed_state t_rsp t_rbp ()) (Ws.stack_word_i64 0L)
              (bk_iv64 ~lo:0 ~hi:20)
          in
          let s = t_add_cell s (Ws.stack_word_i64 40L) (bk_iv64 ~lo:0 ~hi:20) in
          t_add_cell s (Ws.stack_word_i64 80L) (bk_iv64 ~lo:0 ~hi:20)
        in
        let st4 = AI.add_word st4 ~key:t_idx ~data:(bk_iv64 ~lo:0 ~hi:4) in
        let env4 =
          Vsa.Test_seam.constrain_operands ~synth:Hike.Synth.empty ~landmarks:(Cbat_landmarks.create ()) ~env:st4
            (t_load_exp
               (Bil.BinOp
                  ( Bil.PLUS,
                    Bil.Var t_rbp,
                    Bil.BinOp (Bil.TIMES, Bil.Var t_idx, Bil.Int (Cbat_word.to_word (w64 8))) )))
            (bk_iv64 ~lo:0 ~hi:9)
        in
        check "BK-60"
          (let v0 = t_cell_at env4 (Ws.stack_word_i64 0L) in
           let v40 = t_cell_at env4 (Ws.stack_word_i64 40L) in
           let v80 = t_cell_at env4 (Ws.stack_word_i64 80L) in
           Ws.elem (w64 15) v0 && Ws.elem (w64 15) v40 && Ws.elem (w64 15) v80));

    (* The guard's operand windows observed through the inverse denote: on a
       TOP env the leaf meet preserves the raw row. *)



















    pin "BK-71" "the NEG row — the neg'd [0,9]: 0 ∈, −1 ∈"
      (fun () ->
        let s11 =
          Vsa.Test_seam.constrain_operands ~synth:Hike.Synth.empty ~landmarks:(Cbat_landmarks.create ()) ~env:(mk_env [])
            (Bil.BinOp (Bil.LT, Bil.UnOp (Bil.NEG, Bil.Var s_t), Bil.Int (Cbat_word.to_word (s_r32 10))))
            (Ws.singleton (Cbat_word.of_word Word.b1))
        in
        let c11 = s_w32_of_env s11 s_t in
        check "BK-71" (Ws.elem (s_r32 0) c11 && Ws.elem (s_r32 0xFFFFFFFF) c11));





    pin "BK-74"
      "the SIGNED ext row — the pre-image [0, 0xFF] on a top env; the meet with \
       {0x100} is empty, so the env is the dead-path bottom (observed)"
      (fun () ->
        let env15b = mk_env [ (s_t, Ws.singleton (s_r32 0x100)) ] in
        let env15b' =
          Vsa.Test_seam.constrain_operands ~synth:Hike.Synth.empty ~landmarks:(Cbat_landmarks.create ()) ~env:env15b
            (Bil.BinOp
               ( Bil.LT,
                 Bil.Cast (Bil.SIGNED, 64, Bil.Var s_t),
                 Bil.Int (Cbat_word.to_word (Cbat_word.of_int ~width:64 0x100)) ))
            (Ws.singleton (Cbat_word.of_word Word.b1))
        in
        let c15b = s_w32_of_env env15b' s_t in
        let row15b =
          s_w32_of_env
            (Vsa.Test_seam.constrain_operands ~synth:Hike.Synth.empty ~landmarks:(Cbat_landmarks.create ()) ~env:(mk_env [])
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
          && AI.equal env15b' AI.bottom && Ws.is_bottom c15b));

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
            (Vsa.Test_seam.constrain_operands ~synth:Hike.Synth.empty ~landmarks:(Cbat_landmarks.create ()) ~env:env16
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
          Vsa.Test_seam.constrain_operands ~synth:Hike.Synth.empty ~landmarks:(Cbat_landmarks.create ()) ~env:env16c
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
             (Vsa.Test_seam.constrain_operands ~synth:Hike.Synth.empty ~landmarks:(Cbat_landmarks.create ()) ~env:(mk_env [])
                (Bil.Int (Cbat_word.to_word (s_r32 5)))
                (Ws.singleton (s_r32 7)))
             AI.bottom
          && AI.equal
               (Vsa.Test_seam.constrain_operands ~synth:Hike.Synth.empty ~landmarks:(Cbat_landmarks.create ()) ~env:(mk_env [])
                  (Bil.Int (Cbat_word.to_word (s_r32 5)))
                  (Ws.singleton (s_r32 5)))
               (mk_env [])));



    pin "BK-80"
      "the Ite inverse with a true condition — only the true branch is constrained"
      (fun () ->
        let env10 =
          mk_env [ (s_t, bk_iv32 ~lo:0 ~hi:10); (s_u, bk_iv32 ~lo:0 ~hi:10) ]
        in
        let env10' =
          Vsa.Test_seam.constrain_operands ~synth:Hike.Synth.empty ~landmarks:(Cbat_landmarks.create ()) ~env:env10
            (Bil.Ite (Bil.Int Word.b1, Bil.Var s_t, Bil.Var s_u))
            (Ws.singleton (s_r32 5))
        in
        check "BK-80"
          (Ws.elem (s_r32 5) (s_w32_of_env env10' s_t)
          && Ws.equal (s_w32_of_env env10' s_u)
               (AI.find_word 32 env10 (Var.base s_u))));

    pin "BK-81"
      "the Ite inverse with an unknown condition — both branches keep their state"
      (fun () ->
        let c11 = Var.create ~is_virtual:true ~fresh:false "s_c11" (Type.Imm 1) in
        let env11 =
          mk_env
            [ (s_t, bk_iv32 ~lo:0 ~hi:10); (s_u, bk_iv32 ~lo:0 ~hi:10);
              (c11, Ws.top 1) ]
        in
        let env11' =
          Vsa.Test_seam.constrain_operands ~synth:Hike.Synth.empty ~landmarks:(Cbat_landmarks.create ()) ~env:env11
            (Bil.Ite (Bil.Var c11, Bil.Var s_t, Bil.Var s_u))
            (Ws.singleton (s_r32 5))
        in
        check "BK-81"
          (Ws.equal (s_w32_of_env env11' s_t)
             (AI.find_word 32 env11 (Var.base s_t))
          && Ws.equal (s_w32_of_env env11' s_u)
               (AI.find_word 32 env11 (Var.base s_u))));



    pin "BK-83"
      "the AND singleton mask keeps the constrained bits and leaves the rest \
       free — the hull [0x30, 0xFFFFFF3F]"
      (fun () ->
        let env13 =
          Vsa.Test_seam.constrain_operands ~synth:Hike.Synth.empty ~landmarks:(Cbat_landmarks.create ())
            ~env:(mk_env [])
            (Bil.BinOp (Bil.AND, Bil.Var s_t,
               Bil.Int (Cbat_word.to_word (s_r32 0xF0))))
            (Ws.singleton (s_r32 0x30))
        in
        let r = s_w32_of_env env13 s_t in
        check "BK-83"
          (Ws.elem (s_r32 0x30) r
          && Ws.elem (s_r32 0xFFFFFF3F) r
          && (not (Ws.elem (s_r32 0x2F) r))
          && not (Ws.elem (s_r32 0xFFFFFF40) r)));

    pin "BK-84"
      "the low cast of a zero-extended narrow value — low:32[pad:64[x]] — \
       collapses to x: the constraint [0,0xF] narrows x to [0,0xF], not the \
       truncation hull"
      (fun () ->
        let x = Var.create ~is_virtual:true ~fresh:false "bk_x" (Type.Imm 32) in
        let env = mk_env [ (x, bk_iv32 ~lo:0 ~hi:0xFFFFFFFF) ] in
        let widened = Bil.Cast (Bil.UNSIGNED, 64, Bil.Var x) in
        let env' =
          Vsa.Test_seam.constrain_operands ~synth:Hike.Synth.empty ~landmarks:(Cbat_landmarks.create ())
            ~env (Bil.Cast (Bil.LOW, 32, widened)) (bk_iv32 ~lo:0 ~hi:0xF)
        in
        let r = AI.find_word 32 env' (Var.base x) in
        check "BK-84"
          (Ws.min_elem r = Some (w32 0) && Ws.max_elem r = Some (w32 0xF)));

    pin "BK-85"
      "a signed guard over low:32[x] keeps the valid value 2 and excludes both values whose low word is 16"
      (fun () ->
        let x = Var.create ~is_virtual:true ~fresh:false "bk85_x" (Type.Imm 64) in
        let y = Var.create ~is_virtual:true ~fresh:false "bk85_y" (Type.Imm 32) in
        let out = Cbat_word.of_int64 ~width:64 0xFFFFFFFF00000010L in
        let env =
          mk_env
            [ (x, Ws.of_list ~width:64 [ w64 2; w64 0x10; out ]);
              (y, Ws.singleton (w32 4)) ]
        in
        let env' =
          Vsa.Test_seam.constrain_operands ~synth:Hike.Synth.empty ~landmarks:(Cbat_landmarks.create ())
            ~env
            (Bil.BinOp
               ( Bil.SLT,
                 Bil.Cast (Bil.LOW, 32, Bil.Var x),
                 Bil.Var y ))
            (Ws.singleton (Cbat_word.of_word Word.b1))
        in
        let r = AI.find_word 64 env' (Var.base x) in
        check "BK-85" (Ws.elem (w64 2) r && not (Ws.elem (w64 0x10) r) && not (Ws.elem out r)));

    pin "BK-86"
      "a guard the operand already satisfies is still seeded — the \
       flag-indirected loop head (CF := t < 100; if CF goto body) seeds CF at \
       its post state (CF = {0,1}: the widened counter's range admits both \
       outcomes, so the edge constraint is not the identity); the body's cell \
       at RBP-8 is the widened two-piece counter hull (its signed bound is 99)"
      (fun () ->
        let m = memv "l3c2_m" in
        let cf = v1 "l3c2_cf" in
        let sub1, body1 =
          mk_l3c2_loop ~prologue:true ~seed:(Some (w32 0)) ~cmp:Bil.SLT
            ~c:(w32 100) ~body_op:Bil.PLUS ~body_k:(w32 1) ~flag:true
        in
        let sol1 = run_anchored sub1 in
        let cell1 =
          cell_at m (version_at sub1 body1 frame_ptr) (iter_state_of sub1 sol1 body1)
        in
        (* The head is the block that defines the flag. *)
        let header_tid =
          Term.enum blk_t sub1 |> Seq.find_map ~f:(fun b ->
              if Term.enum def_t b |> Seq.exists ~f:(fun d ->
                      Var.same (Var.base (Def.lhs d)) cf)
              then Some (Term.tid b)
              else None)
          |> Base.Option.value_exn
        in
        let cfv = value_after sub1 sol1 header_tid cf in
        check "BK-86.flag-seeded"
          (not (Ws.is_bottom cfv)
          && Ws.elem Cbat_word.b0 cfv
          && Ws.elem Cbat_word.b1 cfv);
        check "BK-86.cell"
          (Ws.max_elem_signed cell1 = Some (w32 99)
          && Ws.elem (w32 0x80000000) cell1
          && Ws.elem (w32 99) cell1));

    (* ---------------------------------------------------------------- *)
    (* T07 / A4: the four-way table. *)

    pin "BK-87"
      "A4 table — syntactic x cast-UNSIGNED: the compared var is defined by \
       Cast(UNSIGNED,64,t).  The exit edge stays live, the head's cell keeps \
       the reachable exit value 4, and the body's cell excludes it (the \
       refinement fired)"
      (fun () ->
        let live, keeps, fired =
          a4_cell ~op:(Bil.Cast (Bil.UNSIGNED, 64, Bil.Var a4_t)) ~v_w:64
            ~c:(w64 4) ~exit:(w32 4) ~seed:(w32 0) ~body_k:(w32 1)
            ~inline:false
        in
        check "BK-87.live" live;
        check "BK-87.head-keeps" keeps;
        check "BK-87.body-excludes" fired);

    pin "BK-88"
      "A4 table — syntactic x extract-hull: the compared var is defined by \
       Extract(31,16,t) (the top half-word).  The exit edge stays live, the \
       head's cell keeps the reachable exit value 0x40000, and the body's \
       cell excludes it (the operand constraint [0, 0x3FFFF] is exact here)"
      (fun () ->
        let live, keeps, fired =
          a4_cell ~op:(Bil.Extract (31, 16, Bil.Var a4_t)) ~v_w:16
            ~c:(a4_w16 4) ~exit:(w32 0x40000) ~seed:(w32 0)
            ~body_k:(w32 0x10000) ~inline:false
        in
        check "BK-88.live" live;
        check "BK-88.head-keeps" keeps;
        check "BK-88.body-excludes" fired);

    pin "BK-89"
      "A4 table — range x cast-UNSIGNED: the guard's operand is \
       Cast(UNSIGNED,64,t) itself.  The exit edge stays live, the head's cell \
       keeps the reachable exit value 4, and the body's cell excludes it"
      (fun () ->
        let live, keeps, fired =
          a4_cell ~op:(Bil.Cast (Bil.UNSIGNED, 64, Bil.Var a4_t)) ~v_w:64
            ~c:(w64 4) ~exit:(w32 4) ~seed:(w32 0) ~body_k:(w32 1)
            ~inline:true
        in
        check "BK-89.live" live;
        check "BK-89.head-keeps" keeps;
        check "BK-89.body-excludes" fired);

    pin "BK-90"
      "A4 table — range x extract-hull: the guard's operand is \
       Extract(31,16,t) itself.  The exit edge stays live, the head's cell \
       keeps the reachable exit value 0x40000, and the body's cell excludes \
       it"
      (fun () ->
        let live, keeps, fired =
          a4_cell ~op:(Bil.Extract (31, 16, Bil.Var a4_t)) ~v_w:16
            ~c:(a4_w16 4) ~exit:(w32 0x40000) ~seed:(w32 0)
            ~body_k:(w32 0x10000) ~inline:true
        in
        check "BK-90.live" live;
        check "BK-90.head-keeps" keeps;
        check "BK-90.body-excludes" fired);

    (* ---------------------------------------------------------------- *)
    (* T07 / A4 candidate 3: [evidence_constraint]'s non-negativity proof.
       It reads the operand's CURRENT denotation and tests its UNSIGNED
       max against the half line.  A wrapping set has a low unsigned max
       and high (negative) elements, so the proof fires on a set that is
       not non-negative and the SLT/SLE evidence row drops the reachable
       negatives. *)

    pin "BK-91"
      "A4 candidate — the wrapping cur [0xFFFFFFF0, 0x10] has unsigned max \
       0x10 < 2^31, so the SLT evidence row [0,4] drops the reachable value \
       0xFFFFFFF0 (signed −16 <s 5)"
      (fun () ->
        let cur =
          Ws.of_clp (Clp.interval ~width:32 (s_r32 0xFFFFFFF0) (s_r32 0x10))
        in
        let env = mk_env [ (s_t, cur) ] in
        let env' =
          Vsa.Test_seam.constrain_operands ~synth:Hike.Synth.empty
            ~landmarks:(Cbat_landmarks.create ()) ~env
            (Bil.BinOp (Bil.SLT, Bil.Var s_t, Bil.Int (Cbat_word.to_word (s_r32 5))))
            (Ws.singleton (Cbat_word.of_word Word.b1))
        in
        check "BK-91" (Ws.elem (s_r32 0xFFFFFFF0) (s_w32_of_env env' s_t)));

    pin "BK-92"
      "A4 loop — a wrapping counter (seeded 0xFFFFFFFE, +1, guard SLT(t,2)): \
       the reachable head values are {0xFFFFFFFE, 0xFFFFFFFF, 0, 1, 2}; the \
       body's IN cell must keep the negatives and the guard must stay able \
       to be false at the head"
      (fun () ->
        let cond =
          Bil.BinOp (Bil.SLT, Bil.Var a4_t, Bil.Int (Cbat_word.to_word (s_r32 2)))
        in
        let sub, body_tid =
          mk_l3_chain_loop ~name:"a4" ~seed:(Some (s_r32 0xFFFFFFFE)) ~v_w:32
            ~chain:None ~cond ~body_k:(w32 1)
        in
        let sol = run_anchored sub in
        let head = List.nth (Term.enum blk_t sub |> Seq.to_list) 2 in
        let head_in = Graphlib.Std.Solution.get sol (Term.tid head) in
        let head_post = Vsa.Test_seam.denote_defs ~synth:Hike.Synth.empty head head_in in
        let cond_ws =
          match Vsa.Test_seam.denote_imm_exp ~synth:Hike.Synth.empty cond head_post with
          | Ok ws -> ws
          | Error _ -> failwith "a4: the guard does not denote"
        in
        let body_cell =
          cell_at (memv "a4_m") (version_at sub body_tid frame_ptr)
            (Graphlib.Std.Solution.get sol body_tid)
        in
        check "BK-92.keeps" (Ws.elem (s_r32 0xFFFFFFFE) body_cell);
        check "BK-92.live" (Ws.elem Cbat_word.b0 cond_ws));

    pin "BK-94"
      "the extract constraint — Extract(15,0,x) constrained to [0,3]: the \
       operand constraint is [0, 0xFFFF0003] (the largest x whose low half \
       is <= 3), so the rule fires and its hull is the exact reachable \
       maximum"
      (fun () ->
        let x = Var.create ~is_virtual:true ~fresh:false "bk94_x" (Type.Imm 32) in
        let env = mk_env [ (x, Ws.top 32) ] in
        let cstr16 = Ws.of_clp (Clp.interval ~width:16 (a4_w16 0) (a4_w16 3)) in
        let env' =
          Vsa.Test_seam.constrain_operands ~synth:Hike.Synth.empty
            ~landmarks:(Cbat_landmarks.create ()) ~env
            (Bil.Extract (15, 0, Bil.Var x)) cstr16
        in
        let r = AI.find_word 32 env' (Var.base x) in
        check "BK-94.fires" (not (Ws.equal r (Ws.top 32)));
        check "BK-94.max" (Ws.max_elem r = Some (s_r32 0xFFFF0003)));

    pin "BK-93"
      "A4 table — the BASE cell (no cast/extract anywhere): the guard compares \
       the loaded var directly.  The exit edge stays live, the head's cell \
       keeps the reachable exit value 4, and the body's cell excludes it"
      (fun () ->
        let cond =
          Bil.BinOp (Bil.LT, Bil.Var a4_t, Bil.Int (Cbat_word.to_word (w32 4)))
        in
        let sub, body_tid =
          mk_l3_chain_loop ~name:"a4" ~seed:(Some (w32 0)) ~v_w:32 ~chain:None
            ~cond ~body_k:(w32 1)
        in
        let sol = run_anchored sub in
        let head = List.nth (Term.enum blk_t sub |> Seq.to_list) 2 in
        let head_in = Graphlib.Std.Solution.get sol (Term.tid head) in
        let head_post = Vsa.Test_seam.denote_defs ~synth:Hike.Synth.empty head head_in in
        let cond_ws =
          match Vsa.Test_seam.denote_imm_exp ~synth:Hike.Synth.empty cond head_post with
          | Ok ws -> ws
          | Error _ -> failwith "a4: the guard does not denote"
        in
        (* The cell at RBP-8 in each block's own state: every block
           carries its own frame-pointer version. *)
        let cell_in tid st =
          cell_at (memv "a4_m") (version_at sub tid frame_ptr) st in
        check "BK-93.live" (Ws.elem Cbat_word.b0 cond_ws);
        check "BK-93.head-keeps" (Ws.elem (w32 4) (cell_in (Term.tid head) head_in));
        check "BK-93.body-excludes"
          (not (Ws.elem (w32 4)
                 (cell_in body_tid (Graphlib.Std.Solution.get sol body_tid)))));

    pin "BK-97"
      "the low-cast guard window reads the operand's reachable set —        SLT(low:32[x], 8) true with x = {0..9}: the pre-image is the        populated window's piece only, so x reads {0..7} (the wide hull        would keep the full range and never bound a counter)"
      (fun () ->
        let x = Var.create ~is_virtual:true ~fresh:false "k97_x" (Type.Imm 64) in
        let ws09 =
          let ws = ref (Ws.bottom 64) in
          for k = 0 to 9 do
            ws := Ws.union !ws (Ws.singleton (w64 k))
          done;
          !ws in
        let env = AI.add_word AI.top ~key:x ~data:ws09 in
        let env' =
          Vsa.Test_seam.constrain_operands ~synth:Hike.Synth.empty
            ~landmarks:(Cbat_landmarks.create ()) ~env
            (Bil.BinOp (Bil.SLT, Bil.Cast (Bil.LOW, 32, Bil.Var x),
                        Bil.Int (Cbat_word.to_word (w32 8))))
            (Ws.singleton (Cbat_word.of_word Word.b1)) in
        let r = AI.find_word 64 env' (Var.base x) in
        check "BK-97"
          (Ws.min_elem r = Some (w64 0) && Ws.max_elem r = Some (w64 7)));

    (* T10 continuation: the -O0 store-head loop (the increment store in
       the walked block), the guard's bound in a cell.  The taken edge
       admits t in {0,1}, so the head's IN counter cell must stay bounded
       (the loop exits at 2) whatever shape the increment store takes. *)
    pin "BK-98"
      "the nested-load increment store (mem[c] := mem[c] + 1) inside the \
       walked head block — the guard's bound cell still bounds the counter \
       cell through the walk's store handshake (the head's IN cell at \
       RBP-8 stays within {0..2}, never the 32-bit range)"
      (fun () ->
        let sub, head_tid =
          mk_l3c6_storehead_loop ~nested:true ~seed:(Some (w32 0)) ~bound:(w32 2) in
        let sol = run_anchored sub in
        let cell =
          cell_at (memv "l3c6_m") (version_at sub head_tid frame_ptr) (iter_state_of sub sol head_tid) in
        check "BK-98" (bounded_above cell (w32 2)));

    pin "BK-99"
      "the def-carried increment (v := t + 1; mem[c] := v) in the same \
       walked head block bounds the same counter cell — the control for \
       BK-98's nested shape"
      (fun () ->
        let sub, head_tid =
          mk_l3c6_storehead_loop ~nested:false ~seed:(Some (w32 0)) ~bound:(w32 2) in
        let sol = run_anchored sub in
        let cell =
          cell_at (memv "l3c6_m") (version_at sub head_tid frame_ptr) (iter_state_of sub sol head_tid) in
        check "BK-99" (bounded_above cell (w32 2)));

    (* ---------------------------------------------------------------- *)
    (* A5: the walk's write sites skip what changes nothing, and the
       collapsed seed delivers the walked state's own value.  The
       counting refine names each actual env write, so an equal delivery
       is observable as a missing count, never as the returned env. *)

    pin "BK-95"
      "the replay's write sites skip a fact that changes nothing — the \
       load's read fact already narrows x, so x's output fact and the \
       guard def's {1} write nothing; the block's input fact (the guard's \
       operand) narrows the entry once, while the unconsumed seed u names no \
       local def and so carries no fact of its own"
      (fun () ->
        let m = memv "w5_m" in
        let rsp = sp in
        let rbp = frame_ptr in
        let x = Var.create ~is_virtual:false ~fresh:false "w5_x" (Type.Imm 32) in
        let zf = v1 "w5_zf" in
        let addr =
          Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8)))
        in
        let sub, tids =
          sub_of "w5_skip"
            [ [ Def.create rbp (Bil.Var rsp) ], [ (1, mk_goto) ];
              [ Def.create x (Bil.Load (Bil.Var m, addr, LittleEndian, `r32));
                Def.create zf
                  (Bil.BinOp
                     (Bil.SLT, Bil.Var x, Bil.Int (Cbat_word.to_word (w32 5)))) ],
              [ (2, mk_goto) ];
              [ Def.create m
                  (Bil.Store
                     ( Bil.Var m, addr,
                       Bil.Int (Cbat_word.to_word (w32 5)),
                       LittleEndian, `r32 )) ],
              [] ]
        in
        let guard_tid = tids.(1) in
        let ssa = sub in
        let entry =
          AI.add_memory (anchored_entry ()) ~key:m
            ~data:(Mem.top { Mem.addr_width = 64; Mem.addressable_width = 8 })
        in
        let sol =
          static_graph_vsa ~synth:Hike.Synth.empty ~abi:Hike_abi.x86_64_sysv
            sub
            (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv ~entry sub)
        in
        let rctx = mk_rctx ~synth:Hike.Synth.empty ~abi:Hike_abi.x86_64_sysv ssa in
        let guard_blk =
          Term.enum blk_t ssa |> Seq.to_list
          |> List.find (fun b -> Tid.equal (Term.tid b) guard_tid)
        in
        let zf = version_at ssa guard_tid zf in
        let edge_env =
          AI.add_word (Graphlib.Std.Solution.get sol guard_tid) ~key:zf
            ~data:(Ws.singleton Cbat_word.b1)
        in
        (* The read fact narrows x before its def; the output facts are
           then the replayed values (no write). *)
        let out, output_writes, input_writes =
          Vsa.Test_seam.refine_edge_count_writes ~sol ~rctx
            ~seeds:(Var.Set.singleton zf) edge_env guard_blk
        in
        check "BK-95.output-equal" (output_writes = 0);
        check "BK-95.input-none" (input_writes = 0);
        (* The guard's signed row reaches x: the two-piece SLT pre-image
           [0,4] u [2^31, max] (the loaded value's non-negativity is not
           proven). *)
        check "BK-95.row"
          ((not (Ws.is_top (wr_value ssa guard_tid out x)))
          && Ws.max_elem_signed (wr_value ssa guard_tid out x) = Some (w32 4)
          && Ws.elem (w32 0x80000000) (wr_value ssa guard_tid out x));
        (* The input site: the guard block defines x nowhere, so the
           operand's fact holds at the entry, where it strictly narrows;
           the unconsumed seed u names no local def, so the SSA walk
           carries no fact for it. *)
        let x2 = Var.create ~is_virtual:false ~fresh:false "w5_gx" (Type.Imm 32) in
        let zf2 = v1 "w5_gzf" in
        let u = Var.create ~is_virtual:false ~fresh:false "w5_u" (Type.Imm 32) in
        let sub2, tids2 =
          sub_of "w5_carry"
            [ [ Def.create zf2
                  (Bil.BinOp
                     (Bil.SLT, Bil.Var x2, Bil.Int (Cbat_word.to_word (w32 5)))) ],
              [ (1, mk_goto) ];
              [], [] ]
        in
        let guard2 = tids2.(0) in
        let sol2 =
          static_graph_vsa ~synth:Hike.Synth.empty ~abi:Hike_abi.x86_64_sysv
            sub2
            (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv ~entry:(anchored_entry ()) sub2)
        in
        let rctx2 = mk_rctx ~synth:Hike.Synth.empty ~abi:Hike_abi.x86_64_sysv sub2 in
        let guard2_blk =
          Term.enum blk_t sub2 |> Seq.to_list
          |> List.find (fun b -> Tid.equal (Term.tid b) guard2)
        in
        (* The seed names the block's own definition. *)
        let zf2 = version_at sub2 guard2 zf2 in
        let out2, output2, input2 =
          Vsa.Test_seam.refine_edge_count_writes ~sol:sol2 ~rctx:rctx2
            ~seeds:(Core.Set.union (Var.Set.singleton zf2) (Var.Set.singleton u))
            (AI.add_word
               (AI.add_word (Graphlib.Std.Solution.get sol2 guard2) ~key:zf2
                  ~data:(Ws.singleton Cbat_word.b1))
               ~key:u ~data:(bk_iv32 ~lo:2 ~hi:5))
            guard2_blk
        in
        check "BK-95.output-equal2" (output2 = 0);
        check "BK-95.input" (input2 = 1);
        check "BK-95.seed-kept"
          (Ws.equal (AI.find_word 32 out2 (Var.base u)) (bk_iv32 ~lo:2 ~hi:5)));

    pin "BK-96"
      "the collapsed seed delivers the walked state's own value — the seed \
       vars name the delivery and the walk reads each constraint from the \
       env it walks, so the guard's row reaches x and the unconsumed seed \
       keeps its env value [2,5]"
      (fun () ->
        let x2 = Var.create ~is_virtual:false ~fresh:false "w6_gx" (Type.Imm 32) in
        let zf = v1 "w6_zf" in
        let u = Var.create ~is_virtual:false ~fresh:false "w6_u" (Type.Imm 32) in
        let sub, tids =
          sub_of "w6_seeds"
            [ [ Def.create zf
                  (Bil.BinOp
                     (Bil.SLT, Bil.Var x2, Bil.Int (Cbat_word.to_word (w32 5)))) ],
              [ (1, mk_goto) ];
              [], [] ]
        in
        let guard = tids.(0) in
        let sol =
          static_graph_vsa ~synth:Hike.Synth.empty ~abi:Hike_abi.x86_64_sysv
            sub
            (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv ~entry:(anchored_entry ()) sub)
        in
        let ssa = sub in
        let rctx = mk_rctx ~synth:Hike.Synth.empty ~abi:Hike_abi.x86_64_sysv ssa in
        let guard_blk =
          Term.enum blk_t ssa |> Seq.to_list
          |> List.find (fun b -> Tid.equal (Term.tid b) guard)
        in
        let zf = version_at ssa guard zf in
        let u = version_at ssa guard u in
        let out, _, _ =
          Vsa.Test_seam.refine_edge_count_writes ~sol ~rctx
            ~seeds:(Core.Set.union (Var.Set.singleton zf) (Var.Set.singleton u))
            (AI.add_word
               (AI.add_word (Graphlib.Std.Solution.get sol guard) ~key:zf
                  ~data:(Ws.singleton Cbat_word.b1))
               ~key:u ~data:(bk_iv32 ~lo:2 ~hi:5))
            guard_blk
        in
        check "BK-96.delivered"
          (not (Ws.is_top (wr_value ssa guard out x2)));
        check "BK-96.env-value"
          (Ws.equal (wr_value ssa guard out u) (bk_iv32 ~lo:2 ~hi:5)));

    pin "BK-100"
      "a var rewritten after the def that receives its constraint keeps its \
       edge value: the guard bounds z = y's first value, while the edge y is \
       the later y := u"
      (fun () ->
        let x = wr_v32 "w100_x" and y = wr_v32 "w100_y" and z = wr_v32 "w100_z" in
        let u = wr_v32 "w100_u" and zf = v1 "w100_zf" in
        let out, ssa, tid =
          wr_refine "w100" (memv "w100_m") zf
            [ Def.create y (Bil.Var x);
              Def.create z (Bil.Var y);
              Def.create y (Bil.Var u);
              Def.create zf
                (Bil.BinOp (Bil.SLT, Bil.Var z, Bil.Int (Cbat_word.to_word (w32 5)))) ]
        in
        check "BK-100.guarded"
          (not (Ws.elem (w32 50) (wr_value ssa tid out z)));
        check "BK-100.rewritten-kept"
          (Ws.elem (w32 50) (wr_value ssa tid out y)));

    pin "BK-101"
      "a cell stored after the load the guard reads keeps its edge value: \
       the guard bounds x = the loaded value, while the edge cell holds the \
       later store's u"
      (fun () ->
        let m = memv "w101_m" in
        let x = wr_v32 "w101_x" and u = wr_v32 "w101_u" and zf = v1 "w101_zf" in
        let out, ssa, tid =
          wr_refine "w101" m zf
            [ Def.create x (Bil.Load (Bil.Var m, wr_addr, LittleEndian, `r32));
              Def.create m
                (Bil.Store (Bil.Var m, wr_addr, Bil.Var u, LittleEndian, `r32));
              Def.create zf
                (Bil.BinOp (Bil.SLT, Bil.Var x, Bil.Int (Cbat_word.to_word (w32 5)))) ]
        in
        check "BK-101.guarded"
          (not (Ws.elem (w32 50) (wr_value ssa tid out x)));
        check "BK-101.rewritten-kept"
          (Ws.elem (w32 50) (cell_at m (version_at ssa tid frame_ptr) out)));

    pin "BK-102"
      "a store's data takes the guard's constraint: x is stored, the guard \
       bounds x below 7 (unsigned), and the refined edge state holds x ⊆ [0,6] \
       — clang -O0's spilled switch index"
      (fun () ->
        let m = memv "w102_m" in
        let x = wr_v32 "w102_x" and t = wr_v32 "w102_t" and zf = v1 "w102_zf" in
        let out, ssa, tid =
          wr_refine "w102" m zf
            [ Def.create m
                (Bil.Store (Bil.Var m, wr_addr, Bil.Var x, LittleEndian, `r32));
              Def.create t (Bil.Var x);
              Def.create zf
                (Bil.BinOp (Bil.LT, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 7)))) ]
        in
        check "BK-102"
          (Ws.equal (wr_value ssa tid out x)
             (Ws.of_list ~width:32
                [ w32 0; w32 1; w32 2; w32 3; w32 4; w32 5; w32 6 ])));

    pin "BK-103"
      "a store's cell overwritten later takes nothing from the first \
       store's data: the edge cell holds the later u"
      (fun () ->
        let m = memv "w103_m" in
        let x = wr_v32 "w103_x" and u = wr_v32 "w103_u" in
        let t = wr_v32 "w103_t" and zf = v1 "w103_zf" in
        let out, ssa, tid =
          wr_refine "w103" m zf
            [ Def.create m
                (Bil.Store (Bil.Var m, wr_addr, Bil.Var x, LittleEndian, `r32));
              Def.create m
                (Bil.Store (Bil.Var m, wr_addr, Bil.Var u, LittleEndian, `r32));
              Def.create t (Bil.Var x);
              Def.create zf
                (Bil.BinOp (Bil.LT, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 7)))) ]
        in
        check "BK-103"
          (Ws.elem (w32 50) (cell_at m (version_at ssa tid frame_ptr) out)));

    pin "BK-104"
      "a guard on a loaded value narrows the load's address to the slots \
       whose contents can produce it: x = table[i] with table = [20, 10, \
       20, 30] and x = 20 keep i's slots 0 and 2, so i is bounded by 2"
      (fun () ->
        let m = memv "w104_m" in
        let i = v64 "w104_i" and x = wr_v32 "w104_x" and zf = v1 "w104_zf" in
        let le32 n =
          String.init 4 (fun k -> Char.chr ((n lsr (8 * k)) land 0xff)) in
        let img_bytes = Bytes.of_string (String.concat "" (List.map le32 [ 20; 10; 20; 30 ])) in
        let images =
          [ { Cbat_vsa.img_lo = 0x4000L; img_hi = 0x400FL; img_bytes;
              img_slots = Core.Int64.Set.empty } ] in
        let out, ssa, tid =
          Vsa.with_images images (fun () ->
              wr_refine "w104" m zf
                [ Def.create i
                    (Bil.BinOp (Bil.AND, Bil.Var (int_param 0), Bil.Int (Cbat_word.to_word (w64 3))));
                  Def.create x
                    (Bil.Load
                       ( Bil.Var m,
                         Bil.BinOp
                           ( Bil.PLUS, Bil.Int (Cbat_word.to_word (w64 0x4000)),
                             Bil.BinOp (Bil.LSHIFT, Bil.Var i, Bil.Int (Cbat_word.to_word (w64 2))) ),
                         LittleEndian, `r32 ));
                  Def.create zf
                    (Bil.BinOp (Bil.EQ, Bil.Var x, Bil.Int (Cbat_word.to_word (w32 20)))) ])
        in
        let iv = wr_value ssa tid out i in
        check "BK-104.kept" (Ws.elem (w64 0) iv && Ws.elem (w64 2) iv);
        check "BK-104.dropped" (not (Ws.elem (w64 3) iv)));

    pin "BK-105"
      "T27 step 4: cell coverage is element-level — a strided piece whose \
       span crosses a cell but whose elements never read it is not covered; \
       an element on the cell's bytes (or a read reaching in from below) \
       is"
      (fun () ->
        let mv = Mem.top t_mem_idx in
        let cell =
          t_key_of (Ws.of_clp (Clp.interval ~width:64 (w64 0x1001) (w64 0x1008))) in
        let mv =
          Mem.meet_add mv ~key:cell
            ~data:(Mem.Val.create (Ws.singleton (w64 42)) LittleEndian) in
        let line = (Mem.Key.cell_key cell).Cbat_landmarks.origin in
        let strided base step card =
          Cbat_clp.create ~width:64 ~step:(w64 step)
            ~cardn:(Cbat_word.of_int ~width:65 card) (w64 base) in
        check "BK-105.strided-miss"
          (not
             (Vsa.Test_seam.piece_touches_cell mv ~line ~bytes:1
                (strided 0x1000 0x10 2)));
        check "BK-105.strided-hit"
          (Vsa.Test_seam.piece_touches_cell mv ~line ~bytes:1
             (strided 0x1001 0x10 2));
        check "BK-105.read-reaches-in"
          (Vsa.Test_seam.piece_touches_cell mv ~line ~bytes:2
             (strided 0x1000 0x10 1));
        check "BK-105.dense"
          (Vsa.Test_seam.piece_touches_cell mv ~line ~bytes:1
             (strided 0x1000 1 0x11)));

    pin "BK-106"
      "T27 step 4: image coverage is element-level — the whole read must fit \
       (a dense piece starting past the fit range is not covered), and a \
       strided piece is tested on its own grid, not its span"
      (fun () ->
        let img lo hi =
          [ { Vsa.img_lo = lo; img_hi = hi; img_bytes = Bytes.make 8 '\000';
              img_slots = Core.Int64.Set.empty } ] in
        let strided base step card =
          Cbat_clp.create ~width:64 ~step:(w64 step)
            ~cardn:(Cbat_word.of_int ~width:65 card) (w64 base) in
        let dense lo hi = strided lo 1 (hi - lo + 1) in
        Vsa.with_images (img 0x1000L 0x1007L) (fun () ->
            check "BK-106.dense-fits"
              (Vsa.Test_seam.piece_touches_image ~bytes:8 (dense 0x1000 0x1000));
            check "BK-106.dense-overruns"
              (not
                 (Vsa.Test_seam.piece_touches_image ~bytes:8
                    (dense 0x1001 0x1001)));
            check "BK-106.strided-hit"
              (Vsa.Test_seam.piece_touches_image ~bytes:1
                 (strided 0x1000 0x10 3)));
        Vsa.with_images (img 0x1001L 0x1008L) (fun () ->
            check "BK-106.strided-miss"
              (not
                 (Vsa.Test_seam.piece_touches_image ~bytes:1
                    (strided 0x1000 0x10 2))));
        Vsa.with_images (img 0x1000L 0x1003L) (fun () ->
            check "BK-106.too-short"
              (not
                 (Vsa.Test_seam.piece_touches_image ~bytes:8
                    (dense 0x1000 0x1003)))));

    pin "BK-107"
      "T27 step 4b: a dense multi-element address run partitions in one \
       decision — the image reads that miss the guard value drop on both \
       sides of the kept address (8 kept; 0 and 15 dropped)"
      (fun () ->
        let m = memv "w107_m" in
        let i = v64 "w107_i" in
        let x = wr_v32 "w107_x" and zf = v1 "w107_zf" in
        (* 32 bytes, zero except the one 20 at offset 8: every 4-byte read
           is definite, and only the read at 0x4008 meets the guard. *)
        let img_bytes = Bytes.make 32 '\000' in
        Bytes.set img_bytes 8 (Char.chr 20);
        let images =
          [ { Cbat_vsa.img_lo = 0x4000L; img_hi = 0x401FL; img_bytes;
              img_slots = Core.Int64.Set.empty } ] in
        let out, ssa, tid =
          Vsa.with_images images (fun () ->
              wr_refine "w107" m zf
                [ Def.create i
                    (Bil.BinOp
                       ( Bil.AND,
                         Bil.Var (int_param 0),
                         Bil.Int (Cbat_word.to_word (w64 0xF)) ));
                  Def.create x
                    (Bil.Load
                       ( Bil.Var m,
                         Bil.BinOp
                           ( Bil.PLUS,
                             Bil.Int (Cbat_word.to_word (w64 0x4000)),
                             Bil.Var i ),
                         LittleEndian, `r32 ));
                  Def.create zf
                    (Bil.BinOp
                       ( Bil.EQ,
                         Bil.Var x,
                         Bil.Int (Cbat_word.to_word (w32 20)) )) ])
        in
        let iv = wr_value ssa tid out i in
        check "BK-107.kept" (Ws.elem (w64 8) iv);
        check "BK-107.dropped-low" (not (Ws.elem (w64 0) iv));
        check "BK-107.dropped-high" (not (Ws.elem (w64 15) iv)));

    pin "BK-108"
      "T27 step 4: a same-line cell whose hull starts below nb-1 — the \
       bulk read-start range [cl-(nb-1), ch] wraps.  The wrapped range's \
       elements below the hull and the cell's own read start go through \
       the singleton rule, so the Clp bulk result restricted to the \
       small set is exactly the per-singleton (Exact-tier) result"
      (fun () ->
        let mm = { Mem.addr_width = 64; Mem.addressable_width = 8 } in
        let m = memv "w108_m" in
        let i = v64 "w108_i" in
        let st0 = mk_seed_state t_rsp t_rbp () in
        (* The cell [1, 4] (cl = 1 < nb-1 = 3, so its read-start range
           [cl-3, ch] = [-2, 4] wraps) holds 32-bit 0x33333333; the
           produced guard value 0x99999999 misses it. *)
        let k =
          t_key_of (Ws.of_clp (Clp.interval ~width:64 (w64 1) (w64 4))) in
        let mv0 = AI.find_memory mm st0 m in
        let mv' =
          Mem.meet_add mv0 ~key:k
            ~data:
              (Mem.Val.create (Ws.singleton (w32 0x33333333)) LittleEndian)
        in
        let st0 = AI.add_memory st0 ~key:m ~data:mv' in
        let line = Mem.Key.origin k in
        let produced = Ws.singleton (w32 0x99999999) in
        let run els =
          let st = AI.add_word st0 ~key:i ~data:(Ws.of_list ~width:64 els) in
          let out =
            Vsa.Test_seam.constrain_operands ~synth:Hike.Synth.empty
              ~landmarks:(Cbat_landmarks.create ()) ~env:st
              (Bil.Load (Bil.Var m, Bil.Var i, LittleEndian, `r32))
              produced
          in
          plain_value out i
        in
        (* The per-singleton reference: six elements stay on the exact
           tier, so the filter decides each one alone. *)
        let s = [ w64 0; w64 1; w64 2; w64 3; w64 4; w64 5 ] in
        (* Eight far elements push the same set over the budget, so the
           filter takes the bulk partition with the wrapped range. *)
        let pad = List.init 8 (fun k -> w64 (0x1000 + (4 * k))) in
        let exact = run s in
        let clp = run (List.append s pad) in
        let elem ws x = Ws.elem (w64 x) ws in
        (* The wrap: the read at 0 (below the hull's start) reaches the
           cell only through the back-shifted range. *)
        check "BK-108.read-reaches-in"
          (Vsa.Test_seam.piece_touches_cell mv' ~line ~bytes:4
             (Cbat_clp.singleton (w64 0)));
        (* The old per-singleton result: the read at 1 is the cell's
           value and misses the guard (drop); every other read is top. *)
        check "BK-108.singleton-kept"
          (elem exact 0 && elem exact 2 && elem exact 3 && elem exact 4
          && elem exact 5);
        check "BK-108.singleton-dropped" (not (elem exact 1));
        (* The bulk result is exactly the per-singleton result on the
           common elements, and the padding survives whole. *)
        check "BK-108.elementwise"
          (List.for_all
             (fun x -> elem exact x = elem clp x)
             [ 0; 1; 2; 3; 4; 5 ]);
        check "BK-108.padding" (List.for_all (fun w -> Ws.elem w clp) pad);
        check "BK-108.cardinality"
          (Cbat_word.to_int_exn (Ws.cardinality clp) = 13));

    (* The AND pre-image: [x land k <= vhi] bounds x by the largest
       submask of k at most vhi, every unmasked bit set — vhi's own bits
       outside the mask do not lower it. *)
    pin "BK-109" "the AND-mask pre-image keeps every x whose masked bits satisfy the guard"
      (fun () ->
        let x = Var.create ~is_virtual:false ~fresh:false "bk109_x" (Type.Imm 8) in
        let b8 n = Bil.Int (Word.of_int ~width:8 n) in
        let env = AI.add_word AI.top ~key:x ~data:(Ws.top 8) in
        let refined k vhi =
          AI.find_word 8
            (Vsa.Test_seam.constrain_edge ~synth:Hike.Synth.empty ~landmarks:(Cbat_landmarks.create ()) ~env
               (Bil.BinOp (Bil.LE, Bil.BinOp (Bil.AND, Bil.Var x, b8 k), b8 vhi)))
            x
        in
        let w8 = Cbat_word.of_int ~width:8 in
        check "BK-109.ones" (Ws.elem (w8 0xff) (refined 1 2));
        check "BK-109.max" (Ws.elem (w8 0xfb) (refined 5 2));
        check "BK-109.tight" (not (Ws.elem (w8 0xfc) (refined 5 2))));

    (* ~(a | b): the complete_cond push (De Morgan) exposes each flag,
       and the OR=false row constrains both operands when the OR itself
       is met to false. *)
    pin "BK-110" "~(|): complete_cond pushes NOT through OR and the OR-false row constrains both flags"
      (fun () ->
        let cf = Var.create ~is_virtual:false ~fresh:false "bk110_cf" (Type.Imm 1) in
        let zf = Var.create ~is_virtual:false ~fresh:false "bk110_zf" (Type.Imm 1) in
        let env =
          AI.add_word (AI.add_word AI.top ~key:cf ~data:(Ws.top 1)) ~key:zf
            ~data:(Ws.top 1) in
        let cond = Bil.UnOp (Bil.NOT, Bil.BinOp (Bil.OR, Bil.Var cf, Bil.Var zf)) in
        check "BK-110.demorgan"
          (match Cbat_vsa_utils.complete_cond cond with
           | Bil.BinOp (Bil.AND, Bil.UnOp (Bil.NOT, _), Bil.UnOp (Bil.NOT, _)) -> true
           | _ -> false);
        let false_ = Ws.singleton Cbat_word.b0 in
        (* The pushed form (AND of the two negations) reaches each flag. *)
        let pushed =
          Vsa.Test_seam.constrain_edge ~synth:Hike.Synth.empty ~landmarks:(Cbat_landmarks.create ()) ~env
            (Cbat_vsa_utils.complete_cond cond) in
        check "BK-110.pushed-cf" (Ws.equal (AI.find_word 1 pushed cf) false_);
        check "BK-110.pushed-zf" (Ws.equal (AI.find_word 1 pushed zf) false_);
        (* The raw form exercises the NOT row then the OR=false row. *)
        let raw =
          Vsa.Test_seam.constrain_edge ~synth:Hike.Synth.empty ~landmarks:(Cbat_landmarks.create ()) ~env cond in
        check "BK-110.raw-cf" (Ws.equal (AI.find_word 1 raw cf) false_);
        check "BK-110.raw-zf" (Ws.equal (AI.find_word 1 raw zf) false_));

    (* The singleton rule reads each covered address through the point
       path; it must agree with the general read on endianness, loader
       slots and overlay precedence. *)
    pin "BK-112"
      "the per-address image read agrees with the general read: endianness, \
       a loader-owned slot (kept as unknown) and a stored cell over the \
       image decide which of {0, 8} survive the guard x = 20"
      (fun () ->
        let survivors ~tag ~endian ~slots ~store second =
          let m = memv ("w112_m" ^ tag) in
          let i = v64 ("w112_i" ^ tag) in
          let x = wr_v32 ("w112_x" ^ tag) and zf = v1 ("w112_zf" ^ tag) in
          let img_bytes = Bytes.make 16 '\000' in
          Bytes.set img_bytes 0 (Char.chr 20);
          (match second with
           | `Le20 -> Bytes.set img_bytes 8 (Char.chr 20)
           | `Be20 -> Bytes.set img_bytes 11 (Char.chr 20)
           | `Zero -> ());
          let images =
            [ { Cbat_vsa.img_lo = 0x4000L; img_hi = 0x400FL; img_bytes;
                img_slots = Core.Int64.Set.of_list slots } ] in
          let addr k = Bil.Int (Cbat_word.to_word (w64 k)) in
          let out, ssa, tid =
            Vsa.with_images images (fun () ->
                wr_refine ("w112" ^ tag) m zf
                  ((if store then
                      [ Def.create m
                          (Bil.Store (Bil.Var m, addr 0x4008,
                                      Bil.Int (Cbat_word.to_word (w32 7)),
                                      LittleEndian, `r32)) ]
                    else [])
                   @ [ Def.create i
                         (Bil.BinOp (Bil.AND, Bil.Var (int_param 0), addr 8));
                       Def.create x
                         (Bil.Load (Bil.Var m,
                                    Bil.BinOp (Bil.PLUS, addr 0x4000, Bil.Var i),
                                    endian, `r32));
                       Def.create zf
                         (Bil.BinOp (Bil.EQ, Bil.Var x,
                                     Bil.Int (Cbat_word.to_word (w32 20)))) ]))
          in
          let iv = wr_value ssa tid out i in
          (Ws.elem (w64 0) iv, Ws.elem (w64 8) iv) in
        let pair = Alcotest.(pair bool bool) in
        Alcotest.check pair "BK-112.little" (true, false)
          (survivors ~tag:"a" ~endian:LittleEndian ~slots:[] ~store:false `Be20);
        Alcotest.check pair "BK-112.big" (false, true)
          (survivors ~tag:"b" ~endian:BigEndian ~slots:[] ~store:false `Be20);
        Alcotest.check pair "BK-112.slot" (true, true)
          (survivors ~tag:"c" ~endian:LittleEndian ~slots:[ 0x4008L ] ~store:false
             `Zero);
        Alcotest.check pair "BK-112.cell-wins" (true, false)
          (survivors ~tag:"d" ~endian:LittleEndian ~slots:[] ~store:true `Le20));

    (* The cell entries a load leaves owed to the stores that wrote them:
       delivery needs a store certain to write exactly the read's bytes
       in the read's shape; any other store that may touch them blocks. *)
    pin "BK-113"
      "a store delivers a cell entry only when it certainly writes the \
       read's exact bytes in its shape; every other store that may touch \
       the entry blocks it, and a store on another memory leaves it"
      (fun () ->
        let d = Var.create ~is_virtual:true ~fresh:false "bk113_d" (Type.Imm 64) in
        let d32 = Var.create ~is_virtual:true ~fresh:false "bk113_d32" (Type.Imm 32) in
        let a = Var.create ~is_virtual:true ~fresh:false "bk113_a" (Type.Imm 64) in
        let m2 = Var.create ~is_virtual:false ~fresh:false "bk113_m2" (Type.Mem (`r64, `r8)) in
        let addr k = Bil.Int (Cbat_word.to_word (w64 k)) in
        let entry ?(bits = 64) ?(endian = LittleEndian) at =
          let k = t_key_of (Ws.singleton (w64 at)) in
          Vsa.Test_seam.owe_cell Vsa.Test_seam.no_cells ~mem:t_m
            ~range:(Mem.Key.expand k ~bytes:(bits / 8)) ~bits ~endian
            (bk_iv64 ~lo:0 ~hi:9) in
        let run ?(mem = t_m) ?(bits = `r64) ?(endian = LittleEndian) ?(data = d)
            ~at ce =
          let cells = ref ce in
          let env =
            Vsa.Test_seam.constrain_operands ~synth:Hike.Synth.empty ~cells
              ~landmarks:(Cbat_landmarks.create ()) ~env:(mk_env [])
              (Bil.Store (Bil.Var mem, at, Bil.Var data, endian, bits))
              (Ws.top 64) in
          (env, !cells) in
        let owed = Vsa.Test_seam.cells_owed in
        let bounded env v w = not (Ws.is_top (AI.find_word w env v)) in
        let env, ce = run ~at:(addr 0x1000) (entry 0x1000) in
        Alcotest.(check bool) "BK-113.deliver" true
          (bounded env d 64 && Ws.elem (w64 9) (AI.find_word 64 env d)
           && not (Ws.elem (w64 10) (AI.find_word 64 env d)) && not (owed ce));
        let env, ce = run ~at:(addr 0x1000) ~bits:`r32 ~data:d32 (entry 0x1000) in
        Alcotest.(check bool) "BK-113.width-drops" true
          (not (bounded env d32 32) && not (owed ce));
        let env, ce =
          run ~at:(addr 0x1000) ~endian:BigEndian (entry 0x1000) in
        Alcotest.(check bool) "BK-113.endian-drops" true
          (not (bounded env d 64) && not (owed ce));
        let env, ce = run ~at:(addr 0x1004) (entry 0x1000) in
        Alcotest.(check bool) "BK-113.misaligned-blocks" true
          (not (bounded env d 64) && not (owed ce));
        let env, ce = run ~at:(addr 0x1004) (entry 0x1008) in
        Alcotest.(check bool) "BK-113.store-extent-blocks" true
          (not (bounded env d 64) && not (owed ce));
        let env, ce = run ~at:(Bil.Var a) (entry 0x1000) in
        Alcotest.(check bool) "BK-113.unbounded-blocks" true
          (not (bounded env d 64) && not (owed ce));
        let env, ce = run ~at:(addr 0x2000) (entry 0x1000) in
        Alcotest.(check bool) "BK-113.disjoint-keeps" true
          (not (bounded env d 64) && owed ce);
        let env, ce = run ~mem:m2 ~at:(addr 0x1000) (entry 0x1000) in
        Alcotest.(check bool) "BK-113.other-memory-keeps" true
          (not (bounded env d 64) && owed ce);
        let cells = ref (entry 0x1000) in
        let _ =
          Vsa.Test_seam.constrain_operands ~synth:Hike.Synth.empty ~cells
            ~landmarks:(Cbat_landmarks.create ()) ~env:(mk_env [])
            (Bil.Store (Bil.Store (Bil.Var t_m, addr 0x2000, Bil.Var d,
                                   LittleEndian, `r64),
                        addr 0x3000, Bil.Var d, LittleEndian, `r64))
            (Ws.top 64) in
        Alcotest.(check bool) "BK-113.computed-memory-blocks" false (owed !cells));

    (* The disabled-continuation observer runs on a private copy of the
       scalar cells: the guard's seeds and the walk's replay must not reach
       the store every permanent state shares, while the leaf meets still
       record their landmarks. *)
    pin "BK-114"
      "the disabled-continuation observer leaves the shared scalar cells \
       and a later query unchanged"
      (fun () ->
        let x = Var.create ~is_virtual:false ~fresh:false "bk114_x" (Type.Imm 32) in
        let inc =
          Bil.BinOp (Bil.PLUS, Bil.Var x, Bil.Int (Cbat_word.to_word (w32 1))) in
        let sub, tids =
          sub_of "bk114" [ [ Def.create x inc ], [ (0, mk_goto) ] ] in
        let head = tids.(0) in
        let blk =
          Term.enum blk_t sub
          |> Seq.find_exn ~f:(fun b -> Tid.equal (Term.tid b) head) in
        let seed = Ws.singleton (w32 7) in
        let base = AI.add_word AI.top ~key:x ~data:seed in
        let query () = AI.find_word 32 base x in
        let before = query () in
        let rctx = mk_rctx ~synth:Hike.Synth.empty ~abi:Hike_abi.x86_64_sysv sub in
        let disabled =
          Bil.BinOp (Bil.LT, Bil.Var x, Bil.Int (Cbat_word.to_word (w32 3))) in
        Vsa.Test_seam.with_widening_head rctx (Some head) (fun () ->
            Vsa.Test_seam.acquire_unsat ~rctx ~entry:base base blk disabled);
        check "BK-114.seed" (Ws.equal seed before);
        check "BK-114.query" (Ws.equal before (query ()));
        check "BK-114.landmark"
          (not
             (List.is_empty
                (Cbat_landmarks.entries
                   (Vsa.Test_seam.landmarks_of rctx) head
                   (Cbat_landmarks.Word x)))));

    (* SSA scalar refinement follows the exact constrained definition cone.
       The unrelated local has a deliberately stale cell value: a whole-block
       prefix replay would overwrite it while refining [y]. *)
    pin "BK-115"
      "an SSA guard follows its local def chain and leaves unrelated scalar cells untouched"
      (fun () ->
        let x = Var.create ~is_virtual:false ~fresh:false "bk115_x" (Type.Imm 32) in
        let y = Var.create ~is_virtual:false ~fresh:false "bk115_y" (Type.Imm 32) in
        let unrelated =
          Var.create ~is_virtual:false ~fresh:false "bk115_unrelated" (Type.Imm 32) in
        let defs =
          [ Def.create y
              (Bil.BinOp (Bil.PLUS, Bil.Var x,
                          Bil.Int (Cbat_word.to_word (w32 1))));
            Def.create unrelated (Bil.Int (Cbat_word.to_word (w32 99))) ] in
        let cond =
          Bil.BinOp (Bil.LT, Bil.Var y,
                     Bil.Int (Cbat_word.to_word (w32 10))) in
        let sub, tids =
          sub_of ~args:[ Arg.create ~intent:In x (Bil.Var x) ] "bk115"
            [ defs,
              [ (1, fun t -> mk_jmp_to t cond); (2, mk_goto) ];
              [], [ (0, mk_ret) ];
              [], [ (0, mk_ret) ] ] in
        let sol = run_ssa_anchored sub in
        let blk = Term.find_exn blk_t sub tids.(0) in
        let rctx = mk_rctx ~synth:Hike.Synth.empty
            ~abi:Hike_abi.x86_64_sysv sub in
        let entry = Graphlib.Std.Solution.get sol (Term.tid blk) in
        let post = Vsa.Test_seam.denote_defs ~synth:Hike.Synth.empty blk entry in
        let cond =
          Term.first jmp_t blk |> Base.Option.value_exn |> Jmp.cond in
        let guard =
          Core.Set.to_list (Exp.free_vars cond) |> Base.List.hd_exn in
        let unrelated_lhs =
          Term.enum def_t blk |> Seq.map ~f:Def.lhs
          |> Seq.find_exn ~f:(Var.same (Var.base unrelated)) in
        let stale = Ws.singleton (w32 7) in
        let post = AI.add_word post ~key:unrelated_lhs ~data:stale in
        let edge =
          Vsa.Test_seam.constrain_edge ~synth:Hike.Synth.empty ~env:post
            ~landmarks:(Vsa.Test_seam.landmarks_of rctx) cond in
        let out =
          Vsa.Test_seam.refine_edge ~sol ~rctx
            ~seeds:(Var.Set.singleton guard) edge blk in
        let x_in =
          match Def.rhs (Term.enum def_t blk |> Seq.find_exn
                           ~f:(fun d -> Var.same (Def.lhs d) y)) with
          | Bil.BinOp (_, Bil.Var v, _) -> v
          | _ -> failwith "BK-115: missing exact x operand" in
        let x_ws = AI.find_word 32 out x_in in
        check "BK-115.chain-narrows-x"
          (not (Ws.is_top x_ws)
           && not (Ws.elem (w32 9) x_ws)
           && Ws.elem (w32 8) x_ws);
        check "BK-115.unrelated-cell-kept"
          (Ws.equal stale (AI.find_word 32 out unrelated_lhs)));

    (* The SSA observer forces the disabled guard's seed in private cells,
       then follows each exact local def to the conflicting entry input. *)
    pin "BK-116"
      "the SSA disabled-continuation observer reaches an empty meet through a multi-def chain"
      (fun () ->
        let x = Var.create ~is_virtual:false ~fresh:false "bk116_x" (Type.Imm 32) in
        let a = Var.create ~is_virtual:false ~fresh:false "bk116_a" (Type.Imm 32) in
        let y = Var.create ~is_virtual:false ~fresh:false "bk116_y" (Type.Imm 32) in
        (* The chain x -> a -> y: the guard's row reaches x through a's
           own definition, and the excluded region (the live x = 100
           against the chain's [0,2]) separates, so the observer records
           it as a landmark. *)
        let defs =
          [ Def.create a
              (Bil.BinOp (Bil.MINUS, Bil.Var x,
                          Bil.Int (Cbat_word.to_word (w32 1))));
            Def.create y
              (Bil.BinOp (Bil.PLUS, Bil.Var a,
                          Bil.Int (Cbat_word.to_word (w32 1)))) ] in
        let disabled =
          Bil.BinOp (Bil.LT, Bil.Var y,
                     Bil.Int (Cbat_word.to_word (w32 3))) in
        let sub, tids =
          sub_of ~args:[ Arg.create ~intent:In x (Bil.Var x) ] "bk116"
            [ defs, [ (0, fun t -> mk_jmp_to t disabled) ] ] in
        let sol = run_ssa_anchored sub in
        let blk = Term.find_exn blk_t sub tids.(0) in
        let rctx = mk_rctx ~synth:Hike.Synth.empty
            ~abi:Hike_abi.x86_64_sysv sub in
        let a_def =
          Term.enum def_t blk |> Seq.find_exn
            ~f:(fun d -> Var.same (Def.lhs d) a) in
        let x_in =
          match Def.rhs a_def with
          | Bil.BinOp (_, Bil.Var v, _) -> v
          | _ -> failwith "BK-116: missing x input" in
        let disabled =
          Term.first jmp_t blk |> Base.Option.value_exn |> Jmp.cond in
        let head = Term.tid blk in
        (* The observer's seed is private: the shared state keeps its own
           value for the input. *)
        let shared = Graphlib.Std.Solution.get sol head in
        let live_x = Ws.singleton (w32 100) in
        let base = AI.add_word shared ~key:x_in ~data:live_x in
        Vsa.Test_seam.with_widening_head rctx (Some head) (fun () ->
            Vsa.Test_seam.acquire_unsat ~rctx ~entry:base base blk disabled);
        check "BK-116.multi-def-landmark"
          (not
             (List.is_empty
                (Cbat_landmarks.entries
                   (Vsa.Test_seam.landmarks_of rctx) head
                   (Cbat_landmarks.Word x_in))));
        (* The observer keeps its facts private: the shared state still
           holds the input's own value. *)
        check "BK-116.shared-input-unchanged"
          (Ws.equal (Ws.top 32)
             (AI.find_word 32 (Graphlib.Std.Solution.get sol head) x_in)));
  ]

let () = run "backward" tests
