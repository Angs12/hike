(* The inverse denote's leaf facts (T1-T4: the load's cell meet;
   S-family: the guard's operand windows observed through the env). *)
open Bap.Std
open Bap_core_theory
open Test_common
open Test_fixtures

let run () =
(* The load's cell meet: the trace's address range meets every
   intersecting cell; outside cells survive. *)
(  let rsp = Var.create ~is_virtual:false ~fresh:false "RSP" (Type.Imm 64) in
  let rbp = Var.create ~is_virtual:false ~fresh:false "RBP" (Type.Imm 64) in
  let idx = Var.create ~is_virtual:true ~fresh:false "t_idx" (Type.Imm 64) in
  let m = Var.create ~is_virtual:false ~fresh:false "t_m" (Type.Mem (`r64, `r8)) in
  let k = { Mem.addr_width = 64; Mem.addressable_width = 8 } in
  let iv ~lo ~hi =
    Ws.of_clp
      (Clp.create ~width:64 ~step:(w64 1) ~cardn:(Cbat_word.of_int ~width:65 (hi - lo + 1)) (w64 lo))
  in
  let key_of ws = match Mem.Key.of_wordset ws with Some k -> k | None -> failwith "key_of" in
  let add_cell st addr_ws data =
    let mv = AI.find_memory k st m in
    let mv' = Mem.add mv ~key:(key_of addr_ws) ~data:(Mem.Val.create data LittleEndian) in
    AI.add_memory st ~key:m ~data:mv'
  in
  let cell_at st addr_ws =
    let mv = AI.find_memory k st m in
    Mem.Val.data (Mem.find (64, LittleEndian) mv (key_of addr_ws))
  in
  let load_exp addr = Bil.Load (Bil.Var m, addr, LittleEndian, `r64) in
  (* T1: RSP-based meet — [RSP - 8] meets the cell at offset key {-8}. *)
  let st1 = add_cell (mk_seed_state rsp rbp ()) (Ws.singleton (w64 (-8))) (iv ~lo:0 ~hi:20) in
  let env1 =
    Vsa.Test_seam.inverse_denote ~env:st1
      (load_exp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 8)))))
      (iv ~lo:0 ~hi:9)
  in
  check
    "T1: the RSP-based same-block cell meet — [RSP-8] meets the cell at the offset key (the \
     frame's RSP offset 0)"
    (let v = cell_at env1 (Ws.singleton (w64 (-8))) in
     Ws.elem (w64 9) v && not (Ws.elem (w64 15) v));
  (* T2: dynamic-index meet — iterate constraint [0,4] confines the meet; cell 40 survives. *)
  let st2 =
    let s = add_cell (mk_seed_state rsp rbp ()) (Ws.singleton (w64 0)) (iv ~lo:0 ~hi:20) in
    add_cell s (Ws.singleton (w64 40)) (iv ~lo:0 ~hi:20)
  in
  let st2 = AI.add_word st2 ~key:idx ~data:(iv ~lo:0 ~hi:4) in
  let env2 =
    Vsa.Test_seam.inverse_denote ~env:st2
      (load_exp (Bil.BinOp (Bil.PLUS, Bil.Var rbp, Bil.BinOp (Bil.TIMES, Bil.Var idx, Bil.Int (Cbat_word.to_word (w64 8))))))
      (iv ~lo:0 ~hi:9)
  in
  check
    "T2: the dynamic-index meet — the index's iterate constraint [0,4] confines the meet to the \
     cells {0..32}; the cell at 40 (the exit-side) is untouched"
    (let v0 = cell_at env2 (Ws.singleton (w64 0)) in
     let v40 = cell_at env2 (Ws.singleton (w64 40)) in
     Ws.elem (w64 9) v0 && (not (Ws.elem (w64 15) v0)) && Ws.elem (w64 15) v40);
  (* T3: ranged meet — stored [0,64] splits; overlap [8,24] meets, rest keeps original. *)
  let st3 = add_cell (mk_seed_state rsp rbp ()) (iv ~lo:0 ~hi:64) (iv ~lo:0 ~hi:20) in
  let st3 = AI.add_word st3 ~key:idx ~data:(iv ~lo:8 ~hi:24) in
  let env3 =
    Vsa.Test_seam.inverse_denote ~env:st3
      (load_exp (Bil.BinOp (Bil.PLUS, Bil.Var rbp, Bil.Var idx)))
      (iv ~lo:0 ~hi:9)
  in
  check
    "T3: the ranged meet's overlap boundary — the stored [0,64] cell splits: the overlapping part \
     [8,24] meets; the parts [0,8) and (24,64] keep the original (the reads at the split's aligned \
     points — the find' alignment semantics: an unaligned sub-region read returns top)"
    (let v8 = cell_at env3 (Ws.singleton (w64 8)) in
     let v0 = cell_at env3 (Ws.singleton (w64 0)) in
     let v24 = cell_at env3 (Ws.singleton (w64 24)) in
     Ws.elem (w64 9) v8
     && (not (Ws.elem (w64 15) v8))
     && Ws.elem (w64 15) v0
     && Ws.elem (w64 15) v24);
  (* T4: exit-side cells survive — offsets 40 and 80 untouched. *)
  let st4 =
    let s = add_cell (mk_seed_state rsp rbp ()) (Ws.singleton (w64 0)) (iv ~lo:0 ~hi:20) in
    let s = add_cell s (Ws.singleton (w64 40)) (iv ~lo:0 ~hi:20) in
    add_cell s (Ws.singleton (w64 80)) (iv ~lo:0 ~hi:20)
  in
  let st4 = AI.add_word st4 ~key:idx ~data:(iv ~lo:0 ~hi:4) in
  let env4 =
    Vsa.Test_seam.inverse_denote ~env:st4
      (load_exp (Bil.BinOp (Bil.PLUS, Bil.Var rbp, Bil.BinOp (Bil.TIMES, Bil.Var idx, Bil.Int (Cbat_word.to_word (w64 8))))))
      (iv ~lo:0 ~hi:9)
  in
  check
    "T4: the exit-side cells survive — the iterate range [0,32] meets; the exit-side offsets 40 \
     and 80 (the ¬iterate values) are untouched"
    (let v0 = cell_at env4 (Ws.singleton (w64 0)) in
     let v40 = cell_at env4 (Ws.singleton (w64 40)) in
     let v80 = cell_at env4 (Ws.singleton (w64 80)) in
     Ws.elem (w64 9) v0
     && (not (Ws.elem (w64 15) v0))
     && Ws.elem (w64 15) v40
     && Ws.elem (w64 15) v80);
  ())
(* The guard's operand windows observed through the inverse denote: on a
   TOP env the leaf meet preserves the raw row. *)
;
(  let r32 = Cbat_word.of_int ~width:32 in
  let t = Var.create ~is_virtual:true ~fresh:false "s_t" (Type.Imm 32) in
  let u = Var.create ~is_virtual:true ~fresh:false "s_u" (Type.Imm 32) in
  let m = Var.create ~is_virtual:false ~fresh:false "s_m" (Type.Mem (`r32, `r8)) in
  let w32_of_env env v = AI.find_word 32 env (Var.base v) in
  let iv ~lo ~hi =
    Ws.of_clp
      (Clp.create ~width:32 ~step:(r32 1) ~cardn:(Cbat_word.of_int ~width:33 (hi - lo + 1)) (r32 lo))
  in
  let window_of env cond v = AI.find_word 32 (Vsa.Test_seam.inverse_denote ~env cond (Ws.singleton (Cbat_word.of_word Word.b1))) (Var.base v) in
  (* S1: const-second EQ. *)
  check "S1: EQ const-second -> the Var seed {10}"
    (let c = window_of (mk_env []) (Bil.BinOp (Bil.EQ, Bil.Var t, Bil.Int (Cbat_word.to_word (r32 10)))) t in
     Ws.elem (r32 10) c && not (Ws.elem (r32 11) c));
  (* S2: NEQ complement. *)
  check "S2: NEQ const-second -> the wrapped complement (10 ∉; 11, 9 ∈)"
    (let c = window_of (mk_env []) (Bil.BinOp (Bil.NEQ, Bil.Var t, Bil.Int (Cbat_word.to_word (r32 10)))) t in
     (not (Ws.elem (r32 10) c)) && Ws.elem (r32 11) c && Ws.elem (r32 9) c);
  (* S3: two-piece SLT. *)
  check "S3: SLT const-second -> the two-piece [0,3] ∪ [2^31, max] (no gate)"
    (let c = window_of (mk_env []) (Bil.BinOp (Bil.SLT, Bil.Var t, Bil.Int (Cbat_word.to_word (r32 4)))) t in
     Ws.elem (r32 3) c && (not (Ws.elem (r32 4) c)) && Ws.elem (r32 0x80000000) c);
  (* S4: const-first flip. *)
  check "S4: const-first LT -> the UGT flip [11, max] (10 ∉; 11 ∈)"
    (let c = window_of (mk_env []) (Bil.BinOp (Bil.LT, Bil.Int (Cbat_word.to_word (r32 10)), Bil.Var t)) t in
     Ws.elem (r32 11) c && not (Ws.elem (r32 10) c));
  (* S5: var-vs-var LT overlap. *)
  let env5 = mk_env [ (t, iv ~lo:0 ~hi:10); (u, Ws.singleton (r32 10)) ] in
  let c5 = window_of env5 (Bil.BinOp (Bil.LT, Bil.Var t, Bil.Var u)) t in
  check "S5: the var-vs-var LT overlap — t ∈ [0,9] (the u's max 10)"
    (Ws.elem (r32 9) c5 && not (Ws.elem (r32 10) c5));
  (* S6: var-vs-var NEQ complement. *)
  let env6 = mk_env [ (t, iv ~lo:0 ~hi:10); (u, Ws.singleton (r32 5)) ] in
  let c6 = window_of env6 (Bil.BinOp (Bil.NEQ, Bil.Var t, Bil.Var u)) t in
  check
    "S6: the var-vs-var NEQ — the t seed = the complement of the {5} overlap (the interior: the \
     identity — sound)"
    (Ws.elem (r32 0) c6 && Ws.elem (r32 10) c6);
  (* S7: generic comparison with producer recursion. *)
  let env7 = mk_env [ (t, iv ~lo:0 ~hi:10); (u, iv ~lo:0 ~hi:3) ] in
  let env7' =
    Vsa.Test_seam.inverse_denote ~env:env7
      (Bil.BinOp (Bil.LT, Bil.Var t, Bil.BinOp (Bil.PLUS, Bil.Var u, Bil.Int (Cbat_word.to_word (r32 1)))))
      (Ws.singleton (Cbat_word.of_word Word.b1))
  in
  let ct7 = w32_of_env env7' t and cu7 = w32_of_env env7' u in
  check
    "S7: the generic comparison — the t row from the (u+1) value-set [1,4] (t ⊆ [0,3]) + the u \
     producer seed"
    (Ws.elem (r32 3) ct7 && (not (Ws.elem (r32 4) ct7)) && Ws.elem (r32 1) cu7);
  (* S8: producer PLUS hull. *)
  let env8 = mk_env [] in
  let c8 = window_of env8 (Bil.BinOp (Bil.LT, Bil.BinOp (Bil.PLUS, Bil.Var t, Bil.Int (Cbat_word.to_word (r32 1))), Bil.Int (Cbat_word.to_word (r32 10)))) t in
  check "S8: the producer PLUS hull — the circular hull {0xFFFFFFFF} ∪ [0,8] on t"
    (Ws.elem (r32 8) c8 && (not (Ws.elem (r32 9) c8)) && Ws.elem (r32 0xFFFFFFFF) c8);
  (* S9: load operand gives the cell fact — met into the env's memory. *)
  let rsp64 = Var.create ~is_virtual:false ~fresh:false "RSP" (Type.Imm 64) in
  let st9 = mk_seed_state rsp64 rsp64 () in
  let k9 = { Mem.addr_width = 32; Mem.addressable_width = 8 } in
  let mem9 =
    let mv = Mem.top k9 in
    AI.add_memory st9 ~key:m
      ~data:(Mem.add mv ~key:(key_of (Ws.singleton (w64 0)))
               ~data:(Mem.Val.create (iv ~lo:0 ~hi:40) LittleEndian))
  in
  let env9 =
    Vsa.Test_seam.inverse_denote ~env:mem9
      (Bil.BinOp
         ( Bil.LT,
           Bil.Load
             ( Bil.Var m,
               Bil.BinOp (Bil.MINUS, Bil.Var rsp64, Bil.Int (Cbat_word.to_word (w64 8))),
               LittleEndian,
               `r32 ),
           Bil.Int (Cbat_word.to_word (r32 10)) ))
      (Ws.singleton (Cbat_word.of_word Word.b1))
  in
  check "S9: the load operand -> the cell fact meets the env's memory ([0,9] on the cell)"
    (let mv = AI.find_memory k9 env9 m in
     let v = Mem.Val.data (Mem.find (32, LittleEndian) mv (key_of (Ws.singleton (w64 (-8))))) in
     Ws.elem (r32 9) v && not (Ws.elem (r32 10) v));
  (* S10/S11/S13/S15/S16 observed through the same rule. *)
  let s10 =
    Vsa.Test_seam.inverse_denote ~env:(mk_env [])
      (Cbat_vsa_utils.complete_cond
         (Bil.UnOp (Bil.NOT, Bil.BinOp (Bil.LT, Bil.Var t, Bil.Int (Cbat_word.to_word (r32 10))))))
      (Ws.singleton (Cbat_word.of_word Word.b1))
  in
  let c10 = w32_of_env s10 t in
  check "S10: the completed fallthrough of (t <u 10) seeds the UGE side [10, max] (10 ∈; 9 ∉)"
    (Ws.elem (r32 10) c10 && not (Ws.elem (r32 9) c10));
  let s11 =
    Vsa.Test_seam.inverse_denote ~env:(mk_env [])
      (Bil.BinOp (Bil.LT, Bil.UnOp (Bil.NEG, Bil.Var t), Bil.Int (Cbat_word.to_word (r32 10))))
      (Ws.singleton (Cbat_word.of_word Word.b1))
  in
  let c11 = w32_of_env s11 t in
  check "S11: the NEG row — the neg'd [0,9]: 0 ∈, −1 ∈"
    (Ws.elem (r32 0) c11 && Ws.elem (r32 0xFFFFFFFF) c11);
  let s13 =
    Vsa.Test_seam.inverse_denote ~env:(mk_env [])
      (Cbat_vsa_utils.complete_cond
         (Bil.UnOp (Bil.NOT, Bil.BinOp (Bil.EQ, Bil.Var t, Bil.Int (Cbat_word.to_word (r32 10))))))
      (Ws.singleton (Cbat_word.of_word Word.b1))
  in
  let c13 = w32_of_env s13 t in
  check "S13: the completed dual — NOT (t EQ 10) -> the NEQ complement (10 ∉; 11 ∈)"
    (not (Ws.elem (r32 10) c13) && Ws.elem (r32 11) c13);
  let env15 = mk_env [ (t, Ws.of_clp (Clp.create ~width:32 ~step:(r32 1) ~cardn:(Cbat_word.of_int ~width:33 0x10000) (r32 0))) ] in
  let env15' =
    Vsa.Test_seam.inverse_denote ~env:env15
      (Bil.BinOp (Bil.EQ, Bil.Cast (Bil.LOW, 8, Bil.Var t), Bil.Int (Cbat_word.to_word (Cbat_word.of_int ~width:8 5))))
      (Ws.singleton (Cbat_word.of_word Word.b1))
  in
  let c15 = w32_of_env env15' t in
  check "S15a: the LOW cast row — the truncation hull [5, 5 + 2^32 − 2^8] (5 ∈; 5+0x100 ∈; 4 ∉)"
    (Ws.elem (r32 5) c15 && Ws.elem (r32 0x105) c15 && not (Ws.elem (r32 4) c15));
  let env15b = mk_env [ (t, Ws.singleton (r32 0x100)) ] in
  let env15b' =
    Vsa.Test_seam.inverse_denote ~env:env15b
      (Bil.BinOp (Bil.LT, Bil.Cast (Bil.SIGNED, 64, Bil.Var t), Bil.Int (Cbat_word.to_word (Cbat_word.of_int ~width:64 0x100))))
      (Ws.singleton (Cbat_word.of_word Word.b1))
  in
  let c15b = w32_of_env env15b' t in
  (* The pre-image row itself, observed on a top env: [0, 0xFF]. *)
  let row15b =
    w32_of_env
      (Vsa.Test_seam.inverse_denote ~env:(mk_env [])
         (Bil.BinOp (Bil.LT, Bil.Cast (Bil.SIGNED, 64, Bil.Var t), Bil.Int (Cbat_word.to_word (Cbat_word.of_int ~width:64 0x100))))
         (Ws.singleton (Cbat_word.of_word Word.b1)))
      t in
  check "S15b: the SIGNED ext row — the pre-image [0, 0xFF] on a top env; the meet with {0x100} is empty, so the env keeps its value (identity, observed)"
    (Ws.elem (r32 0xFF) row15b
     && not (Ws.elem (r32 0x100) row15b)
     && Ws.equal c15b (Ws.singleton (r32 0x100)));
  (* S16: the per-edge reality — the producer's completion carries the
     negation (NOT over a comparison completes to the negated
     comparison), so the fallthrough edge's cond evaluates TRUE by the
     same rows the taken edge uses. *)
  let x16 = Var.create ~is_virtual:true ~fresh:false "s16_x" (Type.Imm 32) in
  let y16 = Var.create ~is_virtual:true ~fresh:false "s16_y" (Type.Imm 32) in
  let env16 = mk_env [ (x16, iv ~lo:0 ~hi:3); (y16, iv ~lo:0 ~hi:0xFFFFFFFF) ] in
  let b1 = Ws.singleton (Cbat_word.of_word Word.b1) in
  let completes_to op op' swap =
    List.for_all
      (fun (a, b) ->
         Exp.equal
           (Cbat_vsa_utils.complete_cond (Bil.UnOp (Bil.NOT, Bil.BinOp (op, a, b))))
           (if swap then Bil.BinOp (op', b, a) else Bil.BinOp (op', a, b)))
      [ (Bil.Var x16, Bil.Var y16); (Bil.Var y16, Bil.Var x16);
        (Bil.Var x16, Bil.Int (Cbat_word.to_word (r32 7)));
        (Bil.Int (Cbat_word.to_word (r32 7)), Bil.Var x16) ] in
  check
    "S16a: the completion is the negation — NOT over each of the six \
     comparisons (both operand orders, const and var sides) completes \
     structurally to the negated comparison"
    (List.for_all
       (fun (o, o', s) -> completes_to o o' s)
       [ (Bil.LT, Bil.LE, true); (Bil.LE, Bil.LT, true);
         (Bil.SLT, Bil.SLE, true); (Bil.SLE, Bil.SLT, true);
         (Bil.EQ, Bil.NEQ, false); (Bil.NEQ, Bil.EQ, false) ]);
  (* S16b: the concrete precision case — the fallthrough of (x <u y)
     over x = [0,3], y = top, through the completed edge cond
     (y <=u x), seeds y ⊆ [0,3] by the ordinary taken row. *)
  let y16_read = w32_of_env (Vsa.Test_seam.inverse_denote ~env:env16
      (Cbat_vsa_utils.complete_cond
         (Bil.UnOp (Bil.NOT, Bil.BinOp (Bil.LT, Bil.Var x16, Bil.Var y16))))
      b1) y16 in
  check
    "S16b: the completed fallthrough of (x <u y) with x = [0,3], y = top \
     seeds y ⊆ [0,3] (0, 3 ∈; 4 ∉)"
    (Ws.elem (r32 0) y16_read && Ws.elem (r32 3) y16_read && not (Ws.elem (r32 4) y16_read));
  (* S16c: the compound chain — three comparisons in one AND tree
     constrain all three operands through one evaluation path. *)
  let a16 = Var.create ~is_virtual:true ~fresh:false "s16_a" (Type.Imm 32) in
  let c16v = Var.create ~is_virtual:true ~fresh:false "s16_c" (Type.Imm 32) in
  let env16c =
    mk_env
      [ (a16, iv ~lo:0 ~hi:9); (y16, iv ~lo:3 ~hi:7); (c16v, iv ~lo:5 ~hi:9) ] in
  let env16c' =
    Vsa.Test_seam.inverse_denote ~env:env16c
      (Bil.BinOp
         ( Bil.AND,
           Bil.BinOp (Bil.LT, Bil.Var a16, Bil.Var y16),
           Bil.BinOp (Bil.LT, Bil.Var y16, Bil.Var c16v) ))
      b1
  in
  check
    "S16c: the 3-comparison AND chain narrows by the meet — a is cut to \
     [0,6] (the y-max row); y and c keep their values (their rows do not \
     narrow what the env already knows)"
    (let a' = w32_of_env env16c' a16 in
     Ws.elem (r32 6) a' && not (Ws.elem (r32 7) a')
     && Ws.equal (w32_of_env env16c' y16) (AI.find_word 32 env16c (Var.base y16))
     && Ws.equal (w32_of_env env16c' c16v) (AI.find_word 32 env16c (Var.base c16v)));
  (* S14: infeasible constant. *)
  check "S14: the infeasible constant — (Int 5) with {7} -> the empty state; with {5} -> the identity"
    (AI.equal (Vsa.Test_seam.inverse_denote ~env:(mk_env []) (Bil.Int (Cbat_word.to_word (r32 5))) (Ws.singleton (r32 7)))
              AI.bottom
     && AI.equal (Vsa.Test_seam.inverse_denote ~env:(mk_env []) (Bil.Int (Cbat_word.to_word (r32 5))) (Ws.singleton (r32 5)))
                 (mk_env []));
  ())
