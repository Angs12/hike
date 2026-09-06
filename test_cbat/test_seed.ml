(* Trace-exact cell meet (T1-T4) and pure seed collector (S1-S15). *)
open Bap.Std
open Bap_core_theory
open Test_common

let run () =
(* Trace-exact cell meet: the trace's address range meets every intersecting cell; outside cells survive. *)
(  let rsp = Var.create ~is_virtual:false ~fresh:false "RSP" (Type.Imm 64) in
  let rbp = Var.create ~is_virtual:false ~fresh:false "RBP" (Type.Imm 64) in
  let idx = Var.create ~is_virtual:true ~fresh:false "t_idx" (Type.Imm 64) in
  let m = Var.create ~is_virtual:false ~fresh:false "t_m" (Type.Mem (`r64, `r8)) in
  let k = { Mem.addr_width = 64; Mem.addressable_width = 8 } in
  let iv ~lo ~hi =
    Ws.of_clp
      (Clp.create ~width:64 ~step:(w64 1) ~cardn:(W.of_int ~width:65 (hi - lo + 1)) (w64 lo))
  in
  let frame_rsp_rbp =
    Some
      [
        (Var.base rsp, { AI.fconst = Ws.singleton (w64 0); AI.fvars = [] });
        (Var.base rbp, { AI.fconst = Ws.singleton (w64 0); AI.fvars = [] });
      ]
  in
  let mk_state () =
    AI.set_frame
      (AI.add_word
         (AI.add_word AI.top ~key:rsp ~data:(Ws.singleton (w64 0)))
         ~key:rbp
         ~data:(Ws.singleton (w64 0)))
      frame_rsp_rbp
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
  (* T1: RSP-based meet — [RSP - 8] meets the cell at offset key {-8}. *)
  let st1 = add_cell (mk_state ()) (Ws.singleton (w64 (-8))) (iv ~lo:0 ~hi:20) in
  let env1 =
    Vsa.constrain_cell_on_trace ~st:st1 ~live:Var.Map.empty st1 ~mem:(Bil.Var m)
      ~addr:(Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 8)))
      ~size:`r64 ~endian:LittleEndian (iv ~lo:0 ~hi:9)
  in
  check
    "T1: the RSP-based same-block cell meet — [RSP-8] meets the cell at the offset key (the \
     frame's RSP offset 0)"
    (let v = cell_at env1 (Ws.singleton (w64 (-8))) in
     Ws.elem (w64 9) v && not (Ws.elem (w64 15) v));
  (* T2: dynamic-index meet — iterate constraint [0,4] confines the meet; cell 40 survives. *)
  let st2 =
    let s = add_cell (mk_state ()) (Ws.singleton (w64 0)) (iv ~lo:0 ~hi:20) in
    add_cell s (Ws.singleton (w64 40)) (iv ~lo:0 ~hi:20)
  in
  let st2 = AI.add_word st2 ~key:idx ~data:(iv ~lo:0 ~hi:10) in
  let live2 = Var.Map.singleton (Var.base idx) (iv ~lo:0 ~hi:4) in
  let env2 =
    Vsa.constrain_cell_on_trace ~st:st2 ~live:live2 st2 ~mem:(Bil.Var m)
      ~addr:(Bil.BinOp (Bil.PLUS, Bil.Var rbp, Bil.BinOp (Bil.TIMES, Bil.Var idx, Bil.Int (w64 8))))
      ~size:`r64 ~endian:LittleEndian (iv ~lo:0 ~hi:9)
  in
  check
    "T2: the dynamic-index meet — the index's iterate constraint [0,4] confines the meet to the \
     cells {0..32}; the cell at 40 (the exit-side) is untouched"
    (let v0 = cell_at env2 (Ws.singleton (w64 0)) in
     let v40 = cell_at env2 (Ws.singleton (w64 40)) in
     Ws.elem (w64 9) v0 && (not (Ws.elem (w64 15) v0)) && Ws.elem (w64 15) v40);
  (* T3: ranged meet — stored [0,64] splits; overlap [8,24] meets, rest keeps original. *)
  let st3 = add_cell (mk_state ()) (iv ~lo:0 ~hi:64) (iv ~lo:0 ~hi:20) in
  let st3 = AI.add_word st3 ~key:idx ~data:(iv ~lo:8 ~hi:24) in
  let live3 = Var.Map.singleton (Var.base idx) (iv ~lo:8 ~hi:24) in
  let env3 =
    Vsa.constrain_cell_on_trace ~st:st3 ~live:live3 st3 ~mem:(Bil.Var m)
      ~addr:(Bil.BinOp (Bil.PLUS, Bil.Var rbp, Bil.Var idx))
      ~size:`r64 ~endian:LittleEndian (iv ~lo:0 ~hi:9)
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
    let s = add_cell (mk_state ()) (Ws.singleton (w64 0)) (iv ~lo:0 ~hi:20) in
    let s = add_cell s (Ws.singleton (w64 40)) (iv ~lo:0 ~hi:20) in
    add_cell s (Ws.singleton (w64 80)) (iv ~lo:0 ~hi:20)
  in
  let st4 = AI.add_word st4 ~key:idx ~data:(iv ~lo:0 ~hi:10) in
  let live4 = Var.Map.singleton (Var.base idx) (iv ~lo:0 ~hi:4) in
  let env4 =
    Vsa.constrain_cell_on_trace ~st:st4 ~live:live4 st4 ~mem:(Bil.Var m)
      ~addr:(Bil.BinOp (Bil.PLUS, Bil.Var rbp, Bil.BinOp (Bil.TIMES, Bil.Var idx, Bil.Int (w64 8))))
      ~size:`r64 ~endian:LittleEndian (iv ~lo:0 ~hi:9)
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
(* Pure seed collector: guard edge constraint decomposed into leaf seeds. *)
;
(  let r32 = W.of_int ~width:32 in
  let t = Var.create ~is_virtual:true ~fresh:false "s_t" (Type.Imm 32) in
  let u = Var.create ~is_virtual:true ~fresh:false "s_u" (Type.Imm 32) in
  let cf = Var.create ~is_virtual:false ~fresh:false "s_cf" (Type.Imm 1) in
  let m = Var.create ~is_virtual:false ~fresh:false "s_m" (Type.Mem (`r32, `r8)) in
  let mk_env binds = List.fold_left (fun e (v, ws) -> AI.add_word e ~key:v ~data:ws) AI.top binds in
  let var_seed seeds v =
    List.find_map
      (function Vsa.Var (v', c) when Var.equal v' (Var.base v) -> Some c | _ -> None)
      seeds
  in
  let iv ~lo ~hi =
    Ws.of_clp
      (Clp.create ~width:32 ~step:(r32 1) ~cardn:(W.of_int ~width:33 (hi - lo + 1)) (r32 lo))
  in
  let seeds_of cond = Vsa.edge_constraints ~env:(mk_env []) cond (Ws.singleton Word.b1) in
  (* S1: const-second EQ. *)
  check "S1: EQ const-second -> the Var seed {10}"
    (match seeds_of (Bil.BinOp (Bil.EQ, Bil.Var t, Bil.Int (r32 10))) with
    | [ Vsa.Var (v, c) ] ->
        Var.equal v (Var.base t) && Ws.elem (r32 10) c && not (Ws.elem (r32 11) c)
    | _ -> false);
  (* S2: NEQ complement. *)
  check "S2: NEQ const-second -> the wrapped complement (10 ∉; 11, 9 ∈)"
    (match seeds_of (Bil.BinOp (Bil.NEQ, Bil.Var t, Bil.Int (r32 10))) with
    | [ Vsa.Var (v, c) ] ->
        Var.equal v (Var.base t)
        && (not (Ws.elem (r32 10) c))
        && Ws.elem (r32 11) c
        && Ws.elem (r32 9) c
    | _ -> false);
  (* S3: two-piece SLT. *)
  check "S3: SLT const-second -> the two-piece [0,3] ∪ [2^31, max] (no gate)"
    (match seeds_of (Bil.BinOp (Bil.SLT, Bil.Var t, Bil.Int (r32 4))) with
    | [ Vsa.Var (v, c) ] ->
        Var.equal v (Var.base t)
        && Ws.elem (r32 3) c
        && (not (Ws.elem (r32 4) c))
        && Ws.elem (r32 0x80000000) c
    | _ -> false);
  (* S4: const-first flip. *)
  check "S4: const-first LT -> the UGT flip [11, max] (10 ∉; 11 ∈)"
    (match seeds_of (Bil.BinOp (Bil.LT, Bil.Int (r32 10), Bil.Var t)) with
    | [ Vsa.Var (v, c) ] ->
        Var.equal v (Var.base t) && Ws.elem (r32 11) c && not (Ws.elem (r32 10) c)
    | _ -> false);
  (* S5: var-vs-var LT overlap. *)
  let env5 = mk_env [ (t, iv ~lo:0 ~hi:10); (u, Ws.singleton (r32 10)) ] in
  let s5 =
    Vsa.edge_constraints ~env:env5 (Bil.BinOp (Bil.LT, Bil.Var t, Bil.Var u)) (Ws.singleton Word.b1)
  in
  check "S5: the var-vs-var LT overlap — t ∈ [0,9] (the u's max 10)"
    (match var_seed s5 t with
    | Some c -> Ws.elem (r32 9) c && not (Ws.elem (r32 10) c)
    | None -> false);
  (* S6: var-vs-var NEQ complement. *)
  let env6 = mk_env [ (t, iv ~lo:0 ~hi:10); (u, Ws.singleton (r32 5)) ] in
  let s6 =
    Vsa.edge_constraints ~env:env6
      (Bil.BinOp (Bil.NEQ, Bil.Var t, Bil.Var u))
      (Ws.singleton Word.b1)
  in
  check
    "S6: the var-vs-var NEQ — the t seed = the complement of the {5} overlap (the interior: the \
     identity — sound)"
    (match var_seed s6 t with Some c -> Ws.elem (r32 0) c && Ws.elem (r32 10) c | None -> false);
  (* S7: generic comparison with producer recursion. *)
  let env7 = mk_env [ (t, iv ~lo:0 ~hi:10); (u, iv ~lo:0 ~hi:3) ] in
  let s7 =
    Vsa.edge_constraints ~env:env7
      (Bil.BinOp (Bil.LT, Bil.Var t, Bil.BinOp (Bil.PLUS, Bil.Var u, Bil.Int (r32 1))))
      (Ws.singleton Word.b1)
  in
  check
    "S7: the generic comparison — the t row from the (u+1) value-set [1,4] (t ⊆ [0,3]) + the u \
     producer seed"
    (match (var_seed s7 t, var_seed s7 u) with
    | Some ct, Some cu -> Ws.elem (r32 3) ct && (not (Ws.elem (r32 4) ct)) && Ws.elem (r32 1) cu
    | _ -> false);
  (* S8: producer PLUS hull. *)
  let env8 = mk_env [ (t, iv ~lo:0 ~hi:10) ] in
  let s8 =
    Vsa.edge_constraints ~env:env8
      (Bil.BinOp (Bil.LT, Bil.BinOp (Bil.PLUS, Bil.Var t, Bil.Int (r32 1)), Bil.Int (r32 10)))
      (Ws.singleton Word.b1)
  in
  check "S8: the producer PLUS row — the circular hull {0xFFFFFFFF} ∪ [0,8] on t"
    (match var_seed s8 t with
    | Some c -> Ws.elem (r32 8) c && (not (Ws.elem (r32 9) c)) && Ws.elem (r32 0xFFFFFFFF) c
    | None -> false);
  (* S9: load operand gives Cell seed. *)
  let rsp64 = Var.create ~is_virtual:false ~fresh:false "RSP" (Type.Imm 64) in
  check "S9: the Load operand -> the Cell seed ([0,9] on the cell)"
    (match
       Vsa.edge_constraints ~env:(mk_env [])
         (Bil.BinOp
            ( Bil.LT,
              Bil.Load
                ( Bil.Var m,
                  Bil.BinOp (Bil.MINUS, Bil.Var rsp64, Bil.Int (W.of_int ~width:64 8)),
                  LittleEndian,
                  `r32 ),
              Bil.Int (r32 10) ))
         (Ws.singleton Word.b1)
     with
    | [ Vsa.Cell (_, _, _, _, cstr) ] -> Ws.elem (r32 9) cstr && not (Ws.elem (r32 10) cstr)
    | _ -> false);
  (* S10: NOT bijection. *)
  check "S10: the NOT bijection — the FALSE side UGE [10, max] (10 ∈; 9 ∉)"
    (match seeds_of (Bil.UnOp (Bil.NOT, Bil.BinOp (Bil.LT, Bil.Var t, Bil.Int (r32 10)))) with
    | [ Vsa.Var (v, c) ] ->
        Var.equal v (Var.base t) && Ws.elem (r32 10) c && not (Ws.elem (r32 9) c)
    | _ -> false);
  (* S11: NEG row. *)
  check "S11: the NEG row — the neg'd [0,9]: 0 ∈, −1 ∈"
    (match seeds_of (Bil.BinOp (Bil.LT, Bil.UnOp (Bil.NEG, Bil.Var t), Bil.Int (r32 10))) with
    | [ Vsa.Var (v, c) ] ->
        Var.equal v (Var.base t) && Ws.elem (r32 0) c && Ws.elem (r32 0xFFFFFFFF) c
    | _ -> false);
  (* S12: flag-state recovery. *)
  let ctx12 : Vsa.analysis_ctx =
    {
      defs = None;
      stores = None;
      flag_state = Some (cf, Bil.LT, Bil.Var t, r32 10);
      has_sub = false;
    }
  in
  let s12 = Vsa.edge_constraints ~env:(mk_env []) ~ctx:ctx12 (Bil.Var cf) (Ws.singleton Word.b1) in
  check "S12: the flag-state recovery — the cf seed + the recovered t seed [0,9]"
    (match (var_seed s12 cf, var_seed s12 t) with
    | Some cc, Some ct -> Ws.elem Word.b1 cc && Ws.elem (r32 9) ct && not (Ws.elem (r32 10) ct)
    | _ -> false);
  (* S13: NOT-wrapped dual. *)
  check "S13: the dual — NOT (t EQ 10) -> the NEQ complement (10 ∉; 11 ∈)"
    (match seeds_of (Bil.UnOp (Bil.NOT, Bil.BinOp (Bil.EQ, Bil.Var t, Bil.Int (r32 10)))) with
    | [ Vsa.Var (v, c) ] ->
        Var.equal v (Var.base t) && (not (Ws.elem (r32 10) c)) && Ws.elem (r32 11) c
    | _ -> false);
  (* S14: infeasible constant. *)
  check "S14: the Infeasible constant — (Int 5) with {7} -> Infeasible; with {5} -> no seeds"
    (Vsa.edge_constraints ~env:(mk_env []) (Bil.Int (r32 5)) (Ws.singleton (r32 7))
     = [ Vsa.Infeasible ]
    && Vsa.edge_constraints ~env:(mk_env []) (Bil.Int (r32 5)) (Ws.singleton (r32 5)) = []);
  (* S15: cast rows. *)
  let env15 =
    mk_env
      [
        ( t,
          Ws.of_clp (Clp.create ~width:32 ~step:(r32 1) ~cardn:(W.of_int ~width:33 0x10000) (r32 0))
        );
      ]
  in
  let s15a =
    Vsa.edge_constraints ~env:env15
      (Bil.BinOp (Bil.EQ, Bil.Cast (Bil.LOW, 8, Bil.Var t), Bil.Int (W.of_int ~width:8 5)))
      (Ws.singleton Word.b1)
  in
  check "S15a: the LOW cast row — the truncation hull [5, 5 + 2^32 − 2^8] (5 ∈; 5+0x100 ∈; 4 ∉)"
    (match var_seed s15a t with
    | Some c -> Ws.elem (r32 5) c && Ws.elem (r32 0x105) c && not (Ws.elem (r32 4) c)
    | None -> false);
  let env15b = mk_env [ (t, Ws.singleton (r32 0x100)) ] in
  let s15b =
    Vsa.edge_constraints ~env:env15b
      (Bil.BinOp (Bil.LT, Bil.Cast (Bil.SIGNED, 64, Bil.Var t), Bil.Int (W.of_int ~width:64 0x100)))
      (Ws.singleton Word.b1)
  in
  check "S15b: the SIGNED ext row — the pre-image [0, 0xFF] (0xFF ∈; 0x100 ∉)"
    (match var_seed s15b t with
    | Some c -> Ws.elem (r32 0xFF) c && not (Ws.elem (r32 0x100) c)
    | None -> false);
  ())
