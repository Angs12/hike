(* Forward-denotation pins: the transfer over BIR fixtures —
   denote_def/denote_defs/denote_imm_exp/reachable_jumps (the seam's
   forward half).  Checks migrated verbatim from test_vsa; names and
   counts preserved. *)
open Bap.Std
open Bap_core_theory
open Test_common
open Test_fixtures

let run () =
(* Ite else-arm joins both arms. *)
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
;
(  let iv = v64 "t2_iv" in
  let d = Def.create iv (Bil.Int (Cbat_word.to_word (w64 7))) in
  let e_den = Vsa.Test_seam.denote_def d AI.top in
  check "T2-1: gate-free — every def is denoted, no tag needed"
    (Ws.equal (AI.find_word 64 e_den iv) (Ws.singleton (w64 7)));
  ())
;
(* Caller-alias fixture: aliased slot, tracked load, call, post reload. Returns the record. *)
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
  ())
;
(* E3 (the SOUND contract): a store through a TOP address may write any
   cell — the whole memory invalidates (whole-memory top), and the
   pre-store slot value is unprovable: the 0x100 load reads top. *)
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
  let mem1 = AI.find_memory { Mem.addr_width = 64; Mem.addressable_width = 8 } env1 m in
  let env2 = Vsa.Test_seam.denote_def d2 env1 in
  let mem2 = AI.find_memory { Mem.addr_width = 64; Mem.addressable_width = 8 } env2 m in
  check "E2eD-7: gate-free — a top-addr store invalidates the memory (the store may hit any \
         cell: whole-memory top, never the preserved pre-store state)"
    (not (Mem.equal mem1 (Mem.top (Mem.get_idx mem1)))
    && Mem.equal mem2 (Mem.top (Mem.get_idx mem2)));
  let env3 = Vsa.Test_seam.denote_def dload env2 in
  let tv = AI.find_word 64 env3 t in
  check
    "E2eD-8: gate-free — the load at the slot reads top (the top store may hit 0x100, so the \
     pre-store {42} is no longer provable — invalidated, not preserved)"
    (Ws.is_top tv);
  ())
;
(* L2b-2: EQ over {0,1} — is_zero guard sees unwrapped cardn. *)
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
  ())
;
(* L2b-3: lifted 1-bit flag value via unknown[bits]:u1 def. *)
(  let pf = v1 "l2b_pf3" in
  let env_after = Vsa.Test_seam.denote_def (Def.create pf (Bil.Unknown ("l2b_bits", Type.Imm 1))) AI.top in
  let ws = AI.find_word 1 env_after pf in
  check "L2b-3: a lifted 1-bit flag def (val_top (Imm 1)) is {0,1} with cardn 2, not bottom"
    ((not (Ws.is_bottom ws)) && Cbat_word.(=) (Ws.cardinality ws) (Cbat_word.of_int ~width:2 2));
  ())
;
(* L2b-4: overlap comparisons return bool_top, not bottom. *)
(  let x = v64 "l2b_x4" in
  let y = v64 "l2b_y4" in
  let z = v64 "l2b_z4" in
  let ok_lt =
    Result.fold
      (Vsa.Test_seam.denote_imm_exp (Bil.BinOp (Bil.LT, Bil.Var x, Bil.Var y)) AI.top)
      ~ok:(fun ws ->
        (not (Ws.is_bottom ws)) && Cbat_word.(=) (Ws.cardinality ws) (Cbat_word.of_int ~width:2 2))
      ~error:(fun _ -> false)
  in
  let ok_eq =
    Result.fold
      (Vsa.Test_seam.denote_imm_exp (Bil.BinOp (Bil.EQ, Bil.Int (Cbat_word.to_word (w64 0)), Bil.Var z)) AI.top)
      ~ok:(fun ws ->
        (not (Ws.is_bottom ws)) && Cbat_word.(=) (Ws.cardinality ws) (Cbat_word.of_int ~width:2 2))
      ~error:(fun _ -> false)
  in
  check
    "L2b-4: overlap comparisons (LT over two top64 operands; EQ(0, top64)) are {0,1} (bool_top), \
     not bottom"
    (ok_lt && ok_eq);
  ())
;
(* L2b-5: flag-gated branch survives — no unsound pruning. *)
(  let zf = v1 "l2b_zf5" in
  let x = v64 "l2b_x5" in
  let flag_env =
    Vsa.Test_seam.denote_def (Def.create zf (Bil.BinOp (Bil.EQ, Bil.Int (Cbat_word.to_word (w64 0)), Bil.Var x))) AI.top
  in
  let flag_val = AI.find_word 1 flag_env zf in
  (* (a) direct reachable_jumps on a flag-gated jump *)
  let blk2 = blk_of_defs [] in
  let t2 = Term.tid blk2 in
  let blk1' = with_jmps (blk_of_defs []) [ Jmp.create ~cond:(Bil.Var zf) (Goto (Direct t2)) ] in
  let jmp = match Term.enum jmp_t blk1' |> Seq.to_list with [ j ] -> j | _ -> assert false in
  let kept = Vsa.Test_seam.reachable_jumps flag_env (Seq.of_list [ jmp ]) |> Seq.to_list in
  (* (b) loop with flag-gated back-edge. *)
  let cnt = v64 "l2b_cnt5" in
  let sub, tids =
    sub_of "l2b_flag_loop"
      [ [ Def.create zf (Bil.BinOp (Bil.EQ, Bil.Int (Cbat_word.to_word (w64 0)), Bil.Var x)) ],
        [ (2, mk_goto) ];
        [ Def.create cnt (Bil.BinOp (Bil.PLUS, Bil.Var cnt, Bil.Int (Cbat_word.to_word (w64 1)))) ],
        [ (2, mk_goto) ];
        [], [ (1, fun t -> mk_jmp_to t (Bil.Var zf)); (3, fun t -> mk_jmp_to t (Bil.UnOp (Bil.NOT, Bil.Var zf))) ];
        [], [] ]
  in
  let body_tid = tids.(1) in
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
;
(* The image-backed load: an address bounded inside a threaded section
   image reads the image's bytes exactly; every arm the premise does
   not cover keeps the abstract value. *)
(  let img_var = v64 "t_img_base" in
  let m = Var.create ~is_virtual:false ~fresh:false "t_img_m" (Type.Mem (`r64, `r8)) in
  (* Three little-endian 4-byte entries at 0x4000: 0x2d, 0, 0x5a1e. *)
  let img_bytes =
    Bytes.of_string
      "\x2d\x00\x00\x00\x00\x00\x00\x00\x1e\x5a\x00\x00"
  in
  let images =
    [ { Vsa.img_lo = 0x4000L; img_hi = 0x400bL; img_bytes } ]
  in
  let k = { Mem.addr_width = 64; Mem.addressable_width = 8 } in
  let env_with_addrs addrs =
    let st = AI.add_memory AI.top ~key:m ~data:(Mem.top k) in
    AI.add_word st ~key:img_var ~data:(Ws.of_list ~width:64 addrs)
  in
  let load32 addr_exp = Bil.Load (Bil.Var m, addr_exp, LittleEndian, `r32) in
  let var_exp = Bil.Var img_var in
  let word32 v = Cbat_word.of_word (Word.of_int64 ~width:32 v) in
  (* IMG-1: the bounded multi-entry read is the exact image words. *)
  let env3 = env_with_addrs [ w64 0x4000; w64 0x4004; w64 0x4008 ] in
  Vsa.set_section_images images;
  let img1 =
    match Vsa.Test_seam.denote_imm_exp (load32 var_exp) env3 with
    | Ok ws ->
      let card =
        Result.fold (Cbat_word.to_int64 (Ws.cardinality ws)) ~ok:Fun.id ~error:(fun _ -> -1L)
      in
      Ws.elem (word32 0x2dL) ws && Ws.elem (word32 0L) ws
      && Ws.elem (word32 0x5a1eL) ws
      && Int64.equal card 3L
    | Error _ -> false
  in
  check "IMG-1: a bounded image-backed load denotes the exact image words" img1;
  (* IMG-2: the same load with no threaded image keeps the abstract top. *)
  Vsa.set_section_images [];
  let img2 =
    match Vsa.Test_seam.denote_imm_exp (load32 var_exp) env3 with
    | Ok ws -> Ws.is_top ws
    | Error _ -> false
  in
  check "IMG-2: an image-backed load without images keeps the abstract value" img2;
  (* IMG-3: a hull overhanging the image's end stays abstract. *)
  Vsa.set_section_images images;
  let env_over =
    env_with_addrs [ w64 0x400c; w64 0x4010 ] (* 0x400c + 4 > 0x400b *)
  in
  let img3 =
    match Vsa.Test_seam.denote_imm_exp (load32 var_exp) env_over with
    | Ok ws -> Ws.is_top ws
    | Error _ -> false
  in
  check "IMG-3: an access overhanging the image's end keeps the abstract value" img3;
  (* IMG-4: a stored cell in range wins over the image bytes. *)
  let stored = Ws.singleton (word32 0x12345678L) in
  let cell_addr = Ws.singleton (w64 0x4000) in
  let env4 =
    let st = env_with_addrs [ w64 0x4000 ] in
    let mv = AI.find_memory k st m in
    let key = match Mem.Key.of_wordset cell_addr with Some k' -> k' | None -> assert false in
    let mv' = Mem.add mv ~key ~data:(Mem.Val.create stored LittleEndian) in
    AI.add_memory st ~key:m ~data:mv'
  in
  let img4 =
    match Vsa.Test_seam.denote_imm_exp (load32 var_exp) env4 with
    | Ok ws -> Ws.equal ws stored
    | Error _ -> false
  in
  Vsa.set_section_images [];
  check "IMG-4: a stored cell in range wins over the image bytes" img4;
  ());
(* The call-effects transfer: the survive-a-call policy — the preserved
   derivation from the callee's kill summary, the frame-keep decision,
   and the SP restore, each behind the one interface. *)
(  let abi = Hike_abi.x86_64_sysv in
  let module Ce = Vsa.Call_effects in
  let not_return v =
    not (Base.List.exists abi.Hike_abi.return_regs ~f:(Var.same v)) in
  let g1, g2 =
    match Base.List.filter abi.Hike_abi.caller_saved_gprs ~f:not_return with
    | g1 :: g2 :: _ -> (g1, g2)
    | _ -> assert false
  in
  let rdi = Base.List.nth_exn abi.Hike_abi.int_param_regs 0 in
  let x = v64 "ce_x" in
  let mkey lo =
    match Mem.Key.of_wordset (Ws.singleton (w64 lo)) with
    | Some k -> k | None -> assert false
  in
  let idx = { Mem.addr_width = 64; Mem.addressable_width = 8 } in
  (* The pre-call env: a frame with cells at [0x2000; 0x3000] above the
     call-time RSP {0x1000}, one below it at [0x500], and a memory var. *)
  let raw_env ~lanes =
    let mem =
      Mem.add
        (Mem.add
           (Mem.add
              (Mem.top idx)
              ~key:(mkey 0x2000)
              ~data:(Mem.Val.create (Ws.singleton (w64 42)) LittleEndian))
           ~key:(mkey 0x3000)
           ~data:(Mem.Val.create (Ws.singleton (w64 7)) LittleEndian))
        ~key:(mkey 0x500)
        ~data:(Mem.Val.create (Ws.singleton (w64 1)) LittleEndian)
    in
    let m = memv "ce_m" in
    let env =
      AI.add_memory AI.top ~key:m ~data:mem
      |> AI.add_word ~key:abi.Hike_abi.sp
           ~data:(Ws.singleton (w64 0x1000))
    in
    let env =
      Base.List.fold lanes ~init:env ~f:(fun acc v ->
          AI.add_word acc ~key:v ~data:(Ws.singleton (w64 0x2000)))
    in
    (env, m)
  in
  let reads m lo post =
    Mem.Val.data (Mem.find (64, LittleEndian)
                    (AI.find_memory idx post m) (mkey lo))
  in
  (* CE1/CE2: the preserved derivation from the callee's kill summary. *)
  let summary = Core.Set.singleton (module Var) g1 in
  let words_env =
    AI.add_word
      (AI.add_word AI.top ~key:g1 ~data:(Ws.singleton (w64 1)))
      ~key:g2
      ~data:(Ws.singleton (w64 2))
  in
  let kept = Ce.transfer ~abi ~preserved:(Var.Set.singleton x)
      ~site:{ Ce.summary = Some summary; written_lanes = [];
              pushed = false }
      (AI.add_word words_env ~key:x ~data:(Ws.singleton (w64 5))) in
  check "CE1: the kill summary keeps non-written caller-saved GPRs and the base"
    (Ws.equal (AI.find_word 64 kept x) (Ws.singleton (w64 5))
    && Ws.equal (AI.find_word 64 kept g2) (Ws.singleton (w64 2))
    && Ws.is_top (AI.find_word 64 kept g1));
  let killed = Ce.transfer ~abi ~preserved:(Var.Set.singleton x)
      ~site:{ Ce.summary = None; written_lanes = []; pushed = false }
      (AI.add_word words_env ~key:x ~data:(Ws.singleton (w64 5))) in
  check "CE2: no summary (unknown or kill-all) keeps only the base set"
    (Ws.equal (AI.find_word 64 killed x) (Ws.singleton (w64 5))
    && Ws.is_top (AI.find_word 64 killed g1)
    && Ws.is_top (AI.find_word 64 killed g2));
  (* CE3/CE4: the frame-keep decision on the frame cells. *)
  let frame_call ~lanes =
    let e, m = raw_env ~lanes in
    (Ce.transfer ~abi ~preserved:Var.Set.empty
       ~site:{ Ce.summary = None; written_lanes = lanes;
               pushed = false }
       e,
     m)
  in
  let kept_frame, m_kept = frame_call ~lanes:[] in
  check "CE3: frame-keep — cells at/above the call-time RSP survive, below die"
    (Ws.equal (reads m_kept 0x2000 kept_frame) (Ws.singleton (w64 42))
    && Ws.equal (reads m_kept 0x3000 kept_frame) (Ws.singleton (w64 7))
    && Ws.is_top (reads m_kept 0x500 kept_frame));
  let escaped, m_esc = frame_call ~lanes:[ rdi ] in
  check "CE4: an escape lane's range dies with the call, the rest of the frame survives"
    (Ws.is_top (reads m_esc 0x2000 escaped)
    && Ws.equal (reads m_esc 0x3000 escaped) (Ws.singleton (w64 7)));
  (* CE5: the pushed site's SP restore. *)
  let restored = Ce.transfer ~abi ~preserved:Var.Set.empty
      ~site:{ Ce.summary = None; written_lanes = []; pushed = true }
      (AI.add_word AI.top ~key:abi.Hike_abi.sp
         ~data:(Ws.singleton (w64 0x1000))) in
  let rsp' = AI.find_word 64 restored abi.Hike_abi.sp in
  check "CE5: a pushed site's SP gains one word — the popped retaddr"
    (Ws.elem (w64 0x1000) rsp' && Ws.elem (w64 0x1008) rsp');
  (* CE6: a trap keeps no frame and restores no SP (the landing-1
     contract; landing 2 tightens the memory half). *)
  let trap_env, m_trap = raw_env ~lanes:[] in
  let trap = Ce.transfer ~abi
      ~preserved:(Var.Set.singleton abi.Hike_abi.sp)
      ~site:{ Ce.summary = None; written_lanes = []; pushed = false }
      trap_env in
  check "CE6: a trap restores no SP (it pops no retaddr)"
    (Ws.equal (AI.find_word 64 trap abi.Hike_abi.sp)
         (Ws.singleton (w64 0x1000)));
  (* CE7: a trap with a bounded RSP and bounded escapes keeps the frame
     like any call — the escape bounds what the trap may clobber. *)
  let trap_frame = Ce.transfer ~abi
      ~preserved:(Var.Set.singleton abi.Hike_abi.sp)
      ~site:{ Ce.summary = None; written_lanes = []; pushed = false }
      trap_env in
  check "CE7: a trap with a bounded RSP keeps the frame like any call"
    (Ws.equal (reads m_trap 0x2000 trap_frame) (Ws.singleton (w64 42))
    && Ws.equal (reads m_trap 0x3000 trap_frame) (Ws.singleton (w64 7))
    && Ws.is_top (reads m_trap 0x500 trap_frame));
  (* CE8-CE10: an indirect site's summary derivation — the target exp's
     denotation resolves through the run's sub lookup. *)
  let tgt = v64 "ce_tgt" in
  let sub_tid = Tid.create () in
  let g = Base.List.nth_exn abi.Hike_abi.caller_saved_gprs 0 in
  let gs = Core.Set.singleton (module Var) g in
  let lookup v = if Int64.equal v 0x5000L then Some sub_tid else None in
  let summary_of t =
    if Tid.equal t sub_tid then Some gs else None in
  let bounded = AI.add_word AI.top ~key:tgt ~data:(Ws.singleton (w64 0x5000)) in
  check "CE8: a singleton target naming a lifted sub reads its summary"
    (match Ce.indirect_summary ~lookup ~summary_of ~env:bounded (Bil.Var tgt) with
     | Some ws -> Var.Set.equal ws gs
     | None -> false);
  let spread = AI.add_word AI.top ~key:tgt
      ~data:(Ws.of_list ~width:64 [ w64 1; w64 2 ]) in
  check "CE9: an unbounded target resolves to nothing"
    (match Ce.indirect_summary ~lookup ~summary_of ~env:spread (Bil.Var tgt) with
     | None -> true | Some _ -> false);
  let foreign = AI.add_word AI.top ~key:tgt
      ~data:(Ws.singleton (w64 0x9000)) in
  check "CE10: a foreign singleton resolves to nothing"
    (match Ce.indirect_summary ~lookup ~summary_of ~env:foreign (Bil.Var tgt) with
     | None -> true | Some _ -> false);
  (* R-G1: the movaps alignment guard the lifter materializes — the
     SP-derived value's certified nibble AND 0xF equals zero exactly,
     so the guard's EQ denotates {1} and the #GP path is provably
     dead instead of unknown. *)
  let sp = v64 "rg1_rsp" in
  let tmp = v64 "rg1_tmp" in
  let env0 = AI.add_word AI.top ~key:sp ~data:(Ws.stack_word_i64 0L) in
  let env1 =
    Vsa.Test_seam.denote_def
      (Def.create tmp
         (Bil.BinOp (Bil.MINUS, Bil.Var sp, Bil.Int (Cbat_word.to_word (w64 0x48)))))
      env0 in
  let guard =
    Bil.BinOp (Bil.EQ,
               Bil.BinOp (Bil.AND, Bil.Var tmp, Bil.Int (Cbat_word.to_word (w64 0xF))),
               Bil.Int (Cbat_word.to_word (w64 0))) in
  match Vsa.Test_seam.denote_imm_exp guard env1 with
  | Ok ws ->
      check "R-G1: the movaps alignment guard denotates the singleton {1}"
        (Ws.elem (Cbat_word.of_int ~width:1 1) ws
         && not (Ws.elem (Cbat_word.of_int ~width:1 0) ws))
  | Error _ ->
      check "R-G1: the movaps alignment guard denotates the singleton {1}" false;
  ())
