(* Forward-denotation pins: the transfer over BIR fixtures —
   denote_def/denote_defs/denote_imm_exp/reachable_jumps (the seam's
   forward half).  One Alcotest group per pin; each pin builds its own
   fixture, so no state crosses pins.  The image-backed pins arm and
   disarm the section images inside their own closure. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

(* The image-fixture vocabulary the FWD image pins share: one base
   var, one 12-byte image at 0x4000, and an env whose memory is top
   and whose base var holds the given address set. *)
let img_fixture =
  let img_var = v64 "t_img_base" in
  let m = Var.create ~is_virtual:false ~fresh:false "t_img_m" (Type.Mem (`r64, `r8)) in
  let img_bytes = Bytes.of_string "\x2d\x00\x00\x00\x00\x00\x00\x00\x1e\x5a\x00\x00" in
  let images =
    [ { Vsa.img_lo = 0x4000L; img_hi = 0x400bL; img_bytes;
        img_slots = Core.Int64.Set.empty } ] in
  let k = { Mem.addr_width = 64; Mem.addressable_width = 8 } in
  let env_with_addrs addrs =
    let st = AI.add_memory AI.top ~key:m ~data:(Mem.top k) in
    AI.add_word st ~key:img_var ~data:(Ws.of_list ~width:64 addrs)
  in
  let load32 addr_exp = Bil.Load (Bil.Var m, addr_exp, LittleEndian, `r32) in
  (img_var, images, m, k, env_with_addrs, load32)

(* The band round-trip fixture: a runtime-sized SP decrement whose
   pointer is stored and reloaded in a loop.  Returns the sub, its block
   tids and the pointer register. *)
let sp_roundtrip () =
  let m, rsp, rbp = memv "t19_m", v64 "RSP", v64 "t19_rbp" in
  let rax = v64 "t19_rax" in
  let rn = v64 "t19_n" in
  let lit k = Bil.Int (Cbat_word.to_word (w64 k)) in
  let d_rbp = Def.create rbp (Bil.Var rsp) in
  let d_frame = Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, lit 16)) in
  (* n read from a cell: the size is non-literal. *)
  let d_n_cell =
    Def.create m
      (Bil.Store (Bil.Var m, Bil.BinOp (Bil.MINUS, Bil.Var rbp, lit 12),
                  Bil.Int (Cbat_word.to_word (w32 8)), LittleEndian, `r32))
  in
  let d_n_load =
    Def.create rn
      (Bil.Load (Bil.Var m, Bil.BinOp (Bil.MINUS, Bil.Var rbp, lit 12),
                 LittleEndian, `r64))
  in
  let d_sub = Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Var rn)) in
  let d_ptr = Def.create rax (Bil.Var rsp) in
  let d_align =
    Def.create rax
      (Bil.BinOp (Bil.AND, Bil.Var rax, Bil.Int (Cbat_word.to_word (w64 (-4)))))
  in
  let cell = Bil.BinOp (Bil.MINUS, Bil.Var rbp, lit 8) in
  let d_save =
    Def.create m (Bil.Store (Bil.Var m, cell, Bil.Var rax, LittleEndian, `r64))
  in
  let d_reload = Def.create rax (Bil.Load (Bil.Var m, cell, LittleEndian, `r64)) in
  let i = v64 "t19_i" in
  let d_i1 = Def.create i (Bil.BinOp (Bil.PLUS, Bil.Var i, lit 1)) in
  let cond = Bil.BinOp (Bil.LE, Bil.Var i, lit 3) in
  let sub, tids =
    sub_of "t19_sp_roundtrip"
      [ [ d_rbp; d_frame; d_n_cell; d_n_load; d_sub; d_ptr; d_align;
          d_save; d_i1 ],
        [ (1, mk_goto) ];
        [ d_reload ],
        [ (3, fun t -> mk_jmp_to t cond);
          (2, fun t -> mk_jmp_to t (Bil.UnOp (Bil.NOT, cond))) ];
        [],
        [ (1, mk_goto) ];
        [], [] ]
  in
  (sub, tids, rax)

(* The store/load vocabulary of the memory-write pins: one memory var,
   64-bit literals, and [rsp - k] slots on the anchored entry. *)
let st_m = memv "st_m"
let st_lit n = Bil.Int (Cbat_word.to_word (w64 n))
let st_slot k = Bil.BinOp (Bil.MINUS, Bil.Var sp, st_lit k)
let st_store ?(size = `r64) env addr v =
  Vsa.Test_seam.denote_def
    (Def.create st_m (Bil.Store (Bil.Var st_m, addr, v, LittleEndian, size))) env
let st_load ?(size = `r64) env addr =
  match
    Vsa.Test_seam.denote_imm_exp (Bil.Load (Bil.Var st_m, addr, LittleEndian, size)) env
  with
  | Ok v -> v
  | Error _ -> failwith "st_load"
let st_has env addr n = Ws.elem (w64 n) (st_load env addr)

let tests : unit Alcotest.test list =
  [
    (* FWD-01: an Ite whose flag is {0,1} joins both arms. *)
    pin "FWD-01" "Ite with a {0,1}-valued flag joins both arms (no bottom)"
      (fun () ->
        let f32 = Var.create ~is_virtual:false ~fresh:false "flag32" (Type.Imm 32) in
        let env = AI.add_word AI.top ~key:f32 ~data:(Ws.of_list ~width:32 [ w32 0; w32 1 ]) in
        let e =
          Bil.Ite
            (Bil.Var f32, Bil.Int (Cbat_word.to_word (w32 10)), Bil.Int (Cbat_word.to_word (w32 20)))
        in
        match Vsa.Test_seam.denote_imm_exp e env with
        | Ok ws ->
            check "FWD-01" (Ws.elem (w32 10) ws && Ws.elem (w32 20) ws && not (Ws.is_bottom ws))
        | Error _ -> check "FWD-01" false);

    (* FWD-02: gate-free — every def is denoted without a tag. *)


    (* FWD-03: the caller-alias fixture's pre-call state — the slot holds {42}. *)


    (* FWD-04: pre-call rdi is the concrete aliased address {0xd0}. *)


    (* FWD-05: a top-address store invalidates the whole memory. *)
    pin "FWD-05"
      "gate-free — a top-addr store invalidates the memory (the store may hit any cell: \
       whole-memory top, never the preserved pre-store state)"
      (fun () ->
        let m = memv "e2ed_m3" in
        let d1 =
          Def.create m
            (Bil.Store
               ( Bil.Var m, Bil.Int (Cbat_word.to_word (w64 0x100)),
                 Bil.Int (Cbat_word.to_word (w64 42)), LittleEndian, `r64 ))
        in
        let env1 = Vsa.Test_seam.denote_def d1 AI.top in
        let d2 =
          Def.create m
            (Bil.Store
               ( Bil.Var m, Bil.Unknown ("e2ed_top", Type.Imm 64),
                 Bil.Int (Cbat_word.to_word (w64 7)), LittleEndian, `r64 ))
        in
        let idx = { Mem.addr_width = 64; Mem.addressable_width = 8 } in
        let mem1 = AI.find_memory idx env1 m in
        let env2 = Vsa.Test_seam.denote_def d2 env1 in
        let mem2 = AI.find_memory idx env2 m in
        check "FWD-05"
          (not (Mem.equal mem1 (Mem.top (Mem.get_idx mem1)))
          && Mem.equal mem2 (Mem.top (Mem.get_idx mem2))));

    (* FWD-06: the load at the invalidated slot reads top. *)


    (* FWD-07: EQ over a {0,1} operand is bool_top. *)
    pin "FWD-07"
      "EQ over a {0,1} operand is {0,1} (bool_top), not bottom — the is_zero guard sees \
       cardn 2"
      (fun () ->
        let zf = v1 "l2b_zf2" in
        let env = AI.add_word AI.top ~key:zf ~data:(Ws.of_list ~width:1 [ Cbat_word.b0; Cbat_word.b1 ]) in
        let e = Bil.BinOp (Bil.EQ, Bil.Var zf, Bil.Int W.b0) in
        match Vsa.Test_seam.denote_imm_exp e env with
        | Ok ws ->
            check "FWD-07"
              (not (Ws.is_bottom ws)
              && Cbat_word.(=) (Ws.cardinality ws) (Cbat_word.of_int ~width:2 2))
        | Error _ -> check "FWD-07" false);

    (* FWD-08: a lifted 1-bit flag def is {0,1} with cardn 2. *)
    pin "FWD-08" "a lifted 1-bit flag def (val_top (Imm 1)) is {0,1} with cardn 2, not bottom"
      (fun () ->
        let pf = v1 "l2b_pf3" in
        let env_after =
          Vsa.Test_seam.denote_def (Def.create pf (Bil.Unknown ("l2b_bits", Type.Imm 1))) AI.top
        in
        let ws = AI.find_word 1 env_after pf in
        check "FWD-08"
          (not (Ws.is_bottom ws)
          && Cbat_word.(=) (Ws.cardinality ws) (Cbat_word.of_int ~width:2 2)));

    (* FWD-09: overlap comparisons return bool_top. *)
    pin "FWD-09"
      "overlap comparisons (LT over two top64 operands; EQ(0, top64)) are {0,1} (bool_top), \
       not bottom"
      (fun () ->
        let x = v64 "l2b_x4" in
        let y = v64 "l2b_y4" in
        let z = v64 "l2b_z4" in
        let bool_top ws =
          not (Ws.is_bottom ws)
          && Cbat_word.(=) (Ws.cardinality ws) (Cbat_word.of_int ~width:2 2)
        in
        let ok_lt =
          Result.fold
            (Vsa.Test_seam.denote_imm_exp (Bil.BinOp (Bil.LT, Bil.Var x, Bil.Var y)) AI.top)
            ~ok:bool_top ~error:(fun _ -> false)
        in
        let ok_eq =
          Result.fold
            (Vsa.Test_seam.denote_imm_exp
               (Bil.BinOp (Bil.EQ, Bil.Int (Cbat_word.to_word (w64 0)), Bil.Var z))
               AI.top)
            ~ok:bool_top ~error:(fun _ -> false)
        in
        check "FWD-09" (ok_lt && ok_eq));

    (* FWD-10: a flag-gated branch survives — no unsound pruning. *)
    pin "FWD-10"
      "a flag-gated branch survives — reachable_jumps keeps the {0,1}-flag jump and the loop \
       body's solution input is non-bottom with a non-bottom flag (no unsound pruning)"
      (fun () ->
        let zf = v1 "l2b_zf5" in
        let x = v64 "l2b_x5" in
        let flag_env =
          Vsa.Test_seam.denote_def
            (Def.create zf
               (Bil.BinOp (Bil.EQ, Bil.Int (Cbat_word.to_word (w64 0)), Bil.Var x)))
            AI.top
        in
        let flag_val = AI.find_word 1 flag_env zf in
        let blk2 = blk_of_defs [] in
        let t2 = Term.tid blk2 in
        let blk1' =
          with_jmps (blk_of_defs []) [ Jmp.create ~cond:(Bil.Var zf) (Goto (Direct t2)) ]
        in
        let jmp =
          match Term.enum jmp_t blk1' |> Seq.to_list with [ j ] -> j | _ -> assert false
        in
        let kept =
          Vsa.Test_seam.reachable_jumps flag_env (Seq.of_list [ jmp ]) |> Seq.to_list
        in
        let cnt = v64 "l2b_cnt5" in
        let sub, tids =
          sub_of "l2b_flag_loop"
            [ [ Def.create zf
                  (Bil.BinOp (Bil.EQ, Bil.Int (Cbat_word.to_word (w64 0)), Bil.Var x)) ],
              [ (2, mk_goto) ];
              [ Def.create cnt
                  (Bil.BinOp (Bil.PLUS, Bil.Var cnt, Bil.Int (Cbat_word.to_word (w64 1)))) ],
              [ (2, mk_goto) ];
              [],
              [ (1, fun t -> mk_jmp_to t (Bil.Var zf));
                (3, fun t -> mk_jmp_to t (Bil.UnOp (Bil.NOT, Bil.Var zf))) ];
              [], [] ]
        in
        let body_tid = tids.(1) in
        let sol = run_anchored sub in
        let body_st = Graphlib.Std.Solution.get sol body_tid in
        let body_flag = AI.find_word 1 body_st zf in
        check "FWD-10"
          (not (Ws.is_bottom flag_val)
          && List.length kept = 1
          && not (AI.equal body_st AI.bottom)
          && not (Ws.is_bottom body_flag)
          && Ws.elem Cbat_word.b1 body_flag));

    (* FWD-11: a bounded image-backed load denotes the exact image words. *)
    pin "FWD-11" "a bounded image-backed load denotes the exact image words"
      (fun () ->
        let img_var, images, m, _, env_with_addrs, load32 = img_fixture in
        let word32 v = Cbat_word.of_word (Word.of_int64 ~width:32 v) in
        let env3 = env_with_addrs [ w64 0x4000; w64 0x4004; w64 0x4008 ] in
        protect
          ~set:(fun () -> Vsa.set_section_images images)
          ~restore:(fun () -> Vsa.set_section_images [])
          (fun () ->
            let img1 =
              match Vsa.Test_seam.denote_imm_exp (load32 (Bil.Var img_var)) env3 with
              | Ok ws ->
                  let card =
                    Result.fold (Cbat_word.to_int64 (Ws.cardinality ws)) ~ok:Fun.id
                      ~error:(fun _ -> -1L)
                  in
                  Ws.elem (word32 0x2dL) ws && Ws.elem (word32 0L) ws
                  && Ws.elem (word32 0x5a1eL) ws && Int64.equal card 3L
              | Error _ -> false
            in
            check "FWD-11" img1);
        let bytes = Bytes.init 26 (fun i -> Char.chr (if i < 24 then 23 - i else 0)) in
        let images =
          [ { Vsa.img_lo = 0x4000L; img_hi = 0x4019L; img_bytes = bytes;
              img_slots = Core.Int64.Set.empty } ] in
        let env = env_with_addrs (List.init 26 (fun i -> w64 (0x4000 + i))) in
        protect
          ~set:(fun () -> Vsa.set_section_images images)
          ~restore:(fun () -> Vsa.set_section_images [])
          (fun () ->
            let load8 = Bil.Load (Bil.Var m, Bil.Var img_var, LittleEndian, `r8) in
            let expected =
              Ws.of_clp (Clp.interval ~width:8
                  (Cbat_word.of_int ~width:8 0) (Cbat_word.of_int ~width:8 23)) in
            check "FWD-11.ordered-image-producer"
              (match Vsa.Test_seam.denote_imm_exp load8 env with
               | Ok ws -> Ws.equal ws expected
               | Error _ -> false)));

    (* FWD-12: the same load with no threaded image keeps the abstract top. *)
    pin "FWD-12" "an image-backed load without images keeps the abstract value"
      (fun () ->
        let img_var, _images, _m, k, env_with_addrs, load32 = img_fixture in
        let env3 = env_with_addrs [ w64 0x4000; w64 0x4004; w64 0x4008 ] in
        protect
          ~set:(fun () -> Vsa.set_section_images [])
          ~restore:(fun () -> Vsa.set_section_images [])
          (fun () ->
            let img2 =
              match Vsa.Test_seam.denote_imm_exp (load32 (Bil.Var img_var)) env3 with
              | Ok ws -> Ws.is_top ws
              | Error _ -> false
            in
            check "FWD-12" img2));

    (* FWD-13: a hull overhanging the image's end stays abstract. *)
    pin "FWD-13" "an access overhanging the image's end keeps the abstract value"
      (fun () ->
        let img_var, images, _, _, env_with_addrs, load32 = img_fixture in
        let env_over = env_with_addrs [ w64 0x400c; w64 0x4010 ] in
        protect
          ~set:(fun () -> Vsa.set_section_images images)
          ~restore:(fun () -> Vsa.set_section_images [])
          (fun () ->
            let img3 =
              match Vsa.Test_seam.denote_imm_exp (load32 (Bil.Var img_var)) env_over with
              | Ok ws -> Ws.is_top ws
              | Error _ -> false
            in
            check "FWD-13" img3));

    (* FWD-14: a stored cell in range wins over the image bytes. *)
    pin "FWD-14" "a stored cell in range wins over the image bytes"
      (fun () ->
        let img_var, images, m, k, env_with_addrs, load32 = img_fixture in
        let word32 v = Cbat_word.of_word (Word.of_int64 ~width:32 v) in
        let stored = Ws.singleton (word32 0x12345678L) in
        let cell_addr = Ws.singleton (w64 0x4000) in
        let env4 =
          let st = env_with_addrs [ w64 0x4000 ] in
          let mv = AI.find_memory k st m in
          let key =
            match Mem.Key.of_wordset cell_addr with [ k' ] -> k' | _ -> assert false
          in
          let mv' = Mem.add mv ~key ~data:(Mem.Val.create stored LittleEndian) in
          AI.add_memory st ~key:m ~data:mv'
        in
        protect
          ~set:(fun () -> Vsa.set_section_images images)
          ~restore:(fun () -> Vsa.set_section_images [])
          (fun () ->
            let img4 =
              match Vsa.Test_seam.denote_imm_exp (load32 (Bil.Var img_var)) env4 with
              | Ok ws -> Ws.equal ws stored
              | Error _ -> false
            in
            check "FWD-14" img4));

    (* FWD-15: the movaps alignment guard denotates {1} exactly. *)
    pin "FWD-15" "the movaps alignment guard denotates the singleton {1}"
      (fun () ->
        let sp = v64 "rg1_rsp" in
        let tmp = v64 "rg1_tmp" in
        let env0 = AI.add_word AI.top ~key:sp ~data:(Ws.stack_word_i64 0L) in
        let env1 =
          Vsa.Test_seam.denote_def
            (Def.create tmp
               (Bil.BinOp (Bil.MINUS, Bil.Var sp, Bil.Int (Cbat_word.to_word (w64 0x48)))))
            env0
        in
        let guard =
          Bil.BinOp
            ( Bil.EQ,
              Bil.BinOp (Bil.AND, Bil.Var tmp, Bil.Int (Cbat_word.to_word (w64 0xF))),
              Bil.Int (Cbat_word.to_word (w64 0)) )
        in
        match Vsa.Test_seam.denote_imm_exp guard env1 with
        | Ok ws ->
            check "FWD-15"
              (Ws.elem (Cbat_word.of_int ~width:1 1) ws
              && not (Ws.elem (Cbat_word.of_int ~width:1 0) ws))
        | Error _ -> check "FWD-15" false);

    (* FWD-16: the coercer makes operand widths uniform; a mismatched
       equality reaching the domain is a contract violation and answers
       top — never a coerced comparison.  A one-bit top is the bounded
       {0,1}, so both booleans must be present. *)
    pin "FWD-16" "a width-mismatched equality answers top" (fun () ->
        let v = v64 "t16_v" in
        let eq =
          Bil.BinOp (Bil.EQ, Bil.Var v, Bil.Int (Cbat_word.to_word (w32 5)))
        in
        let bool_top ws =
          Ws.bitwidth ws = 1
          && Ws.elem (Cbat_word.of_int ~width:1 0) ws
          && Ws.elem (Cbat_word.of_int ~width:1 1) ws
          && not (Ws.is_bottom ws)
        in
        let top1 =
          match
            Vsa.Test_seam.denote_imm_exp eq
              (AI.add_word AI.top ~key:v ~data:(Ws.singleton (w64 5)))
          with
          | Ok ws -> bool_top ws
          | Error _ -> false
        in
        let v2 = v64 "t16_w" in
        let eq2 =
          Bil.BinOp (Bil.EQ, Bil.Var v2, Bil.Int (Cbat_word.to_word (w32 0)))
        in
        let top1' =
          match
            Vsa.Test_seam.denote_imm_exp eq2
              (AI.add_word AI.top ~key:v2
                 ~data:(Ws.of_list ~width:64 [ w64 0; w64 0x200 ]))
          with
          | Ok ws -> bool_top ws
          | Error _ -> false
        in
        check "FWD-16" (top1 && top1'));

    (* FWD-17: a concat keeps its operands' order across representations.
       A zero high half and an unbounded low half is the low-64 range
       [0, 2^64-1], never the high-64 multiples. *)
    pin "FWD-17"
      "a concat keeps its operands' order across representations: a zero \
       high half with an unbounded low half is the low-64 range, never the \
       high-64 multiples"
      (fun () ->
        let e =
          Bil.Concat
            ( Bil.Int (Cbat_word.to_word (w64 0)),
              Bil.Unknown ("t_top64", Type.Imm 64) )
        in
        match Vsa.Test_seam.denote_imm_exp e AI.top with
        | Error _ -> check "FWD-17" false
        | Ok ws ->
          check "FWD-17"
            (not (Ws.is_top ws)
            && Ws.bitwidth ws = 128
            && Ws.elem (Cbat_word.of_int ~width:128 1) ws));

    (* FWD-18: an arithmetic op with mismatched operand widths answers top
       at the common width. *)

    (* FWD-19: the band round trip — a stored stack pointer reloads
       with its band, so the through-pointer accesses stay bounded. *)
    pin "FWD-19"
      "a stored band pointer reloads with its band (the store->load round trip keeps the origin)"
      (fun () ->
        let sub, tids, rax = sp_roundtrip () in
        let envs, _, _ =
          solve ~callee:(callee_of (Program.create ~subs:[ sub ] ()))
            Theory.Target.unknown sub
        in
        (* The RELOAD block's post state holds the reloaded value; the
           through-pointer reads keep the band only if that value is
           still the Stack-origin Rel.  Read by tid, never by map order. *)
        let reload_tid = tids.(1) in
        let post =
          match Core.Map.find envs reload_tid with
          | Some (_, post) -> post
          | None -> AI.bottom
        in
        check "FWD-19"
          (match Vsa.WordSet.stack_offsets (AI.find_word 64 post rax) with
           | Some _ -> true
           | None -> false));

    pin "FWD-21" "a store through a mixed-kind address writes each leaf's cells (weakly)"
      (fun () ->
        let p = v64 "fwd21_p" in
        let strided =
          Ws.of_clp (Clp.create ~width:64 ~step:(w64 8)
                       ~cardn:(Cbat_word.of_int ~width:65 20) (w64 0x10000)) in
        let addr = Ws.join strided (Ws.singleton (w64 0x5000)) in
        let env = AI.add_word AI.top ~key:p ~data:addr in
        let env = st_store env (st_lit 0x5000) (st_lit 42) in
        let env = st_store env (Bil.Var p) (st_lit 7) in
        check "FWD-21.old" (st_has env (st_lit 0x5000) 42);
        check "FWD-21.new" (st_has env (st_lit 0x5000) 7));

    pin "FWD-22" "a store through a two-slot stack address is a weak update of both slots"
      (fun () ->
        let q = v64 "fwd22_q" in
        let env =
          AI.add_word (anchored_entry ()) ~key:q
            ~data:(Ws.join (Ws.stack_word_i64 (-32L)) (Ws.stack_word_i64 (-24L))) in
        let env = st_store env (st_slot 32) (st_lit 5) in
        let env = st_store env (st_slot 24) (st_lit 6) in
        let env = st_store env (Bil.Var q) (st_lit 9) in
        check "FWD-22.lo" (st_has env (st_slot 32) 5 && st_has env (st_slot 32) 9);
        check "FWD-22.hi" (st_has env (st_slot 24) 6 && st_has env (st_slot 24) 9));

    pin "FWD-23" "a store inside a wider cell at another start invalidates the cell"
      (fun () ->
        let env = anchored_entry () in
        let env = st_store env (st_slot 64) (st_lit 0) in
        let env = st_store ~size:`r32 env (st_slot 60)
            (Bil.Int (Word.of_int ~width:32 2)) in
        (* The qword at rsp-64 now holds 0x2_0000_0000. *)
        check "FWD-23" (st_has env (st_slot 64) 0x200000000));

    pin "FWD-24" "a wider store invalidates the narrower cells inside its bytes"
      (fun () ->
        let env = anchored_entry () in
        let env = st_store ~size:`r32 env (st_slot 60)
            (Bil.Int (Word.of_int ~width:32 2)) in
        let env = st_store env (st_slot 64) (st_lit 0) in
        let hi = st_load ~size:`r32 env (st_slot 60) in
        check "FWD-24" (Ws.elem (w32 0) hi));

    pin "FWD-25" "a weak store on its own grid keeps the joined slots; a strong one overwrites"
      (fun () ->
        let q = v64 "fwd25_q" in
        let env =
          AI.add_word (anchored_entry ()) ~key:q
            ~data:(Ws.stack_word (Clp.create ~width:64 ~step:(w64 8)
                                    ~cardn:(Cbat_word.of_int ~width:65 2)
                                    (Cbat_word.of_int ~width:64 (-32)))) in
        let env = st_store env (st_slot 32) (st_lit 5) in
        let env = st_store env (st_slot 24) (st_lit 6) in
        let env = st_store env (Bil.Var q) (st_lit 9) in
        let exact env a xs =
          Ws.equal (st_load env a) (Ws.of_list ~width:64 (List.map w64 xs)) in
        check "FWD-25.weak" (exact env (st_slot 32) [ 5; 9 ] && exact env (st_slot 24) [ 6; 9 ]);
        let env = st_store env (st_slot 24) (st_lit 1) in
        check "FWD-25.strong" (exact env (st_slot 24) [ 1 ] && exact env (st_slot 32) [ 5; 9 ]));

    pin "FWD-26" "a store through a stack-or-NULL pointer writes the stack slot (weakly)"
      (fun () ->
        let p = v64 "fwd26_p" in
        let env =
          AI.add_word (anchored_entry ()) ~key:p
            ~data:(Ws.join (Ws.stack_word_i64 (-16L)) (Ws.singleton (w64 0))) in
        let env = st_store env (st_slot 16) (st_lit 42) in
        let env = st_store env (Bil.Var p) (st_lit 7) in
        check "FWD-26" (st_has env (st_slot 16) 42 && st_has env (st_slot 16) 7));

    pin "FWD-27"
      "EQ/NEQ on same-origin stack singletons compare by offsets: p == p is true, p == (p - 8) \
       is false and its NEQ is true (the saturated stack cardinality no longer hides it)"
      (fun () ->
        let p = v64 "fwd27_p" in
        let q = v64 "fwd27_q" in
        let env =
          AI.add_word
            (AI.add_word AI.top ~key:p ~data:(Ws.stack_word_i64 (-16L)))
            ~key:q ~data:(Ws.stack_word_i64 (-24L)) in
        let btrue = Ws.singleton Cbat_word.b1 and bfalse = Ws.singleton Cbat_word.b0 in
        let denote e =
          match Vsa.Test_seam.denote_imm_exp e env with
          | Ok ws -> ws
          | Error _ -> Ws.bottom 1 in
        check "FWD-27.eq-self"
          (Ws.equal (denote (Bil.BinOp (Bil.EQ, Bil.Var p, Bil.Var p))) btrue);
        check "FWD-27.eq-distinct"
          (Ws.equal (denote (Bil.BinOp (Bil.EQ, Bil.Var p, Bil.Var q))) bfalse);
        check "FWD-27.neq-distinct"
          (Ws.equal (denote (Bil.BinOp (Bil.NEQ, Bil.Var p, Bil.Var q))) btrue));

    pin "FWD-28"
      "an Ite with a decided condition returns the taken branch and still reports the untaken \
       branch's type error; an undecided condition joins both"
      (fun () ->
        let lit n = Bil.Int (Cbat_word.to_word (w64 n)) in
        let one = Bil.Int (Cbat_word.to_word (Cbat_word.b1)) in
        let zero = Bil.Int (Cbat_word.to_word (Cbat_word.b0)) in
        let bad = Bil.Var (Var.create "fwd28_unk" Type.Unk) in
        let c = v1 "fwd28_c" in
        let denote e env = Vsa.Test_seam.denote_imm_exp e env in
        let is_val e n =
          match denote e AI.top with
          | Ok ws -> Ws.equal ws (Ws.singleton (w64 n))
          | Error _ -> false in
        check "FWD-28.taken"
          (is_val (Bil.Ite (one, lit 7, lit 9)) 7
          && is_val (Bil.Ite (zero, lit 7, lit 9)) 9);
        check "FWD-28.error-kept"
          (Result.is_error (denote (Bil.Ite (one, lit 7, bad)) AI.top)
          && Result.is_error (denote (Bil.Ite (zero, bad, lit 9)) AI.top));
        check "FWD-28.undecided-joins"
          (match denote (Bil.Ite (Bil.Var c, lit 7, lit 9)) AI.top with
           | Ok ws -> Ws.equal ws (Ws.join (Ws.singleton (w64 7)) (Ws.singleton (w64 9)))
           | Error _ -> false));

    pin "FWD-29"
      "reachable_jumps stops at an always-taken jump without denoting a later guard"
      (fun () ->
        let dead = v1 "fwd29_dead" in
        let env = AI.add_word AI.top ~key:dead ~data:(Ws.bottom 1) in
        let t = Term.tid (blk_of_defs []) in
        let first = mk_goto t in
        let later = mk_jmp_to t (Bil.Var dead) in
        let kept =
          Vsa.Test_seam.reachable_jumps env (Seq.of_list [ first; later ])
          |> Seq.to_list in
        check "FWD-29" (List.length kept = 1));
  ]

let () = run "forward" tests
