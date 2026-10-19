(* VSA pass pins.  One Alcotest group per pin; each pin builds its own
   fixture, so no state crosses pins.  The Call_effects transfer pins
   (CE-01..CE-15) live with their module, not here. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

(* A 32-bit fixture var (the branch-assume and BIR-loop pins). *)
let i32 (n : string) : var = Var.create ~is_virtual:false ~fresh:false n (Type.Imm 32)

(* constrain_edge over the anchored top env, reading [v] at [width]. *)
let assume (width : int) (v : var) (cond : exp) : Ws.t =
  AI.find_word width
    (Vsa.Test_seam.constrain_edge ~synth:Hike.Synth.empty ~landmarks:(Cbat_landmarks.create ()) ~env:AI.top
       (Jmp.cond (mk_jmp_to (Tid.create ()) cond)))
    v

(* The block IN-state of [tid] in a solved sub. *)
let in_state (sol : Vsa.vsa_sol) (tid : tid) : AI.t =
  Graphlib.Std.Solution.get sol tid

(* The entry block's tid (the P3 anchor reads its input state). *)
let entry_tid_of (sub : sub term) : tid =
  match Term.first blk_t sub with Some b -> Term.tid b | None -> assert false

(* Slice fixtures: a guard bounds some bits of [x]; the fallthrough runs
   [between], then reads the same bits into [y] (read block, then an exit
   whose IN-state shows [y]); the taken edge goes to a second exit.  The
   shape is a switch's byte bound: [lea eax,[rdi-K]; cmp al,N; ja default]. *)
type slice_fixture = {
  sf_sub : sub term;
  sf_read_exit : tid;
  sf_y : var;
}

let byte_const (n : int) : exp = Bil.Int (Cbat_word.to_word (Cbat_word.of_int ~width:8 n))

let low8 (e : exp) : exp = Bil.Cast (Bil.LOW, 8, e)

let mk_slice_sub ~(x : var) ?(between = []) ?(call = false)
    ?(narrow = low8) ?(bound = 0x25) () : slice_fixture =
  let y = Var.create ~is_virtual:false ~fresh:false "sl_y" (Type.Imm 32) in
  let guard = Bil.BinOp (Bil.LT, byte_const bound, narrow (Bil.Var x)) in
  let read = Def.create y (Bil.Cast (Bil.UNSIGNED, 32, narrow (Bil.Var x))) in
  let callee_tid = Term.tid (mk_selfloop_callee "sl_callee") in
  let mid = if call then (2, fun t -> mk_call_jmp t callee_tid) else (2, mk_goto) in
  let sub, tids =
    sub_of "slice"
      [ [], [ (4, fun t -> mk_jmp_to t guard); (1, mk_goto) ];
        between, [ mid ];
        [ read ], [ (3, mk_goto) ];
        [], [ (3, mk_ret) ];
        [], [ (5, mk_goto) ];
        [], [ (5, mk_ret) ] ]
  in
  { sf_sub = sub; sf_read_exit = tids.(3); sf_y = y }

let slice_y (fx : slice_fixture) : Ws.t =
  let sol = run_anchored fx.sf_sub in
  AI.find_word 32 (in_state sol fx.sf_read_exit) fx.sf_y

let slice_x () : var = Var.create ~is_virtual:false ~fresh:false "sl_x" (Type.Imm 32)

let slice_bounded (ws : Ws.t) (n : int) : bool = bounded_above ws (w32 n)

let tests : unit Alcotest.test list =
  [
    (* D4: branch-assume refinement — gate-free, every guard shape. *)
    pin "VSA-01" "D4-1: assume (x < 5) refines x to [0,4]"
      (fun () ->
        let ivar = i32 "i" in
        let c =
          assume 32 ivar
            (Bil.BinOp (Bil.LT, Bil.Var ivar, Bil.Int (Cbat_word.to_word (w32 5))))
        in
        check "VSA-01" (Ws.min_elem c = Some (w32 0) && Ws.max_elem c = Some (w32 4)));

    pin "VSA-02" "D4-2: assume (x <= 5) refines x to [0,5]"
      (fun () ->
        let ivar = i32 "i" in
        let c =
          assume 32 ivar
            (Bil.BinOp (Bil.LE, Bil.Var ivar, Bil.Int (Cbat_word.to_word (w32 5))))
        in
        check "VSA-02" (Ws.min_elem c = Some (w32 0) && Ws.max_elem c = Some (w32 5)));

    pin "VSA-03" "D4-3: assume (x == 5) refines x to {5}"
      (fun () ->
        let ivar = i32 "i" in
        let c =
          assume 32 ivar
            (Bil.BinOp (Bil.EQ, Bil.Var ivar, Bil.Int (Cbat_word.to_word (w32 5))))
        in
        check "VSA-03" (Ws.min_elem c = Some (w32 5) && Ws.max_elem c = Some (w32 5)));

    pin "VSA-04" "D4-4: doubt — constant condition keeps the state (top)"
      (fun () ->
        let ivar = i32 "i" in
        let c = assume 32 ivar (Bil.Int (Cbat_word.to_word (w32 1))) in
        check "VSA-04" (Ws.is_top c));

    pin "VSA-05" "D4-5: doubt — width-mismatched guard keeps the state (top)"
      (fun () ->
        let ivar = i32 "i" in
        let c =
          assume 32 ivar
            (Bil.BinOp (Bil.LT, Bil.Var ivar, Bil.Int (Cbat_word.to_word (w64 5))))
        in
        check "VSA-05" (Ws.is_top c));

    pin "VSA-06"
      "D4-6: gate-free (spec §2.1) — the NEQ guard refines to TOP−{5} (5 ∉, 0 ∈, non-top)"
      (fun () ->
        let ivar = i32 "i" in
        let c =
          assume 32 ivar
            (Bil.BinOp (Bil.NEQ, Bil.Var ivar, Bil.Int (Cbat_word.to_word (w32 5))))
        in
        check "VSA-06"
          ((not (Ws.is_top c)) && (not (Ws.elem (w32 5) c)) && Ws.elem (w32 0) c));

    pin "VSA-07" "D4-7: assume (flag) forces the flag to {1}"
      (fun () ->
        let fv = v1 "zf" in
        let c = assume 1 fv (Bil.Var fv) in
        check "VSA-07" (Ws.elem Cbat_word.b1 c && not (Ws.elem Cbat_word.b0 c)));

    pin "VSA-08" "D4-8: assume (NOT flag) forces the flag to {0}"
      (fun () ->
        let fv = v1 "zf" in
        let c = assume 1 fv (Bil.UnOp (Bil.NOT, Bil.Var fv)) in
        check "VSA-08" (Ws.elem Cbat_word.b0 c && not (Ws.elem Cbat_word.b1 c)));

    (* D4-9: the BIR-level loop — the back edge refined by "i < 5", the
       exit view carrying the exit-iteration values. *)
    pin "VSA-09"
      "D4-9 (BIR loop): the partition — the iterate view's counter is bounded by the guard (⊆ [0,4]) and the exit view carries the exit-iteration values (min ≥ 5)"
      (fun () ->
        let i = i32 "i" in
        let iv = Bil.Var i in
        let lt5 = Bil.BinOp (Bil.LT, iv, Bil.Int (Cbat_word.to_word (w32 5))) in
        let nlt5 = Bil.UnOp (Bil.NOT, lt5) in
        let sub, tids =
          sub_of "d4_loop"
            [ [ Def.create i (Bil.Int (Cbat_word.to_word (w32 0))) ], [ (1, mk_goto) ];
              [ Def.create i (Bil.BinOp (Bil.PLUS, iv, Bil.Int (Cbat_word.to_word (w32 1)))) ],
              [ (2, mk_goto) ];
              [], [ (3, fun t -> mk_jmp_to t nlt5); (1, fun t -> mk_jmp_to t lt5) ];
              [], [] ]
        in
        let sol = run_anchored sub in
        let c_iter = AI.find_word 32 (in_state sol tids.(1)) i in
        let c_exit = AI.find_word 32 (in_state sol tids.(3)) i in
        check "VSA-09"
          ((not (Ws.is_top c_iter))
          && (Base.Option.filter (Ws.max_elem c_iter)
                ~f:(fun w -> Cbat_word.(<=) w (w32 4))
             |> Option.is_some)
          && (not (Ws.is_top c_exit))
          && Base.Option.filter (Ws.min_elem c_exit)
               ~f:(fun w -> Cbat_word.(>=) w (w32 5))
             |> Option.is_some));

    (* D6: coercing width helpers — mismatched ops coerce, never raise. *)


























    (* D6-14: a mixed-width rshift reaching the domain is the pass's
       contract violation; the domain answers top at the common width
       (no crash, no not_implemented fire). *)


    (* D6b: Exact lift2 default width — mismatched sets widen to 64. *)








    (* E6: not_implemented logs through Event.Log only; stderr stays clean. *)




    (* T3: gate-free flag-guard refinement. *)


    pin "VSA-32" "T3-7: mixed-def — f IS refined to {1} on the taken edge"
      (fun () ->
        let f, _ctx, sub, exit_tid, _, _, _ = mk_flag_sub ~mixed:true in
        let sol = run_anchored sub in
        let c = AI.find_word 1 (in_state sol exit_tid) f in
        check "VSA-32" (Ws.elem Cbat_word.b1 c && not (Ws.elem Cbat_word.b0 c)));



    (* T4: the caller-alias fixpoint — the post-call state. *)
    pin "VSA-34" "T4-7: caller-alias — the post-call reload reads TOP (sound)"
      (fun () ->
        let fx = mk_caller_alias () in
        let sol = run_anchored fx.ca_sub in
        let post_ai = in_state sol fx.ca_post_tid in
        check "VSA-34" (Ws.is_top (AI.find_word 64 post_ai fx.ca_r2)));



    pin "VSA-36" "T4-9: RSP is preserved across the call"
      (fun () ->
        let fx = mk_caller_alias () in
        let callee =
          Term.enum sub_t fx.ca_ctx
          |> Seq.find ~f:(fun s -> String.equal (Sub.name s) "t4_callee")
          |> Base.Option.value_exn in
        let ssa =
          ssa_of_subs [ jump_compiled fx.ca_sub; jump_compiled callee ] (Sub.name fx.ca_sub) in
        let sol = run_ssa_anchored ssa in
        check "VSA-36"
          (Ws.equal (sp_after_block ssa sol fx.ca_post_tid) (Ws.singleton (w64 0x2000))));

    pin "VSA-37" "T4-10: RBP is preserved across the call"
      (fun () ->
        let fx = mk_caller_alias () in
        let sol = run_anchored fx.ca_sub in
        let post_ai = in_state sol fx.ca_post_tid in
        check "VSA-37"
          (Ws.equal (AI.find_word 64 post_ai fx.ca_rbp) (Ws.singleton (w64 0x100))));





    (* F1: the map lattice's fold visits the explicitly-stored bindings. *)




    (* D7: degenerate cast/extract sizes degrade to top. *)












    (* D8: a signed widening cast is top at the target width; the source
   width remains part of the input value's identity. *)














    (* D7-15: the crash shape RAX := high:0[RAX] after a call — the
       untagged cast is denoted and the fixpoint completes. *)
    pin "VSA-52"
      "D7-15 (BIR): RAX := high:0[RAX] after a call — fixpoint completes rc=0, RAX = top(64)"
      (fun () ->
        let rax, _ctx, sub, final_tid = mk_high0_cast_sub () in
        let sol = run_anchored sub in
        let final_ai = in_state sol final_tid in
        check "VSA-52" (Ws.is_top (AI.find_word 64 final_ai rax)));

    (* E2eH: equal's short-circuit changes no observable result. *)








    (* E2eC: the counter-shift BIR loop — the [0,N) window survives the
       shift. *)
    pin "VSA-57"
      "E2eC-13 (BIR loop): the partition — the iterate view's counter is bounded by the guard (⊆ [0,4]) and the exit view carries the exit-iteration values (min ≥ 5)"
      (fun () ->
        let i = i32 "i" in
        let x = v64 "x" in
        let y = v64 "y" in
        let iv = Bil.Var i in
        let xv = Bil.Var x in
        let lt5 = Bil.BinOp (Bil.LT, iv, Bil.Int (Cbat_word.to_word (w32 5))) in
        let nlt5 = Bil.UnOp (Bil.NOT, lt5) in
        let sub, tids =
          sub_of "e2ec_loop"
            [ [ Def.create i (Bil.Int (Cbat_word.to_word (w32 0)));
                Def.create x (Bil.Int (Cbat_word.to_word (w64 16))) ],
              [ (1, mk_goto) ];
              (* The body increments first: y = x << (i+1) ∈ {32..512}, in case 1. *)
              [ Def.create i (Bil.BinOp (Bil.PLUS, iv, Bil.Int (Cbat_word.to_word (w32 1))));
                Def.create y (Bil.BinOp (Bil.LSHIFT, xv, iv)) ],
              [ (2, mk_goto) ];
              [], [ (3, fun t -> mk_jmp_to t nlt5); (1, fun t -> mk_jmp_to t lt5) ];
              [], [] ]
        in
        let sol = run_anchored sub in
        let c_iter = AI.find_word 32 (in_state sol tids.(1)) i in
        let c_exit = AI.find_word 32 (in_state sol tids.(3)) i in
        check "VSA-57"
          ((not (Ws.is_top c_iter))
          && (Base.Option.filter (Ws.max_elem c_iter)
                ~f:(fun w -> Cbat_word.(<=) w (w32 4))
             |> Option.is_some)
          && (not (Ws.is_top c_exit))
          && Base.Option.filter (Ws.min_elem c_exit)
               ~f:(fun w -> Cbat_word.(>=) w (w32 5))
             |> Option.is_some));

    (* E2eD: channel-2 negative — the heap-indexed store never seeds. *)


    (* P3: the gate-free entry RSP anchor. *)
    pin "VSA-60"
      "P3-1: gate-free — the entry RSP anchor is denoted (entry input state carries RSP = the symbolic segment base at offset 0 — StackOff{0})"
      (fun () ->
        let rsp_var = sp in
        let sub = mk_p3_anchor_sub () in
        let sol = run_anchored sub in
        let st = in_state sol (entry_tid_of sub) in
        check "VSA-60" (Ws.equal (AI.find_word 64 st rsp_var) (Ws.stack_word_i64 0L)));

    (* L2b: the full 1-bit domain reads cardinality 2. *)


    pin "VSA-66"
      "round-pair: the two-def [(x >> k) << k] idiom — a temp saves x, the shift-back becomes the mask"
      (fun () ->
        let rax = v64 "at_rr_rax" in
        let d_shr =
          Def.create rax
            (Bil.BinOp (Bil.RSHIFT, Bil.Var rax, Bil.Int (Cbat_word.to_word (w64 2))))
        in
        let d_shl =
          Def.create rax
            (Bil.BinOp (Bil.LSHIFT, Bil.Var rax, Bil.Int (Cbat_word.to_word (w64 2))))
        in
        let sub = straight_sub "at_round" [ d_shr; d_shl ] in
        let sub' = Vsa.Test_seam.normalize_round sub in
        let rhs_of tid =
          Term.enum blk_t sub' |> Seq.concat_map ~f:(Term.enum def_t)
          |> Seq.find_map ~f:(fun d ->
                 if Tid.equal (Term.tid d) tid then Some (Def.rhs d) else None)
        in
        let mask = Word.of_int64 ~width:64 (-4L) in
        (* The shift def keeps the true shifted value (its flag readers
           stay exact); a temp holds the pre-shift operand; the
           shift-back is the mask over the temp. *)
        let defs =
          Term.enum blk_t sub' |> Seq.concat_map ~f:(Term.enum def_t) |> Seq.to_list
        in
        (* The mask's operand is a temp whose own def copies the
           pre-shift operand [rax]. *)
        let temp_of_shl =
          match rhs_of (Term.tid d_shl) with
          | Some (Bil.BinOp (Bil.AND, Bil.Var tv, Bil.Int _)) -> Some tv
          | _ -> None
        in
        let temp_copies_x =
          Base.Option.value_map temp_of_shl ~default:false ~f:(fun tv ->
              Base.List.exists defs ~f:(fun d ->
                  Var.equal (Def.lhs d) tv
                  &&
                  match Def.rhs d with
                  | Bil.Var v -> Var.equal v rax
                  | _ -> false))
        in
        check "VSA-66"
          (temp_copies_x
           &&
           match rhs_of (Term.tid d_shr), rhs_of (Term.tid d_shl) with
           | Some (Bil.BinOp (Bil.RSHIFT, _, _)),
             Some (Bil.BinOp (Bil.AND, _, Bil.Int m)) ->
             Word.equal m mask
           | _ -> false));

    (* A3: the main solve reads the threaded section images — a load from
       a section address denotes the image bytes, not top. *)
    pin "VSA-67"
      "the main solve is image-armed: a load from a threaded section address denotes the image bytes"
      (fun () ->
        let m = memv "a3_img_m" in
        let r = v64 "a3_img_r" in
        let load =
          Def.create r
            (Bil.Load
               ( Bil.Var m,
                 Bil.Int (Cbat_word.to_word (w64 0x4000)),
                 LittleEndian, `r64 ))
        in
        let sub = straight_sub "a3_image_solve" [ load ] in
        let images =
          [ { Vsa.img_lo = 0x4000L; img_hi = 0x4007L;
              img_bytes = Bytes.of_string "\x2d\x00\x00\x00\x00\x00\x00\x00";
              img_slots = Core.Int64.Set.empty } ]
        in
        let envs, solved, _ =
          produce ~synth:Hike.Synth.empty ~images (x86_target ())
            (Program.create ~subs:[ sub ] ()) sub
        in
        let blk = Term.first blk_t solved |> Base.Option.value_exn in
        let _, post = Core.Map.find_exn envs (Term.tid blk) in
        check "VSA-67"
          (Ws.equal (AI.find_word 64 post (Sm.version_at_end blk r)) (Ws.singleton (w64 0x2d))));


    pin "VSA-68"
      "a solve paused on a callee past the entry block resumes to the cold \
       solve's result"
      (fun () ->
        let rsi = int_param 1 and rcx = int_param 3 and rbx = callee_saved 0 in
        let k n = Bil.int (Word.of_int64 ~width:64 n) in
        let callee_tid = Tid.create () in
        let sub, tids =
          sub_of "caller"
            [ ([ Def.create rsi (k 5L) ], [ (1, mk_goto) ]);
              ([ Def.create rcx (k 7L) ],
               [ (2, fun t -> mk_call_jmp t callee_tid) ]);
              ([ Def.create rbx Bil.(var rsi + k 1L);
                 Def.create sp Bil.(var sp + k 8L) ],
               [ (0, mk_ret) ]) ] in
        let sub = Hike.Ssa.ssa_sub ~synth:Hike.Synth.empty ~target:(x86_target ()) sub in
        let writes_rcx =
          Vsa.Call_effects.Summary
            (Some (Cbat_var_id.intern_set (Var.Set.singleton rcx))) in
        let solve ~callee =
          Hv.start (x86_target ()) ~lookup:(fun _ -> None) ~images:[]
            ~callee ~block_addrs:(Core.Map.empty (module Addr))
            ~synth:Hike.Synth.empty
            ~foreign_slots:Core.Int64.Set.empty sub in
        let resume p ~callee =
          Hv.resume (x86_target ()) ~lookup:(fun _ -> None) ~images:[]
            ~callee ~foreign_slots:Core.Int64.Set.empty p in
        match solve ~callee:(fun _ -> Vsa.Call_effects.Blocked) with
        | Hv.Done _ -> check "VSA-68.paused" false
        | Hv.Paused p ->
          check "VSA-68.blocked" (Core.Set.equal p.p_blocked (Tid.Set.singleton callee_tid));
          check "VSA-68.seed"
            (AI.equal (Graphlib.Std.Solution.get p.p_seed tids.(2)) AI.bottom);
          match resume p ~callee:(fun _ -> writes_rcx), solve ~callee:(fun _ -> writes_rcx) with
          | Hv.Done (warm, warm_sub, _, _, _), Hv.Done (cold, _, _, _, _) ->
            check "VSA-68.equal"
              (Core.Map.equal (fun (a, b) (c, d) -> AI.equal a c && AI.equal b d) warm cold);
            check "VSA-68.flowed"
              (match Core.Map.find warm tids.(2) with
               | Some (_, post) ->
                 Ws.equal (AI.find_word 64 post
                     (Sm.version_at_end (Term.find_exn blk_t warm_sub tids.(2)) rbx))
                   (Ws.singleton (w64 6))
               | None -> false)
          | _ -> check "VSA-68.done" false);

    (* Slices: a guard on bits of a variable survives to the next read of
       the same bits; the variable's own word keeps today's hull. *)
    pin "VSA-69"
      "slice: a guard on low:8[x] bounds the later read of low:8[x], though x stays wide"
      (fun () ->
        let x = slice_x () in
        let fx = mk_slice_sub ~x () in
        let sol = run_anchored fx.sf_sub in
        let st = in_state sol fx.sf_read_exit in
        check "VSA-69.read" (slice_bounded (AI.find_word 32 st fx.sf_y) 0x25);
        check "VSA-69.owner" (not (slice_bounded (AI.find_word 32 st x) 0xff)));

    pin "VSA-70" "slice: the extract form (bits 15..8) is bounded the same way"
      (fun () ->
        let x = slice_x () in
        let narrow e = Bil.Extract (15, 8, e) in
        let fx = mk_slice_sub ~x ~narrow () in
        check "VSA-70" (slice_bounded (slice_y fx) 0x25));

    pin "VSA-72" "slice: a redefinition of the owner discards the fact"
      (fun () ->
        let x = slice_x () in
        let fx = mk_slice_sub ~x ~between:[ Def.create x (Bil.Var x) ] () in
        check "VSA-72" (not (slice_bounded (slice_y fx) 0x25)));

    pin "VSA-73" "slice: a call that clobbers the owner discards the fact"
      (fun () ->
        let x = int_param 0 in
        let fx = mk_slice_sub ~x ~call:true () in
        check "VSA-73" (not (slice_bounded (slice_y fx) 0x25)));

    pin "VSA-74" "slice: a second guard on the whole register keeps the byte fact"
      (fun () ->
        let x = slice_x () in
        let y = Var.create ~is_virtual:false ~fresh:false "sl_y" (Type.Imm 32) in
        let g1 = Bil.BinOp (Bil.LT, byte_const 0x25, low8 (Bil.Var x)) in
        let g2 = Bil.BinOp (Bil.LT, Bil.Int (Cbat_word.to_word (w32 0x1000)), Bil.Var x) in
        let read = Def.create y (Bil.Cast (Bil.UNSIGNED, 32, low8 (Bil.Var x))) in
        let sub, tids =
          sub_of "slice2"
            [ [], [ (4, fun t -> mk_jmp_to t g1); (1, mk_goto) ];
              [], [ (4, fun t -> mk_jmp_to t g2); (2, mk_goto) ];
              [ read ], [ (3, mk_goto) ];
              [], [ (0, mk_ret) ];
              [], [ (0, mk_ret) ] ]
        in
        let st = in_state (run_anchored sub) tids.(3) in
        check "VSA-74" (slice_bounded (AI.find_word 32 st y) 0x25));

    pin "VSA-75"
      "slice: after a merge the fact is kept only when both paths carry it, as the join of both"
      (fun () ->
        let x = slice_x () in
        let y = Var.create ~is_virtual:false ~fresh:false "sl_y" (Type.Imm 32) in
        let g = v1 "sl_g" in
        let guard n = Bil.BinOp (Bil.LT, byte_const n, low8 (Bil.Var x)) in
        let read = Def.create y (Bil.Cast (Bil.UNSIGNED, 32, low8 (Bil.Var x))) in
        let y_after ~second_guarded =
          let path_b =
            if second_guarded then [ (5, fun t -> mk_jmp_to t (guard 0x30)); (3, mk_goto) ]
            else [ (3, mk_goto) ] in
          let sub, tids =
            sub_of "slice_merge"
              [ [], [ (1, fun t -> mk_jmp_to t (Bil.Var g)); (2, mk_goto) ];
                [], [ (5, fun t -> mk_jmp_to t (guard 0x25)); (3, mk_goto) ];
                [], path_b;
                [ read ], [ (4, mk_goto) ];
                [], [ (0, mk_ret) ];
                [], [ (0, mk_ret) ] ]
          in
          AI.find_word 32 (in_state (run_anchored sub) tids.(4)) y in
        check "VSA-75.both" (slice_bounded (y_after ~second_guarded:true) 0x30);
        check "VSA-75.join" (not (slice_bounded (y_after ~second_guarded:true) 0x25));
        check "VSA-75.one" (not (slice_bounded (y_after ~second_guarded:false) 0x30)));

    pin "VSA-76" "slice: a loop guarded by a byte converges with the byte bounded in the body"
      (fun () ->
        let x = slice_x () in
        let y = Var.create ~is_virtual:false ~fresh:false "sl_y" (Type.Imm 32) in
        let guard = Bil.BinOp (Bil.LT, byte_const 0x25, low8 (Bil.Var x)) in
        let read = Def.create y (Bil.Cast (Bil.UNSIGNED, 32, low8 (Bil.Var x))) in
        let step =
          Def.create x (Bil.BinOp (Bil.PLUS, Bil.Var x, Bil.Int (Cbat_word.to_word (w32 1)))) in
        let sub, tids =
          sub_of "slice_loop"
            [ [], [ (1, mk_goto) ];
              [], [ (4, fun t -> mk_jmp_to t guard); (2, mk_goto) ];
              [ read ], [ (3, mk_goto) ];
              [ step ], [ (1, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let st = in_state (run_anchored sub) tids.(3) in
        check "VSA-76" (slice_bounded (AI.find_word 32 st y) 0x25));

    pin "VSA-77" "waking an unreachable call preserves bottom at its continuation"
      (fun () ->
        let x = Var.with_index (v64 "unreached_load") 1 in
        let m = memv "unreached_mem" in
        let callee = Tid.create () in
        let sub, tids = sub_of "dead_call"
            [ [], [ (1, fun t -> mk_jmp_to t (Bil.Int (Word.zero 1)));
                    (3, mk_goto) ];
              [], [ (2, fun t -> mk_call_jmp t callee) ];
              [ Def.create x (Bil.Load (Bil.Var m, Bil.Var sp, LittleEndian, `r64)) ],
                [ (3, fun t -> mk_jmp_to t Bil.(var x <> int (Word.zero 64)));
                  (3, mk_goto) ];
              [], [ (0, mk_ret) ] ] in
        let sol = Vsa.static_graph_vsa ~abi:sysv ~synth:(ref Hike.Synth.empty)
            ~def_reads:(fun d -> Sm.reads (`Def d))
            ~def_writes:(fun d -> Sm.writes (`Def d))
            ~phi_reads:(fun p -> Sm.reads (`Phi p))
            ~phi_writes:(fun p -> Sm.writes (`Phi p))
            ~jmp_reads:(fun j -> Core.Set.union (Sm.reads (`Jmp j)) (Sm.writes (`Jmp j)))
            ~wake:(Tid.Set.singleton tids.(1)) sub (Vsa.init_sol ~abi:sysv sub) in
        check "VSA-77 unreachable continuation"
          (AI.equal (in_state sol tids.(2)) AI.bottom));

    pin "VSA-78"
      "SSA: redefining a cell's owner keeps the state's physical identity"
      (fun () ->
        let tid = Tid.create () in
        let x = Var.create ~is_virtual:false ~fresh:false "sl_cell" (Type.Imm 32) in
        let store = AI.create_scalars ~variables:[ x ]
            ~blocks:[ (tid, Var.Set.singleton x) ] ~seed:AI.top in
        let st = AI.enter_block store tid AI.top in
        let data = Ws.singleton (w32 7) in
        let st1 = AI.add_word st ~key:x ~data in
        let st2 = AI.add_word st1 ~key:x ~data in
        check "VSA-78" (Stdlib.(st1 == st2)));

    pin "VSA-79"
      "SSA: a definition drops the owner's slices, and they stay gone after \
       a projection and a phi copy"
      (fun () ->
        let tid = Tid.create () in
        let x = Var.create ~is_virtual:false ~fresh:false "sl_def_x" (Type.Imm 32) in
        let y = Var.create ~is_virtual:false ~fresh:false "sl_def_y" (Type.Imm 32) in
        let store = AI.create_scalars ~variables:[ x; y ]
            ~blocks:[ (tid, Var.Set.of_list [ x; y ]) ] ~seed:AI.top in
        let st = AI.enter_block store tid AI.top in
        let st = AI.add_slice st x ~hi:7 ~lo:0
            ~data:(Ws.singleton (Cbat_word.of_int ~width:8 0x25)) in
        let def = Ws.singleton (w32 0x1234abcd) in
        let after = AI.add_word st ~key:x ~data:def in
        check "VSA-79.cell" (Ws.equal (AI.find_word 32 after x) def);
        let keep = Cbat_var_id.intern_set (Var.Set.of_list [ x; y ]) in
        let projected = AI.project ~keep ~block:tid after in
        check "VSA-79.owner-slices"
          (Ws.is_top (AI.find_slice projected x ~hi:7 ~lo:0));
        let copied = AI.copy_slices ~from:projected ~source:x ~target:y st in
        check "VSA-79.copy" (Ws.is_top (AI.find_slice copied y ~hi:7 ~lo:0)));

    pin "VSA-80"
      "SSA: a projection keeps only the target's live bindings, leaves its \
       memory, and joins the target block"
      (fun () ->
        let src = Tid.create () and dst = Tid.create () in
        let source_only = i32 "sl_proj_source" in
        let stale = i32 "sl_proj_stale" in
        let phi = i32 "sl_proj_phi" in
        let live = i32 "sl_proj_live" in
        let free = i32 "sl_proj_free" in
        let target_local = i32 "sl_proj_target" in
        let ws n = Ws.singleton (w32 n) in
        let store = AI.create_scalars
            ~variables:[ source_only; stale; phi; live; free; target_local ]
            ~blocks:[ (src, Var.Set.of_list [ source_only; free ]);
                      (dst, Var.Set.singleton target_local) ]
            ~seed:AI.top in
        let st = AI.enter_block store src AI.top in
        let st = AI.add_word st ~key:source_only ~data:(ws 0x11) in
        let st = AI.add_word st ~key:free ~data:(ws 0x33) in
        let st = AI.add_word st ~key:stale ~data:(ws 0x22) in
        let st = AI.add_word st ~key:phi ~data:(ws 0x44) in
        let st = AI.add_word st ~key:live ~data:(ws 0x55) in
        let mem = memv "sl_proj_mem" in
        let mem_idx = { Mem.addr_width = 64; Mem.addressable_width = 8 } in
        let mval =
          Mem.add (Mem.top mem_idx)
            ~key:
              (match Mem.Key.of_wordset (Ws.singleton (w64 0x1000)) with
               | [ k ] -> k
               | _ -> failwith "key")
            ~data:(Mem.Val.create (ws 7) LittleEndian) in
        let st = AI.add_memory st ~key:mem ~data:mval in
        let keep = Cbat_var_id.intern_set (Var.Set.of_list [ phi; live; free ]) in
        let projected = AI.project ~keep ~block:dst st in
        check "VSA-80.stale" (Ws.is_top (AI.find_word 32 projected stale));
        check "VSA-80.phi" (Ws.equal (AI.find_word 32 projected phi) (ws 0x44));
        check "VSA-80.live" (Ws.equal (AI.find_word 32 projected live) (ws 0x55));
        check "VSA-80.free" (Ws.equal (AI.find_word 32 projected free) (ws 0x33));
        (* A target-local write hits its cell without touching the env, so
           the physical identity proves the scalar view joined [dst]. *)
        let after = AI.add_word projected ~key:target_local ~data:(ws 0x66) in
        check "VSA-80.block" (Stdlib.(after == projected));
        check "VSA-80.memory"
          (Mem.equal (AI.find_memory mem_idx projected mem) mval));

    pin "VSA-81"
      "SSA: a two-predecessor join keeps only target phi values; a \
       source-only value common to both edges does not reappear"
      (fun () ->
        let x = callee_saved 0 and y = callee_saved 1 in
        let c = int_param 0 in
        let k n = Bil.Int (Cbat_word.to_word (w64 n)) in
        let sub, tids =
          sub_of "phi_only_join"
            [ [ Def.create x (k 7) ],
              [ (1, fun t ->
                     mk_jmp_to t
                       (Bil.BinOp (Bil.LT, Bil.Var c, k 5)));
                (2, mk_goto) ];
              [ Def.create y (k 0x11);
                Def.create (v64 "phi_only_read1") (Bil.Var x) ],
              [ (3, mk_goto) ];
              [ Def.create y (k 0x22);
                Def.create (v64 "phi_only_read2") (Bil.Var x) ],
              [ (3, mk_goto) ];
              [ Def.create (callee_saved 2)
                  (Bil.BinOp (Bil.PLUS, Bil.Var y, k 1)) ],
              [ (4, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let ssa = ssa_of_subs [ jump_compiled sub ] "phi_only_join" in
        let sol = run_ssa_anchored ssa in
        let join = Term.find_exn blk_t ssa tids.(3) in
        let join_phi =
          Term.enum phi_t join
          |> Seq.find ~f:(fun p -> Var.same (Var.base (Phi.lhs p)) y)
          |> Base.Option.value_exn in
        let source_phis =
          [ tids.(1); tids.(2) ]
          |> Base.List.concat_map ~f:(fun tid ->
              Term.find_exn blk_t ssa tid
              |> Term.enum phi_t |> Seq.map ~f:Phi.lhs |> Seq.to_list)
          |> Base.List.filter ~f:(fun v -> Var.same (Var.base v) x)
        in
        let st = in_state sol tids.(3) in
        check "VSA-81 source-only phis reach both edges"
          (Base.List.length source_phis = 2);
        check "VSA-81 source-only value dropped"
          (Base.List.for_all source_phis ~f:(fun v ->
               Ws.is_top (AI.find_word 64 st v)));
        check "VSA-81 target phi kept"
          (Ws.elem (w64 0x11) (AI.find_word 64 st (Phi.lhs join_phi))
           && Ws.elem (w64 0x22) (AI.find_word 64 st (Phi.lhs join_phi)));
        let phi_cell = AI.project ~keep:Core.Int.Set.empty
            ~block:tids.(3) st in
        check "VSA-81 target phi cell"
          (Ws.elem (w64 0x11) (AI.find_word 64 phi_cell (Phi.lhs join_phi))
           && Ws.elem (w64 0x22)
                (AI.find_word 64 phi_cell (Phi.lhs join_phi)));
        let keep = Cbat_var_id.intern_set (Var.Set.singleton (Phi.lhs join_phi)) in
        check "VSA-81 top stays top"
          (AI.equal AI.top (AI.project ~keep ~block:tids.(3) AI.top));
        check "VSA-81 bottom stays bottom"
          (AI.equal AI.bottom (AI.project ~keep ~block:tids.(3) AI.bottom)));

    (* SSA construction supplies every non-entry word input through a phi. *)
    pin "VSA-82"
      "SSA: after construction a non-entry block has no free word input \
       outside its phi lhs set"
      (fun () ->
        let x = callee_saved 0 and y = callee_saved 1 in
        let c = int_param 0 in
        let k n = Bil.Int (Cbat_word.to_word (w64 n)) in
        let sub, tids =
          sub_of "ssa_free_inputs"
            [ [ Def.create x (k 7) ],
              [ (1, fun t ->
                     mk_jmp_to t
                       (Bil.BinOp (Bil.LT, Bil.Var c, k 5)));
                (2, mk_goto) ];
              [ Def.create y (k 0x11) ], [ (3, mk_goto) ];
              [ Def.create y (k 0x22) ], [ (3, mk_goto) ];
              [ Def.create (callee_saved 2)
                  (Bil.BinOp (Bil.PLUS, Bil.Var y, k 1)) ],
              [ (4, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let ssa = ssa_of_subs [ jump_compiled sub ] "ssa_free_inputs" in
        let def_reads d = Hike.Stack_model.reads (`Def d) in
        let def_writes d = Hike.Stack_model.writes (`Def d) in
        let jmp_reads j =
          Core.Set.union (Hike.Stack_model.reads (`Jmp j))
            (Hike.Stack_model.writes (`Jmp j)) in
        let free_word_inputs b =
          (* Reads with no prior local definition or incoming phi. *)
          let phis =
            Term.enum phi_t b |> Seq.map ~f:Phi.lhs |> Seq.to_list
            |> Var.Set.of_list in
          let written, needed =
            Term.enum def_t b
            |> Seq.fold ~init:(phis, Var.Set.empty)
                 ~f:(fun (written, needed) d ->
                     (Core.Set.union written (def_writes d),
                      Core.Set.union needed
                        (Core.Set.diff (def_reads d) written)))
          in
          let needed =
            Term.enum jmp_t b
            |> Seq.fold ~init:needed ~f:(fun needed j ->
                Core.Set.union needed
                  (Core.Set.diff (jmp_reads j)
                     (Core.Set.union written
                        (Hike.Stack_model.writes (`Jmp j)))))
          in
          Core.Set.diff needed phis
          |> Core.Set.filter ~f:(fun v ->
                 match Var.typ v with Type.Imm _ -> true | _ -> false)
        in
        let entry = Vsa.entry_block_of ssa in
        let is_entry b =
          Base.Option.value_map entry ~default:false
            ~f:(fun e -> Tid.equal (Term.tid e) (Term.tid b)) in
        let offenders =
          Term.enum blk_t ssa |> Seq.to_list
          |> Base.List.concat_map ~f:(fun b ->
                 if is_entry b then []
                 else Core.Set.to_list (free_word_inputs b))
        in
        check "VSA-82 no non-entry free word input outside the phi lhs set"
          (Base.List.is_empty offenders);
        let join = Term.find_exn blk_t ssa tids.(3) in
        let without_phis = Term.filter phi_t join ~f:(fun _ -> false) in
        check "VSA-82 missing phi is detected"
          (not (Core.Set.is_empty (free_word_inputs without_phis))));

    pin "VSA-83"
      "SSA: the entry's index-0 ABI input is seeded, and a free word input \
       on the entry is exempt from the join check"
      (fun () ->
        let p = int_param 0 and out = callee_saved 0 in
        let sub, _ =
          sub_of "entry_boundary"
            [ [ Def.create out (Bil.Var p) ], [ (0, mk_ret) ] ]
        in
        let ssa = ssa_of_subs [ jump_compiled sub ] "entry_boundary" in
        let entry =
          Vsa.entry_block_of ssa |> Base.Option.value_exn in
        let probe = Var.with_index (v64 "entry_probe") 1 in
        let ssa =
          Term.map blk_t ssa ~f:(fun b ->
              if Tid.equal (Term.tid b) (Term.tid entry) then
                Term.append def_t b (Def.create probe (Bil.Var p))
              else b)
        in
        let seeded = Ws.singleton (w64 0x77) in
        let entry_state =
          AI.add_word (anchored_entry ()) ~key:p ~data:seeded in
        let sol =
          static_graph_vsa ~synth:Hike.Synth.empty ~abi:Hike_abi.x86_64_sysv
            ssa
            (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv ~entry:entry_state ssa)
        in
        let st = in_state sol (Term.tid entry) in
        check "VSA-83.entry-seed" (Ws.equal (AI.find_word 64 st p) seeded);
        check "VSA-83.entry-def" (Ws.equal (AI.find_word 64 st probe) seeded));

    pin "VSA-84"
      "SSA: both outgoing edges agree with ordered independent source replay"
      (fun () ->
        let x = callee_saved 0 and y = callee_saved 1 in
        let c = int_param 0 and mem = memv "post_branch_mem" in
        let k n = Bil.Int (Cbat_word.to_word (w64 n)) in
        let load = Bil.Load (Bil.Var mem, k 0x1000, LittleEndian, `r64) in
        let store data = Def.create mem
            (Bil.Store (Bil.Var mem, k 0x1000, data, LittleEndian, `r64)) in
        let sub, tids = sub_of "post_branch"
            [ [ store (k 0x11);
                Def.create x (Bil.BinOp (Bil.PLUS, load, k 0x11));
                store (Bil.Var x) ],
              [ (1, fun t -> mk_jmp_to t
                     (Bil.BinOp (Bil.LT, Bil.Var c, k 5)));
                (2, mk_goto) ];
              [ Def.create y (Bil.Var x) ], [ (3, mk_goto) ];
              [ Def.create y (Bil.Var x) ], [ (3, mk_goto) ];
              [], [ (0, mk_ret) ] ] in
        let ssa = ssa_of_subs [ jump_compiled sub ] "post_branch" in
        let sol = run_ssa_anchored ssa in
        let source = Term.find_exn blk_t ssa tids.(0) in
        let pre = AI.copy_scalars (in_state sol tids.(0)) in
        let replay = Vsa.Test_seam.denote_defs ~synth:Hike.Synth.empty source pre in
        let read env = Vsa.Test_seam.denote_imm_exp ~synth:Hike.Synth.empty load env
          |> Result.get_ok in
        let expected = read replay in
        check "VSA-84 ordered stores" (Ws.equal expected (Ws.singleton (w64 0x22)));
        Base.List.iter [ tids.(1); tids.(2) ] ~f:(fun tid ->
            let target = Term.find_exn blk_t ssa tid in
            let phi = Term.enum phi_t target
              |> Seq.find ~f:(fun p -> Var.same (Phi.lhs p) x)
              |> Base.Option.value_exn in
            let state = in_state sol tid in
            check "VSA-84 edge memory" (Ws.equal (read state) expected);
            check "VSA-84 edge scalar"
              (Ws.equal (AI.find_word 64 state (Phi.lhs phi)) expected)));

    pin "VSA-85"
      "SSA: a changed IN state refreshes the cached loop edge and exit value"
      (fun () ->
        let x = callee_saved 0 and y = callee_saved 1 in
        let k n = Bil.Int (Cbat_word.to_word (w64 n)) in
        let sub, tids = sub_of "post_loop"
            [ [ Def.create x (k 0) ], [ (1, mk_goto) ];
              [], [ (2, fun t -> mk_jmp_to t
                       (Bil.BinOp (Bil.LT, Bil.Var x, k 5)));
                    (3, mk_goto) ];
              [ Def.create x (Bil.BinOp (Bil.PLUS, Bil.Var x, k 1)) ],
              [ (1, mk_goto) ];
              [ Def.create y (Bil.Var x) ], [ (0, mk_ret) ] ] in
        let ssa = ssa_of_subs [ jump_compiled sub ] "post_loop" in
        let sol = run_ssa_anchored ssa in
        let exit = Term.find_exn blk_t ssa tids.(3) in
        let phi = Term.enum phi_t exit
          |> Seq.find ~f:(fun p -> Var.same (Phi.lhs p) x)
          |> Base.Option.value_exn in
        check "VSA-85 exit value"
          (Ws.equal (AI.find_word 64 (in_state sol tids.(3)) (Phi.lhs phi))
             (Ws.singleton (w64 5))));

    pin "VSA-86"
      "SSA: revisited successors reuse separate taken and fallthrough refinements"
      (fun () ->
        let p = int_param 0 and x = callee_saved 0 in
        let y = callee_saved 1 and out = callee_saved 2 in
        let k n = Bil.Int (Cbat_word.to_word (w64 n)) in
        let sub, tids = sub_of "post_refinement"
            [ [ Def.create x (Bil.BinOp (Bil.PLUS, Bil.Var p, k 1));
                Def.create y (Bil.BinOp (Bil.PLUS, Bil.Var x, k 1)) ],
              [ (1, fun t -> mk_jmp_to t
                     (Bil.BinOp (Bil.LT, Bil.Var x, k 5)));
                (2, mk_goto) ];
              [ Def.create out (Bil.Var y) ],
              [ (2, fun t -> mk_jmp_to t (Bil.Int (Word.zero 1))); (1, mk_goto) ];
              [ Def.create out (Bil.Var y) ],
              [ (1, fun t -> mk_jmp_to t (Bil.Int (Word.zero 1))); (2, mk_goto) ];
              [], [ (0, mk_ret) ] ] in
        let ssa = ssa_of_subs [ jump_compiled sub ] "post_refinement" in
        let entry = AI.add_word (anchored_entry ()) ~key:p
            ~data:(Ws.of_clp (Clp.interval ~width:64 (w64 0) (w64 9))) in
        let sol = static_graph_vsa ~synth:Hike.Synth.empty ~abi:sysv ssa
            (Vsa.init_sol ~abi:sysv ~entry ssa) in
        let edge tid =
          let b = Term.find_exn blk_t ssa tid in
          let p = Term.enum phi_t b
            |> Seq.find ~f:(fun p -> Var.same (Phi.lhs p) y)
            |> Base.Option.value_exn in
          AI.find_word 64 (in_state sol tid) (Phi.lhs p) in
        let low = edge tids.(1) and high = edge tids.(2) in
        check "VSA-86 taken" (Ws.elem (w64 2) low && bounded_above low (w64 5));
        check "VSA-86 fallthrough"
          (Ws.elem (w64 11) high && not (Ws.elem (w64 2) high)));

    pin "VSA-87"
      "SSA: read-only inputs stay in the environment without duplicate cells"
      (fun () ->
        let input = int_param 0 and output = callee_saved 0 in
        let sub, _ = sub_of "readonly_cell"
            [ [ Def.create output
                  (Bil.BinOp (Bil.PLUS, Bil.Var input,
                     Bil.Int (Cbat_word.to_word (w64 1)))) ],
              [ (0, mk_ret) ] ] in
        let ssa = ssa_of_subs [ jump_compiled sub ] "readonly_cell" in
        let entry = Vsa.entry_block_of ssa |> Base.Option.value_exn in
        let defined = Term.enum def_t entry
          |> Seq.find ~f:(fun d -> Var.same (Def.lhs d) output)
          |> Base.Option.value_exn |> Def.lhs in
        let seed = AI.add_word (anchored_entry ()) ~key:input
            ~data:(Ws.singleton (w64 42)) in
        let sol = static_graph_vsa ~synth:Hike.Synth.empty ~abi:sysv ssa
            (Vsa.init_sol ~abi:sysv ~entry:seed ssa) in
        let state = in_state sol (Term.tid entry) in
        check "VSA-87 input remains available"
          (Ws.equal (AI.find_word 64 state input) (Ws.singleton (w64 42)));
        let projected = AI.project ~keep:Core.Int.Set.empty
            ~block:(Term.tid entry) state in
        check "VSA-87 no read-only fallback cell"
          (Ws.is_top (AI.find_word 64 projected input));
        check "VSA-87 defined output retains its cell"
          (Ws.equal (AI.find_word 64 projected defined) (Ws.singleton (w64 43)));
        check "VSA-87 absent variable reads top"
          (Ws.is_top (AI.find_word 64 projected (v64 "readonly_missing"))));
  ]

let () = run "vsa" tests
