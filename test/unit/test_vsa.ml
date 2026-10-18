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
        let sol = run_anchored fx.ca_sub in
        let post_ai = in_state sol fx.ca_post_tid in
        check "VSA-36"
          (Ws.equal (AI.find_word 64 post_ai fx.ca_rsp) (Ws.singleton (w64 0x2000))));

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
        let envs, _, _ =
          produce ~synth:Hike.Synth.empty ~images (x86_target ())
            (Program.create ~subs:[ sub ] ()) sub
        in
        let blk = Term.first blk_t sub |> Base.Option.value_exn in
        let _, post = Core.Map.find_exn envs (Term.tid blk) in
        check "VSA-67"
          (Ws.equal (AI.find_word 64 post r) (Ws.singleton (w64 0x2d))));


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
          | Hv.Done (warm, _, _, _), Hv.Done (cold, _, _, _) ->
            check "VSA-68.equal"
              (Core.Map.equal (fun (a, b) (c, d) -> AI.equal a c && AI.equal b d) warm cold);
            check "VSA-68.flowed"
              (match Core.Map.find warm tids.(2) with
               | Some (_, post) ->
                 Ws.equal (AI.find_word 64 post rbx) (Ws.singleton (w64 6))
               | None -> false)
          | _ -> check "VSA-68.done" false);
  ]

let () = run "vsa" tests
