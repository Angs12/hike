(* VSA pass pins.  One Alcotest group per pin; each pin builds its own
   fixture, so no state crosses pins.  The Call_effects transfer pins
   (C1-1..C1-5) live with their module, not here. *)

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
    (Vsa.Test_seam.constrain_edge ~landmarks:(Cbat_landmarks.create ()) ~env:AI.top
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
    pin "VSA-10" "D6-1: CLP equal on width-mismatched CLPs -> false (no raise)"
      (fun () ->
        let p32 = Clp.of_list ~width:32 [ w32 1; w32 2 ] in
        let p64 = Clp.of_list ~width:64 [ w64 1; w64 2 ] in
        check "VSA-10" ((not (Clp.equal p32 p64)) && not (Clp.equal p64 p32)));

    pin "VSA-11" "D6-2: CLP subset on width-mismatched CLPs -> false (no raise)"
      (fun () ->
        let p32 = Clp.of_list ~width:32 [ w32 1; w32 2 ] in
        let p64 = Clp.of_list ~width:64 [ w64 1; w64 2 ] in
        check "VSA-11" ((not (Clp.subset p32 p64)) && not (Clp.subset p64 p32)));

    pin "VSA-12" "D6-3: CLP intersection on width-mismatched CLPs -> wider operand"
      (fun () ->
        let p32 = Clp.of_list ~width:32 [ w32 1; w32 2 ] in
        let p64 = Clp.of_list ~width:64 [ w64 1; w64 2 ] in
        let r = Clp.intersection p32 p64 in
        check "VSA-12" (Clp.bitwidth r = 64 && Clp.equal r p64));

    pin "VSA-13" "D6-4: CLP add on width-mismatched CLPs -> coerced result (no raise)"
      (fun () ->
        let p32 = Clp.of_list ~width:32 [ w32 1; w32 2 ] in
        let p64 = Clp.of_list ~width:64 [ w64 1; w64 2 ] in
        let r = Clp.add p32 p64 in
        check "VSA-13"
          (Clp.bitwidth r = 64 && Clp.elem (w64 2) r && Clp.elem (w64 3) r && Clp.elem (w64 4) r));

    pin "VSA-14" "D6-5: CLP mul on width-mismatched CLPs -> coerced result (no raise)"
      (fun () ->
        let p32 = Clp.of_list ~width:32 [ w32 1; w32 2 ] in
        let p64 = Clp.of_list ~width:64 [ w64 1; w64 2 ] in
        let r = Clp.mul p32 p64 in
        check "VSA-14" (Clp.bitwidth r = 64 && Clp.elem (w64 1) r && Clp.elem (w64 4) r));

    pin "VSA-15" "D6-6: CLP logand on width-mismatched CLPs -> no raise, width 64"
      (fun () ->
        let p32 = Clp.of_list ~width:32 [ w32 1; w32 2 ] in
        let p64 = Clp.of_list ~width:64 [ w64 1; w64 2 ] in
        let r = Clp.logand p32 p64 in
        check "VSA-15" (Clp.bitwidth r = 64 && not (Clp.is_bottom r)));

    pin "VSA-16" "D6-7: CLP logxor on width-mismatched CLPs -> no raise, width 64"
      (fun () ->
        let p32 = Clp.of_list ~width:32 [ w32 1; w32 2 ] in
        let p64 = Clp.of_list ~width:64 [ w64 1; w64 2 ] in
        let r = Clp.logxor p32 p64 in
        check "VSA-16" (Clp.bitwidth r = 64 && not (Clp.is_bottom r)));

    pin "VSA-17" "D6-8: CLP div on width-mismatched CLPs -> no raise, width 64"
      (fun () ->
        let p32 = Clp.of_list ~width:32 [ w32 1; w32 2 ] in
        let p64 = Clp.of_list ~width:64 [ w64 1; w64 2 ] in
        let r = Clp.div p32 p64 in
        check "VSA-17" (Clp.bitwidth r = 64 && not (Clp.is_bottom r)));

    pin "VSA-18" "D6-9: CLP sdiv on width-mismatched CLPs -> no raise, width 64"
      (fun () ->
        let p32 = Clp.of_list ~width:32 [ w32 1; w32 2 ] in
        let p64 = Clp.of_list ~width:64 [ w64 1; w64 2 ] in
        let r = Clp.sdiv p32 p64 in
        check "VSA-18" (Clp.bitwidth r = 64 && not (Clp.is_bottom r)));

    pin "VSA-19" "D6-10: CLP union/join on width-mismatched CLPs -> no raise, width 64"
      (fun () ->
        let p32 = Clp.of_list ~width:32 [ w32 1; w32 2 ] in
        let p64 = Clp.of_list ~width:64 [ w64 1; w64 2 ] in
        let r = Clp.join p32 p64 in
        check "VSA-19" (Clp.bitwidth r = 64 && Clp.elem (w64 1) r && Clp.elem (w64 2) r));

    pin "VSA-20" "D6-11: CLP widen_join on width-mismatched CLPs -> no raise"
      (fun () ->
        let p32 = Clp.of_list ~width:32 [ w32 1; w32 2 ] in
        let p64 = Clp.of_list ~width:64 [ w64 1; w64 2 ] in
        let r = Clp.widen_join p32 p64 in
        check "VSA-20" (Clp.bitwidth r = 64 && Clp.elem (w64 1) r));

    pin "VSA-21" "D6-12: CLP meet (alias) on width mismatch -> wider operand"
      (fun () ->
        let p32 = Clp.of_list ~width:32 [ w32 1; w32 2 ] in
        let p64 = Clp.of_list ~width:64 [ w64 1; w64 2 ] in
        let r = Clp.meet p32 p64 in
        check "VSA-21" (Clp.bitwidth r = 64 && Clp.equal r p64));

    pin "VSA-22" "D6-13: same-width CLP ops unaffected (regression)"
      (fun () ->
        let p32 = Clp.of_list ~width:32 [ w32 1; w32 2 ] in
        let q = Clp.of_list ~width:32 [ w32 10; w32 12 ] in
        let r = Clp.add p32 q in
        check "VSA-22" (Clp.bitwidth r = 32 && Clp.elem (w32 11) r && Clp.elem (w32 13) r));

    (* D6-14: the exit state is block INPUT (j absent) — denote the def to
       read the postcondition; the mixed-width rshift computes. *)
    pin "VSA-23" "D6-14 (BIR loop): mixed-width rshift COMPUTES (lane A), no crash, no guard fire"
      (fun () ->
        let j = i32 "j" in
        let _, _, sub, exit_tid =
          mk_counter_loop ~exit_defs:(fun i ->
              [ Def.create j
                  (Bil.BinOp (Bil.RSHIFT, Bil.Var i, Bil.Int (Cbat_word.to_word (w64 1)))) ])
        in
        let comp = "rshift: mixed-width shift operands (32 and 64 bits)" in
        let fired_r = fired comp (fun () -> ignore (run_anchored sub)) in
        let sol = run_anchored sub in
        let exit_ai = in_state sol exit_tid in
        let i = i32 "i" in
        let j_after =
          Vsa.Test_seam.denote_def
            (Def.create j
               (Bil.BinOp (Bil.RSHIFT, Bil.Var i, Bil.Int (Cbat_word.to_word (w64 1)))))
            exit_ai
        in
        check "VSA-23"
          ((not fired_r) && not (Ws.is_top (AI.find_word 32 j_after j))));

    (* D6b: FinSet lift2 default width — mismatched sets widen to 64. *)
    pin "VSA-24" "D6b-1: FinSet union on width-mismatched sets -> no assert, width 64"
      (fun () ->
        let f32 = Fs.of_list ~width:32 [ w32 1; w32 2 ] in
        let f64 = Fs.of_list ~width:64 [ w64 1; w64 2 ] in
        check "VSA-24" (Fs.bitwidth (Fs.union f32 f64) = 64));

    pin "VSA-25" "D6b-2: FinSet intersection on width-mismatched sets -> no assert, width 64"
      (fun () ->
        let f32 = Fs.of_list ~width:32 [ w32 1; w32 2 ] in
        let f64 = Fs.of_list ~width:64 [ w64 1; w64 2 ] in
        check "VSA-25" (Fs.bitwidth (Fs.intersection f32 f64) = 64));

    pin "VSA-26" "D6b-3: FinSet add on width-mismatched sets -> no assert, width 64"
      (fun () ->
        let f32 = Fs.of_list ~width:32 [ w32 1; w32 2 ] in
        let f64 = Fs.of_list ~width:64 [ w64 1; w64 2 ] in
        check "VSA-26" (Fs.bitwidth (Fs.add f32 f64) = 64));

    pin "VSA-27" "D6b-4: same-width FinSet union/intersection still exact (regression)"
      (fun () ->
        let a = Fs.of_list ~width:32 [ w32 1; w32 2 ] in
        let b = Fs.of_list ~width:32 [ w32 2; w32 3 ] in
        check "VSA-27"
          (Fs.equal (Fs.union a b) (Fs.of_list ~width:32 [ w32 1; w32 2; w32 3 ])
          && Fs.equal (Fs.intersection a b) (Fs.of_list ~width:32 [ w32 2 ])));

    (* E6: not_implemented logs through Event.Log only; stderr stays clean. *)
    pin "VSA-28" "E6-1: no per-hit stderr line naming the component (Event.Log only)"
      (fun () ->
        let probe = "e6-log-probe" in
        let captured =
          capture_stderr (fun () ->
              List.iter
                (fun _ -> ignore (Cbat_vsa_utils.not_implemented ~top:42 probe))
                [ 1; 2; 3; 4; 5 ])
        in
        let probe_lines =
          String.split_on_char '\n' captured
          |> List.filter (fun l -> contains_substring l probe)
        in
        check "VSA-28" (List.length probe_lines = 0));

    pin "VSA-29" "E6-2: no not_implemented marker leaks to stderr at all"
      (fun () ->
        let probe = "e6-log-probe" in
        let captured =
          capture_stderr (fun () ->
              List.iter
                (fun _ -> ignore (Cbat_vsa_utils.not_implemented ~top:42 probe))
                [ 1; 2; 3; 4; 5 ])
        in
        check "VSA-29"
          ((not (contains_substring captured "not_implemented"))
          && not (contains_substring captured "(degrading to top)")));

    (* T3: gate-free flag-guard refinement. *)
    pin "VSA-30" "T3-1: gate-free — the guard refines x to {5}"
      (fun () ->
        let x = v64 "t3_x" in
        let c =
          assume 64 x
            (Bil.BinOp (Bil.EQ, Bil.Var x, Bil.Int (Cbat_word.to_word (w64 5))))
        in
        check "VSA-30" (Ws.min_elem c = Some (w64 5) && Ws.max_elem c = Some (w64 5)));

    pin "VSA-31" "T3-2: gate-free (spec §2.1) — the guard refines x to {5}"
      (fun () ->
        let x = v64 "t3_x" in
        let c =
          assume 64 x
            (Bil.BinOp (Bil.EQ, Bil.Var x, Bil.Int (Cbat_word.to_word (w64 5))))
        in
        check "VSA-31" (Ws.min_elem c = Some (w64 5) && Ws.max_elem c = Some (w64 5)));

    pin "VSA-32" "T3-7: mixed-def — f IS refined to {1} on the taken edge"
      (fun () ->
        let f, _ctx, sub, exit_tid, _, _, _ = mk_flag_sub ~mixed:true in
        let sol = run_anchored sub in
        let c = AI.find_word 1 (in_state sol exit_tid) f in
        check "VSA-32" (Ws.elem Cbat_word.b1 c && not (Ws.elem Cbat_word.b0 c)));

    pin "VSA-33" "T3-8: single-def flag — f2 IS refined to {1} on the taken edge"
      (fun () ->
        let f2, _ctx, sub2, exit_tid2, _, _, _ = mk_flag_sub ~mixed:false in
        let sol2 = run_anchored sub2 in
        let c2 = AI.find_word 1 (in_state sol2 exit_tid2) f2 in
        check "VSA-33" (Ws.elem Cbat_word.b1 c2 && not (Ws.elem Cbat_word.b0 c2)));

    (* T4: the caller-alias fixpoint — the post-call state. *)
    pin "VSA-34" "T4-7: caller-alias — the post-call reload reads TOP (sound)"
      (fun () ->
        let fx = mk_caller_alias () in
        let sol = run_anchored fx.ca_sub in
        let post_ai = in_state sol fx.ca_post_tid in
        check "VSA-34" (Ws.is_top (AI.find_word 64 post_ai fx.ca_r2)));

    pin "VSA-35" "T4-8: post-call memory is TOP entirely (find_memory = Mem.top)"
      (fun () ->
        let fx = mk_caller_alias () in
        let sol = run_anchored fx.ca_sub in
        let post_ai = in_state sol fx.ca_post_tid in
        check "VSA-35"
          (Mem.equal
             (AI.find_memory { addr_width = 64; addressable_width = 8 } post_ai fx.ca_m)
             (Mem.top { addr_width = 64; addressable_width = 8 })));

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

    pin "VSA-38" "T4-11: callee-saved RBX is preserved across the call"
      (fun () ->
        let fx = mk_caller_alias () in
        let sol = run_anchored fx.ca_sub in
        let post_ai = in_state sol fx.ca_post_tid in
        check "VSA-38"
          (Ws.equal (AI.find_word 64 post_ai fx.ca_rbx) (Ws.singleton (w64 0x2040))));

    pin "VSA-39" "T4-12: caller-saved rdi is TOPed across the call"
      (fun () ->
        let fx = mk_caller_alias () in
        let sol = run_anchored fx.ca_sub in
        let post_ai = in_state sol fx.ca_post_tid in
        check "VSA-39" (Ws.is_top (AI.find_word 64 post_ai fx.ca_rdi)));

    (* F1: the map lattice's fold visits the explicitly-stored bindings. *)
    pin "VSA-40" "F1-1: fold enumerates the explicitly-stored bindings (keys+data)"
      (fun () ->
        let m = Map.add (Map.add Map.top ~key:1 ~data:10) ~key:2 ~data:20 in
        let seen = Map.fold m ~init:[] ~f:(fun ~key ~data acc -> (key, data) :: acc) in
        check "VSA-40" (List.sort compare seen = [ (1, 10); (2, 20) ]));

    pin "VSA-41" "F1-2: fold over top (absent = top) visits nothing"
      (fun () ->
        check "VSA-41"
          (Map.fold Map.top ~init:[] ~f:(fun ~key ~data acc -> (key, data) :: acc) = []));

    (* D7: degenerate cast/extract sizes degrade to top. *)
    pin "VSA-42" "D7-1: Clp.cast HIGH sz=0 -> top(64), no raise"
      (fun () ->
        let c64 = Clp.create (w64 16) in
        check "VSA-42" (Clp.is_top (Clp.cast Bil.HIGH 0 c64)));

    pin "VSA-43" "D7-2: Clp.cast HIGH sz>width -> top(64), no raise"
      (fun () ->
        let c64 = Clp.create (w64 16) in
        check "VSA-43" (Clp.is_top (Clp.cast Bil.HIGH 128 c64)));

    pin "VSA-44" "D7-3: Clp.cast UNSIGNED sz=0 -> top(32), no raise"
      (fun () ->
        let c32 = Clp.create (w32 16) in
        check "VSA-44" (Clp.is_top (Clp.cast Bil.UNSIGNED 0 c32)));

    pin "VSA-45" "D7-4: Clp.cast SIGNED sz=0 -> top(32), no raise"
      (fun () ->
        let c32 = Clp.create (w32 16) in
        check "VSA-45" (Clp.is_top (Clp.cast Bil.SIGNED 0 c32)));

    pin "VSA-46" "D7-5: Clp.cast LOW sz=0 -> top(32), no raise"
      (fun () ->
        let c32 = Clp.create (w32 16) in
        check "VSA-46" (Clp.is_top (Clp.cast Bil.LOW 0 c32)));

    pin "VSA-47" "D7-6: Clp.extract ~lo:width -> top (no assert)"
      (fun () ->
        let c32 = Clp.create (w32 16) in
        check "VSA-47" (Clp.is_top (Clp.extract ~lo:32 c32)));

    pin "VSA-48" "D7-7: Clp.extract ~hi:(-1) -> top (no raise)"
      (fun () ->
        let c32 = Clp.create (w32 16) in
        check "VSA-48" (Clp.is_top (Clp.extract ~hi:(-1) c32)));

    pin "VSA-49"
      "D7-8: composite cast HIGH sz=0 -> top(64) (CLP-backed top, not the FinSet.top stub)"
      (fun () ->
        check "VSA-49" (Ws.is_top (Ws.cast Bil.HIGH 0 (Ws.singleton (w64 16)))));

    pin "VSA-50" "D7-9: composite extract hi<lo -> top(32)"
      (fun () ->
        check "VSA-50" (Ws.is_top (Ws.extract ~hi:0 ~lo:5 (Ws.singleton (w32 16)))));

    pin "VSA-51" "D7-9b: composite extract hi<0 (lo defaults 0) -> top(32)"
      (fun () ->
        check "VSA-51" (Ws.is_top (Ws.extract ~hi:(-1) (Ws.singleton (w32 16)))));

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
    pin "VSA-53" "E2eH-1: equal on the SAME CLP value (physical identity) -> true"
      (fun () ->
        let p = Clp.of_list ~width:32 [ w32 1; w32 2; w32 4 ] in
        check "VSA-53" (Clp.equal p p));

    pin "VSA-54" "E2eH-2: equal on structurally-equal separately-built CLPs -> true"
      (fun () ->
        let p = Clp.of_list ~width:32 [ w32 1; w32 2; w32 4 ] in
        let q = Clp.of_list ~width:32 [ w32 1; w32 2; w32 4 ] in
        check "VSA-54" (Clp.equal p q));

    pin "VSA-55" "E2eH-3: unequal CLPs still compare false (canonize path intact)"
      (fun () ->
        let p = Clp.of_list ~width:32 [ w32 1; w32 2; w32 4 ] in
        let r = Clp.of_list ~width:32 [ w32 1; w32 2; w32 3 ] in
        check "VSA-55" (not (Clp.equal p r)));

    pin "VSA-56" "E2eH-4: width-mismatched CLPs still compare false, no raise"
      (fun () ->
        let p = Clp.of_list ~width:32 [ w32 1; w32 2; w32 4 ] in
        check "VSA-56" (not (Clp.equal p (Clp.top 64))));

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

    pin "VSA-58"
      "E2eC-14 (BIR loop): the counter window survives the body shift — the iterate view's counter stays ⊆ [0,4] (y = x << (i+1) ∈ {32..512})"
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
              [ Def.create i (Bil.BinOp (Bil.PLUS, iv, Bil.Int (Cbat_word.to_word (w32 1))));
                Def.create y (Bil.BinOp (Bil.LSHIFT, xv, iv)) ],
              [ (2, mk_goto) ];
              [], [ (3, fun t -> mk_jmp_to t nlt5); (1, fun t -> mk_jmp_to t lt5) ];
              [], [] ]
        in
        let sol = run_anchored sub in
        let c_iter = AI.find_word 32 (in_state sol tids.(1)) i in
        check "VSA-58"
          ((not (Ws.is_top c_iter))
          && (Base.Option.filter (Ws.max_elem c_iter)
                ~f:(fun w -> Cbat_word.(<=) w (w32 4))
             |> Option.is_some)));

    (* E2eD: channel-2 negative — the heap-indexed store never seeds. *)
    pin "VSA-59" "E2eD-4: gate-free — the heap store's data var is denoted ({99})"
      (fun () ->
        let _, _, _, _, sub, exit_tid = mk_e2ed_heap_sub () in
        let sol = run_anchored sub in
        let exit_ai = in_state sol exit_tid in
        let vv = AI.find_word 64 exit_ai (v64 "e2ed_v") in
        check "VSA-59" (Ws.equal vv (Ws.singleton (w64 99))));

    (* P3: the gate-free entry RSP anchor. *)
    pin "VSA-60"
      "P3-1: gate-free — the entry RSP anchor is denoted (entry input state carries RSP = the symbolic segment base at offset 0 — StackOff{0})"
      (fun () ->
        let rsp_var = v64 "RSP" in
        let sub = mk_p3_anchor_sub () in
        let sol = run_anchored sub in
        let st = in_state sol (entry_tid_of sub) in
        check "VSA-60" (Ws.equal (AI.find_word 64 st rsp_var) (Ws.stack_word_i64 0L)));

    (* L2b: the full 1-bit domain reads cardinality 2. *)
    pin "VSA-61"
      "L2b-1: the full 1-bit domain {0,1} reads cardn 2 (non-bottom; the FinSet cardinality no longer wraps at the set width)"
      (fun () ->
        let full = Ws.top 1 in
        let full_l = Ws.of_list ~width:1 [ Cbat_word.b0; Cbat_word.b1 ] in
        check "VSA-61"
          ((not (Ws.is_bottom full))
          && Cbat_word.(=) (Ws.cardinality full) (Cbat_word.of_int ~width:2 2)
          && (not (Ws.is_bottom full_l))
          && Cbat_word.(=) (Ws.cardinality full_l) (Cbat_word.of_int ~width:2 2)));
  ]

let () = run "vsa" tests
