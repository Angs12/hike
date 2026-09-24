(* The Test Seam's context builder: the seam must carry production's own
   defaults, so a seam-level refine runs the context the fixpoint runs. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

let abi = Hike_abi.x86_64_sysv

let tests : unit Alcotest.test list =
  [
    (* SC-A: a guard [x SLT 5] over a load from a stack cell that has a
       non-negative constant store — provably non-negative though the load's
       abstract value is TOP.  The builder's oracle makes the signed row the
       interval [0,4], so the walk's [x] is [0,4]. *)
    pin "SEAM-01"
      "the seam builder wires the non-negativity oracle — the SLT row on a provably non-negative load is the interval [0,4]"
      (fun () ->
        let m = memv "sc_m" in
        let rsp = v64 "RSP" in
        let rbp = v64 "RBP" in
        let x = Var.create ~is_virtual:false ~fresh:false "sc_x" (Type.Imm 32) in
        let zf = v1 "sc_zf" in
        let addr =
          Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8)))
        in
        let sub, tids =
          sub_of "sc_nonneg"
            [ [ Def.create rbp (Bil.Var rsp) ], [ (1, mk_goto) ];
              [ Def.create x (Bil.Load (Bil.Var m, addr, LittleEndian, `r32));
                Def.create zf
                  (Bil.BinOp
                     (Bil.SLT, Bil.Var x, Bil.Int (Cbat_word.to_word (w32 5)))) ],
              [ (2, mk_goto) ];
              [ Def.create m
                  (Bil.Store
                     ( Bil.Var m,
                       addr,
                       Bil.Int (Cbat_word.to_word (w32 5)),
                       LittleEndian,
                       `r32 )) ],
              [] ]
        in
        let guard_tid = tids.(1) in
        let entry =
          AI.add_memory (anchored_entry ()) ~key:m
            ~data:(Mem.top { Mem.addr_width = 64; Mem.addressable_width = 8 })
        in
        let sol =
          Vsa.static_graph_vsa ~abi (Program.create ~subs:[ sub ] ()) sub
            (Vsa.init_sol ~abi ~entry sub)
        in
        let cfg =
          Sub.to_graph sub
          |> Graphs.Tid.Node.remove Graphs.Tid.start
          |> Graphs.Tid.Node.remove Graphs.Tid.exit
        in
        let rctx = Vsa.Test_seam.mk_rctx ~cfg ~abi sub in
        let guard_blk =
          Term.enum blk_t sub |> Seq.to_list
          |> List.find (fun b -> Tid.equal (Term.tid b) guard_tid)
        in
        let out =
          Vsa.Test_seam.refine_edge ~sol ~rctx
            ~seeds:[ (zf, Ws.singleton Cbat_word.b1) ]
            (Graphlib.Std.Solution.get sol guard_tid) guard_blk
        in
        let row = Ws.of_clp (Clp.interval ~width:32 (w32 0) (w32 4)) in
        check "SEAM-01" (Ws.precedes (AI.find_word 32 out x) row));

    (* SC-B: the context's landmark table is the one source of truth: a refine
       run under the context's widening head records the empty meet's boundary
       in that same table. *)
    pin "SEAM-02" "the context's landmark table is empty before the widening window"
      (fun () ->
        let sub = straight_sub "sc_lm" [] in
        let cfg =
          Sub.to_graph sub
          |> Graphs.Tid.Node.remove Graphs.Tid.start
          |> Graphs.Tid.Node.remove Graphs.Tid.exit
        in
        let rctx = Vsa.Test_seam.mk_rctx ~cfg ~abi sub in
        let lm = Vsa.Test_seam.landmarks_of rctx in
        let head = Tid.for_name "sc_lm_head" in
        check "SEAM-02"
          (match Cbat_landmarks.entries_for_head lm head with
          | [] -> true
          | _ -> false));

    pin "SEAM-03"
      "a refine under the context's widening head records the empty meet's boundary in the context's own table"
      (fun () ->
        let sub = straight_sub "sc_lm" [] in
        let cfg =
          Sub.to_graph sub
          |> Graphs.Tid.Node.remove Graphs.Tid.start
          |> Graphs.Tid.Node.remove Graphs.Tid.exit
        in
        let rctx = Vsa.Test_seam.mk_rctx ~cfg ~abi sub in
        let lm = Vsa.Test_seam.landmarks_of rctx in
        let x = Var.create ~is_virtual:false ~fresh:false "sc_lm_x" (Type.Imm 32) in
        let head = Tid.for_name "sc_lm_head" in
        let env = AI.add_word AI.top ~key:x ~data:(Ws.singleton (w32 0)) in
        let cond =
          Bil.BinOp (Bil.EQ, Bil.Var x, Bil.Int (Cbat_word.to_word (w32 20)))
        in
        Vsa.Test_seam.with_widening_head rctx (Some head) (fun () ->
            ignore (Vsa.Test_seam.constrain_edge ~landmarks:lm ~env cond));
        check "SEAM-03"
          (match Cbat_landmarks.entries_for_head lm head with
          | e :: _ -> Cbat_word.equal e.Cbat_landmarks.bound (w32 20)
          | [] -> false));
  ]

let () = run "seam" tests
