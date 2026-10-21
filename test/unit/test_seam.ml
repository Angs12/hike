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
       interval [0,4], so the walk's [x] is [0,4].

       The store follows the load in the guard's own block: the oracle's
       store index is keyed by the address expression, and in the SSA form
       a block's address names that block's own phi version, so only a
       store beside the load shares its address. *)
    pin "SEAM-01"
      "the seam builder wires the non-negativity oracle — the SLT row on a provably non-negative load is the interval [0,4]"
      (fun () ->
        let m = memv "sc_m" in
        let rsp = sp in
        let rbp = frame_ptr in
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
                     (Bil.SLT, Bil.Var x, Bil.Int (Cbat_word.to_word (w32 5))));
                Def.create m
                  (Bil.Store
                     ( Bil.Var m,
                       addr,
                       Bil.Int (Cbat_word.to_word (w32 5)),
                       LittleEndian,
                       `r32 )) ],
              [ (2, mk_goto) ];
              [], [ (2, mk_ret) ] ]
        in
        let guard_tid = tids.(1) in
        let entry =
          AI.add_memory (anchored_entry ()) ~key:m
            ~data:(Mem.top { Mem.addr_width = 64; Mem.addressable_width = 8 })
        in
        let sol =
          static_graph_vsa ~synth:Hike.Synth.empty ~abi sub
            (Vsa.init_sol ~abi ~entry sub)
        in
        let rctx = mk_rctx ~synth:Hike.Synth.empty ~abi sub in
        let guard_blk =
          Term.enum blk_t sub |> Seq.to_list
          |> List.find (fun b -> Tid.equal (Term.tid b) guard_tid)
        in
        (* The guard block's own definitions: the state and the walk name
           the flag and the loaded word by their versions. *)
        let zf_v = Base.Option.value_exn (def_version sub guard_tid zf) in
        let x_v = Base.Option.value_exn (def_version sub guard_tid x) in
        let out =
          Vsa.Test_seam.refine_edge ~sol ~rctx
            ~seeds:(Var.Set.singleton zf_v)
            (AI.add_word (Graphlib.Std.Solution.get sol guard_tid) ~key:zf_v
               ~data:(Ws.singleton Cbat_word.b1))
            guard_blk
        in
        let row = Ws.of_clp (Clp.interval ~width:32 (w32 0) (w32 4)) in
        check "SEAM-01" (Ws.equal (AI.find_word 32 out x_v) row));

    (* SC-B: the context's landmark table is the one source of truth: a refine
       run under the context's widening head records the empty meet's boundary
       in that same table. *)

    pin "SEAM-03"
      "a refine under the context's widening head records the empty meet's boundary in the context's own table"
      (fun () ->
        let sub = straight_sub "sc_lm" [] in
        let rctx = mk_rctx ~synth:Hike.Synth.empty ~abi sub in
        let lm = Vsa.Test_seam.landmarks_of rctx in
        let x = Var.create ~is_virtual:false ~fresh:false "sc_lm_x" (Type.Imm 32) in
        let head = Tid.for_name "sc_lm_head" in
        let env = AI.add_word AI.top ~key:x ~data:(Ws.singleton (w32 0)) in
        let cond =
          Bil.BinOp (Bil.EQ, Bil.Var x, Bil.Int (Cbat_word.to_word (w32 20)))
        in
        Vsa.Test_seam.with_widening_head rctx (Some head) (fun () ->
            ignore (Vsa.Test_seam.constrain_edge ~synth:Hike.Synth.empty ~landmarks:lm ~env cond));
        check "SEAM-03"
          (match Cbat_landmarks.entries lm head (Cbat_landmarks.Word x) with
          | e :: _ -> Cbat_word.equal e.Cbat_landmarks.bound (w32 20)
          | [] -> false));

    (* SC-D: x := y * -1 over the same provably non-negative y.  x is
       non-positive, so the SLT row must not take the non-negativity
       tier; the identity keeps x's value. *)
    pin "SEAM-04"
      "TIMES by a negative literal is not a non-negativity proof — the SLT row on x = y * -1 leaves x unconstrained"
      (fun () ->
        let m = memv "sc_neg_m" in
        let rsp = sp in
        let rbp = frame_ptr in
        let y = Var.create ~is_virtual:false ~fresh:false "sc_neg_y" (Type.Imm 32) in
        let x = Var.create ~is_virtual:false ~fresh:false "sc_neg_x" (Type.Imm 32) in
        let zf = v1 "sc_neg_zf" in
        let addr =
          Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8)))
        in
        let sub, tids =
          sub_of "sc_neg"
            [ [ Def.create rbp (Bil.Var rsp) ], [ (1, mk_goto) ];
              [ Def.create y (Bil.Load (Bil.Var m, addr, LittleEndian, `r32));
                Def.create x
                  (Bil.BinOp (Bil.TIMES, Bil.Var y,
                     Bil.Int (Cbat_word.to_word
                                (Cbat_word.of_int64 ~width:32 (-1L)))));
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
          static_graph_vsa ~synth:Hike.Synth.empty ~abi sub
            (Vsa.init_sol ~abi ~entry sub)
        in
        let rctx = mk_rctx ~synth:Hike.Synth.empty ~abi sub in
        let guard_blk =
          Term.enum blk_t sub |> Seq.to_list
          |> List.find (fun b -> Tid.equal (Term.tid b) guard_tid)
        in
        (* The guard block's own definitions: the walk names the flag and
           the derived word by their versions. *)
        let zf_v = Base.Option.value_exn (def_version sub guard_tid zf) in
        let x_v = Base.Option.value_exn (def_version sub guard_tid x) in
        let out =
          Vsa.Test_seam.refine_edge ~sol ~rctx
            ~seeds:(Var.Set.singleton zf_v)
            (AI.add_word (Graphlib.Std.Solution.get sol guard_tid) ~key:zf_v
               ~data:(Ws.singleton Cbat_word.b1))
            guard_blk
        in
        check "SEAM-04"
          (Ws.elem (Cbat_word.of_int64 ~width:32 (-1L))
             (AI.find_word 32 out x_v)
           && not (Ws.is_top (AI.find_word 32 out x_v))));
    (* The edge step reads a guard no state satisfies as a dead edge. *)
    pin "SEAM-05"
      "refine_edge_inline: an empty guard meet is a dead edge; a satisfiable or merely narrowing guard and a discarded walk are not"
      (fun () ->
        let x = Var.create ~is_virtual:false ~fresh:false "dead_x" (Type.Imm 32) in
        let zf = v1 "dead_zf" in
        let c32 k = Bil.Int (Cbat_word.to_word (w32 k)) in
        (* A guard that names a flag the block defines reads that
           definition's version: the state holds the version, not the
           base variable. *)
        let flag_version sub =
          let blk = List.hd (Term.enum blk_t sub |> Seq.to_list) in
          match def_version sub (Term.tid blk) zf with
          | Some v -> v
          | None -> zf
        in
        let edge ?(defs = []) ?(discarded = false) xval cond_of =
          let sub = straight_sub "dead_edge" defs in
          let entry =
            AI.add_word (anchored_entry ()) ~key:x ~data:xval in
          let sol = static_graph_vsa ~synth:Hike.Synth.empty ~abi sub (Vsa.init_sol ~abi ~entry sub) in
          let rctx = mk_rctx ~synth:Hike.Synth.empty ~abi sub in
          let blk = List.hd (Term.enum blk_t sub |> Seq.to_list) in
          let env = Graphlib.Std.Solution.get sol (Term.tid blk) in
          let out = ref AI.bottom in
          Vsa.Test_seam.with_widening_head rctx (Some (Tid.for_name "dead_head"))
            (fun () ->
              out :=
                Vsa.Test_seam.refine_edge_inline ~sol ~rctx ~discarded blk env
                  (cond_of sub));
          (!out, rctx)
        in
        let two = Ws.of_list ~width:32 [ w32 1; w32 5 ] in
        let dead out = AI.equal out AI.bottom in
        let both =
          Bil.BinOp (Bil.AND, Bil.BinOp (Bil.LT, Bil.Var x, c32 3),
                     Bil.BinOp (Bil.LT, c32 2, Bil.Var x)) in
        let o, _ = edge two (fun _ -> both) in
        check "SEAM-05.empty-meet" (dead o);
        let o, _ = edge two (fun _ -> Bil.BinOp (Bil.LT, Bil.Var x, c32 3)) in
        check "SEAM-05.narrowing"
          ((not (dead o)) && Ws.equal (AI.find_word 32 o x) (Ws.singleton (w32 1)));
        let o, _ =
          edge two
            (fun _ ->
               Bil.BinOp (Bil.AND, Bil.BinOp (Bil.LT, Bil.Var x, c32 6),
                          Bil.BinOp (Bil.LT, c32 0, Bil.Var x)))
        in
        check "SEAM-05.satisfiable" ((not (dead o)) && Ws.equal (AI.find_word 32 o x) two);
        let o, _ = edge ~discarded:true two (fun _ -> both) in
        check "SEAM-05.discarded" (not (dead o));
        let o, _ =
          edge (Ws.bottom 32) (fun _ -> Bil.BinOp (Bil.EQ, Bil.Var x, c32 3))
        in
        check "SEAM-05.unreached-read" (dead o);
        let o, _ =
          edge ~defs:[ Def.create zf (Bil.BinOp (Bil.EQ, Bil.Var x, c32 3)) ]
            two (fun sub -> Bil.Var (flag_version sub)) in
        check "SEAM-05.flag-def" (dead o);
        let o, _ =
          edge two (fun _ -> Bil.BinOp (Bil.EQ, c32 3, c32 4)) in
        check "SEAM-05.constants" (dead o);
        let o, rctx =
          edge (Ws.singleton (w32 0))
            (fun _ -> Bil.BinOp (Bil.EQ, Bil.Var x, c32 20)) in
        check "SEAM-05.dead-with-landmark"
          (dead o
           && List.exists
                (fun (e : Cbat_landmarks.lm_entry) -> Cbat_word.equal e.bound (w32 20))
                (Cbat_landmarks.entries (Vsa.Test_seam.landmarks_of rctx)
                   (Tid.for_name "dead_head") (Cbat_landmarks.Word x))));
  ]

let () = run "seam" tests
