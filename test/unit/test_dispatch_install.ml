(* In-VSA dispatch install pins: the synthetic materialize_transfer
   callback drives the source rewrite, the plan/graph/WTO refresh and the
   same-fan-out delivery.  No Hike-layer enumeration is involved. *)

open Bap.Std
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

module D = Cbat_vsa.Dispatch

let w (n : int64) : Cbat_word.t = Cbat_word.of_int64 ~width:64 n
let wexp (n : int64) : exp = Bil.Int (Cbat_word.to_word (w n))
let eq (a : exp) (b : exp) : exp = Bil.BinOp (Bil.EQ, a, b)

(* The solver seam with the slopes the fixtures expect. *)
let solve_sub ?(resolved = Tid.Map.empty) ?materialize_transfer (sub : sub term) =
  Vsa.static_graph_vsa ~abi:sysv
    ~synth:(ref Hike.Synth.empty)
    ~def_reads:(fun d -> Sm.reads (`Def d))
    ~def_writes:(fun d -> Sm.writes (`Def d))
    ~phi_reads:(fun p -> Sm.reads (`Phi p))
    ~phi_writes:(fun p -> Sm.writes (`Phi p))
    ~jmp_reads:(fun j ->
      Core.Set.union (Sm.reads (`Jmp j)) (Sm.writes (`Jmp j)))
    ~resolved ?materialize_transfer sub
    (Vsa.init_sol ~abi:sysv ~entry:(anchored_entry ()) sub)

let in_state (sol : Vsa.vsa_sol) tid =
  Graphlib.Std.Solution.get sol tid

let source_blk sub tid = Term.find_exn blk_t sub tid

let indirect_jmp (blk : blk term) : jmp term =
  Term.enum jmp_t blk
  |> Seq.find_exn ~f:(fun j ->
      match Jmp.kind j with Goto (Indirect _) -> true | _ -> false)

let mat ~sub ~base targets : D.materialized = { D.base; targets; sub }

(* A two-target indirect Goto.  The targets carry a phi for the dispatch
   value, so the delivered edge states expose the per-arm guard.  The sub
   stays unversioned: the indirect edge is not in the CFG before the
   install, so SSA would make the targets independent roots. *)
let jump_fixture () =
  let t = v64 "dsp_t" in
  let p1 = v64 "dsp_p1" and p2 = v64 "dsp_p2" in
  let sub, tids =
    raw_sub_of "dsp_jump"
      [ [ Def.create t (Bil.Var (v64 "dsp_in")) ],
        [ (1, fun _ -> Jmp.create (Goto (Indirect (Bil.Var t)))) ];
        [], [ (3, mk_goto) ];
        [], [ (3, mk_goto) ];
        [], [ (0, mk_ret) ] ]
  in
  let add_phi tid p sub =
    let blk = Term.find_exn blk_t sub tid in
    let builder =
      Blk.Builder.init ~copy_defs:true ~copy_phis:true ~copy_jmps:true blk in
    Blk.Builder.add_phi builder
      (Phi.of_list p [ (tids.(0), Bil.Var t) ]);
    Term.map blk_t sub ~f:(fun b ->
        if Tid.equal (Term.tid b) tid then Blk.Builder.result builder else b)
  in
  let sub = add_phi tids.(1) p1 sub |> add_phi tids.(2) p2 in
  (sub, tids, t, p1, p2)

let two_targets (tids : tid array) : (Cbat_word.t * tid) list =
  [ (w 0x400010L, tids.(1)); (w 0x400020L, tids.(2)) ]

let tests : unit Alcotest.test list =
  [
    (* A two-target materialization installs the ordered chain and both
       case edges receive their refined state in the same fan-out. *)
    pin "INST-01" "a two-target indirect Goto installs and delivers both arms"
      (fun () ->
        let sub, tids, _t, p1, p2 = jump_fixture () in
        let calls = ref 0 in
        let mat_transfer ~state ~source:_ ~blk:_ ~jmp:_ ~env:_ =
          incr calls;
          Some (mat ~sub:(Vsa.state_sub state) ~base:None (two_targets tids))
        in
        let sol, state = solve_sub ~materialize_transfer:mat_transfer sub in
        let sub' = Vsa.state_sub state in
        let src = source_blk sub' tids.(0) in
        let jmps = Term.enum jmp_t src |> Seq.to_list in
        let target_expr =
          let j = indirect_jmp (source_blk sub tids.(0)) in
          match Jmp.kind j with
          | Goto (Indirect e) -> e
          | _ -> assert false
        in
        let targets =
          List.map
            (fun j ->
              match Jmp.kind j with
              | Goto (Direct t) -> t
              | _ -> assert false)
            jmps
        in
        check "INST-01 one arm per word"
          (Base.List.equal Tid.equal targets [ tids.(1); tids.(2) ]);
        check "INST-01 ordered guards"
          (Base.List.equal Exp.equal (List.map Jmp.cond jmps)
             [ eq target_expr (wexp 0x400010L);
               Bil.Int (Word.one 1) ]);
        check "INST-01 both edges delivered"
          ((not (AI.equal (in_state sol tids.(1)) AI.bottom))
          && not (AI.equal (in_state sol tids.(2)) AI.bottom));
        let pv tid p =
          AI.find_word 64 (in_state sol tid) p
        in
        check "INST-01 arm 1 value"
          (Ws.equal (pv tids.(1) p1) (Ws.singleton (w 0x400010L)));
        check "INST-01 arm 2 value"
          (Ws.elem (w 0x400020L) (pv tids.(2) p2));
        check "INST-01 one callback" (Int.equal !calls 1));

    (* None leaves the indirect transfer and the resolved extra edges
       exactly as the no-callback baseline. *)
    pin "INST-02" "a None callback leaves the indirect jmp and its edges unchanged"
      (fun () ->
        let sub, tids, _t, _p1, _p2 = jump_fixture () in
        let jmp = indirect_jmp (source_blk sub tids.(0)) in
        let jmp_tid = Term.tid jmp in
        let resolved =
          Tid.Map.singleton jmp_tid
            (Tid.Set.of_list [ tids.(1); tids.(2) ])
        in
        let baseline, _ = solve_sub ~resolved sub in
        let none ~state:_ ~source:_ ~blk:_ ~jmp:_ ~env:_ = None in
        let sol, state = solve_sub ~resolved ~materialize_transfer:none sub in
        let src = source_blk (Vsa.state_sub state) tids.(0) in
        let jmps = Term.enum jmp_t src |> Seq.to_list in
        check "INST-02 one indirect jmp"
          (match jmps with
           | [ j ] ->
             Tid.equal (Term.tid j) jmp_tid
             && (match Jmp.kind j with
                 | Goto (Indirect e) -> Exp.equal e (match Jmp.kind jmp with
                     | Goto (Indirect e0) -> e0
                     | _ -> assert false)
                 | _ -> false)
           | _ -> false);
        check "INST-02 same target 1 state"
          (AI.equal (in_state baseline tids.(1)) (in_state sol tids.(1)));
        check "INST-02 same target 2 state"
          (AI.equal (in_state baseline tids.(2)) (in_state sol tids.(2)));
        check "INST-02 both edges still live"
          ((not (AI.equal (in_state sol tids.(1)) AI.bottom))
          && not (AI.equal (in_state sol tids.(2)) AI.bottom)));

    (* A materialization that adds a block installs its facts/graph vertex
       before the drain; the solve continues in the same call. *)
    pin "INST-03" "a new block joins the sub, facts and graph without a restart"
      (fun () ->
        let sub, tids, t, _p1, _p2 = jump_fixture () in
        let new_tid = Tid.create () in
        let new_blk =
          Blk.create ~tid:new_tid
            ~defs:[ Def.create (v64 "dsp_new_y") (Bil.Var t) ]
            ~jmps:[ Jmp.create (Goto (Direct tids.(3))) ] ()
        in
        let calls = ref 0 in
        let mat_transfer ~state ~source:_ ~blk:_ ~jmp:_ ~env:_ =
          incr calls;
          let sub = Term.append blk_t (Vsa.state_sub state) new_blk in
          Some
            (mat ~sub ~base:None
               [ (w 0x400010L, tids.(1)); (w 0x400020L, new_tid) ])
        in
        let sol, state = solve_sub ~materialize_transfer:mat_transfer sub in
        check "INST-03 callback once" (Int.equal !calls 1);
        check "INST-03 block in the solve view"
          (Option.is_some (Term.find blk_t (Vsa.state_sub state) new_tid));
        check "INST-03 facts installed"
          (Core.Map.mem state.Cbat_vsa.Runctx.rc_blocks new_tid);
        check "INST-03 vertex processed"
          (not (AI.equal (in_state sol new_tid) AI.bottom)));

    (* Only the installed source's plan is replaced; another source's
       cached plan object is physically unchanged. *)
    pin "INST-04" "the source plan changes, another source plan does not"
      (fun () ->
        let sub, tids, _t, _p1, _p2 = jump_fixture () in
        let before_src = ref None and before_other = ref None in
        let plan_of st tid =
          match st.Cbat_vsa.Runctx.rs_plan with
          | Some f -> Some (f tid)
          | None -> None
        in
        let mat_transfer ~state ~source:_ ~blk:_ ~jmp:_ ~env:_ =
          before_src := plan_of state tids.(0);
          before_other := plan_of state tids.(1);
          Some (mat ~sub:(Vsa.state_sub state) ~base:None (two_targets tids))
        in
        let _, state = solve_sub ~materialize_transfer:mat_transfer sub in
        let f =
          match state.Cbat_vsa.Runctx.rs_plan with
          | Some f -> f
          | None -> assert false
        in
        let after_src = f tids.(0) and after_other = f tids.(1) in
        check "INST-04 source plan replaced"
          (not (Base.phys_equal (Base.Option.value_exn !before_src) after_src));
        check "INST-04 other plan physical"
          (Base.phys_equal (Base.Option.value_exn !before_other) after_other));

    (* A non-variable target expression is bound once: one fresh def is
       appended before the arm jmps, and every guard reads its lhs. *)
    pin "INST-05" "a non-stable target gets one binding def before the arms"
      (fun () ->
        let t = v64 "dsp_bt" in
        let target_exp =
          Bil.BinOp (Bil.PLUS, Bil.Var t, Bil.Int (Cbat_word.to_word (w64 0)))
        in
        let sub, tids =
          sub_of "dsp_bind"
            [ [ Def.create t (Bil.Var (v64 "dsp_bin")) ],
              [ (1, fun _ ->
                    Jmp.create (Goto (Indirect target_exp))) ];
              [ Def.create (v64 "dsp_by1") (Bil.Var t) ], [ (3, mk_goto) ];
              [ Def.create (v64 "dsp_by2") (Bil.Var t) ], [ (3, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let orig = source_blk sub tids.(0) in
        let orig_defs =
          Term.enum def_t orig |> Seq.map ~f:Term.tid |> Seq.to_list
          |> Tid.Set.of_list
        in
        let mat_transfer ~state ~source:_ ~blk:_ ~jmp:_ ~env:_ =
          Some
            (mat ~sub:(Vsa.state_sub state) ~base:None
               [ (w 0x400010L, tids.(1)); (w 0x400020L, tids.(2)) ])
        in
        let sol, state = solve_sub ~materialize_transfer:mat_transfer sub in
        let src = source_blk (Vsa.state_sub state) tids.(0) in
        let defs = Term.enum def_t src |> Seq.to_list in
        let fresh =
          List.filter
            (fun d -> not (Core.Set.mem orig_defs (Term.tid d)))
            defs
        in
        let jmps = Term.enum jmp_t src |> Seq.to_list in
        check "INST-05 one binding def" (Int.equal (List.length fresh) 1);
        let d =
          match fresh with [ d ] -> d | _ -> assert false in
        let v = Def.lhs d in
        check "INST-05 virtual binding"
          (Var.is_virtual v
          && Exp.equal (Def.rhs d)
               (match Jmp.kind (indirect_jmp orig) with
                | Goto (Indirect e) -> e
                | _ -> assert false));
        check "INST-05 guards read the binding"
          (Base.List.equal Exp.equal (List.map Jmp.cond jmps)
             [ eq (Bil.Var v) (wexp 0x400010L);
               Bil.Int (Word.one 1) ]);
        check "INST-05 both arms delivered"
          ((not (AI.equal (in_state sol tids.(1)) AI.bottom))
          && not (AI.equal (in_state sol tids.(2)) AI.bottom)));
    (* A callback that binds the base summand in its returned source view
       keeps that def: the install merges the callback's source defs with
       the current jmp chain. *)
    pin "INST-06" "a callback's source defs survive the jmp rewrite"
      (fun () ->
        let sub, tids, t, _p1, _p2 = jump_fixture () in
        let base = v64 "dsp_base_bound" in
        let base_def = Def.create base (Bil.Var t) in
        let mat_transfer ~state ~source:_ ~blk:_ ~jmp:_ ~env:_ =
          let sub = Vsa.state_sub state in
          let src = source_blk sub tids.(0) in
          let src = Term.append def_t src base_def in
          let sub = Term.update blk_t sub src in
          Some (mat ~sub ~base:None (two_targets tids))
        in
        let _, state = solve_sub ~materialize_transfer:mat_transfer sub in
        let src = source_blk (Vsa.state_sub state) tids.(0) in
        check "INST-06 callback def retained"
          (Option.is_some (Term.find def_t src (Term.tid base_def)));
        check "INST-06 arms installed"
          (Int.equal (Term.length jmp_t src) 2));

    (* A conditional indirect Goto keeps every arm conditional and leaves
       the original false continuation after the chain. *)
    pin "INST-07" "a conditional indirect Goto preserves the false edge"
      (fun () ->
        let t = v64 "dsp_ct" and c = v1 "dsp_cc" in
        let p1 = v64 "dsp_cp1" and p2 = v64 "dsp_cp2" in
        let sub, tids =
          raw_sub_of "dsp_cond"
            [ [], [ (1, fun _ ->
                        Jmp.create ~cond:(Bil.Var c)
                          (Goto (Indirect (Bil.Var t))));
                    (3, mk_goto) ];
              [], [ (4, mk_goto) ];
              [], [ (4, mk_goto) ];
              [], [ (4, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let add_phi tid p sub =
          let blk = Term.find_exn blk_t sub tid in
          let builder =
            Blk.Builder.init ~copy_defs:true ~copy_phis:true ~copy_jmps:true
              blk
          in
          Blk.Builder.add_phi builder
            (Phi.of_list p [ (tids.(0), Bil.Var t) ]);
          Term.map blk_t sub ~f:(fun b ->
              if Tid.equal (Term.tid b) tid then Blk.Builder.result builder
              else b)
        in
        let sub =
          add_phi tids.(1) p1 sub |> add_phi tids.(2) p2
        in
        let mat_transfer ~state ~source:_ ~blk:_ ~jmp:_ ~env:_ =
          Some
            (mat ~sub:(Vsa.state_sub state) ~base:None
               [ (w 0x400010L, tids.(1)); (w 0x400020L, tids.(2)) ])
        in
        let sol, state = solve_sub ~materialize_transfer:mat_transfer sub in
        let src = source_blk (Vsa.state_sub state) tids.(0) in
        let jmps = Term.enum jmp_t src |> Seq.to_list in
        check "INST-07 false edge kept" (Int.equal (List.length jmps) 3);
        let arm1 = List.nth jmps 0 and arm2 = List.nth jmps 1
        and tail = List.nth jmps 2 in
        check "INST-07 arm guards conjoin the condition"
          (Exp.equal (Jmp.cond arm1)
             (Bil.BinOp (Bil.AND, Bil.Var c,
                         eq (Bil.Var t) (wexp 0x400010L)))
          && Exp.equal (Jmp.cond arm2)
               (Bil.BinOp (Bil.AND, Bil.Var c,
                           eq (Bil.Var t) (wexp 0x400020L))));
        check "INST-07 tail is the original false continuation"
          (match Jmp.kind tail with
           | Goto (Direct tid) -> Tid.equal tid tids.(3)
           | _ -> false);
        check "INST-07 arm values"
          (Ws.equal (AI.find_word 64 (in_state sol tids.(1)) p1)
             (Ws.singleton (w 0x400010L))
          && Ws.equal (AI.find_word 64 (in_state sol tids.(2)) p2)
               (Ws.singleton (w 0x400020L)));
        check "INST-07 false edge delivered"
          (not (AI.equal (in_state sol tids.(3)) AI.bottom)));

    (* The staged builder finalizes the complete rewrite itself: the source
       arms and the new case block are SSA-complete, and an old target that
       gains the source edge gains the matching phi operand. *)
    pin "INST-08" "the materialized sub is SSA-complete on the source/new edges"
      (fun () ->
        let target = x86_target () in
        let synth = Hike.Synth.empty in
        let t = v64 "ssa_t" and x = v64 "ssa_x" and y = v64 "ssa_y" in
        let input = v64 "ssa_in" in
        let sub, tids =
          sub_of "ssa_dispatch"
            [ [ Def.create t (Bil.Var input); Def.create x (Bil.Var input) ],
              [ (1, fun _ -> Jmp.create (Goto (Indirect (Bil.Var t)))) ];
              [ Def.create x (Bil.Var input) ], [ (2, mk_goto) ];
              [ Def.create y (Bil.Var x) ], [ (3, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let addrs = [| 0x100000L; 0x100010L; 0x100020L; 0x100030L |] in
        let addr_of tid =
          let rec find i =
            if Tid.equal tids.(i) tid then addrs.(i)
            else if i + 1 < Array.length tids then find (i + 1)
            else assert false
          in
          Addr.of_int64 (find 0)
        in
        let sub =
          Term.map blk_t sub ~f:(fun b ->
              Term.set_attr b address (addr_of (Term.tid b)))
        in
        let block_addrs =
          Term.enum blk_t sub
          |> Seq.fold ~init:Addr.Map.empty ~f:(fun m b ->
                 Core.Map.set m
                   ~key:
                     (Base.Option.value_exn (Term.get_attr b address))
                   ~data:(Term.tid b))
        in
        let case_addr = 0x200000L in
        let case_tid = Tid.create () in
        let case_blk =
          let b =
            Blk.create ~tid:case_tid ~jmps:[ Hike_return.create () ] ()
          in
          Term.set_attr b address (Addr.of_int64 case_addr)
        in
        let fragment = Sub.create ~name:"ssa_case" ~blks:[ case_blk ] () in
        let source = source_blk sub tids.(0) in
        let jmp = indirect_jmp source in
        let targets =
          [ (w 0x100020L, tids.(2)); (w case_addr, case_tid) ]
        in
        let rewritten, _trap =
          D.rewrite_source
            { D.base = None; targets; sub }
            ~kind:D.Jump ~blk:source ~jmp
            ~is_intra:(fun _ -> true) ~false_target:None
        in
        let working = Term.update blk_t sub rewritten in
        let edges =
          Term.enum jmp_t rewritten
          |> Seq.filter_map ~f:(fun j ->
                 match Jmp.kind j with
                 | Goto (Direct d) -> Some (tids.(0), d)
                 | _ -> None)
          |> Seq.to_list
        in
        let delta =
          Hike.Cfg_complete.materialize_site ~target ~abi:sysv
            ~callee_tid:Fun.id ~rip_address:(fun _ -> false) ~claim:Fun.id
            ~synth ~block_addrs ~old:sub ~working
            ~cases:[ (case_addr, case_tid, fragment) ] ~edges
        in
        let built = delta.Hike.Cfg_complete.delta_sub in
        Hike_test.Verify_ssa.sub ~synth ~target ~what:"INST-08" built;
        let src = source_blk built tids.(0) in
        let arms = Term.enum jmp_t src |> Seq.to_list in
        check "INST-08 source arms are direct"
          (List.length arms = 2
          && List.for_all
               (fun j ->
                 match Jmp.kind j with Goto (Direct _) -> true | _ -> false)
               arms);
        check "INST-08 new case block present"
          (Option.is_some (Term.find blk_t built case_tid)
          && Core.Set.mem delta.Hike.Cfg_complete.new_blocks case_tid);
        let b = source_blk built tids.(2) in
        check "INST-08 old target gained the source phi operand"
          (Term.enum phi_t b
          |> Seq.exists ~f:(fun p ->
                 Phi.values p
                 |> Seq.exists ~f:(fun (src, _) -> Tid.equal src tids.(0)))));
  ]

let () = run "dispatch_install" tests
