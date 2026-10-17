open Bap.Std
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

let tests : unit Alcotest.test list =
  [
    pin "FLOW-01"
      "the BIR flow solver applies construct transfers in CFG direction and term order"
      (fun () ->
        let x = v64 "flow_x" and y = v64 "flow_y" in
        let sub, tids =
          sub_of "bir_flow"
            [ [ Def.create x (Bil.Int (Cbat_word.to_word (w64 0))) ],
              [ (1, mk_goto) ];
              [ Def.create y (Bil.Var x) ],
              [ (1, mk_goto); (2, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let middle = Term.find blk_t sub tids.(1) |> Base.Option.value_exn in
        let phi =
          Phi.of_list (v64 "flow_phi")
            [ (tids.(0), Bil.Var x); (tids.(1), Bil.Var y) ]
        in
        let builder =
          Blk.Builder.init ~copy_defs:true ~copy_phis:true ~copy_jmps:true middle
        in
        Blk.Builder.add_phi builder phi;
        let middle = Blk.Builder.result builder in
        let sub =
          Term.map blk_t sub ~f:(fun blk ->
              if Tid.equal (Term.tid blk) tids.(1) then middle else blk)
        in
        let add state n = Core.Set.add state n in
        let def state _ = add state 1 in
        let phi state _ = add state 2 in
        let jmp state j =
          match Jmp.kind j with
          | Goto _ -> Core.Set.remove state 1
          | _ -> add state 8
        in
        let graph = Sub.to_graph sub in
        let initial = Tid.Map.singleton Graphs.Tid.start Core.Int.Set.empty in
        let forward =
          Hike_bir_flow.run ~graph ~sub ~rev:false ~initial
            ~default:Core.Int.Set.empty ~equal:Core.Set.equal
            ~merge:Core.Set.union
            ~def ~phi ~jmp
        in
        let forward_entry =
          Core.Map.find_exn forward.after tids.(0)
        in
        let forward_exit =
          Core.Map.find_exn forward.before tids.(2)
        in
        let reverse =
          Hike_bir_flow.run ~graph ~sub ~rev:true
            ~initial:(Tid.Map.singleton Graphs.Tid.exit (add Core.Int.Set.empty 16))
            ~default:Core.Int.Set.empty ~equal:Core.Set.equal
            ~merge:Core.Set.union
            ~def ~phi ~jmp
        in
        let reverse_entry =
          Core.Map.find_exn reverse.before tids.(0)
        in
        check "forward jmp transfer" (not (Core.Set.mem forward_entry 1));
        check "forward phi transfer" (Core.Set.mem forward_exit 2);
        check "reverse def transfer" (Core.Set.mem reverse_entry 1);
        check "reverse phi transfer" (Core.Set.mem reverse_entry 2);
        check "reverse ret transfer" (Core.Set.mem reverse_entry 8);
        check "reverse exit seed" (Core.Set.mem reverse_entry 16));

    pin "FLOW-02"
      "liveness (compiled gen/kill) equals the closure-driven reverse flow over a loop with in-block kills and a non-killing phi"
      (fun () ->
        let x = v64 "live_x" and y = v64 "live_y" and z = v64 "live_z" in
        let sub, tids =
          sub_of "bir_live"
            [ [ Def.create x (Bil.Var y); Def.create y (Bil.Var z) ],
              [ (1, mk_goto) ];
              [ Def.create z (Bil.BinOp (Bil.PLUS, Bil.Var x, Bil.Var z));
                Def.create x (Bil.Var z) ],
              [ (1, mk_goto); (2, mk_goto) ];
              [ Def.create y (Bil.Var x) ], [ (0, mk_ret) ] ]
        in
        let loop = Term.find blk_t sub tids.(1) |> Base.Option.value_exn in
        let builder =
          Blk.Builder.init ~copy_defs:true ~copy_phis:true ~copy_jmps:true loop
        in
        Blk.Builder.add_phi builder
          (Phi.of_list x [ (tids.(0), Bil.Var y); (tids.(1), Bil.Var z) ]);
        let loop = Blk.Builder.result builder in
        let sub =
          Term.map blk_t sub ~f:(fun blk ->
              if Tid.equal (Term.tid blk) tids.(1) then loop else blk)
        in
        let set vs = Core.Set.of_list (module Var) vs in
        let dreads d = Exp.free_vars (Def.rhs d) in
        let dwrites d = set [ Def.lhs d ] in
        let preads p =
          Phi.values p
          |> Seq.fold ~init:Var.Set.empty ~f:(fun acc (_, e) ->
                 Core.Set.union acc (Exp.free_vars e))
        in
        let jreads j = Exp.free_vars (Jmp.cond j) in
        let graph = Sub.to_graph sub in
        let initial = Tid.Map.singleton Graphs.Tid.exit (set [ z ]) in
        let reference =
          Hike_bir_flow.run ~graph ~sub ~rev:true ~initial
            ~default:Var.Set.empty ~equal:Core.Set.equal ~merge:Core.Set.union
            ~def:(fun live d ->
                Core.Set.union (Core.Set.diff live (dwrites d)) (dreads d))
            ~phi:(fun live p -> Core.Set.union live (preads p))
            ~jmp:(fun live j -> Core.Set.union live (jreads j))
        in
        let compiled =
          Hike_bir_flow.liveness ~graph ~sub ~initial
            ~def:(fun d -> (dwrites d, dreads d))
            ~phi:(fun p -> (Var.Set.empty, preads p))
            ~jmp:(fun j -> (Var.Set.empty, jreads j))
        in
        let same a b = Core.Map.equal Core.Set.equal a b in
        check "before" (same reference.before compiled.before);
        check "after" (same reference.after compiled.after);
        check "loop carries z live in"
          (Core.Set.mem (Core.Map.find_exn compiled.before tids.(1)) z));
  ]

let () = run "bir_flow" tests
