open Bap.Std
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

let eliminate sub =
  let target = x86_target () and synth = Hike.Synth.empty in
  let ssa = ssa_of_subs [ sub ] (Sub.name sub) in
  let result = Hike.Dce.dce_sub ~synth ~target ssa in
  Hike_test.Verify_ssa.sub ~synth ~target ~what:"dead-code elimination" result;
  result

let check_definitions expected sub =
  let actual =
    Term.enum blk_t sub
    |> Seq.concat_map ~f:(Term.enum def_t)
    |> Seq.map ~f:(fun d -> Var.base (Def.lhs d))
    |> Seq.to_list
  in
  let variables = Alcotest.(list (testable Var.pp Var.equal)) in
  Alcotest.check variables "remaining definitions"
    (List.sort Var.compare expected)
    (List.sort Var.compare actual)

let tests =
  [
    case "dead flag chains disappear; named values, loads and stores remain"
      (fun () ->
        let abi = Hike.Abi.of_target (x86_target ()) in
        let temporary =
          Var.create ~is_virtual:true "dead_temporary" (Type.Imm 64)
        in
        let loaded = Var.create ~is_virtual:true "unread_load" (Type.Imm 64) in
        let named = v64 "unread_named" and memory = memv "memory" in
        let sub, _ =
          raw_sub_of "dead_chain"
            [
              ( [
                  Def.create temporary
                    Bil.(var (int_param 0) lxor var (int_param 1));
                  Def.create abi.Hike.Abi.zero_flag
                    Bil.(var temporary = var (int_param 2));
                  Def.create named
                    Bil.(var (int_param 0) lxor var (int_param 3));
                  Def.create loaded
                    (Bil.Load
                       ( Bil.Var memory,
                         Bil.Var (int_param 0),
                         LittleEndian,
                         `r64 ));
                  Def.create memory
                    (Bil.Store
                       ( Bil.Var memory,
                         Bil.Var (int_param 0),
                         Bil.Var (int_param 1),
                         LittleEndian,
                         `r64 ));
                ],
                [ (0, mk_ret) ] );
            ]
        in
        check_definitions [ named; loaded; memory ] (eliminate sub));
    case "a flag used by a conditional branch remains" (fun () ->
        let flag = (Hike.Abi.of_target (x86_target ())).Hike.Abi.zero_flag in
        let sub, _ =
          raw_sub_of "live_flag"
            [
              ( [ Def.create flag Bil.(var (int_param 0) = var (int_param 1)) ],
                [ (1, fun t -> mk_jmp_to t (Bil.Var flag)); (2, mk_goto) ] );
              ([], [ (0, mk_ret) ]);
              ([], [ (0, mk_ret) ]);
            ]
        in
        check_definitions [ flag ] (eliminate sub));
  ]

let () = run "dead-code elimination" [ ("liveness", tests) ]
