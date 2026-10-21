(* Indirect-target resolution pins. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

(* A singleton word-set from an int64 address. *)
let ws_singleton (v : int64) : Cbat_vsa.WordSet.t =
  Cbat_vsa.WordSet.singleton (w64 (Int64.to_int v))

(* The j-th jmp of the i-th block. *)
let jmps_of_blk sub i =
  List.nth (Term.enum blk_t sub |> Seq.to_list) i
  |> Term.enum jmp_t |> Seq.to_list

let tests : unit Alcotest.test list =
  [
    ( "target resolution",
      [
        case "only a known singleton becomes a direct call" (fun () ->
            let callee = Tid.for_name "resolved_callee" in
            let lookup address =
              if Int64.equal address 0x1000L then Some callee else None
            in
            let check_target =
              Alcotest.(check (option (testable Tid.pp Tid.equal)))
            in
            List.iter
              (fun (name, targets, expected) ->
                check_target name expected
                  (Hike.Resolve.resolve_target ~lookup targets))
              [
                ("known singleton", ws_singleton 0x1000L, Some callee);
                ( "multiple destinations",
                  Ws.union (ws_singleton 0x1000L) (ws_singleton 0x1008L),
                  None );
                ("foreign singleton", ws_singleton 0x9999L, None);
                ("unknown", Ws.top 64, None);
                ("unreachable", Ws.bottom 64, None);
              ]);
      ] );
    ( "return epilogues",
      List.map
        (fun (name, transfer, returns) ->
          case name (fun () ->
              let target = v64 "loaded_return_address" in
              let load =
                Def.create target
                  (Bil.Load
                     ( Bil.Var (memv "return_memory"),
                       Bil.Var sp,
                       LittleEndian,
                       `r64 ))
              in
              let sub, _ =
                sub_of "return_epilogue"
                  [
                    ([ load ], [ (1, transfer target) ]); ([], [ (0, mk_ret) ]);
                  ]
              in
              let _, completed, _ =
                produce ~synth:Hike.Synth.empty (x86_target ())
                  (Program.create ~subs:[ sub ] ())
                  sub
              in
              match jmps_of_blk completed 0 with
              | [ jump ] -> (
                  Alcotest.(check bool)
                    "canonical return" returns (Hike_return.is_jmp jump);
                  if not returns then
                    match Jmp.kind jump with
                    | Call call ->
                        check "the real call keeps its target"
                          (match Call.target call with
                          | Indirect (Bil.Var v) -> Var.same v target
                          | _ -> false);
                        check "the real call keeps its return edge"
                          (Call.return call <> None)
                    | _ -> Alcotest.fail "expected a real call")
              | _ -> Alcotest.fail "expected one completed transfer"))
        [
          ( "a tail call through the return address becomes a return",
            (fun target _ ->
              Jmp.create
                (Call (Call.create ~target:(Indirect (Bil.Var target)) ()))),
            true );
          ( "a goto through the return address becomes a return",
            (fun target _ -> Jmp.create (Goto (Indirect (Bil.Var target)))),
            true );
          ( "a returning call through the same value remains a real call",
            (fun target continuation ->
              Jmp.create
                (Call
                   (Call.create ~return:(Direct continuation)
                      ~target:(Indirect (Bil.Var target)) ()))),
            false );
        ] );

    (* J3: a foreign pointer target is untouched by the completion. *)
    pin "RES-15" "T22-J3: a foreign pointer target is untouched by the rewrite"
      (fun () ->
        let j3_t = v64 "t22_j3_t" in
        let j3_ld = Def.create j3_t (Bil.Int (Cbat_word.to_word (q64 0x400000L))) in
        let j3, _ =
          sub_of "t22_foreign"
            [ [ j3_ld ], [ (1, fun _ -> Jmp.create (Goto (Indirect (Bil.Var j3_t)))) ];
              [], [ (0, mk_ret) ] ]
        in
        let _, j3', _ =
          produce ~synth:Hike.Synth.empty (x86_target ()) (Program.create ~subs:[ j3 ] ()) j3
        in
        check "RES-15"
          (match jmps_of_blk j3' 0 with
           | [ j ] -> (
               match Jmp.kind j with Goto (Indirect _) -> true | _ -> false)
           | _ -> false));

    pin "RES-23" "the completion names the false edge and carries each destination once"
      (fun () ->
        let edge t = Jmp.create ~cond:(Bil.Var (v64 "c")) (Goto (Direct t)) in
        let jmps_of (sub : sub term) (i : int) : jmp term list =
          let blks = Term.enum blk_t sub |> Seq.to_list in
          Term.enum jmp_t (Base.List.nth_exn blks i) |> Seq.to_list
        in
        let targets (js : jmp term list) : tid list =
          Base.List.filter_map js ~f:(fun j ->
              match Jmp.kind j with Goto (Direct t) -> Some t | _ -> None)
        in
        let unconditional (j : jmp term) : bool =
          match Jmp.cond j with
          | Bil.Int w -> Word.equal w (Word.one 1)
          | _ -> false
        in
        (* a guard plus an explicit goto to the SAME block: one edge *)
        let sub, tids =
          sub_of "edge_dup" [ ([], [ (1, edge); (1, mk_goto) ]); ([], [ (0, mk_ret) ]) ]
        in
        (match jmps_of (Hike.Cfg_complete.materialize_fallthroughs sub) 0 with
         | [ j ] ->
             check "RES-23a: one unconditional edge to the shared target"
               (unconditional j
                && (match Jmp.kind j with
                    | Goto (Direct t) -> Tid.equal t tids.(1)
                    | _ -> false))
         | _ -> check "RES-23a: one edge" false);
        (* a lone conditional goto: the false edge (the term-order
           successor, block 1) becomes explicit *)
        let sub, tids =
          sub_of "edge_implicit"
            [ ([], [ (2, edge) ]); ([], [ (0, mk_ret) ]); ([], [ (0, mk_ret) ]) ]
        in
        check "RES-23b: the guard and its named false edge"
          (targets (jmps_of (Hike.Cfg_complete.materialize_fallthroughs sub) 0)
           = [ tids.(2); tids.(1) ]);
        (* two distinct destinations stay two *)
        let sub, tids =
          sub_of "edge_two"
            [ ([], [ (2, edge); (1, mk_goto) ]);
              ([], [ (0, mk_ret) ]);
              ([], [ (0, mk_ret) ]) ]
        in
        check "RES-23c: distinct destinations stay"
          (targets (jmps_of (Hike.Cfg_complete.materialize_fallthroughs sub) 0)
           = [ tids.(2); tids.(1) ]));

    (* A re-lifted block joins the program through the chain's own
       normalizers: a def the lifter gave two memory nodes fissions,
       so the one-def-one-node invariant holds for lifted code too. *)
  ]

let () = run "resolve" tests
