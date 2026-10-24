(* Definition queries use the state before that definition. Rewrites retain
   existing states; newly introduced definitions have no analysis state. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

(* The def with the given tid in the sub. *)
let find_def (sub : sub term) (dtid : Tid.t) : def term =
  Term.enum blk_t sub
  |> Seq.concat_map ~f:(Term.enum def_t)
  |> Seq.find ~f:(fun d -> Tid.equal (Term.tid d) dtid)
  |> Base.Option.value_exn

(* Promote rewrite over the fixture facts: map the stamped sub and mint
   the hike_argN defs. *)
let promote_rewrite_synth (facts : Hike.Kb.facts) (sub : sub term) :
    Hike.Synth.table * sub term =
  let prog = Program.create ~subs:[ sub ] () in
  let ctx =
    Hike.Sections.attribute ~facts ~word:8 ~entry:Hike.Stack_model.segment_base
      ~spans:[] prog
  in
  let facts, ctx, rewrites =
    fixture_ownership ~word:8 ~entry:Hike.Stack_model.segment_base ~facts
      ~ctx ~spans:[] prog
  in
  let synth, prog =
    Hike.Promote.rewrite_program ~word:8 ~entry:Hike.Stack_model.segment_base
      ~facts ~trees:ctx.sub_trees ~rewrites prog
  in
  (synth, Term.first sub_t prog |> Base.Option.value_exn)

let tests =
  [
    case "definition queries follow the block's transfer order" (fun () ->
        let x = v64 "et_x" and y = v64 "et_y" in
        let dx = Def.create x (Bil.Int (Cbat_word.to_word (w64 7))) in
        let dy = Def.create y Bil.(var x + int (Cbat_word.to_word (w64 1))) in
        let facts, sub =
          fixture_facts_sub ~synth:Hike.Synth.empty
            (straight_sub "et_chain" [ dx; dy ])
        in
        let block = Term.first blk_t sub |> Base.Option.value_exn in
        let dx = find_def sub (Term.tid dx)
        and dy = find_def sub (Term.tid dy) in
        let pre, _ = Core.Map.find_exn facts.envs (Term.tid block) in
        check_bound "first definition receives the block pre-state"
          (Vsa.env_tag dx) (AI.equal pre);
        let x = Def.lhs dx and y = Def.lhs dy in
        let query ?def value =
          match facts.denote ~blk:block ?def (Bil.Var value) with
          | Ok value -> value
          | Error _ -> Alcotest.fail "definition query failed"
        in
        check_ws "x before its definition" (Ws.top 64) (query ~def:dx x);
        check_ws "x after its definition"
          (Ws.singleton (w64 7))
          (query ~def:dy x);
        check_ws "y after both definitions" (Ws.singleton (w64 8)) (query y));
    (* The seam's gate-free answers, crossed through [facts.denote]. *)
    case "a memory-bearing query on a tagged def answers in its tag env"
      (fun () ->
        let facts0 =
          Kb.build
            ~lookup:(fun _ -> None)
            ~block_envs:Tid.Map.empty
            ~block_addrs:(Core.Map.empty (module Addr))
            ~target:(x86_target ()) ~defs:Var.Map.empty
        in
        let m = memv "ets_m" in
        let y = v64 "ets_y" in
        let addr_w = w64 0x1000 in
        let mem_idx =
          { Cbat_vsa.Mem.addr_width = 64; Cbat_vsa.Mem.addressable_width = 8 }
        in
        let cell =
          Mem.add (Mem.top mem_idx)
            ~key:
              (match Mem.Key.of_wordset (Ws.singleton addr_w) with
              | [ k ] -> k
              | _ -> failwith "key")
            ~data:
              (Mem.Val.create
                 (Ws.singleton (Cbat_word.of_int ~width:32 7))
                 LittleEndian)
        in
        let tag_env = AI.add_memory (anchored_entry ()) ~key:m ~data:cell in
        let blk4 =
          blk_of_defs [ Def.create y (Bil.Int (Cbat_word.to_word (w64 0))) ]
        in
        let d4 =
          Vsa.set_env_tag tag_env
            (Term.first def_t blk4 |> Base.Option.value_exn)
        in
        check "ENV-09"
          (match
             facts0.denote ~blk:blk4 ~def:d4
               (Bil.Load
                  ( Bil.Var m,
                    Bil.Int (Cbat_word.to_word addr_w),
                    LittleEndian,
                    `r32 ))
           with
          | Ok ws -> Ws.equal ws (Ws.singleton (Cbat_word.of_int ~width:32 7))
          | Error _ -> false));
    (* Env5: an untagged def answers TOP even when the record's pre binds
       the queried var. *)
    case "an untagged def answers TOP (minted after the boundary)" (fun () ->
        let x = v64 "ets_x" in
        let y = v64 "ets_y" in
        let pre5 = mk_env [ (x, Ws.singleton (w64 5)) ] in
        let blk5 = blk_of_defs [ Def.create y (Bil.Var x) ] in
        let d5 = Term.first def_t blk5 |> Base.Option.value_exn in
        let facts5 =
          Kb.build
            ~lookup:(fun _ -> None)
            ~block_envs:(Tid.Map.singleton (Term.tid blk5) (pre5, pre5))
            ~block_addrs:(Core.Map.empty (module Addr))
            ~target:(x86_target ()) ~defs:Var.Map.empty
        in
        check "ENV-10"
          (match facts5.denote ~blk:blk5 ~def:d5 (Bil.Var x) with
          | Ok ws -> Ws.is_top ws
          | Error _ -> false));
    (* Env6: a no-def query evaluates in the block's post state. *)
    case "a no-def query evaluates in the post state" (fun () ->
        let x = v64 "ets_x" in
        let pre6 = mk_env [ (x, Ws.singleton (w64 1)) ] in
        let post6 = mk_env [ (x, Ws.singleton (w64 2)) ] in
        let blk6 = blk_of_defs [] in
        let facts6 =
          Kb.build
            ~lookup:(fun _ -> None)
            ~block_envs:(Tid.Map.singleton (Term.tid blk6) (pre6, post6))
            ~block_addrs:(Core.Map.empty (module Addr))
            ~target:(x86_target ()) ~defs:Var.Map.empty
        in
        check "ENV-11"
          (match facts6.denote ~blk:blk6 (Bil.Var x) with
          | Ok ws -> Ws.equal ws (Ws.singleton (w64 2))
          | Error _ -> false));
    case "promotion preserves existing states and leaves new arguments untagged"
      (fun () ->
        let m = memv "etp_m" in
        let store =
          Def.create m
            (Bil.Store
               ( Bil.Var m,
                 Bil.BinOp
                   (Bil.PLUS, Bil.Var sp, Bil.Int (Cbat_word.to_word (w64 16))),
                 Bil.Int (Cbat_word.to_word (w64 9)),
                 LittleEndian,
                 `r64 ))
        in
        let sub, _ =
          sub_of "etp_promote"
            [
              ( [ store ],
                [
                  ( 1,
                    fun t ->
                      Jmp.create
                        (Call
                           (Call.create ~return:(Direct t)
                              ~target:(Indirect (Bil.Var (v64 "etp_tptr")))
                              ())) );
                ] );
              ([], [ (0, mk_ret) ]);
            ]
        in
        let facts, before = fixture_facts_sub ~synth:Hike.Synth.empty sub in
        let synth, after = promote_rewrite_synth facts before in
        let old_store = find_def before (Term.tid store) in
        let new_store = find_def after (Term.tid store) in
        check "store was rewritten"
          (not (Exp.equal (Def.rhs old_store) (Def.rhs new_store)));
        check "rewritten store retains the same state"
          (match (Vsa.env_tag old_store, Vsa.env_tag new_store) with
          | Some old, Some current -> AI.equal old current
          | _ -> false);
        let block = Term.first blk_t after |> Base.Option.value_exn in
        let arguments =
          Term.enum def_t block
          |> Seq.filter ~f:(fun d ->
              Hike.Stack_model.is_call_arg synth (Def.lhs d))
          |> Seq.to_list
        in
        match arguments with
        | [ arg ] -> (
            check "new argument has no analysis state"
              (Option.is_none (Vsa.env_tag arg));
            match facts.denote ~blk:block ~def:arg (Def.rhs arg) with
            | Ok value ->
                check_ws "new argument query is unknown" (Ws.top 64) value
            | Error _ -> Alcotest.fail "new argument query failed")
        | _ -> Alcotest.fail "expected one outgoing stack argument");
  ]

let () = run "env_tag" [ ("queries", tests) ]
