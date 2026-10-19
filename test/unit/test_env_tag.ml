(* Env Tag pins: the stamp round-trip, absence, slot survival through
   def rewrites, the seam's gate-free answers, and the sweep's fold
   alignment.  One Alcotest group per pin; each pin builds its own
   fixture, so no state crosses pins. *)

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
    Hike.Sections.attribute ~facts ~word:8
      ~entry:Hike.Stack_model.segment_base ~spans:[] prog
  in
  let synth, prog =
    Hike.Promote.rewrite_program ~word:8
      ~entry:Hike.Stack_model.segment_base ~facts ~spans:[] ~ctx
      prog
  in
  (synth, Term.first sub_t prog |> Base.Option.value_exn)

let promote_rewrite facts sub = snd (promote_rewrite_synth facts sub)

let tests : unit Alcotest.test list =
  [
    (* Env1: the stamp round-trip and the pointer payload. *)
    pin "ENV-01" "a def outside the boundary has no Env Tag" (fun () ->
        let v = v64 "et_v" in
        let d = Def.create v (Bil.Int (Cbat_word.to_word (w64 5))) in
        check "ENV-01" (Option.is_none (Vsa.env_tag d)));





    (* Env3: the sweep stamps each def with the env its own transfer
       reads — the chain advances through [denote_def] and the final env
       is the block post. *)
    pin "ENV-06" "the first def's tag is the block pre" (fun () ->
        let x = v64 "et_x" in
        let y = v64 "et_y" in
        let dx = Def.create x (Bil.Int (Cbat_word.to_word (w64 7))) in
        let dy =
          Def.create y
            (Bil.BinOp (Bil.PLUS, Bil.Var x, Bil.Int (Cbat_word.to_word (w64 1))))
        in
        let sub = straight_sub "et_chain" [ dx; dy ] in
        let envs, sub', _ =
          produce ~synth:Hike.Synth.empty (x86_target ()) (Program.create ~subs:[ sub ] ()) sub
        in
        let blk = Term.first blk_t sub' |> Base.Option.value_exn in
        let pre, _ = Core.Map.find_exn envs (Term.tid blk) in
        let dx' = find_def sub' (Term.tid dx) in
        let tag_dx = Vsa.env_tag dx' in
        check "ENV-06"
          (match tag_dx with Some e -> AI.equal e pre | None -> false));

    pin "ENV-07" "the second def's tag is the first transfer's product" (fun () ->
        let x = v64 "et_x" in
        let y = v64 "et_y" in
        let dx = Def.create x (Bil.Int (Cbat_word.to_word (w64 7))) in
        let dy =
          Def.create y
            (Bil.BinOp (Bil.PLUS, Bil.Var x, Bil.Int (Cbat_word.to_word (w64 1))))
        in
        let sub = straight_sub "et_chain" [ dx; dy ] in
        let _, sub', _ =
          produce ~synth:Hike.Synth.empty (x86_target ()) (Program.create ~subs:[ sub ] ()) sub
        in
        let dx' = find_def sub' (Term.tid dx) in
        let dy' = find_def sub' (Term.tid dy) in
        let tag_dx = Vsa.env_tag dx' in
        let tag_dy = Vsa.env_tag dy' in
        check "ENV-07"
          (match (tag_dx, tag_dy) with
          | Some e1, Some e2 -> AI.equal e2 (Vsa.Test_seam.denote_def ~synth:Hike.Synth.empty dx' e1)
          | _ -> false));



    (* The seam's gate-free answers, crossed through [facts.denote]. *)
    pin "ENV-09" "a memory-bearing query on a tagged def answers in its tag env"
      (fun () ->
        let facts0 =
          Kb.build ~lookup:(fun _ -> None) ~block_envs:Tid.Map.empty
            ~block_addrs:(Core.Map.empty (module Addr))
            ~target:(x86_target ())
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
    pin "ENV-10" "an untagged def answers TOP (minted after the boundary)"
      (fun () ->
        let x = v64 "ets_x" in
        let y = v64 "ets_y" in
        let pre5 = mk_env [ (x, Ws.singleton (w64 5)) ] in
        let blk5 = blk_of_defs [ Def.create y (Bil.Var x) ] in
        let d5 = Term.first def_t blk5 |> Base.Option.value_exn in
        let facts5 =
          Kb.build ~lookup:(fun _ -> None)
            ~block_envs:(Tid.Map.singleton (Term.tid blk5) (pre5, pre5))
            ~block_addrs:(Core.Map.empty (module Addr))
            ~target:(x86_target ())
        in
        check "ENV-10"
          (match facts5.denote ~blk:blk5 ~def:d5 (Bil.Var x) with
          | Ok ws -> Ws.is_top ws
          | Error _ -> false));

    (* Env6: a no-def query evaluates in the block's post state. *)
    pin "ENV-11" "a no-def query evaluates in the post state" (fun () ->
        let x = v64 "ets_x" in
        let pre6 = mk_env [ (x, Ws.singleton (w64 1)) ] in
        let post6 = mk_env [ (x, Ws.singleton (w64 2)) ] in
        let blk6 = blk_of_defs [] in
        let facts6 =
          Kb.build ~lookup:(fun _ -> None)
            ~block_envs:(Tid.Map.singleton (Term.tid blk6) (pre6, post6))
            ~block_addrs:(Core.Map.empty (module Addr))
            ~target:(x86_target ())
        in
        check "ENV-11"
          (match facts6.denote ~blk:blk6 (Bil.Var x) with
          | Ok ws -> Ws.equal ws (Ws.singleton (w64 2))
          | Error _ -> false));

    (* Env7: the VSA_DEBUG differential's invariant on a multi-def block —
       every def-level query's tag answer equals the raw replay. *)


    (* The promote path: [Hike.Promote.rewrite_program] maps the stamped
       sub and mints the hike_argN defs; a mapped-but-surviving def still
       answers from its tag, a minted def from TOP. *)
    pin "ENV-13" "the promote rewrite actually rewrote the surviving def"
      (fun () ->
        let m = memv "etp_m" in
        let x = v64 "etp_x" in
        let dx = Def.create x (Bil.Int (Cbat_word.to_word (w64 7))) in
        let store =
          Def.create m
            (Bil.Store
               ( Bil.Var m,
                 Bil.BinOp
                   ( Bil.PLUS,
                     Bil.Var sp,
                     Bil.Int (Cbat_word.to_word (w64 16)) ),
                 Bil.Int (Cbat_word.to_word (w64 9)),
                 LittleEndian,
                 `r64 ))
        in
        let sub, _ =
          sub_of "etp_promote"
            [ [ dx; store ],
              [ (1,
                 fun t ->
                   Jmp.create
                     (Call
                        (Call.create ~return:(Direct t)
                           ~target:(Indirect (Bil.Var (v64 "etp_tptr")))
                           ()))) ];
              [], [ (0, mk_ret) ] ]
        in
        let facts, sub' = fixture_facts_sub ~synth:Hike.Synth.empty sub in
        let sub'' = promote_rewrite facts sub' in
        let store'' = find_def sub'' (Term.tid store) in
        check "ENV-13"
          (not (Exp.equal (Def.rhs store'') (Def.rhs store))));

    pin "ENV-14" "the promote rewrite keeps a mapped def's Env Tag"
      (fun () ->
        let m = memv "etp_m" in
        let x = v64 "etp_x" in
        let dx = Def.create x (Bil.Int (Cbat_word.to_word (w64 7))) in
        let store =
          Def.create m
            (Bil.Store
               ( Bil.Var m,
                 Bil.BinOp
                   ( Bil.PLUS,
                     Bil.Var sp,
                     Bil.Int (Cbat_word.to_word (w64 16)) ),
                 Bil.Int (Cbat_word.to_word (w64 9)),
                 LittleEndian,
                 `r64 ))
        in
        let sub, _ =
          sub_of "etp_promote"
            [ [ dx; store ],
              [ (1,
                 fun t ->
                   Jmp.create
                     (Call
                        (Call.create ~return:(Direct t)
                           ~target:(Indirect (Bil.Var (v64 "etp_tptr")))
                           ()))) ];
              [], [ (0, mk_ret) ] ]
        in
        let facts, sub' = fixture_facts_sub ~synth:Hike.Synth.empty sub in
        let sub'' = promote_rewrite facts sub' in
        let store'' = find_def sub'' (Term.tid store) in
        check "ENV-14" (Base.Option.is_some (Vsa.env_tag store'')));



    (* Env9: the fresh hike_argN def carries no tag and answers TOP. *)
    pin "ENV-16" "the minted hike_argN def has no Env Tag" (fun () ->
        let m = memv "etp_m" in
        let x = v64 "etp_x" in
        let dx = Def.create x (Bil.Int (Cbat_word.to_word (w64 7))) in
        let store =
          Def.create m
            (Bil.Store
               ( Bil.Var m,
                 Bil.BinOp
                   ( Bil.PLUS,
                     Bil.Var sp,
                     Bil.Int (Cbat_word.to_word (w64 16)) ),
                 Bil.Int (Cbat_word.to_word (w64 9)),
                 LittleEndian,
                 `r64 ))
        in
        let sub, _ =
          sub_of "etp_promote"
            [ [ dx; store ],
              [ (1,
                 fun t ->
                   Jmp.create
                     (Call
                        (Call.create ~return:(Direct t)
                           ~target:(Indirect (Bil.Var (v64 "etp_tptr")))
                           ()))) ];
              [], [ (0, mk_ret) ] ]
        in
        let facts, sub' = fixture_facts_sub ~synth:Hike.Synth.empty sub in
        let synth, sub'' = promote_rewrite_synth facts sub' in
        let arg =
          Term.enum def_t (Term.first blk_t sub'' |> Base.Option.value_exn)
          |> Seq.find ~f:(fun d ->
              Hike.Stack_model.is_call_arg synth (Def.lhs d))
        in
        check_bound "ENV-16" arg (fun d ->
            Base.Option.is_none (Vsa.env_tag d)));


  ]

let () = run "env_tag" tests
