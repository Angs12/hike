(* Env Tag pins: the stamp round-trip, absence, slot survival through
   def rewrites, and the sweep's fold alignment. *)
open Bap.Std
open Bap_core_theory
open Test_common
open Test_fixtures

let find_def (sub : sub term) (dtid : Tid.t) : def term =
  Term.enum blk_t sub
  |> Seq.concat_map ~f:(Term.enum def_t)
  |> Seq.find ~f:(fun d -> Tid.equal (Term.tid d) dtid)
  |> Base.Option.value_exn

let run () =
(  (* Env1: the stamp round-trip and the pointer payload. *)
  let v = v64 "et_v" in
  let d = Def.create v (Bil.Int (Cbat_word.to_word (w64 5))) in
  let env = anchored_entry () in
  check "Env1: a def outside the boundary has no Env Tag"
    (Option.is_none (Vsa.env_tag d));
  let stamped = Vsa.set_env_tag env d in
  check "Env1: the stamped def reads its before-env back"
    (match Vsa.env_tag stamped with Some e -> AI.equal e env | None -> false);
  check "Env1: the tag carries the env pointer, not a copy"
    (match Vsa.env_tag stamped with
     | Some e -> Base.phys_equal e env
     | None -> false);

  (* Env2: value slots survive the post-boundary def rewrites. *)
  let rewritten =
    Def.with_rhs stamped (Bil.Int (Cbat_word.to_word (w64 6)))
  in
  check "Env2: the Env Tag survives Def.with_rhs"
    (match Vsa.env_tag rewritten with
     | Some e -> AI.equal e env
     | None -> false);
  let mapped = Term.map def_t (blk_of_defs [ stamped ]) ~f:(fun x -> x) in
  check "Env2: the Env Tag survives Term.map"
    (match Term.first def_t mapped with
     | Some d -> (match Vsa.env_tag d with Some e -> AI.equal e env | None -> false)
     | None -> false);

  (* Env3: the sweep stamps each def with the env its own transfer
     reads — the chain advances through [denote_def] and the final env
     is the block post. *)
  let x = v64 "et_x" in
  let y = v64 "et_y" in
  let dx = Def.create x (Bil.Int (Cbat_word.to_word (w64 7))) in
  let dy =
    Def.create y
      (Bil.BinOp (Bil.PLUS, Bil.Var x, Bil.Int (Cbat_word.to_word (w64 1))))
  in
  let sub = straight_sub "et_chain" [ dx; dy ] in
  let envs, sub', _ =
    produce Theory.Target.unknown (Program.create ~subs:[ sub ] ()) sub
  in
  let blk = Term.first blk_t sub' |> Base.Option.value_exn in
  let pre, post = Core.Map.find_exn envs (Term.tid blk) in
  let dx' = find_def sub' (Term.tid dx) in
  let dy' = find_def sub' (Term.tid dy) in
  let tag_dx = Vsa.env_tag dx' in
  let tag_dy = Vsa.env_tag dy' in
  check "Env3: the first def's tag is the block pre"
    (match tag_dx with Some e -> AI.equal e pre | None -> false);
  check "Env3: the second def's tag is the first transfer's product"
    (match tag_dx, tag_dy with
     | Some e1, Some e2 -> AI.equal e2 (Vsa.Test_seam.denote_def dx e1)
     | _ -> false);
  check "Env3: the block post is the last transfer's product"
    (match tag_dy with
     | Some e -> AI.equal post (Vsa.Test_seam.denote_def dy e)
     | None -> false);
  ()
)

(* The seam's gate-free answers, crossed through [facts.denote]. *)
let run_seam () =
  let facts0 =
    Kb.build ~block_envs:Tid.Map.empty
      ~block_addrs:(Core.Map.empty (module Addr))
      ~target:Theory.Target.unknown
  in
  let m = memv "ets_m" in
  let x = v64 "ets_x" in
  let y = v64 "ets_y" in
  let addr_w = w64 0x1000 in
  let mem_idx = { Cbat_vsa.Mem.addr_width = 64; Cbat_vsa.Mem.addressable_width = 8 } in
  let cell =
    Mem.add (Mem.top mem_idx)
      ~key:
        (match Mem.Key.of_wordset (Ws.singleton addr_w) with
         | Some k -> k
         | None -> assert false)
      ~data:(Mem.Val.create (Ws.singleton (Cbat_word.of_int ~width:32 7)) LittleEndian)
  in
  let tag_env = AI.add_memory (anchored_entry ()) ~key:m ~data:cell in

  (* Env4: the tag answers a memory-bearing query exactly. *)
  let blk4 = blk_of_defs [ Def.create y (Bil.Int (Cbat_word.to_word (w64 0))) ] in
  let d4 =
    Vsa.set_env_tag tag_env
      (Term.first def_t blk4 |> Base.Option.value_exn)
  in
  check "Env4: a memory-bearing query on a tagged def answers in its tag env"
    (match
       facts0.denote ~blk:blk4 ~def:d4
         (Bil.Load (Bil.Var m, Bil.Int (Cbat_word.to_word addr_w), LittleEndian, `r32))
     with
     | Ok ws -> Ws.equal ws (Ws.singleton (Cbat_word.of_int ~width:32 7))
     | Error _ -> false);

  (* Env5: an untagged def answers TOP even when the record's pre binds
     the queried var. *)
  let pre5 = mk_env [ (x, Ws.singleton (w64 5)) ] in
  let blk5 = blk_of_defs [ Def.create y (Bil.Var x) ] in
  let d5 = Term.first def_t blk5 |> Base.Option.value_exn in
  let facts5 =
    Kb.build
      ~block_envs:(Tid.Map.singleton (Term.tid blk5) (pre5, pre5))
      ~block_addrs:(Core.Map.empty (module Addr))
      ~target:Theory.Target.unknown
  in
  check "Env5: an untagged def answers TOP (minted after the boundary)"
    (match facts5.denote ~blk:blk5 ~def:d5 (Bil.Var x) with
     | Ok ws -> Ws.is_top ws
     | Error _ -> false);

  (* Env6: a no-def query evaluates in the block's post state. *)
  let pre6 = mk_env [ (x, Ws.singleton (w64 1)) ] in
  let post6 = mk_env [ (x, Ws.singleton (w64 2)) ] in
  let blk6 = blk_of_defs [] in
  let facts6 =
    Kb.build
      ~block_envs:(Tid.Map.singleton (Term.tid blk6) (pre6, post6))
      ~block_addrs:(Core.Map.empty (module Addr))
      ~target:Theory.Target.unknown
  in
  check "Env6: a no-def query evaluates in the post state"
    (match facts6.denote ~blk:blk6 (Bil.Var x) with
     | Ok ws -> Ws.equal ws (Ws.singleton (w64 2))
     | Error _ -> false);

  (* Env7: the VSA_DEBUG differential's invariant on a multi-def block —
     every def-level query's tag answer equals the raw replay. *)
  let a = v64 "ets_a" in
  let b = v64 "ets_b" in
  let c = v64 "ets_c" in
  let sub =
    straight_sub "ets_diff"
      [ Def.create a (Bil.Int (Cbat_word.to_word (w64 7)));
        Def.create b
          (Bil.BinOp (Bil.PLUS, Bil.Var a, Bil.Int (Cbat_word.to_word (w64 1))));
        Def.create c
          (Bil.BinOp (Bil.TIMES, Bil.Var b, Bil.Int (Cbat_word.to_word (w64 3)))) ]
  in
  let facts7, sub' = fixture_facts_sub sub in
  let blk7 = Term.first blk_t sub' |> Base.Option.value_exn in
  let pre7 =
    match Core.Map.find facts7.envs (Term.tid blk7) with
    | Some (pre, _) -> pre
    | None -> AI.top
  in
  let defs7 = Term.enum def_t blk7 |> Seq.to_list in
  let mismatch d =
    let actual = facts7.denote ~blk:blk7 ~def:d (Def.rhs d) in
    let replay = Vsa.solve_denote ~pre:pre7 ~blk:blk7 ~def:d (Def.rhs d) in
    match actual, replay with
    | Ok x, Ok y -> not (Ws.equal x y)
    | Error x, Error y -> not (Type.Error.equal x y)
    | _ -> true
  in
  check "Env7: the tag answers equal the raw replay on a multi-def block (0 mismatches)"
    (Base.List.length defs7 >= 3
     && Base.List.for_all defs7 ~f:(fun d -> Base.Option.is_some (Vsa.env_tag d))
     && not (Base.List.exists defs7 ~f:mismatch));
  ()

(* The promote path: [Hike_promote.rewrite_program] maps the stamped sub
   and mints the hike_argN defs; a mapped-but-surviving def still
   answers from its tag, a minted def from TOP. *)
let promote_rewrite (facts : Hike.Kb.facts) (sub : sub term) : sub term =
  let prog = Program.create ~subs:[ sub ] () in
  let ctx =
    Hike.Sections.attribute ~facts ~word:8
      ~entry:Hike.Stack_model.segment_base ~spans:[] prog
  in
  let prog =
    Hike.Promote.rewrite_program ~word:8
      ~entry:Hike.Stack_model.segment_base ~facts ~symtab:None ~spans:[] ~ctx
      prog
  in
  Term.first sub_t prog |> Base.Option.value_exn

let run_promote () =
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
                     ~target:(Indirect (Bil.Var (v64 "etp_tptr"))) ()))) ];
        [], [ (0, mk_ret) ] ]
  in
  let facts, sub' = fixture_facts_sub sub in
  let sub'' = promote_rewrite facts sub' in
  let blk'' = Term.first blk_t sub'' |> Base.Option.value_exn in
  (* Env8: the promote rewrite keeps a mapped def's Env Tag, and the
     seam answers from it (the tag env has x = {7}; no tag would be TOP). *)
  let store'' = find_def sub'' (Term.tid store) in
  check "Env8: the promote rewrite actually rewrote the surviving def"
    (not (Exp.equal (Def.rhs store'') (Def.rhs store)));
  check "Env8: the promote rewrite keeps a mapped def's Env Tag"
    (Base.Option.is_some (Vsa.env_tag store''));
  check "Env8: the seam answers a rewritten def from its tag"
    (match facts.denote ~blk:blk'' ~def:store'' (Bil.Var x) with
     | Ok ws -> Ws.equal ws (Ws.singleton (w64 7))
     | Error _ -> false);
  (* Env9: the fresh hike_argN def carries no tag and answers TOP. *)
  let arg =
    Term.enum def_t blk''
    |> Seq.find ~f:(fun d -> Hike.Stack_model.is_call_arg (Def.lhs d))
  in
  check_bound "Env9: the minted hike_argN def has no Env Tag" arg
    (fun d -> Base.Option.is_none (Vsa.env_tag d));
  check_bound "Env9: the minted def answers TOP through the seam" arg
    (fun d ->
       match facts.denote ~blk:blk'' ~def:d (Bil.Var (Def.lhs d)) with
       | Ok ws -> Ws.is_top ws
       | Error _ -> false);
  ()
