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

(* The dispatch guard lives in the TARGET domain: the whole target
   expression equals the case word (a composed table's guards subtract
   the table base first; a plain bounded set has none). *)
let eq_target ~synth (a : var) (b : var) (w : int64) j =
  match Jmp.cond j with
  | Bil.BinOp
      (Bil.EQ, Bil.BinOp (Bil.PLUS, Bil.Var a', Bil.Var b'), face) ->
    Var.same (Var.base a') a && Var.same (Var.base b') b
    && Base.Option.equal Int64.equal
         (Hike_synth_addr.address_of_exp synth face) (Some w)
  | _ -> false

(* The drive's arming: every indirect transfer's destinations are
   [words], each naming a block by its address attr. *)
let armed (words : int64 list) (sub : sub term) : sub term =
  Hike.Cfg_complete.arm_dispatches ~dests:(fun _ -> words) sub

(* [sub] with block [i] at address [addrs.(i)]. *)
let with_addrs (addrs : int64 array) (sub : sub term) : sub term =
  let sb = Sub.Builder.create ~tid:(Term.tid sub) ~name:(Sub.name sub) () in
  Term.enum blk_t sub
  |> Seq.iteri ~f:(fun i b ->
      Sub.Builder.add_blk sb (Term.set_attr b address (Addr.of_int64 addrs.(i))));
  Sub.Builder.result sb

(* [of_wordset] fans: the pinned fixtures are single-piece address lines. *)
let check_key1 name ks f =
  check name (match ks with [ k ] -> f k | _ -> false)

let abi = Hike.Abi.x86_64_sysv

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
              let solution =
                static_graph_vsa ~synth:Hike.Synth.empty ~abi
                  ~resolved:Tid.Map.empty sub (Vsa.init_sol ~abi sub)
              in
              let loads =
                Hike.Cfg_complete.retaddr_defs ~abi ~synth:Hike.Synth.empty
                  ~sol:solution sub
              in
              check "the target's definition reads the return-address cell"
                (Core.Set.mem loads (Term.tid load));
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

    (* J2: the jump-table dispatch — the target var's denotation joins
       two in-sub block constants; block_addrs names both blocks' tids,
       so every word of the set resolves in-sub. *)
    pin "RES-08"
      "N8-DISP: the dispatch becomes a target-guarded series, one goto per case target, plus its named false edge"
      (fun () ->
        let j2_sel = v64 "t22_j2_sel" in
        let j2_base = v64 "t22_j2_base" in
        let j2_bdef = Def.create j2_base (Bil.Int (Cbat_word.to_word (q64 0x2000L))) in
        let j2_t1 = Def.create j2_sel (Bil.Int (Cbat_word.to_word (q64 0x1008L))) in
        let j2_t2 = Def.create j2_sel (Bil.Int (Cbat_word.to_word (q64 0x1010L))) in
        let head_flag = v1 "t22_flag" in
        let j2, tids =
          sub_of "t22_dispatch"
            [ [ j2_bdef ], [ (1, fun t -> mk_jmp_to t (Bil.Var head_flag)); (2, mk_goto) ];
              [ j2_t1 ], [ (3, mk_goto) ];
              [ j2_t2 ], [ (3, mk_goto) ];
              [], [ (4, fun _ -> Jmp.create (Goto (Indirect (Bil.BinOp (Bil.PLUS, Bil.Var j2_sel, Bil.Var j2_base))))) ];
              [], [ (6, mk_goto) ];
              [], [ (6, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let b1_tid = tids.(4) in
        let b2_tid = tids.(5) in
        let j2 =
          with_addrs [| 0x1000L; 0x1100L; 0x1200L; 0x1300L; 0x3008L; 0x3010L; 0x1400L |] j2
          |> armed [ 0x3008L; 0x3010L ]
        in
        let envs, j2', ba' =
          produce ~synth:Hike.Synth.empty (x86_target ())
            ~block_addrs:[ (0x3008L, b1_tid); (0x3010L, b2_tid) ]
            (Program.create ~subs:[ j2 ] ()) j2
        in
        let facts =
          { (Hike.Kb.build ~lookup:(fun _ -> None) ~block_envs:envs
               ~block_addrs:ba' ~target:(x86_target ())) with
            foreign_slots = Core.Int64.Set.empty }
        in
        let synth, program =
          Hike.Split_blocks.materialize ~facts
            (Program.create ~subs:[ j2' ] ())
        in
        let j2'' = Term.enum sub_t program |> Seq.hd_exn in
        check "RES-08"
          (match jmps_of_blk j2'' 3 with
           | g1 :: g2 :: _ ->
             (match Jmp.kind g1, Jmp.kind g2 with
              | Goto (Direct t1), Goto (Direct t2) ->
                Tid.equal t1 b1_tid && Tid.equal t2 b2_tid
                && eq_target ~synth j2_sel j2_base 0x3008L g1
                && Hike.Stack_model.is_true_cond (Jmp.cond g2)
              | _ -> false)
           | _ -> false));

    (* The bake pin: a one-word resolution materializes nothing — the
       dispatch stays as it came; the unconditional default is
       unrepresentable. *)
    pin "RES-09"
      "FUSED-BAKE: a one-word resolution materializes nothing (the dispatch stays)"
      (fun () ->
        let j5_sel = v64 "t22_j5_sel" in
        let j5_base = v64 "t22_j5_base" in
        let j5_bdef = Def.create j5_base (Bil.Int (Cbat_word.to_word (q64 0x2000L))) in
        let j5_t1 = Def.create j5_sel (Bil.Int (Cbat_word.to_word (q64 0x1008L))) in
        let j5, j5_tids =
          sub_of "t22_bake"
            [ [ j5_bdef; j5_t1 ],
              [ (1, fun _ -> Jmp.create (Goto (Indirect (Bil.BinOp (Bil.PLUS, Bil.Var j5_sel, Bil.Var j5_base))))) ];
              [], [ (2, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let _, j5', _ =
          produce ~synth:Hike.Synth.empty (x86_target ())
            ~block_addrs:[ (0x3008L, j5_tids.(1)) ]
            (Program.create ~subs:[ j5 ] ()) j5
        in
        check "RES-09"
          (match jmps_of_blk j5' 0 with
           | [ j ] -> (
               match Jmp.kind j with
               | Goto (Indirect (Bil.BinOp (Bil.PLUS, Bil.Var a, Bil.Var b))) ->
                 Var.same (Var.base a) j5_sel && Var.same (Var.base b) j5_base
               | _ -> false)
           | _ -> false));

    (* The growth pin: the loop closes through the analysis edges — the
       case body's increment flows back to the head, the selector widens
       in the same run that first resolved the dispatch. *)
    pin "RES-10"
      "FUSED-GROWTH: the selector widens in the same run (the loop closed through analysis edges)"
      (fun () ->
        let j6_sel = v64 "t22_j6_sel" in
        let j6_base = v64 "t22_j6_base" in
        let j6_bdef = Def.create j6_base (Bil.Int (Cbat_word.to_word (q64 0x2000L))) in
        let j6_s1 = Def.create j6_sel (Bil.Int (Cbat_word.to_word (q64 0x1008L))) in
        let j6_s2 = Def.create j6_sel (Bil.Int (Cbat_word.to_word (q64 0x1010L))) in
        let j6_pad = v64 "t22_j6_pad" in
        let j6_pivot = Def.create j6_pad (Bil.Int (Cbat_word.to_word (q64 0L))) in
        let j6_pivot = Term.set_attr j6_pivot address (Cbat_word.to_word (q64 0x3010L)) in
        let j6, j6_tids =
          sub_of "t22_growth"
            [ [ j6_bdef; j6_s1 ], [ (1, mk_goto) ];
              [], [ (1, fun _ -> Jmp.create (Goto (Indirect (Bil.BinOp (Bil.PLUS, Bil.Var j6_sel, Bil.Var j6_base))))) ];
              [ j6_s2 ], [ (1, mk_goto) ];
              [ j6_pivot ], [ (4, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let envs6, solved6, _ =
          produce ~synth:Hike.Synth.empty (x86_target ())
            ~block_addrs:[ (0x3008L, j6_tids.(2)); (0x300cL, j6_tids.(3)) ]
            (Program.create ~subs:[ j6 ] ()) j6
        in
        let head_post =
          match Core.Map.find envs6 j6_tids.(1) with
          | Some (_, post) -> post
          | None -> Cbat_vsa.AI.top
        in
        let head_sel = Cbat_vsa.AI.find_word 64 head_post
            (Hike.Stack_model.version_at_end (Term.find_exn blk_t solved6 j6_tids.(1)) j6_sel) in
        let sel_card =
          match Cbat_word.to_int64 (Cbat_vsa.WordSet.cardinality head_sel) with
          | Ok c -> c
          | Error _ -> 0L
        in
        check "RES-10" (Int64.equal sel_card 2L));

    (* The liveness pin: a resolution whose word set is incomplete (a
       word naming no in-sub block) renders nothing — a partial series
       would drop live cases — so the indirect transfer stays exactly
       as it came, and the word rides the fact channels to the
       driver's decode instead. *)
    pin "RES-13"
      "FUSED-LIVE: a partially-resolvable dispatch stays the indirect transfer (no partial series)"
      (fun () ->
        let j7_sel = v64 "t22_j7_sel" in
        let j7_base = v64 "t22_j7_base" in
        let j7_bdef = Def.create j7_base (Bil.Int (Cbat_word.to_word (q64 0x2000L))) in
        let j7_s1 = Def.create j7_sel (Bil.Int (Cbat_word.to_word (q64 0x1008L))) in
        let j7_s2 = Def.create j7_sel (Bil.Int (Cbat_word.to_word (q64 0x1010L))) in
        let j7_s3 = Def.create j7_sel (Bil.Int (Cbat_word.to_word (q64 0x7000L))) in
        let j7_flag = v1 "t22_j7_flag" in
        let j7_pad = v64 "t22_j7_pad" in
        let j7_pivot = Def.create j7_pad (Bil.Int (Cbat_word.to_word (q64 0L))) in
        let j7_pivot = Term.set_attr j7_pivot address (Cbat_word.to_word (q64 0x3008L)) in
        let j7, j7_tids =
          sub_of "t22_live"
            [ [ j7_bdef ],
              [ (1, fun t -> mk_jmp_to t (Bil.Var j7_flag));
                (2, fun t ->
                      mk_jmp_to t (Bil.UnOp (Bil.NOT, Bil.Var j7_flag)));
                (3, mk_goto) ];
              [ j7_s1 ], [ (4, mk_goto) ];
              [ j7_s2 ], [ (4, mk_goto) ];
              [ j7_s3 ], [ (4, mk_goto) ];
              [], [ (5, fun _ -> Jmp.create (Goto (Indirect (Bil.BinOp (Bil.PLUS, Bil.Var j7_sel, Bil.Var j7_base))))) ];
              [ j7_pivot ], [ (6, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let _, j7', _ =
          produce ~synth:Hike.Synth.empty (x86_target ())
            ~block_addrs:
            [ (0x3008L, j7_tids.(5)); (0x3010L, j7_tids.(6));
              (0x9000L, Tid.create ()) ]
            (Program.create ~subs:[ j7 ] ()) j7
        in
        check "RES-13"
          (match jmps_of_blk j7' 4 with
           | [ j ] -> (
               match Jmp.kind j with
               | Goto (Indirect (Bil.BinOp (Bil.PLUS, Bil.Var a, Bil.Var b))) ->
                 Var.same (Var.base a) j7_sel && Var.same (Var.base b) j7_base
               | _ -> false)
           | _ -> false));

    (* J4: a word the run's map cannot name is a decline, not a failure —
       it rides the fact channels to the driver's decode. *)

    pin "RES-14"
      "T22-J4: a dispatch word the map cannot name declines (the transfer stays, no failure)"
      (fun () ->
        let j4_sel = v64 "t22_j4_sel" in
        let j4_base = v64 "t22_j4_base" in
        let j4_bdef = Def.create j4_base (Bil.Int (Cbat_word.to_word (q64 0x2000L))) in
        let j4_t1 = Def.create j4_sel (Bil.Int (Cbat_word.to_word (q64 0x1008L))) in
        let j4_t2 = Def.create j4_sel (Bil.Int (Cbat_word.to_word (q64 0x1010L))) in
        let j4_flag = v1 "t22_j4_flag" in
        let j4, j4_tids =
          sub_of "t22_map_miss"
            [ [ j4_bdef ], [ (1, fun t -> mk_jmp_to t (Bil.Var j4_flag)); (2, mk_goto) ];
              [ j4_t1 ], [ (3, mk_goto) ];
              [ j4_t2 ], [ (3, mk_goto) ];
              [], [ (4, fun _ -> Jmp.create (Goto (Indirect (Bil.BinOp (Bil.PLUS, Bil.Var j4_sel, Bil.Var j4_base))))) ];
              [], [ (6, mk_goto) ];
              [], [ (6, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let _, j4', _ =
          produce ~synth:Hike.Synth.empty (x86_target ())
            ~block_addrs:[ (0x3008L, j4_tids.(4)); (0x400000L, j4_tids.(5)) ]
            (Program.create ~subs:[ j4 ] ()) j4
        in
        check "RES-14"
          (match jmps_of_blk j4' 3 with
           | [ j ] -> (
               match Jmp.kind j with
               | Goto (Indirect (Bil.BinOp (Bil.PLUS, Bil.Var a, Bil.Var b))) ->
                 Var.same (Var.base a) j4_sel && Var.same (Var.base b) j4_base
               | _ -> false)
           | _ -> false));

    (* The materializer retargets an existing indirect transfer to the
       addresses named by the case. *)
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

    (* J3b: the TOP target (an undefined var) stays too. *)

    (* J5 (the ret-not-dispatch pin): the epilogue's target VALUE is
       bounded — the corpus crash shape — and the resolution leaves it
       alone: no split, no growth, no loud failure.  The retaddr fact is
       the load's ADDRESS denotation (the entry-RSP cell). *)

    pin "RES-19"
      "RET-ND1: a bounded retaddr target is not a dispatch (no raise, no growth)"
      (fun () ->
        let j5_ra = v64 "t22_j5b_ra" in
        let j5_m = memv "t22_j5b_m" in
        let j5_ld =
          Def.create j5_ra
            (Bil.Load (Bil.Var j5_m, Bil.Var sp, LittleEndian, `r64))
        in
        let j5, j5_tids =
          sub_of "t22_bounded_ret"
            [ [ j5_ld ],
              [ (1, fun _ ->
                    Jmp.create
                      (Call (Call.create ~target:(Indirect (Bil.Var j5_ra)) ()))) ];
              [], [ (0, mk_ret) ] ]
        in
        check_key1 "RES-19"
          (Mem.Key.of_wordset (Ws.stack_word_i64 0L))
          (fun k ->
            let entry =
              AI.add_memory (anchored_entry ()) ~key:j5_m
                ~data:
                  (Mem.add
                     (Mem.top { Mem.addr_width = 64; Mem.addressable_width = 8 })
                     ~key:k
                     ~data:(Mem.Val.create (Ws.singleton (w64 0)) LittleEndian))
            in
            let sol =
              static_graph_vsa ~synth:Hike.Synth.empty ~abi:Hike.Abi.x86_64_sysv
                j5
                (Cbat_vsa.init_sol ~abi:Hike.Abi.x86_64_sysv ~entry j5)
            in
            let retaddr = Hike.Cfg_complete.retaddr_defs
                ~abi:Hike.Abi.x86_64_sysv ~synth:Hike.Synth.empty ~sol j5 in
            let resolved5', events5 =
              Hike.Cfg_complete.resolve_phase ~sol ~synth:Hike.Synth.empty
                ~retaddr ~block_addrs:
                  (Core.Map.of_alist_exn (module Addr)
                     [ (Addr.of_int64 0x3008L, j5_tids.(1)) ])
                ~foreign_slots:Core.Int64.Set.empty
                j5 Tid.Map.empty
            in
            (not events5) && Core.Map.is_empty resolved5'));

    (* The completion owns the edge set: a conditional goto's false edge
       is named, and a destination two jumps share is carried once. *)
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
    pin "RES-25" "a table word and a direct goto resolve one case block"
      (fun () ->
        let rdx = v64 "t25_rdx" in
        let rcx = v64 "t25_rcx" in
        let rax = v64 "t25_rax" in
        let m = memv "t25_m" in
        let base_def = Def.create rdx (Bil.Int (Cbat_word.to_word (q64 0x4000L))) in
        let zero_def = Def.create rcx (Bil.Int (Cbat_word.to_word (q64 0L))) in
        let four_def = Def.create rcx (Bil.Int (Cbat_word.to_word (q64 1L))) in
        let flag = v1 "t25_flag" in
        let load_def =
          Def.create rax
            (Bil.Cast
               ( Bil.SIGNED, 64,
                 Bil.Load
                   ( Bil.Var m,
                     Bil.BinOp
                       ( Bil.PLUS, Bil.Var rdx,
                         Bil.BinOp (Bil.LSHIFT, Bil.Var rcx, Bil.Int (Word.of_int ~width:64 2)) ),
                     LittleEndian, `r32 ) ))
        in
        let add_def =
          Def.create rax (Bil.BinOp (Bil.PLUS, Bil.Var rax, Bil.Var rdx))
        in
        (* The two-word relative table at 0x4000: entry 0 names the
           block at 0x3000, entry 1 the block at 0x3008. *)
        let word_bytes (k : int) : string =
          let delta = if k land 1 = 0 then -0x1000L else -0xFF8L in
          let w = Int64.logand delta 0xFFFFFFFFL in
          String.init 4 (fun i ->
              Char.chr (Int64.to_int (Int64.logand (Int64.shift_right_logical w (8 * i)) 0xFFL)))
        in
        let img_bytes = Bytes.of_string (String.concat "" (Base.List.init 2 ~f:word_bytes)) in
        let images =
          [ { Cbat_vsa.img_lo = 0x4000L; img_hi = 0x4007L; img_bytes;
              img_slots = Core.Int64.Set.empty } ] in
        let sub25, tids =
          sub_of "t25_tbl"
            [ [ ],
              [ (1, fun t -> mk_jmp_to t (Bil.Var flag));
                (2, fun t -> mk_jmp_to t (Bil.UnOp (Bil.NOT, Bil.Var flag))) ];
              [ zero_def ], [ (3, mk_goto) ];
              [ four_def ], [ (3, mk_goto) ];
              [ base_def; load_def; add_def ],
                [ (0, fun _ -> Jmp.create (Goto (Indirect (Bil.Var rax)))) ];
              [ ], [ (5, mk_goto) ];
              [ ], [ (7, mk_goto) ];
              [ ], [ (7, mk_goto) ];
              [ ], [ (0, mk_ret) ] ]
        in
        let real_addr tid =
          if Tid.equal tid tids.(0) then 0x2000L
          else if Tid.equal tid tids.(1) then 0x2008L
          else if Tid.equal tid tids.(2) then 0x2010L
          else if Tid.equal tid tids.(3) then 0x2018L
          else if Tid.equal tid tids.(4) then 0x2020L
          else if Tid.equal tid tids.(5) then 0x3000L
          else if Tid.equal tid tids.(6) then 0x3008L
          else if Tid.equal tid tids.(7) then 0x2028L
          else 0L
        in
        (* Every block carries its address. *)
        let stamped =
          let blks = Term.enum blk_t sub25 |> Seq.to_list in
          let stamped_blks =
            Base.List.map blks ~f:(fun b ->
                Term.set_attr b address
                  (Addr.of_int64 (real_addr (Term.tid b))))
          in
          let sb =
            Sub.Builder.create ~tid:(Term.tid sub25) ~name:(Sub.name sub25) ()
          in
          Base.List.iter stamped_blks ~f:(Sub.Builder.add_blk sb);
          Sub.Builder.result sb |> armed [ 0x3000L; 0x3008L ]
        in
        let envs, sub25', ba' =
          produce ~synth:Hike.Synth.empty ~block_addrs:
            [ (0x2000L, tids.(0)); (0x2008L, tids.(1)); (0x2010L, tids.(2));
              (0x2018L, tids.(3)); (0x2020L, tids.(4)); (0x3000L, tids.(5));
              (0x3008L, tids.(6)); (0x2028L, tids.(7)) ]
            ~images (x86_target ())
            (Program.create ~subs:[ stamped ] ()) stamped
        in
        (* The dispatch materializes after the solve, in split-blocks:
           the bounded denotation names the case blocks, the composed
           base gives the guards' delta coordinate. *)
        let facts =
          { (Hike.Kb.build ~lookup:(fun _ -> None) ~block_envs:envs
               ~block_addrs:ba' ~target:(x86_target ())) with
            images;
            foreign_slots = Core.Int64.Set.empty }
        in
        let _, materialized =
          Hike.Split_blocks.materialize ~facts
            (Program.create ~subs:[ sub25' ] ())
        in
        let sub25'' = Term.enum sub_t materialized |> Seq.hd_exn in
        let blk_of tid =
          Term.enum blk_t sub25'' |> Seq.find_exn ~f:(fun b -> Tid.equal (Term.tid b) tid)
        in
        let disp = blk_of tids.(3) in
        let disp_jmps = Term.enum jmp_t disp |> Seq.to_list in
        let has_case t =
          Base.List.exists disp_jmps ~f:(fun j ->
              match Jmp.kind j with
              | Goto (Direct t') -> Tid.equal t' t
              | _ -> false)
        in
        let resolved =
          has_case tids.(5) && has_case tids.(6)
          && Base.List.exists disp_jmps ~f:(fun j ->
                 not (Hike.Stack_model.is_true_cond (Jmp.cond j)))
          && not
               (Base.List.exists disp_jmps ~f:(fun j ->
                    match Jmp.kind j with
                    | Goto (Indirect _) -> true
                    | _ -> false))
        in
        let map_names_case =
          match Core.Map.find ba' (Addr.of_int64 0x3000L) with
          | Some t -> Tid.equal t tids.(5)
          | None -> false
        in
        check "RES-25a the dispatch resolves to its case blocks" resolved;
        check "RES-25b the map names the case block" map_names_case);

    (* The protected-gcc shape: the table base is a module address kept in
       a callee-saved register, and the epilogue's pop of that register
       precedes the dispatch block in term order without reaching it.
       The guards subtract the base summand the denotation names. *)
    pin "RES-26" "a module-address base guards table data, not runtime targets"
      (fun () ->
        Hike_origin.Regions.install [ (Hike_section.Rodata, 0x4000L, 0x4007L) ];
        let rdx = v64 "t26_rdx" in
        let rcx = v64 "t26_rcx" in
        let rax = v64 "t26_rax" in
        let tmp = v64 "t26_tmp" in
        let m = memv "t26_m" in
        let flag = v1 "t26_flag" in
        let synth, base = Hike_synth.mint_module_addr ~addr_bits:64 0x4000L Hike_synth.empty in
        let base_def = Def.create rdx (Bil.Var base) in
        let zero_def = Def.create rcx (Bil.Int (Cbat_word.to_word (q64 0L))) in
        let one_def = Def.create rcx (Bil.Int (Cbat_word.to_word (q64 1L))) in
        let pop_def = Def.create rdx (Bil.Load (Bil.Var m, Bil.Var sp, LittleEndian, `r64)) in
        let load_def =
          Def.create rax
            (Bil.Cast
               ( Bil.SIGNED, 64,
                 Bil.Load
                   ( Bil.Var m,
                     Bil.BinOp
                       ( Bil.PLUS, Bil.Var rdx,
                         Bil.BinOp (Bil.LSHIFT, Bil.Var rcx, Bil.Int (Word.of_int ~width:64 2)) ),
                     LittleEndian, `r32 ) ))
        in
        let copy_def = Def.create tmp (Bil.Var rdx) in
        let add_def = Def.create rax (Bil.BinOp (Bil.PLUS, Bil.Var rax, Bil.Var tmp)) in
        let word_bytes (delta : int64) : string =
          let w = Int64.logand delta 0xFFFFFFFFL in
          String.init 4 (fun i ->
              Char.chr (Int64.to_int (Int64.logand (Int64.shift_right_logical w (8 * i)) 0xFFL)))
        in
        let img_bytes = Bytes.of_string (word_bytes (-0x1000L) ^ word_bytes (-0xFF8L)) in
        let images =
          [ { Cbat_vsa.img_lo = 0x4000L; img_hi = 0x4007L; img_bytes;
              img_slots = Core.Int64.Set.empty } ] in
        let sub26, tids =
          sub_of "t26_tbl"
            [ [ base_def ],
              [ (1, fun t -> mk_jmp_to t (Bil.Var flag));
                (2, fun t -> mk_jmp_to t (Bil.UnOp (Bil.NOT, Bil.Var flag))) ];
              [ zero_def ], [ (4, mk_goto) ];
              [ one_def ], [ (4, mk_goto) ];
              [ pop_def ], [ (0, mk_ret) ];
              [ load_def; copy_def; add_def ],
                [ (0, fun _ -> Jmp.create (Goto (Indirect (Bil.Var rax)))) ];
              [ ], [ (3, mk_goto) ];
              [ ], [ (3, mk_goto) ] ]
        in
        let addrs = [| 0x2000L; 0x2008L; 0x2010L; 0x2018L; 0x2020L; 0x3000L; 0x3008L |] in
        let stamped =
          let sb = Sub.Builder.create ~tid:(Term.tid sub26) ~name:(Sub.name sub26) () in
          Term.enum blk_t sub26
          |> Seq.iteri ~f:(fun i b ->
              Sub.Builder.add_blk sb (Term.set_attr b address (Addr.of_int64 addrs.(i))));
          Sub.Builder.result sb |> armed [ 0x3000L; 0x3008L ]
        in
        let block_addrs = Base.List.init 7 ~f:(fun i -> (addrs.(i), tids.(i))) in
        let envs, sub26', ba' =
          produce ~synth ~block_addrs ~images (x86_target ())
            (Program.create ~subs:[ stamped ] ()) stamped
        in
        let facts =
          { (Hike.Kb.build ~lookup:(fun _ -> None) ~block_envs:envs
               ~block_addrs:ba' ~target:(x86_target ())) with
            images;
            foreign_slots = Core.Int64.Set.empty }
        in
        let facts = Hike.Kb.with_synth facts (Hike.Synth.union facts.synth synth) in
        let _, materialized =
          Hike.Split_blocks.materialize ~facts (Program.create ~subs:[ sub26' ] ())
        in
        let disp =
          Term.enum sub_t materialized |> Seq.hd_exn |> Term.enum blk_t
          |> Seq.find_exn ~f:(fun b -> Tid.equal (Term.tid b) tids.(4))
        in
        let jmps = Term.enum jmp_t disp |> Seq.to_list in
        let data_guard delta j =
          let found = ref false in
          (object
            inherit [unit] Exp.visitor
            method! visit_binop op a b () =
              (match op, a, b with
               | Bil.EQ, Bil.BinOp (Bil.MINUS, Bil.Var r, Bil.Var t), Bil.Int w
                 when Var.same (Var.base r) rax && Var.same (Var.base t) tmp
                      && Int64.equal (Word.to_int64_exn w) delta ->
                 found := true
               | _ -> ())
          end)#visit_exp (Jmp.cond j) ();
          !found
        in
        let goes_to t j =
          match Jmp.kind j with Goto (Direct t') -> Tid.equal t t' | _ -> false
        in
        Hike_origin.Regions.install [];
        check "RES-26a both cases resolve"
          (Base.List.exists jmps ~f:(goes_to tids.(5))
           && Base.List.exists jmps ~f:(goes_to tids.(6)));
        check "RES-26b the guard compares table data against word - base"
          (Base.List.exists jmps ~f:(fun j ->
               data_guard (-0x1000L) j || data_guard (-0xFF8L) j)));

    (* Both completion consumers share the phase's return-address set;
       the dispatch cases and return keep their original edges. *)
    pin "RES-27"
      "RETADDR-ONCE: a shared retaddr set keeps dispatch and return edges"
      (fun () ->
        let ra = v64 "t27_ra" in
        let rar = v64 "t27_rar" in
        let m = memv "t27_m" in
        let sel = v64 "t27_sel" in
        let base = v64 "t27_base" in
        let flag = v1 "t27_flag" in
        let ra_ld =
          Def.create ra
            (Bil.Load (Bil.Var m, Bil.Var sp, LittleEndian, `r64))
        in
        let rar_ld =
          Def.create rar
            (Bil.Load (Bil.Var m, Bil.Var sp, LittleEndian, `r64))
        in
        let base_def =
          Def.create base (Bil.Int (Cbat_word.to_word (q64 0x2000L)))
        in
        let sel1 = Def.create sel (Bil.Int (Cbat_word.to_word (q64 0x1008L))) in
        let sel2 = Def.create sel (Bil.Int (Cbat_word.to_word (q64 0x1010L))) in
        let sub, tids =
          sub_of "t27_retaddr_dispatch"
            [ [ ra_ld; base_def ],
              [ (1, fun t -> mk_jmp_to t (Bil.Var flag)); (2, mk_goto) ];
              [ sel1 ], [ (4, mk_goto) ];
              [ sel2 ], [ (4, mk_goto) ];
              [], [ (6, mk_goto) ];
              [],
              [ (3, fun _ ->
                    Jmp.create
                      (Goto
                         (Indirect
                            (Bil.BinOp
                               (Bil.PLUS, Bil.Var sel, Bil.Var base))))) ];
              [], [ (6, mk_goto) ];
              [ rar_ld ],
              [ (0, fun _ -> Jmp.create (Goto (Indirect (Bil.Var rar)))) ] ]
        in
        let abi = Hike.Abi.x86_64_sysv in
        let block_addrs =
          Core.Map.of_alist_exn (module Addr)
            [ (Addr.of_int64 0x3008L, tids.(3));
              (Addr.of_int64 0x3010L, tids.(5)) ]
        in
        let sol =
          static_graph_vsa ~synth:Hike.Synth.empty ~abi ~resolved:Tid.Map.empty
            sub (Cbat_vsa.init_sol ~abi sub)
        in
        let retaddr =
          Hike.Cfg_complete.retaddr_defs ~abi ~synth:Hike.Synth.empty ~sol sub
        in
        let resolved, grew =
          Hike.Cfg_complete.resolve_phase ~sol ~synth:Hike.Synth.empty
            ~block_addrs ~foreign_slots:Core.Int64.Set.empty ~retaddr sub
            Tid.Map.empty
        in
        let materialized =
          Hike.Cfg_complete.materialize ~sol ~synth:Hike.Synth.empty
            ~block_addrs ~foreign_slots:Core.Int64.Set.empty ~retaddr sub
        in
        let outcome (s : sub term) =
          let blk tid = Term.find blk_t s tid in
          let return_edge =
            match blk tids.(6) with
            | Some b -> (
                match Term.enum jmp_t b |> Seq.to_list with
                | [ j ] -> Hike_return.is_jmp j
                | _ -> false)
            | None -> false
          in
          let dispatch_stays =
            match blk tids.(4) with
            | Some b -> (
                match Term.enum jmp_t b |> Seq.to_list with
                | [ j ] -> (
                    match Jmp.kind j with Goto (Indirect _) -> true | _ -> false)
                | _ -> false)
            | None -> false
          in
          return_edge && dispatch_stays
          && Int.equal (Term.enum blk_t s |> Seq.length) 7
        in
        let dispatch_cases =
          match
            Core.Map.find resolved (Term.tid (sub_jmp sub 4 0))
          with
          | Some ts ->
            Core.Set.equal ts (Tid.Set.of_list [ tids.(3); tids.(5) ])
          | None -> false
        in
        check "RES-27a the fixture has both return-address cells"
          (Core.Set.mem retaddr (Term.tid ra_ld)
           && Core.Set.mem retaddr (Term.tid rar_ld));
        check "RES-27b the dispatch keeps its two cases" (grew && dispatch_cases);
        check "RES-27c materialization keeps the return and dispatch"
          (outcome materialized));
  ]

let () = run "resolve" tests
