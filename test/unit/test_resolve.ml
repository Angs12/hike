(* Indirect-target resolution pins.  One Alcotest group per pin; each pin
   builds its own fixture, so no state crosses pins. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

(* 64-bit literal word (native-int [w64] covers 63 bits only). *)

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
let eq_target (a : var) (b : var) (w : int64) j =
  match Jmp.cond j with
  | Bil.BinOp
      (Bil.EQ, Bil.BinOp (Bil.PLUS, Bil.Var a', Bil.Var b'), Bil.Int w') ->
    Var.equal a' a && Var.equal b' b && Int64.equal (Word.to_int64_exn w') w
  | _ -> false

(* [of_wordset] fans: the pinned fixtures are single-piece address lines. *)
let check_key1 name ks f =
  check name (match ks with [ k ] -> f k | _ -> false)

let tests : unit Alcotest.test list =
  [
    (* T4-RES: the target-resolution predicate's four classes. *)
    pin "RES-01"
      "T4-RES singleton: a singleton naming a lifted sub resolves direct"
      (fun () ->
        let callee_tid = Tid.for_name "res_callee" in
        let lifted v = if Int64.equal v 0x1000L then Some callee_tid else None in
        check "RES-01"
          (Hike.Resolve.resolve_target ~lookup:lifted (ws_singleton 0x1000L)
           = Some callee_tid));

    pin "RES-02" "T4-RES multi: a bounded two-target set takes the pointer call"
      (fun () ->
        let callee_tid = Tid.for_name "res_callee" in
        let lifted v = if Int64.equal v 0x1000L then Some callee_tid else None in
        check "RES-02"
          (Hike.Resolve.resolve_target ~lookup:lifted
             (Cbat_vsa.WordSet.union (ws_singleton 0x1000L) (ws_singleton 0x1008L))
           = None));

    pin "RES-03" "T4-RES foreign: a foreign singleton takes the pointer call"
      (fun () ->
        let callee_tid = Tid.for_name "res_callee" in
        let lifted v = if Int64.equal v 0x1000L then Some callee_tid else None in
        check "RES-03"
          (Hike.Resolve.resolve_target ~lookup:lifted (ws_singleton 0x9999L) = None));

    pin "RES-04" "T4-RES top: an unresolvable target set takes the pointer call"
      (fun () ->
        let callee_tid = Tid.for_name "res_callee" in
        let lifted v = if Int64.equal v 0x1000L then Some callee_tid else None in
        check "RES-04"
          (Hike.Resolve.resolve_target ~lookup:lifted (Cbat_vsa.WordSet.top 64) = None));

    (* T22-J1: the lifted return epilogue — [#t := mem[RSP]]; call #t
       noreturn — the target var's reaching def is the retaddr read. *)
    pin "RES-05" "T22-J1: the epilogue's [RSP] load is the retaddr read"
      (fun () ->
        let j1_ra = v64 "t22_j1_ra" in
        let j1_ld =
          Def.create j1_ra
            (Bil.Load (Bil.Var (memv "t22_j1_m"), Bil.Var sp, LittleEndian, `r64))
        in
        let j1, _ =
          sub_of "t22_ret"
            [ [ j1_ld ],
              [ (1, fun t -> Jmp.create (Call (Call.create ~target:(Indirect (Bil.Var j1_ra)) ()))) ];
              [], [ (0, mk_ret) ] ]
        in
        let j1_retaddr =
          let sol =
            static_graph_vsa ~abi:Hike.Abi.x86_64_sysv
              ~resolved:Tid.Map.empty j1
              (Cbat_vsa.init_sol ~abi:Hike.Abi.x86_64_sysv j1)
          in
          Hike.Cfg_complete.retaddr_defs ~abi:Hike.Abi.x86_64_sysv ~sol j1
        in
        check "RES-05" (Core.Set.mem j1_retaddr (Term.tid j1_ld)));

    pin "RES-06"
      "N8-RET: the epilogue lands in the canonical direct return edge"
      (fun () ->
        let j1_ra = v64 "t22_j1_ra" in
        let j1_ld =
          Def.create j1_ra
            (Bil.Load (Bil.Var (memv "t22_j1_m"), Bil.Var sp, LittleEndian, `r64))
        in
        let j1, _ =
          sub_of "t22_ret"
            [ [ j1_ld ],
              [ (1, fun t -> Jmp.create (Call (Call.create ~target:(Indirect (Bil.Var j1_ra)) ()))) ];
              [], [ (0, mk_ret) ] ]
        in
        let _, j1', _ =
          produce Theory.Target.unknown (Program.create ~subs:[ j1 ] ()) j1
        in
        check "RES-06"
          (match jmps_of_blk j1' 0 with
           | [ j ] -> Hike_return.is_jmp j
           | _ -> false));

    (* The lifted `ret` is a plain `Goto` (BAP lifts `retq` as
       `jmp #retaddr`), not a call; the same retaddr read behind it is
       the epilogue and canonicalizes to a direct return edge. *)
    pin "RES-22"
      "the lifted `ret` Goto canonicalizes to the var-free return"
      (fun () ->
        let j9_ra = v64 "t22_j9_ra" in
        let j9_ld =
          Def.create j9_ra
            (Bil.Load
               (Bil.Var (memv "t22_j9_m"), Bil.Var sp, LittleEndian, `r64))
        in
        let j9, _ =
          sub_of "t22_ret_goto"
            [ [ j9_ld ],
              [ (1, fun _ -> Jmp.create (Goto (Indirect (Bil.Var j9_ra)))) ];
              [], [ (0, mk_ret) ] ]
        in
        let _, j9', _ =
          produce Theory.Target.unknown (Program.create ~subs:[ j9 ] ()) j9
        in
        check "RES-22"
          (match jmps_of_blk j9' 0 with
           | [ j ] -> Hike_return.is_jmp j
           | _ -> false));

    (* J1b: the control — the same target read behind a return=Some call
       is a real indirect call, not the epilogue: no rewrite. *)
    pin "RES-07"
      "T22-J1b: a return=Some call with the same target stays a call (no rewrite)"
      (fun () ->
        let j1_ra = v64 "t22_j1_ra" in
        let j1_ld =
          Def.create j1_ra
            (Bil.Load (Bil.Var (memv "t22_j1_m"), Bil.Var sp, LittleEndian, `r64))
        in
        let j1b, _ =
          sub_of "t22_call"
            [ [ j1_ld ],
              [ (1,
                 fun t ->
                   Jmp.create
                     (Call (Call.create ~return:(Direct t) ~target:(Indirect (Bil.Var j1_ra)) ()))) ];
              [], [ (0, mk_ret) ] ]
        in
        let _, j1b', _ =
          produce Theory.Target.unknown (Program.create ~subs:[ j1b ] ()) j1b
        in
        check "RES-07"
          (match jmps_of_blk j1b' 0 with
           | [ j ] -> (match Jmp.kind j with Call _ -> true | _ -> false)
           | _ -> false));

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
        let _, j2', _ =
          produce Theory.Target.unknown
            ~block_addrs:[ (0x3008L, b1_tid); (0x3010L, b2_tid) ]
            (Program.create ~subs:[ j2 ] ()) j2
        in
        check "RES-08"
          (match jmps_of_blk j2' 3 with
           | g1 :: g2 :: _ ->
             (match Jmp.kind g1, Jmp.kind g2 with
              | Goto (Direct t1), Goto (Direct t2) ->
                Tid.equal t1 b1_tid && Tid.equal t2 b2_tid
                && eq_target j2_sel j2_base 0x3008L g1
                && eq_target j2_sel j2_base 0x3010L g2
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
          produce Theory.Target.unknown
            ~block_addrs:[ (0x3008L, j5_tids.(1)) ]
            (Program.create ~subs:[ j5 ] ()) j5
        in
        check "RES-09"
          (match jmps_of_blk j5' 0 with
           | [ j ] -> (
               match Jmp.kind j with
               | Goto (Indirect (Bil.BinOp (Bil.PLUS, Bil.Var a, Bil.Var b))) ->
                 Var.equal a j5_sel && Var.equal b j5_base
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
        let envs6, _, _ =
          produce Theory.Target.unknown
            ~block_addrs:[ (0x3008L, j6_tids.(2)); (0x300cL, j6_tids.(3)) ]
            (Program.create ~subs:[ j6 ] ()) j6
        in
        let head_post =
          match Core.Map.find envs6 j6_tids.(1) with
          | Some (_, post) -> post
          | None -> Cbat_vsa.AI.top
        in
        let head_sel = Cbat_vsa.AI.find_word 64 head_post j6_sel in
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
          produce Theory.Target.unknown
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
                 Var.equal a j7_sel && Var.equal b j7_base
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
          produce Theory.Target.unknown
            ~block_addrs:[ (0x3008L, j4_tids.(4)); (0x400000L, j4_tids.(5)) ]
            (Program.create ~subs:[ j4 ] ()) j4
        in
        check "RES-14"
          (match jmps_of_blk j4' 3 with
           | [ j ] -> (
               match Jmp.kind j with
               | Goto (Indirect (Bil.BinOp (Bil.PLUS, Bil.Var a, Bil.Var b))) ->
                 Var.equal a j4_sel && Var.equal b j4_base
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
          produce Theory.Target.unknown (Program.create ~subs:[ j3 ] ()) j3
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
              static_graph_vsa ~abi:Hike.Abi.x86_64_sysv
                j5
                (Cbat_vsa.init_sol ~abi:Hike.Abi.x86_64_sysv ~entry j5)
            in
            let resolved5', events5 =
              Hike.Cfg_complete.resolve_phase ~abi:Hike.Abi.x86_64_sysv ~sol
                                ~block_addrs:
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
          Sub.Builder.result sb
        in
        let envs, sub25', ba' =
          produce ~block_addrs:
            [ (0x2000L, tids.(0)); (0x2008L, tids.(1)); (0x2010L, tids.(2));
              (0x2018L, tids.(3)); (0x2020L, tids.(4)); (0x3000L, tids.(5));
              (0x3008L, tids.(6)); (0x2028L, tids.(7)) ]
            ~images Theory.Target.unknown
            (Program.create ~subs:[ stamped ] ()) stamped
        in
        (* The dispatch materializes after the solve, in split-blocks:
           the bounded denotation names the case blocks, the composed
           base gives the guards' delta coordinate. *)
        let facts =
          { (Hike.Kb.build ~lookup:(fun _ -> None) ~block_envs:envs
               ~block_addrs:ba' ~target:Theory.Target.unknown) with
            images;
            foreign_slots = Core.Int64.Set.empty }
        in
        let materialized =
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
              | Goto (Direct t') ->
                Tid.equal t' t
                && not (Hike.Stack_model.is_true_cond (Jmp.cond j))
              | _ -> false)
        in
        let resolved =
          has_case tids.(5) && has_case tids.(6)
          && not
               (Base.List.exists disp_jmps ~f:(fun j ->
                    match Jmp.kind j with
                    | Goto (Indirect _) -> true
                    | _ -> false))
        in
        let direct_same_target =
          match Jmp.kind (Term.enum jmp_t (blk_of tids.(4)) |> Seq.hd_exn) with
          | Goto (Direct t) -> Tid.equal t tids.(5)
          | _ -> false
        in
        let map_names_case =
          match Core.Map.find ba' (Addr.of_int64 0x3000L) with
          | Some t -> Tid.equal t tids.(5)
          | None -> false
        in
        check "RES-25a the dispatch resolves to its case blocks" resolved;
        check "RES-25b the direct caller keeps the case block" direct_same_target;
        check "RES-25c the map names the case block" map_names_case);
  ]

let () = run "resolve" tests
