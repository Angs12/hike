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

(* The dispatch guard lives in the DELTA domain: the target's delta summand
   equals the table's own entry. *)
let eq_delta v w j =
  match Jmp.cond j with
  | Bil.BinOp (Bil.EQ, Bil.Var v', Bil.Int w') ->
    Var.equal v' v && Int64.equal (Word.to_int64_exn w') w
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
            Cbat_vsa.static_graph_vsa ~abi:Hike.Abi.x86_64_sysv
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
           | [ j ] -> Hike__Hike_return.is_jmp j
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
           | [ j ] -> Hike__Hike_return.is_jmp j
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
      "N8-DISP: the dispatch becomes a delta-guarded series, one goto per case target, plus its named false edge"
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
                && eq_delta j2_sel 0x1008L g1 && eq_delta j2_sel 0x1010L g2
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

    pin "RES-11"
      "FUSED-GROWTH: the mid-block case entry split, the fresh entry block took the address"
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
        let _, j6', block_addrs6 =
          produce Theory.Target.unknown
            ~block_addrs:[ (0x3008L, j6_tids.(2)); (0x300cL, j6_tids.(3)) ]
            (Program.create ~subs:[ j6 ] ()) j6
        in
        let j6_fresh = Core.Map.find block_addrs6 (Addr.of_int64 0x3010L) in
        check "RES-11"
          (match j6_fresh with
           | Some t ->
             not (Tid.equal t j6_tids.(3))
             && Base.List.exists (Term.enum blk_t j6' |> Seq.to_list)
                  ~f:(fun b ->
                    match Term.get_attr b address with
                    | Some a -> Word.equal a (Cbat_word.to_word (q64 0x3010L))
                    | None -> false)
           | None -> false));

    pin "RES-12"
      "FUSED-GROWTH: the exit series carries one guarded goto per table entry, plus its named false edge"
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
        let _, j6', block_addrs6 =
          produce Theory.Target.unknown
            ~block_addrs:[ (0x3008L, j6_tids.(2)); (0x300cL, j6_tids.(3)) ]
            (Program.create ~subs:[ j6 ] ()) j6
        in
        let j6_fresh = Core.Map.find block_addrs6 (Addr.of_int64 0x3010L) in
        check "RES-12"
          (match j6_fresh with
           | None -> false
           | Some fresh ->
             (match jmps_of_blk j6' 1 with
              | g1 :: g2 :: _ ->
                (match Jmp.kind g1, Jmp.kind g2 with
                 | Goto (Direct t1), Goto (Direct t2) ->
                   Tid.equal t1 j6_tids.(2) && Tid.equal t2 fresh
                   && eq_delta j6_sel 0x1008L g1 && eq_delta j6_sel 0x1010L g2
                 | _ -> false)
              | _ -> false)));

    (* The liveness pin: a resolution whose materialization declines
       (a cross-sub word keeps the pairs list empty) leaves its eager
       split unclaimed — but the surviving indirect transfer still
       denotes the split's address, so the address-bearing fresh block
       stays (the runtime transfer may land on it). *)
    pin "RES-13"
      "FUSED-LIVE: an unresolved indirect transfer's denotation keeps its split fresh block"
      (fun () ->
        let j7_sel = v64 "t22_j7_sel" in
        let j7_base = v64 "t22_j7_base" in
        let j7_bdef = Def.create j7_base (Bil.Int (Cbat_word.to_word (q64 0x2000L))) in
        let j7_s1 = Def.create j7_sel (Bil.Int (Cbat_word.to_word (q64 0x1008L))) in
        let j7_s2 = Def.create j7_sel (Bil.Int (Cbat_word.to_word (q64 0x7000L))) in
        let j7_flag = v1 "t22_j7_flag" in
        let j7_pad = v64 "t22_j7_pad" in
        let j7_pivot = Def.create j7_pad (Bil.Int (Cbat_word.to_word (q64 0L))) in
        let j7_pivot = Term.set_attr j7_pivot address (Cbat_word.to_word (q64 0x3008L)) in
        let j7, j7_tids =
          sub_of "t22_live"
            [ [ j7_bdef ], [ (1, fun t -> mk_jmp_to t (Bil.Var j7_flag)); (2, mk_goto) ];
              [ j7_s1 ], [ (3, mk_goto) ];
              [ j7_s2 ], [ (3, mk_goto) ];
              [], [ (4, fun _ -> Jmp.create (Goto (Indirect (Bil.BinOp (Bil.PLUS, Bil.Var j7_sel, Bil.Var j7_base))))) ];
              [ j7_pivot ], [ (5, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let _, j7', _ =
          produce Theory.Target.unknown
            ~block_addrs:[ (0x2000L, j7_tids.(4)); (0x9000L, Tid.create ()) ]
            (Program.create ~subs:[ j7 ] ()) j7
        in
        check "RES-13"
          (Base.List.exists (Term.enum blk_t j7' |> Seq.to_list)
             ~f:(fun b ->
               match Term.get_attr b address with
               | Some a -> Word.equal a (Cbat_word.to_word (q64 0x3008L))
               | None -> false)));

    (* J4: a word the run's map cannot name is a loud failure. *)
    pin "RES-14" "T22-J4: a dispatch word the map cannot name fails loudly"
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
        check "RES-14"
          (try
             ignore
               (produce Theory.Target.unknown
                  ~block_addrs:
                    [ (0x3008L, j4_tids.(4)); (0x400000L, j4_tids.(5)) ]
                  (Program.create ~subs:[ j4 ] ()) j4);
             false
           with Failure _ -> true));

    (* The materializer retargets an existing indirect transfer to the
       addresses named by the case. *)
    pin "RES-21"
      "the materializer: a gap word re-lifts its case body and retargets existing blocks"
      (fun () ->
        let j8_sel = v64 "t22_j8_sel" in
        let j8_base = v64 "t22_j8_base" in
        let j8_bdef =
          Def.create j8_base (Bil.Int (Cbat_word.to_word (q64 0x2000L)))
        in
        let j8_t1 =
          Def.create j8_sel (Bil.Int (Cbat_word.to_word (q64 0x1008L)))
        in
        let j8_t2 =
          Def.create j8_sel (Bil.Int (Cbat_word.to_word (q64 0x1010L)))
        in
        let j8_flag = v1 "t22_j8_flag" in
        let j8, j8_tids =
          sub_of "t22_materialize"
            [ [ j8_bdef ],
              [ (1, fun t -> mk_jmp_to t (Bil.Var j8_flag)); (2, mk_goto) ];
              [ j8_t1 ], [ (3, mk_goto) ];
              [ j8_t2 ], [ (3, mk_goto) ];
              [],
              [ (4,
                 fun _ ->
                   Jmp.create
                     (Goto
                        (Indirect
                           (Bil.BinOp (Bil.PLUS, Bil.Var j8_sel, Bil.Var j8_base))))) ];
              [], [ (6, mk_goto) ];
              [], [ (6, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let a = Addr.of_int64 0x3010L in
        let b = Addr.of_int64 0x3014L in
        let materialized =
          let e = Blk.Builder.create ~tid:(Tid.for_addr a) () in
          Blk.Builder.add_jmp e
            (Jmp.create
               (Goto (Direct (Tid.for_addr (Addr.of_int64 0x3008L)))));
          let e = Term.set_attr (Blk.Builder.result e) address a in
          let i = Blk.Builder.create ~tid:(Tid.for_addr b) () in
          let i = Term.set_attr (Blk.Builder.result i) address b in
          [ e; i ]
        in
        let _, sub8', block_addrs8 =
          produce Theory.Target.unknown
            ~block_addrs:
              [ (0x3008L, j8_tids.(4)); (0x400000L, j8_tids.(5)) ]
            ~lift_at:(fun a' ~block_addrs:_ ->
              if Addr.equal a' a then Some materialized else None)
            (Program.create ~subs:[ j8 ] ()) j8
        in
        let named =
          match Core.Map.find block_addrs8 a with
          | Some t -> Tid.equal t (Tid.for_addr a)
          | None -> false
        in
        (* Every new block is registered, not just the dispatch entry. *)
        let registered =
          match Core.Map.find block_addrs8 b with
          | Some t -> Tid.equal t (Tid.for_addr b)
          | None -> false
        in
        let retargeted =
          Term.enum blk_t sub8'
          |> Seq.find ~f:(fun b -> Tid.equal (Term.tid b) (Tid.for_addr a))
          |> Base.Option.value_map ~default:false ~f:(fun b ->
                 match Term.enum jmp_t b |> Seq.to_list with
                 | [ j ] -> (
                     match Jmp.kind j with
                     | Goto (Direct t) -> Tid.equal t j8_tids.(4)
                     | _ -> false)
                 | _ -> false)
        in
        check "RES-21" (named && registered && retargeted));

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
              Cbat_vsa.static_graph_vsa ~abi:Hike.Abi.x86_64_sysv
                j5
                (Cbat_vsa.init_sol ~abi:Hike.Abi.x86_64_sysv ~entry j5)
            in
            let sub5', resolved5', fresh5', _, events5 =
              Hike.Cfg_complete.resolve_phase ~abi:Hike.Abi.x86_64_sysv ~sol
                ~lift_at:(fun _ ~block_addrs:_ -> None)
                ~block_addrs:
                  (Core.Map.of_alist_exn (module Addr)
                     [ (Addr.of_int64 0x3008L, j5_tids.(1)) ])
                ~sub_addrs:(Core.Map.empty (module Addr))
                j5 Tid.Map.empty
            in
            (not events5) && Core.Set.is_empty fresh5'
            && Core.Map.is_empty resolved5'));



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
    pin "RES-24" "the materializer fissions a re-lifted def's memory nodes"
      (fun () ->
        let sel = v64 "t23_sel" in
        let base = v64 "t23_base" in
        let bdef = Def.create base (Bil.Int (Cbat_word.to_word (q64 0x2000L))) in
        let t1 = Def.create sel (Bil.Int (Cbat_word.to_word (q64 0x1008L))) in
        let t2 = Def.create sel (Bil.Int (Cbat_word.to_word (q64 0x1010L))) in
        let flag = v1 "t23_flag" in
        let sub24, tids =
          sub_of "t23_refiss"
            [ [ bdef ],
              [ (1, fun t -> mk_jmp_to t (Bil.Var flag)); (2, mk_goto) ];
              [ t1 ], [ (3, mk_goto) ];
              [ t2 ], [ (3, mk_goto) ];
              [],
              [ (4,
                 fun _ ->
                   Jmp.create
                     (Goto
                        (Indirect
                           (Bil.BinOp (Bil.PLUS, Bil.Var sel, Bil.Var base))))) ];
              [], [ (6, mk_goto) ];
              [], [ (6, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let a = Addr.of_int64 0x3010L in
        let m = memv "t23_m" in
        let src = v64 "t23_src" in
        let dst = v64 "t23_dst" in
        let double_load =
          Def.create dst
            (Bil.Load
               ( Bil.Var m,
                 Bil.Load (Bil.Var m, Bil.Var src, LittleEndian, `r64),
                 LittleEndian, `r64 ))
        in
        let lifted =
          let e = Blk.Builder.create ~tid:(Tid.for_addr a) () in
          Blk.Builder.add_def e double_load;
          Blk.Builder.add_jmp e
            (Jmp.create (Goto (Direct (Tid.for_addr (Addr.of_int64 0x3008L)))));
          let e = Term.set_attr (Blk.Builder.result e) address a in
          [ e ]
        in
        let _, sub24', _ =
          produce Theory.Target.unknown
            ~block_addrs:[ (0x3008L, tids.(4)); (0x400000L, tids.(5)) ]
            ~lift_at:(fun a' ~block_addrs:_ ->
              if Addr.equal a' a then Some lifted else None)
            (Program.create ~subs:[ sub24 ] ()) sub24
        in
        match
          Term.enum blk_t sub24'
          |> Seq.find ~f:(fun b -> Tid.equal (Term.tid b) (Tid.for_addr a))
        with
        | Some b ->
            let defs = Term.enum def_t b |> Seq.to_list in
            let one_node =
              Base.List.for_all defs ~f:(fun d ->
                  Hike__Hike_stack_model.mem_node_count (Def.rhs d) <= 1)
            in
            check "RES-24" (Base.List.length defs >= 2 && one_node)
        | None -> check "RES-24" false);
  ]

let () = run "resolve" tests
