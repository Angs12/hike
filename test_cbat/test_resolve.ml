(* The indirect-target resolution's pins: the resolution predicate's
   four classes ([Hike.Resolve.resolve_target] — the singleton lifted
   sub resolves, the bounded multi-target set, the foreign singleton,
   and TOP take the pointer call), and the producer's indirect-transfer
   classification through the REAL fixpoint (the [T22-J] family: the
   [Ret] epilogue arm, the in-sub [Resolved] dispatch, the [Foreign]
   identity, the untagged structural transfers). *)

open Test_common
open Test_fixtures
open Bap.Std
open Bap_core_theory

module Sm = Hike.Stack_model
module Pr = Hike.Sections
module Hv = Hike.Vsa

(* 64-bit literal word (native-int [w64] covers 63 bits only). *)
let q64 (v : int64) : Cbat_word.t = Cbat_word.of_int64 ~width:64 v

(* The target-resolution predicate's four classes. *)

let run_t4_resolution () =
  let callee_tid = Tid.for_name "res_callee" in
  let lifted v = if Int64.equal v 0x1000L then Some callee_tid else None in
  let ws_singleton (v : int64) : Cbat_vsa.WordSet.t =
    Cbat_vsa.WordSet.singleton (w64 (Int64.to_int v))
  in
  (* 1. singleton lifted sub: the Resolved Call Site (direct). *)
  check "T4-RES singleton: a singleton naming a lifted sub resolves direct"
    (Hike.Resolve.resolve_target ~lookup:lifted (ws_singleton 0x1000L)
     = Some callee_tid);
  (* 2. bounded multi-target set: the pointer call. *)
  check "T4-RES multi: a bounded two-target set takes the pointer call"
    (Hike.Resolve.resolve_target ~lookup:lifted
       (Cbat_vsa.WordSet.union (ws_singleton 0x1000L)
          (ws_singleton 0x1008L))
     = None);
  (* 3. foreign singleton (no lifted sub at the address): pointer call. *)
  check "T4-RES foreign: a foreign singleton takes the pointer call"
    (Hike.Resolve.resolve_target ~lookup:lifted (ws_singleton 0x9999L) = None);
  (* 4. unresolvable (TOP): pointer call. *)
  check "T4-RES top: an unresolvable target set takes the pointer call"
    (Hike.Resolve.resolve_target ~lookup:lifted (Cbat_vsa.WordSet.top 64) = None);
  ()

(* Lane N8: the completion's rewrite — the indirect-transfer classes
   land in the BIR TERMS (the real [Ret] jmp, the guarded-goto
   dispatch series); the classes are no longer a map. *)

let jmps_of_blk sub i =
  List.nth (Term.enum blk_t sub |> Seq.to_list) i
  |> Term.enum jmp_t |> Seq.to_list

let run_jmp_kinds () =
  (* J1: the lifted return epilogue — [#t := mem[RSP]]; call #t
     noreturn — the target var's reaching def is the retaddr read. *)
  let j1_ra = v64 "t22_j1_ra" in
  let j1_ld =
    Def.create j1_ra (Bil.Load (Bil.Var (memv "t22_j1_m"), Bil.Var sp,
                                LittleEndian, `r64))
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
  let j1_retaddr =
    let sol =
      Cbat_vsa.static_graph_vsa
        ~abi:Hike_abi.x86_64_sysv
        ~resolved:Tid.Map.empty (Program.create ~subs:[ j1 ] ()) j1
        (Cbat_vsa.init_sol ~abi:Hike_abi.x86_64_sysv j1)
    in
    Hike.Cfg_complete.retaddr_defs ~abi:Hike.Abi.x86_64_sysv ~sol j1
  in
  check "T22-J1: the epilogue's [RSP] load is the retaddr read"
    (Core.Set.mem j1_retaddr (Term.tid j1_ld));
  check "N8-RET: the epilogue lands in the canonical return shape (a var-free return-less call)"
    (match jmps_of_blk j1' 0 with
     | [ j ] -> (
         match Jmp.kind j with
         | Call c -> (
             match (Call.return c, Call.target c) with
             | None, Indirect (Bil.Unknown _) -> true
             | _ -> false)
         | _ -> false)
     | _ -> false);
  (* J1b: the control — the same target read behind a return=Some call
     is a real indirect call, not the epilogue: no rewrite. *)
  let j1b, _ =
    sub_of "t22_call"
      [ [ j1_ld ],
        [ (1,
           fun t ->
             Jmp.create (Call (Call.create ~return:(Direct t) ~target:(Indirect (Bil.Var j1_ra)) ()))) ];
        [], [ (0, mk_ret) ] ]
  in
  let _, j1b', _ =
    produce Theory.Target.unknown (Program.create ~subs:[ j1b ] ()) j1b
  in
  check "T22-J1b: a return=Some call with the same target stays a call (no rewrite)"
    (match jmps_of_blk j1b' 0 with
     | [ j ] -> (
         match Jmp.kind j with Call _ -> true | _ -> false)
     | _ -> false);
  (* J2: the jump-table dispatch — the target var's denotation joins
     two in-sub block constants; block_addrs names both blocks' tids,
     so every word of the set resolves in-sub.  The exit series is one
     conditional goto per distinct case target, guarded in the delta
     domain — no unconditional default exists. *)
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
  (* the guards live in the DELTA domain: the target's delta summand
     equals the table's own entry *)
  let eq_delta v w j =
    match Jmp.cond j with
    | Bil.BinOp (Bil.EQ, Bil.Var v', Bil.Int w') ->
      Var.equal v' v
      && Int64.equal (Word.to_int64_exn w') w
    | _ -> false
  in
  check "N8-DISP: the dispatch becomes a delta-guarded series, one goto per case target"
    (match jmps_of_blk j2' 3 with
     | [ g1; g2 ] ->
       (match Jmp.kind g1, Jmp.kind g2 with
        | Goto (Direct t1), Goto (Direct t2) ->
          Tid.equal t1 b1_tid && Tid.equal t2 b2_tid
          && eq_delta j2_sel 0x1008L g1 && eq_delta j2_sel 0x1010L g2
        | _ -> false)
     | _ -> false);
  (* The bake pin: a one-word resolution materializes nothing — the
     dispatch stays as it came; the unconditional default is
     unrepresentable.  The analysis edge (the resolved case) still
     exists; only the BIR claim is withheld. *)
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
  check "FUSED-BAKE: a one-word resolution materializes nothing (the dispatch stays)"
    (match jmps_of_blk j5' 0 with
     | [ j ] -> (
         match Jmp.kind j with
         | Goto (Indirect (Bil.BinOp (Bil.PLUS, Bil.Var a, Bil.Var b))) ->
           Var.equal a j5_sel && Var.equal b j5_base
         | _ -> false)
     | _ -> false);
  (* The growth pin: the loop closes through the analysis edges — the
     case body's increment flows back to the head, the selector widens
     in the same run that first resolved the dispatch, the mid-block
     case entry splits as soon as the resolution names it (nothing
     targets the container, so the prefix drops), and the exit series
     carries one guarded goto per table entry. *)
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
  let envs6, j6', block_addrs6 =
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
    | Error _ -> 0L in
  let j6_fresh = Core.Map.find block_addrs6 (Addr.of_int64 0x3010L) in
  check "FUSED-GROWTH: the selector widens in the same run (the loop closed through analysis edges)"
    (Int64.equal sel_card 2L);
  check "FUSED-GROWTH: the mid-block case entry split, the fresh entry block took the address"
    (match j6_fresh with
     | Some t ->
       not (Tid.equal t j6_tids.(3))
       && Base.List.exists (Term.enum blk_t j6' |> Seq.to_list)
            ~f:(fun b ->
              match Term.get_attr b address with
              | Some a -> Word.equal a (Cbat_word.to_word (q64 0x3010L))
              | None -> false)
     | None -> false);
  check "FUSED-GROWTH: the exit series carries one guarded goto per table entry"
    (match j6_fresh with
     | None -> false
     | Some fresh ->
       (match jmps_of_blk j6' 1 with
        | [ g1; g2 ] ->
          (match Jmp.kind g1, Jmp.kind g2 with
           | Goto (Direct t1), Goto (Direct t2) ->
             Tid.equal t1 j6_tids.(2) && Tid.equal t2 fresh
             && eq_delta j6_sel 0x1008L g1 && eq_delta j6_sel 0x1010L g2
           | _ -> false)
        | _ -> false));
  (* The retraction pin: a resolution whose materialization declines
     (a cross-sub word keeps the pairs list empty) leaves its eager
     split unclaimed — the exit prune retracts it, and no pred-less
     block survives. *)
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
    sub_of "t22_retract"
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
  check "FUSED-RETRACT: the unclaimed eager split is retracted at exit"
    (Base.List.find_map (Term.enum blk_t j7' |> Seq.to_list)
       ~f:(fun b ->
         match Term.get_attr b address with
         | Some a when Word.equal a (Cbat_word.to_word (q64 0x3008L)) -> Some true
         | _ -> None)
     = None);
  (* J4: a word the run's map cannot name is a loud failure — a
     resolvable dispatch (the set's size within the block count) whose
     table word names no block is an analysis loss, never a silent
     foreign transfer.  The map here carries an unrelated second block
     so the shape test passes and the lookup itself is what misses. *)
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
  check "T22-J4: a dispatch word the map cannot name fails loudly"
    (try
       ignore
         (produce Theory.Target.unknown
            ~block_addrs:
              [ (0x3008L, j4_tids.(4)); (0x400000L, j4_tids.(5)) ]
            (Program.create ~subs:[ j4 ] ()) j4);
       false
     with Failure _ -> true);
  (* J3: a foreign pointer target (a constant naming no block) — the
     indirect transfer stays. *)
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
  check "T22-J3: a foreign pointer target is untouched by the rewrite"
    (match jmps_of_blk j3' 0 with
     | [ j ] -> (
         match Jmp.kind j with Goto (Indirect _) -> true | _ -> false)
     | _ -> false);
  (* J3b: the TOP target (an undefined var) stays too. *)
  let j3b_top = v64 "t22_j3b_top" in
  let j3b, _ =
    sub_of "t22_top"
      [ [], [ (1, fun _ -> Jmp.create (Goto (Indirect (Bil.Var j3b_top)))) ];
        [], [ (0, mk_ret) ] ]
  in
  let _, j3b', _ =
    produce Theory.Target.unknown (Program.create ~subs:[ j3b ] ()) j3b
  in
  check "T22-J3b: a TOP target is untouched by the rewrite"
    (match jmps_of_blk j3b' 0 with
     | [ j ] -> (
         match Jmp.kind j with Goto (Indirect _) -> true | _ -> false)
     | _ -> false)

let run () =
  run_t4_resolution ();
  run_jmp_kinds ()
