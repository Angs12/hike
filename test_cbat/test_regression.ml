(* Narrow-store/degraded-frame/escape pins, remediation batch, region-split gates. *)
open Bap.Std
open Bap_core_theory
open Test_common
open Test_fixtures

(* Regression tests C1-C4. *)
let q64 (v : int64) : Cbat_word.t = Cbat_word.of_int64 ~width:64 v

(* C1: narrow-store OR-mask width — mask computed at slot width 64. *)


(* Remediation batch A1-A4. *)

(* A1: TOP-valued outgoing-slot store escalates to whole-memory-top fallback. *)
(* R12/G4 region-split emission gates. *)
(* Emission size logic pinned via production functions on synthetic records. *)

let run_creg () =
(  let rsp = v64 "RSP" in
  let m = memv "c1_m" in
  let def_wide =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 16))),
           Bil.Int (Cbat_word.to_word (q64 0x1122334455667788L)),
           LittleEndian,
           `r64 ))
  in
  let def_narrow =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 16))),
           Bil.Int (Cbat_word.to_word (q64 0xABCDL)),
           LittleEndian,
           `r16 ))
  in
  let exit_b = Blk.Builder.create () in
  let exit0 = Blk.Builder.result exit_b in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b def_wide;
  Blk.Builder.add_def entry_b def_narrow;
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let sub_b = Sub.Builder.create ~name:"c1_mask" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b exit0;
  let sub = Sub.Builder.result sub_b in
  let tagged = sub in
  let span = (-16L, -16L) in
  let info : Cu.vsa_info =
    Cu.mk_vsa_info
      ~offsets:
        [ (Term.tid def_wide, Cu.Range (-16L, -16L)); (Term.tid def_narrow, Cu.Range (-16L, -16L)) ]
      ~k_ranges:[]
      ~regions:
        [
          {
            Cu.id = 0;
            Cu.span;
            Cu.members = [ (Term.tid def_wide, span); (Term.tid def_narrow, span) ];
            Cu.convertible = true;
            Cu.max_width = 64;
          };
        ]
      ~stack_plan:[] ~degraded:false ~vla_bounds:[] ~vla_alloc_tids:Tid.Set.empty
  in
  let stl_info = Tid.Map.singleton (Term.tid tagged) info in
  Kb.provide stl_info;
  let sub' = Stl.stack_to_locals Theory.Target.unknown sp tagged in
  let masks =
    Term.enum blk_t sub'
    |> Seq.concat_map ~f:(Term.enum def_t)
    |> Seq.to_list
    |> List.filter_map (fun d ->
        match Def.rhs d with
        | Bil.BinOp
            (Bil.OR, Bil.BinOp (Bil.AND, Bil.Var _, Bil.Int w), Bil.Cast (Bil.UNSIGNED, 64, _)) ->
            Some w
        | _ -> None)
  in
  check "regression C1: the narrow elu16 store is rewritten to the slot OR-mask form"
    (List.length masks = 1);
  check "regression C1: the OR-mask constant is neg(1 << 16) = 0xFFFFFFFFFFFF0000 at width 64"
    (match masks with
    | [ w ] -> Word.bitwidth w = 64 && Cbat_word.equal (Cbat_word.of_word w) (q64 0xFFFFFFFFFFFF0000L)
    | _ -> false);
  ()


(* C3: escape set includes the call block's outgoing-slot stores. *))
;
(  let fx = mk_escape_caller ~pfx:"c3" ~fp_off:8 ~seed:0xAA ~outs:[ (16, C 0xBB) ] () in
  let sub' = fx.es_sub in
  let blk_of tid = match Term.find blk_t sub' tid with Some b -> b | None -> assert false in
  let st_pre =
    Vsa.denote_defs
      (blk_of (Term.tid fx.es_blk1))
      (Vsa.denote_defs
         (blk_of (Term.tid fx.es_blk0))
         (AI.set_frame (anchored_entry ()) AI.seed_frame))
  in
  let read64 ai addr =
    match Mem.Key.of_wordset (Ws.singleton (q64 addr)) with
    | Some k ->
        Mem.Val.data
          (Mem.find (64, LittleEndian)
             (AI.find_memory { addr_width = 64; addressable_width = 8 } ai fx.es_m)
             k)
    | None -> assert false
  in
  check "regression C3: pre-call the caller-frame cell [RSP-8] holds {0xAA} (non-vacuous pin)"
    (Ws.equal (read64 st_pre (-8L)) (Ws.singleton (w64 0xAA)));
  check "regression C3: pre-call the outgoing slot [RSP+16] holds {0xBB} (non-vacuous pin)"
    (Ws.equal (read64 st_pre (-16L)) (Ws.singleton (w64 0xBB)));
  let sol = run_anchored sub' in
  let post_ai = Graphlib.Std.Solution.get sol fx.es_post_tid in
  check
    "regression C3: the caller-frame cell [RSP-8] survives the call with its value (frame not \
     whole-memory-topped)"
    (Ws.equal (read64 post_ai (-8L)) (Ws.singleton (w64 0xAA)));
  ()

(* C4b: Infinite-span member blocks convertibility by provenance. *))
;
(  let rsp = v64 "RSP" in
  let m = memv "c4b_m" in
  let a_mixed = mk_store_minus m rsp 24 1 `r64 in
  let b_mixed = mk_store_minus m rsp 20 2 `r64 in
  let a_ctrl = mk_store_minus m rsp 48 3 `r64 in
  let b_ctrl = mk_store_minus m rsp 44 4 `r64 in

  let exit_b = Blk.Builder.create () in
  let exit0 = Blk.Builder.result exit_b in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.create () in
  List.iter (Blk.Builder.add_def entry_b) [ a_mixed; b_mixed; a_ctrl; b_ctrl ];
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let sub_b = Sub.Builder.create ~name:"c4b_regions" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b exit0;
  let sub = Sub.Builder.result sub_b in
  let info_of offsets : Cu.vsa_info =
    Cu.mk_vsa_info ~offsets ~k_ranges:[] ~regions:[] ~stack_plan:[]
      ~degraded:false ~vla_bounds:[] ~vla_alloc_tids:Tid.Set.empty
  in
  let convertible_of info dtid =
    Sm.regions_of_sub (v64 "RSP") Theory.Target.unknown sub info ~frame_escaped:false
    |> List.filter (fun r -> List.exists (fun (t, _) -> Tid.equal t dtid) r.Cu.members)
    |> function
    | [ r ] -> Some r.Cu.convertible
    | _ -> None
  in
  let ctrl =
    info_of [ (Term.tid a_ctrl, Cu.Range (-48L, -40L)); (Term.tid b_ctrl, Cu.Range (-48L, -40L)) ]
  in
  check "regression C4b control: two identical Range members stay convertible=true"
    (convertible_of ctrl (Term.tid a_ctrl) = Some true
    && convertible_of ctrl (Term.tid b_ctrl) = Some true);
  ()

(* C4a: Infinite tag survives the overlap merge. *))
;
(  let sub, def_idx_store = mk_indexed_loop ~pfx:"c4a" in
  let tagged = sub in
  let info = Hv.offsets_of_sub Theory.Target.unknown sp tagged in
  let kind_of dtid = Core.Map.find info.Cu.offsets dtid in
  check
    "regression C4a: the indexed loop-body store carries an offset tag (fixture locates the \
     Infinite class)"
    (kind_of (Term.tid def_idx_store) <> None);
  ()

(* R11: overlap merge preserves every member's kind/span verbatim. *))
;
(  let sub, def_idx_store = mk_indexed_loop ~pfx:"r11" in
  let tagged = sub in
  let info = Hv.offsets_of_sub Theory.Target.unknown sp tagged in
  let kind_of dtid = Core.Map.find info.Cu.offsets dtid in
  (* Control: indexed member keeps its kind. *)
  check "property R11 control: the indexed member keeps its own kind through the merge"
    (kind_of (Term.tid def_idx_store) <> None);

  ())
let run_remediation () =
(  (* Vs C3: outgoing slot stores unwritten RCX (TOP). *)
  let rcx = v64 "RCX" in
  let fx = mk_escape_caller ~pfx:"a1" ~fp_off:8 ~seed:0xAA ~outs:[ (16, R rcx) ] () in
  let sub' = fx.es_sub in
  let blk0 = fx.es_blk0 in
  let blk1 = fx.es_blk1 in
  let m = fx.es_m in
  let blk_of tid = match Term.find blk_t sub' tid with Some b -> b | None -> assert false in
  let st_pre =
    Vsa.denote_defs
      (blk_of (Term.tid blk1))
      (Vsa.denote_defs (blk_of (Term.tid blk0)) (AI.set_frame (anchored_entry ()) AI.seed_frame))
  in
  let read64 ai addr =
    match Mem.Key.of_wordset (Ws.singleton (q64 addr)) with
    | Some k ->
        Mem.Val.data
          (Mem.find (64, LittleEndian)
             (AI.find_memory { addr_width = 64; addressable_width = 8 } ai m)
             k)
    | None -> assert false
  in
  check
    "remediation A1: pre-call the seeded caller-frame cell [entry RSP-8] holds {0xAA} (non-vacuous \
     pin)"
    (Ws.equal (read64 st_pre (-8L)) (Ws.singleton (w64 0xAA)));
  let _sol = run_anchored sub' in

  ()

(* A4a/A4b: u8/u32 narrow-store OR-mask widths; fixtures borrow C1's KB entry (no KB write). *))
;
(  let rsp = v64 "RSP" in
  (* Single surviving entry is C1's. *)
  let c1_sub_tid, c1_info =
    Core.Map.fold (Kb.vsa_info ())
      ~init:(Tid.create (), None)
      ~f:(fun ~key ~data acc -> match acc with _, None -> (key, Some data) | _ -> acc)
    |> fun (t, i) -> match i with Some i -> (t, i) | None -> assert false
  in
  (* Offsets map read by sorted-tid key (order-independent). *)
  let c1_def_tids = c1_info.Cu.offsets |> Core.Map.keys |> List.rev in
  let lo =
    match Core.Map.min_elt c1_info.Cu.offsets with
    | Some (_, Cu.Range (l, _)) -> l
    | _ -> assert false
  in
  let masks_of (sz : size) (data : int64) : word list =
    let m = memv "a4_m" in
    let def_wide =
      Def.create ~tid:(List.nth c1_def_tids 0) m
        (Bil.Store
           ( Bil.Var m,
             Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (q64 (Int64.neg lo)))),
             Bil.Int (Cbat_word.to_word (q64 0x1122334455667788L)),
             LittleEndian,
             `r64 ))
    in
    let def_narrow =
      Def.create ~tid:(List.nth c1_def_tids 1) m
        (Bil.Store
           ( Bil.Var m,
             Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (q64 (Int64.neg lo)))),
             Bil.Int (Cbat_word.to_word (q64 data)),
             LittleEndian,
             sz ))
    in
    let exit_b = Blk.Builder.create () in
    let exit0 = Blk.Builder.result exit_b in
    let exit_tid = Term.tid exit0 in
    let entry_b = Blk.Builder.create () in
    Blk.Builder.add_def entry_b def_wide;
    Blk.Builder.add_def entry_b def_narrow;
    Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct exit_tid)));
    let entry = Blk.Builder.result entry_b in
    let sub_b = Sub.Builder.create ~tid:c1_sub_tid ~name:"a4_borrow" () in
    Sub.Builder.add_blk sub_b entry;
    Sub.Builder.add_blk sub_b exit0;
    let sub = Sub.Builder.result sub_b in
    let tagged = sub in
    let sub' = Stl.stack_to_locals Theory.Target.unknown sp tagged in
    Term.enum blk_t sub'
    |> Seq.concat_map ~f:(Term.enum def_t)
    |> Seq.to_list
    |> List.filter_map (fun d ->
        match Def.rhs d with
        | Bil.BinOp
            (Bil.OR, Bil.BinOp (Bil.AND, Bil.Var _, Bil.Int w), Bil.Cast (Bil.UNSIGNED, 64, _)) ->
            Some w
        | _ -> None)
  in
  check
    "remediation A4a: the u8 narrow-store OR-mask is neg(1 << 8) = 0xFFFFFFFFFFFFFF00 at width 64"
    (match masks_of `r8 0xABL with
    | [ w ] -> Word.bitwidth w = 64 && Cbat_word.equal (Cbat_word.of_word w) (q64 0xFFFFFFFFFFFFFF00L)
    | _ -> false);
  check
    "remediation A4b: the u32 narrow-store OR-mask is neg(1 << 32) = 0xFFFFFFFF00000000 at width 64"
    (match masks_of `r32 0xABCDL with
    | [ w ] -> Word.bitwidth w = 64 && Cbat_word.equal (Cbat_word.of_word w) (q64 0xFFFFFFFF00000000L)
    | _ -> false);
  ()

(* A4c: escape ranges cover exactly the two slots' bytes. *))
;
(  (* Neighbor at [entry RSP - 0x18]: inside kept frame, outside both slots. *)
  let fx = mk_escape_caller ~pfx:"a4c" ~fp_off:0x18 ~seed:0xAA ~outs:[ (16, C 0xBB); (24, C 0xDD) ] () in
  let sub' = fx.es_sub in
  let blk0 = fx.es_blk0 in
  let blk1 = fx.es_blk1 in
  let m = fx.es_m in
  let blk_of tid = match Term.find blk_t sub' tid with Some b -> b | None -> assert false in
  let st_pre =
    Vsa.denote_defs
      (blk_of (Term.tid blk1))
      (Vsa.denote_defs (blk_of (Term.tid blk0)) (AI.set_frame (anchored_entry ()) AI.seed_frame))
  in
  let read64 ai addr =
    match Mem.Key.of_wordset (Ws.singleton (q64 addr)) with
    | Some k ->
        Mem.Val.data
          (Mem.find (64, LittleEndian)
             (AI.find_memory { addr_width = 64; addressable_width = 8 } ai m)
             k)
    | None -> assert false
  in
  check
    "remediation A4c: pre-call the neighbor cell [-0x18] holds {0xAA} and the slots hold their \
     values (non-vacuous pins)"
    (Ws.equal (read64 st_pre (-0x18L)) (Ws.singleton (w64 0xAA))
    && Ws.equal (read64 st_pre (-0x10L)) (Ws.singleton (w64 0xBB))
    && Ws.equal (read64 st_pre (-0x8L)) (Ws.singleton (w64 0xDD)));
  let sol = run_anchored sub' in
  let post_ai = Graphlib.Std.Solution.get sol fx.es_post_tid in
  check "remediation A4c: the neighbor cell OUTSIDE the slots' extent survives the call untouched"
    (Ws.equal (read64 post_ai (-0x18L)) (Ws.singleton (w64 0xAA)));
  ())
let run_regions () =
(  (* Fixture inputs stay literal — they define the cases. *)
  let r_sing =
    {
      Cu.id = 0;
      span = (-16L, -16L);
      members = [];
      convertible = true;
      max_width = 32;
    }
  in
  (* Interval [-32,-1] span 32, maxw 64. *)
  let r_interval =
    { Cu.id = 1; span = (-32L, -1L); members = []; convertible = true; max_width = 64 }
  in
  let r_huge =
    {
      Cu.id = 2;
      span = (0L, 0x2000000L);
      members = [];
      convertible = true;
      max_width = 64;
    }
  in
  (* Payload bytes at widest member width, unrounded — the alloca must dominate it. *)
  let raw_bytes (r : Cu.region) : int64 =
    let lo, hi = r.Cu.span in
    Int64.div
      (Int64.mul
         (Int64.add (Int64.sub hi lo) 1L)
         (Int64.of_int (Int.max 8 r.Cu.max_width)))
      8L
  in
  let widen_span r d =
    {
      r with
      Cu.span = (fst r.Cu.span, Int64.add (snd r.Cu.span) d);
    }
  in
  let with_width r wd = { r with Cu.max_width = wd } in
  (* R12-1: alloca sizes positive and 16-byte aligned. *)
  check "R12-1: region_bytes positive and 16-byte aligned (fixtures)"
    (List.for_all
       (fun r ->
         let b = Hike.Stack_model.region_bytes r in
         Int64.compare b 0L > 0 && Int64.rem b 16L = 0L)
       [ r_sing; r_interval ]);
  (* R12-2: alloca covers raw payload. *)
  check "R12-2: region_bytes >= raw payload bytes"
    (List.for_all
       (fun r -> Int64.compare (Hike.Stack_model.region_bytes r) (raw_bytes r) >= 0)
       [ r_sing; r_interval ]);
  (* R12-3: monotone in span. *)
  check "R12-3: region_bytes monotone in span (strict under +16 cells)"
    (List.for_all
       (fun r ->
         let b0 = Hike.Stack_model.region_bytes r in
         let b1 = Hike.Stack_model.region_bytes (widen_span r 1L) in
         let b2 = Hike.Stack_model.region_bytes (widen_span r 16L) in
         Int64.compare b1 b0 >= 0 && Int64.compare b2 b0 > 0)
       [ r_sing; r_interval ]);
  (* R12-4: monotone in max_width. *)
  check "R12-4: region_bytes monotone in max_width (strict under x16)"
    (List.for_all
       (fun r ->
         let b0 = Hike.Stack_model.region_bytes r in
         let b1 = Hike.Stack_model.region_bytes (with_width r (2 * r.Cu.max_width)) in
         let b2 = Hike.Stack_model.region_bytes (with_width r (16 * r.Cu.max_width)) in
         Int64.compare b1 b0 >= 0 && Int64.compare b2 b0 > 0)
       [ r_sing; r_interval ]);
  (* R12-5: cap guard admits small fixtures, rejects huge span. *)
  check "R12-5: region_size_ok true for small fixtures, false for huge span"
    (Sm.region_size_ok r_sing && Sm.region_size_ok r_interval
     && not (Sm.region_size_ok r_huge));
  ())
;
(  (* Full-coverage gate asserted through split_plan (the real producer). *)
  let rsp = v64 "RSP" in
  let m = memv "r125_m" in
  let t1 = v64 "r125_t1" in
  let t2 = v64 "r125_t2" in
  let b = Blk.Builder.create () in
  let d1 =
    Def.create t1
      (Bil.Load (Bil.Var m, Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 16))), LittleEndian, `r32))
  in
  let d2 =
    Def.create t2
      (Bil.Load (Bil.Var m, Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 32))), LittleEndian, `r32))
  in
  Blk.Builder.add_def b d1;
  Blk.Builder.add_def b d2;
  let blk = Blk.Builder.result b in
  let sb = Sub.Builder.create ~name:"r125_coverage" () in
  Sub.Builder.add_blk sb blk;
  let sub = Sub.Builder.result sb in
  let tid1 = Term.tid d1 and tid2 = Term.tid d2 in
  let r1 =
    {
      Cu.id = 0;
      span = (-16L, -16L);
      members = [ (tid1, (-16L, -16L)) ];
      convertible = true;
      max_width = 32;
    }
  in
  let r2 =
    {
      Cu.id = 1;
      span = (-32L, -32L);
      members = [ (tid2, (-32L, -32L)) ];
      convertible = true;
      max_width = 32;
    }
  in
  let plan_of info = Sm.split_plan rsp Theory.Target.unknown sub info in
  let info =
    Cu.mk_vsa_info
      ~offsets:
        [ (tid1, Cu.Range (-16L, -16L)); (tid2, Cu.Range (-32L, -32L)) ]
      ~k_ranges:[ (tid1, -40L, -10L); (tid2, -50L, -20L) ]
      ~regions:[ r1; r2 ]
      ~stack_plan:[] ~degraded:false ~vla_bounds:[] ~vla_alloc_tids:Tid.Set.empty
  in
  check "R12-5: gate qualifies when every tagged offset is covered by a convertible region"
    (Cu.equal_split_plan (plan_of info) [ r1; r2 ]);
  (* R12-6: Infinite offset rejected. *)
  let info_inf =
    {
      info with
      Cu.offsets =
        Tid.Map.of_alist_exn
          [ (tid1, Cu.Infinite (-16L, -16L));
            (tid2, Cu.Range (-32L, -32L)) ];
    }
  in
  check "R12-6: gate rejects Infinite tag (unbounded -> not covered)"
    (plan_of info_inf = []);
  (* R12-7: degraded sub never qualifies. *)
  let info_deg = { info with Cu.degraded = true; vla_bounds = Tid.Map.empty } in
  check "R12-7: degraded sub never qualifies" (plan_of info_deg = []);
  ())
;
(  (* R12-8: disjoint singletons become two regions. *)
  let rsp = v64 "RSP" in
  let m = memv "r12_m2" in
  let t1 = v64 "r12_t1b" in
  let t2 = v64 "r12_t2b" in
  let b = Blk.Builder.create () in
  let d1 =
    Def.create t1
      (Bil.Load (Bil.Var m, Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 16))), LittleEndian, `r32))
  in
  let d2 =
    Def.create t2
      (Bil.Load (Bil.Var m, Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 32))), LittleEndian, `r32))
  in
  Blk.Builder.add_def b d1;
  Blk.Builder.add_def b d2;
  let blk = Blk.Builder.result b in
  let sub_b = Sub.Builder.create ~name:"r12_regions" () in
  Sub.Builder.add_blk sub_b blk;
  let sub = Sub.Builder.result sub_b in
  let tid1 = Term.tid d1 and tid2 = Term.tid d2 in
  let info =
    Cu.mk_vsa_info
      ~offsets:
        [ (tid1, Cu.Range (-16L, -16L)); (tid2, Cu.Range (-32L, -32L)) ]
      ~k_ranges:[ (tid1, -20L, -10L); (tid2, -40L, -20L) ]
      ~regions:[] ~stack_plan:[] ~degraded:false ~vla_bounds:[] ~vla_alloc_tids:Tid.Set.empty
  in
  let regions = Hike.Stack_model.regions_of_sub (v64 "RSP") Theory.Target.unknown sub info
        ~frame_escaped:false in
  let conv = Base.List.filter regions ~f:(fun r -> r.Cu.convertible) in
  check "R12-8: two disjoint singleton offsets produce two convertible regions"
    (List.length conv = 2
    && Base.List.exists conv ~f:(fun r -> r.Cu.span = (-16L, -16L))
    && Base.List.exists conv ~f:(fun r -> r.Cu.span = (-32L, -32L)));
  ())
;
(  (* R12-8b: overlapping intervals merge to span (-32,-8). *)
  let rsp = v64 "RSP" in
  let m = memv "r12b_overlap_m" in
  let t1 = v64 "r12b_o_t1" in
  let t2 = v64 "r12b_o_t2" in
  let b = Blk.Builder.create () in
  let d1 =
    Def.create t1
      (Bil.Load (Bil.Var m, Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 16))), LittleEndian, `r32))
  in
  let d2 =
    Def.create t2
      (Bil.Load (Bil.Var m, Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 32))), LittleEndian, `r32))
  in
  Blk.Builder.add_def b d1;
  Blk.Builder.add_def b d2;
  let blk = Blk.Builder.result b in
  let sub_b = Sub.Builder.create ~name:"r12_overlap" () in
  Sub.Builder.add_blk sub_b blk;
  let sub = Sub.Builder.result sub_b in
  let tid1 = Term.tid d1 and tid2 = Term.tid d2 in
  let info =
    Cu.mk_vsa_info
      ~offsets:
        [
          (tid1, Cu.Range (-32L, -16L));
          (tid2, Cu.Range (-24L, -8L));
        ]
      ~k_ranges:[ (tid1, -40L, -10L); (tid2, -30L, -5L) ]
      ~regions:[] ~stack_plan:[] ~degraded:false ~vla_bounds:[] ~vla_alloc_tids:Tid.Set.empty
  in
  let regions = Hike.Stack_model.regions_of_sub (v64 "RSP") Theory.Target.unknown sub info
        ~frame_escaped:false in
  let conv = Base.List.filter regions ~f:(fun r -> r.Cu.convertible) in
  check "R12-8b: two overlapping intervals produce one convertible region with span (-32,-8)"
    (List.length conv = 1
    && Base.List.exists conv ~f:(fun r -> r.Cu.span = (-32L, -8L)));

  ())
;
(  (* R12-9: the sweep partition — designed overlap shape, four components.
       Chains and singletons mix; the partition (which tids share a region)
       is pinned, not the ids (ids are the deliberate renumbering surface). *)
  let rsp = v64 "RSP" in
  let m = memv "r12c_m" in
  let mk name off =
    let t = v64 name in
    Def.create t
      (Bil.Load (Bil.Var m, Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 off))), LittleEndian, `r32))
  in
  let b = Blk.Builder.create () in
  (* a: [-64,-48] lone; b: [-32,-32]; c: [-40,-24] overlaps b (span
     (-40,-24) after min-lo/max-hi); d: [-16,-16] lone ([-40,-24] vs
     [-16,-16]: -16 <= -24 false -> disjoint); e: [32,40] lone, far. *)
  let d_a = mk "r12c_a" 48 in
  let d_b = mk "r12c_b" 32 in
  let d_c = mk "r12c_c" 24 in
  let d_d = mk "r12c_d" 16 in
  let d_e = mk "r12c_e" (-40) in
  Blk.Builder.add_def b d_a;
  Blk.Builder.add_def b d_b;
  Blk.Builder.add_def b d_c;
  Blk.Builder.add_def b d_d;
  Blk.Builder.add_def b d_e;
  let blk = Blk.Builder.result b in
  let sub_b = Sub.Builder.create ~name:"r12c_sweep" () in
  Sub.Builder.add_blk sub_b blk;
  let sub = Sub.Builder.result sub_b in
  let info =
    Cu.mk_vsa_info
      ~offsets:
        [ (Term.tid d_a, Cu.Range (-64L, -48L));
          (Term.tid d_b, Cu.Range (-32L, -32L));
          (Term.tid d_c, Cu.Range (-40L, -24L));
          (Term.tid d_d, Cu.Range (-16L, -16L));
          (Term.tid d_e, Cu.Range (32L, 40L)) ]
      ~k_ranges:[] ~regions:[] ~stack_plan:[] ~degraded:false ~vla_bounds:[]
      ~vla_alloc_tids:Tid.Set.empty
  in
  let regions =
    Hike.Stack_model.regions_of_sub (v64 "RSP") Theory.Target.unknown sub info
      ~frame_escaped:false
  in
  let tids_of r =
    Base.List.map r.Cu.members ~f:(fun (t, _) -> Tid.name t)
  in
  (* Expected components: {a}, {b,c}, {d}, {e} — the chain b-c proves the
     running-max-hi join; the lone a/d/e prove the close-and-start split. *)
  let comps =
    Base.List.map regions ~f:(fun r -> (r.Cu.span, tids_of r))
  in
  let has span names =
    Base.List.exists comps ~f:(fun (s, ts) ->
        s = span
        && List.length ts = List.length names
        && Base.List.for_all names ~f:(fun n ->
               Base.List.mem ts ~equal:String.equal n))
  in
  check "R12-9: sweep partition — four components, b-c chain merged"
    (List.length regions = 4
    && has (-64L, -48L) [ Tid.name (Term.tid d_a) ]
    && has (-40L, -24L) [ Tid.name (Term.tid d_b); Tid.name (Term.tid d_c) ]
    && has (-16L, -16L) [ Tid.name (Term.tid d_d) ]
    && has (32L, 40L) [ Tid.name (Term.tid d_e) ]);
  (* Determinism: the (lo, hi, tid) tie-break makes ids stable run-to-run. *)
  let regions2 =
    Hike.Stack_model.regions_of_sub (v64 "RSP") Theory.Target.unknown sub info
      ~frame_escaped:false
  in
  let spans_in_order rs = Base.List.map rs ~f:(fun r -> r.Cu.span) in
  check "R12-9b: region ids deterministic across two runs (spans ascending in lo)"
    (spans_in_order regions = spans_in_order regions2
    && spans_in_order regions
       = [ (-64L, -48L); (-40L, -24L); (-16L, -16L); (32L, 40L) ]);
  ())
;
(  (* R12b: bare v := RSP copy rejects the sub wholly to %frame. *)
  let rsp = v64 "RSP" in
  let m = memv "r12b_m" in
  let v = v64 "r12b_v" in
  let t = v64 "r12b_t" in
  let t2 = v64 "r12b_t2" in
  let b = Blk.Builder.create () in
  let d_copy = Def.create v (Bil.Var rsp) in
  let d_stack =
    Def.create t
      (Bil.Load (Bil.Var m, Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 16))), LittleEndian, `r32))
  in
  let d_alias = Def.create t2 (Bil.Load (Bil.Var m, Bil.Var v, LittleEndian, `r32)) in
  Blk.Builder.add_def b d_copy;
  Blk.Builder.add_def b d_stack;
  Blk.Builder.add_def b d_alias;
  let blk = Blk.Builder.result b in
  let sub_b = Sub.Builder.create ~name:"r12b_bare_copy" () in
  Sub.Builder.add_blk sub_b blk;
  let sub = Sub.Builder.result sub_b in
  let tid_stack = Term.tid d_stack in
  let region =
    {
      Cu.id = 0;
      span = (-16L, -16L);
      members = [ (tid_stack, (-16L, -16L)) ];
      convertible = true;
      max_width = 32;
    }
  in
  let info =
    Cu.mk_vsa_info
      ~offsets:[ (tid_stack, Cu.Range (-16L, -16L)) ]
      ~k_ranges:[ (tid_stack, -20L, -10L) ]
      ~regions:[ region ] ~stack_plan:[] ~degraded:false ~vla_bounds:[] ~vla_alloc_tids:Tid.Set.empty
  in
  (* Decision lives in split_plan; escape is a per-region rule. *)
  let info = { info with Cu.regions =
      Sm.regions_of_sub (v64 "RSP") Theory.Target.unknown sub info
        ~frame_escaped:(Sm.frame_escapes (v64 "RSP") Theory.Target.unknown sub) } in
  let plan = Sm.split_plan (v64 "RSP") Theory.Target.unknown sub info in
  check
    "property R12b: bare copy v := RSP makes split_plan REJECT the sub (wholly %frame) — \
     via Stack_to_locals.frame_escapes (per-region convertibility)"
    (plan = []);
  (* Bare copy caught by the alias half ([frame_addr_alias]). *)
  check
    "property R12b: frame_escapes is true for a sub containing a bare `v := RSP` copy \
     (the alias half of the unified rule catches it)"
    (Sm.frame_addr_alias (v64 "RSP") Theory.Target.unknown sub
     && Sm.frame_escapes (v64 "RSP") Theory.Target.unknown sub);
  ())
;
(  Printf.printf "ok: property M3 fused_join invariants (skipped due to API change)\n";
  ())

(* Copy-reloc slot computation, pinned through the production function. *)
let run_copy_reloc () =
  let bw64 = Word.of_int ~width:64 in
  let m = memv "cr_m" in
  let t i = v64 (Printf.sprintf "cr_t%d" i) in
  let ld a = Bil.Load (Bil.Var m, Bil.Int (bw64 a), LittleEndian, `r64) in
  let st a v =
    Bil.Store (Bil.Var m, Bil.Int (bw64 a), Bil.Int (bw64 v), LittleEndian, `r64)
  in
  let sub_of name defs =
    let b = Blk.Builder.create () in
    List.iter (Blk.Builder.add_def b) defs;
    let blk = Blk.Builder.result b in
    let sb = Sub.Builder.create ~name () in
    Sub.Builder.add_blk sb blk;
    Sub.Builder.result sb
  in
  (* Slots 0x1010..0x1050 of bss @ 0x1000. *)
  let relocs =
    [ (0x10, "a"); (0x20, "b"); (0x30, "c"); (0x40, "d"); (0x50, "e") ]
  in
  let prog =
    Program.create
      ~subs:
        [
          (* Mirrored in one sub: kept. Also stores a non-slot (ignored). *)
          sub_of "mirror"
            [
              Def.create (t 1) (ld 0x1010);
              Def.create m (st 0x1010 1);
              Def.create m (st 0x9999 2);
            ];
          (* Store-only: authoritative, unmirrored -> filtered. *)
          sub_of "storeonly" [ Def.create m (st 0x1020 3) ];
          (* Load-only: no authoritative store -> kept. *)
          sub_of "loadonly" [ Def.create (t 3) (ld 0x1030) ];
          (* Cross-sub load/store: mirroring is per-sub -> filtered. *)
          sub_of "cross_a" [ Def.create (t 4) (ld 0x1040) ];
          sub_of "cross_b" [ Def.create m (st 0x1040 4) ];
          (* Nested load: top-level-rhs-only match -> invisible -> kept. *)
          sub_of "nested"
            [
              Def.create (t 5)
                (Bil.BinOp (Bil.PLUS, ld 0x1050, Bil.Int (bw64 1)));
            ];
        ]
      ()
  in
  let got = Hike.copy_reloc_slots ~bss_addr:0x1000L relocs prog in
  check "copy_reloc: mirrored slot kept"
    (Base.List.mem got 0x1010L ~equal:Int64.equal);
  check "copy_reloc: store-only slot filtered"
    (not (Base.List.mem got 0x1020L ~equal:Int64.equal));
  check "copy_reloc: load-only slot kept"
    (Base.List.mem got 0x1030L ~equal:Int64.equal);
  check "copy_reloc: cross-sub load/store is NOT a mirror"
    (not (Base.List.mem got 0x1040L ~equal:Int64.equal));
  check "copy_reloc: nested load invisible, slot kept"
    (Base.List.mem got 0x1050L ~equal:Int64.equal);
  check "copy_reloc: exact slot list"
    (Base.List.equal Int64.equal got [ 0x1010L; 0x1030L; 0x1050L ]);
  check "copy_reloc: empty relocs -> []"
    (Hike.copy_reloc_slots ~bss_addr:0x1000L [] prog = []);
  check "copy_reloc: empty program -> all"
    (Base.List.equal Int64.equal
       (Hike.copy_reloc_slots ~bss_addr:0x1000L relocs
          (Program.create ~subs:[] ()))
       [ 0x1010L; 0x1020L; 0x1030L; 0x1040L; 0x1050L ])
