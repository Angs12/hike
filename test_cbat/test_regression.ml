(* Narrow-store/degraded-frame/escape pins, remediation batch, region-split gates. *)
open Bap.Std
open Bap_core_theory
open Test_common
open Test_fixtures

module A = Hike.Sections

(* Regression tests C1-C4. *)
let q64 (v : int64) : Cbat_word.t = Cbat_word.of_int64 ~width:64 v

(* Remediation batch A1-A4. *)
(* R12 region-allocation size rule (S15). *)

let run_creg () =
(  (* C1: the narrow-store shape — a wide (r64) and a narrow (r16) store
       on the SAME converted cell re-point at the region mem var: the
       memory node and the whole-access store's lhs both name it, the
       address expression and the access width are kept (the Region
       conversion is width-agnostic — the emitter GEPs the same bytes). *)
  let rsp = v64 "RSP" in
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
           Bil.Int (Cbat_word.to_word (Cbat_word.of_int ~width:16 0xABCD)),
           LittleEndian,
           `r16 ))
  in
  let sub, _ =
    sub_of "c1_mask"
      [ [ def_wide; def_narrow ], [ (1, mk_goto) ];
        [], [] ]
  in
  let sub' = rewrite_one sub in
  let narrow' =
    Term.enum blk_t sub'
    |> Seq.concat_map ~f:(Term.enum def_t)
    |> Seq.find ~f:(fun d -> Tid.equal (Term.tid d) (Term.tid def_narrow))
  in
  check "C1: the narrow r16 store converts to the region mem, keeping its address and width"
    (match narrow' with
     | Some d ->
        (match Def.rhs d with
         | Bil.Store (Bil.Var mem, Bil.BinOp (Bil.MINUS, Bil.Var b, Bil.Int _), _, _, `r16) ->
             Var.same mem (Sm.region_mem 1) && Var.same b rsp
             && Var.equal (Def.lhs d) mem
         | _ -> false)
     | None -> false);
  ()


(* C3: escape set includes the call block's outgoing-slot stores. *))
;
(  let fx = mk_escape_caller ~pfx:"c3" ~fp_off:8 ~seed:0xAA ~outs:[ (16, C 0xBB) ] () in
  let sub' = fx.es_sub in
  let blk_of tid = match Term.find blk_t sub' tid with Some b -> b | None -> assert false in
  let st_pre =
    Vsa.Test_seam.denote_defs
      (blk_of (Term.tid fx.es_blk1))
      (Vsa.Test_seam.denote_defs
         (blk_of (Term.tid fx.es_blk0))
         (anchored_entry ()))
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
  check "C3: pre-call the caller-frame cell [RSP-8] holds {0xAA} (non-vacuous pin)"
    (Ws.equal (read64 st_pre (-8L)) (Ws.singleton (w64 0xAA)));
  check "C3: pre-call the outgoing slot [RSP+16] holds {0xBB} (non-vacuous pin)"
    (Ws.equal (read64 st_pre (-16L)) (Ws.singleton (w64 0xBB)));
  let sol = run_anchored sub' in
  let post_ai = Graphlib.Std.Solution.get sol fx.es_post_tid in
  check
    "C3: the caller-frame cell [RSP-8] survives the call with its value (frame not \
     whole-memory-topped)"
    (Ws.equal (read64 post_ai (-8L)) (Ws.singleton (w64 0xAA)));
  ()

(* C4b: the widened (Infinite-class) member's storage, through the REAL
   chain's tree. *))
;
(  (* The finalized storage of the def's own component. *)
  let storage_of_def ctx sub dtid : A.range_storage option =
    match Core.Map.find ctx.A.sub_trees (Term.tid sub) with
    | Some tree ->
        A.Tree.to_sequence tree |> Seq.to_list
        |> Base.List.find_map ~f:(fun (_, rs) ->
               if
                 Base.List.exists rs.A.members ~f:(fun mm ->
                     Base.Option.equal Tid.equal mm.A.m_def (Some dtid))
               then Some rs
               else None)
    | None -> None
  in
  let rsp = v64 "RSP" in
  let m = memv "c4b_m" in
  (* The control: two overlapping constant stores [RSP-48]/[RSP-44]
     merge into one bounded component — Region storage. *)
  let a_ctrl = mk_store_minus m rsp 48 3 `r64 in
  let b_ctrl = mk_store_minus m rsp 44 4 `r64 in
  let sub_ctrl = fst (sub_of "c4b_ctrl" [ [ a_ctrl; b_ctrl ], [] ]) in
  let ctx_ctrl = fixture_ctx [ sub_ctrl ] in
  check_bound "C4b control: the constant stores' merged component takes Region storage"
    (storage_of_def ctx_ctrl sub_ctrl (Term.tid a_ctrl))
    (fun rs -> rs.A.storage = A.Stack_region 1);
  (* The mixed variant: the indexed loop's widened store (the
     Infinite class — C4a pins its tag) contributes a full-scope
     identity member.  Its component takes Frame storage, never
     Region, and it JOINS the loop's constant cells (the tree's
     together-or-not-at-all rule). *)
  let sub_mixed, def_idx_store = mk_indexed_loop ~pfx:"c4b" in
  let ctx_mixed = fixture_ctx [ sub_mixed ] in
  check_bound "C4b: the widened member's component takes Frame storage, never Region"
    (storage_of_def ctx_mixed sub_mixed (Term.tid def_idx_store))
    (fun rs -> rs.A.storage = A.Stack_residue);
  check "C4b: the constant cell joins the widened member's Frame component (together, not Region)"
    (match Core.Map.find ctx_mixed.A.sub_trees (Term.tid sub_mixed) with
     | Some tree ->
         (match A.storage_of_range tree (A.range Sm.Stack (pos (-16L)) (pos (-9L))) with
          | Some rs -> rs.A.storage = A.Stack_residue
          | None -> false)
     | None -> false);
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
    Vsa.Test_seam.denote_defs
      (blk_of (Term.tid blk1))
      (Vsa.Test_seam.denote_defs (blk_of (Term.tid blk0)) (anchored_entry ()))
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
  ()

(* A4a/A4b: DELETED with the scalar-local splice (S22) — the OR-mask
   widths pinned a mechanism the Region conversion replaces. *))
;
(  (* A4c: escape ranges cover exactly the two slots' bytes. *)
  (* Neighbor at [entry RSP - 0x18]: inside kept frame, outside both slots. *)
  let fx = mk_escape_caller ~pfx:"a4c" ~fp_off:0x18 ~seed:0xAA ~outs:[ (16, C 0xBB); (24, C 0xDD) ] () in
  let sub' = fx.es_sub in
  let blk0 = fx.es_blk0 in
  let blk1 = fx.es_blk1 in
  let m = fx.es_m in
  let blk_of tid = match Term.find blk_t sub' tid with Some b -> b | None -> assert false in
  let st_pre =
    Vsa.Test_seam.denote_defs
      (blk_of (Term.tid blk1))
      (Vsa.Test_seam.denote_defs (blk_of (Term.tid blk0)) (anchored_entry ()))
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
  (* The size rule (S15): a Region component's alloca bytes are its
     occupied span aligned ONCE (align16), never span*width — an
     8-byte occupied span yields a 16-byte alloca.  (R12-1..R12-4
     pinned the deleted region_bytes arithmetic; the overlap merge and
     the deterministic ascending ids are pinned by AT1-TREE in
     test_attrib.ml; R12-5/8/8b/9/9b pinned the deleted split_plan /
     regions_of_sub partition surface.) *)
  let m = memv "r12_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let d_rbp = Def.create rbp (Bil.Var rsp) in
  let d =
    Def.create (v64 "r12_t")
      (Bil.Load
         ( Bil.Var m,
           Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))),
           LittleEndian, `r64 ))
  in
  let sub = straight_sub "r12_span8" [ d_rbp; d ] in
  let ctx = fixture_ctx [ sub ] in
  let tree =
    Base.Option.value_exn (Core.Map.find ctx.A.sub_trees (Term.tid sub))
  in
  let l =
    A.layout_of_tree ~word:8 ~entry:Hike.Stack_model.segment_base
      ~abi:Hike.Abi.x86_64_sysv ~sub tree
  in
  check "R12: a Region binding of occupied span 8 bytes allocates 16 (aligned once, no width factor)"
    (l.Sm.regions = [ (1, (pos (-8L), pos (-1L)), 16L) ])


(* The bare-copy sub's fate is its TAGS: the tagged singleton region
   converts; the untagged aliased read emits through the real-address
   lane — its guarantee is the corpus battery's oracle. *)

(* The fp-GPR lane (ADR 0008): heap-RBP must not be granted stack semantics
   by NAME. The fixtures run through the REAL chain (the attribution's
   collector denotes addresses — names are never consulted); the
   name-grants-nothing claim is pinned by the S2/S2b twin. *)
let storage_at ctx sub sec lo hi : A.storage option =
  Base.Option.bind (Core.Map.find ctx.A.sub_trees (Term.tid sub))
    ~f:(fun tree ->
      Base.Option.map (A.storage_of_range tree (A.range sec lo hi))
        ~f:(fun rs -> rs.A.storage))

let run_fp_gpr () =
(  (* S2: a proven rsp access plus an UNTAGGED heap-RBP store. The heap
       store is not stack traffic at all (its address is a plain heap
       integer), so it contributes no sub-tree member: the rsp store's
       cell still takes Region storage — stack-ness is the VSA's value
       proof alone. *)
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let m = memv "s2_m" in
  let def_heap = Def.create rbp (Bil.Int (Cbat_word.to_word (w64 0x400000))) in
  let def_rsp =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 16))),
           Bil.Int (Cbat_word.to_word (w64 1)),
           LittleEndian,
           `r64 ))
  in
  let def_heap_store =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.PLUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 0x100))),
           Bil.Int (Cbat_word.to_word (w64 9)),
           LittleEndian,
           `r64 ))
  in
  let sub, _ =
    sub_of "s2_heap_rbp"
      [ [ def_heap; def_rsp; def_heap_store ], [ (1, mk_goto) ];
        [], [] ]
  in
  let ctx = fixture_ctx [ sub ] in
  check
    "S2 (fp-GPR): an untagged heap-RBP store does NOT degrade the sub \
     (the rsp cell keeps Region storage — stack-ness is the value proof alone)"
    (storage_at ctx sub Sm.Stack (pos (-16L)) (pos (-9L)) = Some (A.Stack_region 1));
  ())
;
(  (* S2b: the NAME control — the identical sub with the untagged heap
       store based on a NON-fp GPR (RBX). Same shape; only the base
       register's name differs — the pair pins that a name grants
       nothing. *)
  let rsp = v64 "RSP" in
  let rbx = v64 "RBX" in
  let m = memv "s2b_m" in
  let def_heap = Def.create rbx (Bil.Int (Cbat_word.to_word (w64 0x400000))) in
  let def_rsp =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 16))),
           Bil.Int (Cbat_word.to_word (w64 1)),
           LittleEndian,
           `r64 ))
  in
  let def_heap_store =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.PLUS, Bil.Var rbx, Bil.Int (Cbat_word.to_word (w64 0x100))),
           Bil.Int (Cbat_word.to_word (w64 9)),
           LittleEndian,
           `r64 ))
  in
  let sub, _ =
    sub_of "s2b_heap_rbx"
      [ [ def_heap; def_rsp; def_heap_store ], [ (1, mk_goto) ];
        [], [] ]
  in
  let ctx = fixture_ctx [ sub ] in
  check
    "S2b (fp-GPR control): the identical sub with an RBX-based heap store is \
     NOT degraded — storage-ness comes from the value proof, not the name"
    (storage_at ctx sub Sm.Stack (pos (-16L)) (pos (-9L)) = Some (A.Stack_region 1));
  ())
;
(  (* S3: the value-true twin — a real prologue ([RBP := RSP]) makes RBP
       sp-derived, so the [RBP - 0x30] access IS stack traffic by VALUE:
       its cell takes Region storage.  The proof route, never the name. *)
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let m = memv "s3_m" in
  let def_prologue = Def.create rbp (Bil.Var rsp) in
  let def_store =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 0x30))),
           Bil.Int (Cbat_word.to_word (w64 9)),
           LittleEndian,
           `r64 ))
  in
  let callee = mk_selfloop_callee "s3_callee" in
  let sub, _ =
    sub_of "s3_prologue"
      [ [ def_prologue; def_store ], [ (1, fun t -> mk_call_jmp t (Term.tid callee)) ];
        [], [] ]
  in
  let ctx = fixture_ctx [ sub ] in
  check
    "S3 (fp-GPR): the value-true twin — an [RBP := RSP] prologue makes RBP \
     sp-derived, so the sub's frame access takes Region storage (values alone decide)"
    (storage_at ctx sub Sm.Stack (pos (-48L)) (pos (-41L)) = Some (A.Stack_region 1));
  ())
;

