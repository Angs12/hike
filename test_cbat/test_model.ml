(* The model/producer surface pins.

   - [run_producer_record]: the producer composed end-to-end
     ([Hike.Vsa.fixpoint], the shape test) — the VLA detection through
     the REAL fixpoint (the entry seeds RSP at the symbolic segment
     base, the production universe).
   - Later lanes (layout/frame geometry, stack-to-locals fission,
     emitter VLA/SP-Slot shapes, Abi/Kb domains) follow. *)

open Test_common
open Test_fixtures
open Bap.Std
open Bap_core_theory

module Sm = Hike.Stack_model
module Pr = Hike.Sections
module Hv = Hike.Vsa
(* The consumer-side one-line alias (the src convention). *)
module Abi = Hike.Abi

(* A register list names exactly [names]. *)
let names_are (vs : var list) (names : string list) : bool =
  Base.List.map vs ~f:(fun v -> Var.name v) = names

(* 64-bit literal word (native-int [w64] covers 63 bits only). *)
let q64 (v : int64) : Cbat_word.t = Cbat_word.of_int64 ~width:64 v

let minus_addr sp (off : int64) : exp =
  Bil.BinOp (Bil.MINUS, Bil.Var sp, Bil.Int (Cbat_word.to_word (w64 (Int64.to_int off))))

let tid_set (tids : tid list) : Tid.Set.t =
  List.fold_left (fun s t -> Core.Set.add s t) Tid.Set.empty tids

(* Lane A: the producer record (the composed producer end-to-end).     *)

let run_producer_record () =
  (* A5: the dynamic-allocation events and the stamp round-trip. *)
  let a5_rbx = v64 "pr_a5_rbx" in
  let a5_rcx = v64 "pr_a5_rcx" in
  let a5_lit = Def.create sp (Bil.BinOp (Bil.MINUS, Bil.Var sp, Bil.Int (Cbat_word.to_word (w64 0x28)))) in
  let a5_rbx_def = Def.create a5_rbx (Bil.Int (Cbat_word.to_word (w64 0x80))) in
  let a5_bnd =
    Def.create sp (Bil.BinOp (Bil.MINUS, Bil.Var sp, Bil.Var a5_rbx))
  in
  let a5 = straight_sub "pr_a5_vla" [ a5_lit; a5_rbx_def; a5_bnd ] in
  check "PR-A5: neither the literal decrement nor the chain-resolved constant is the event — a size the code fixes keeps the SP at a bounded interval"
    (Core.Set.is_empty
       (Pr.dynamic_alloc_tids_of ~sp ~denote:Hike.Vsa.denote_exp_at a5));
  (* [a5_rcx] is never defined: its denotation is TOP — the
     runtime-unbounded size. *)
  let a5_vla =
    Def.create sp (Bil.BinOp (Bil.MINUS, Bil.Var sp, Bil.Var a5_rcx))
  in
  let a5u = straight_sub "pr_a5_vla_unb" [ a5_vla ] in
  let a5u_events =
    Pr.dynamic_alloc_tids_of ~sp ~denote:Hike.Vsa.denote_exp_at a5u in
  check "PR-A5: the runtime-unbounded decrement is the event; the literal decrement is not"
    (Core.Set.equal a5u_events (tid_set [ Term.tid a5_vla ]));
  let a5_stamped = Sm.stamp_dyn_allocs ~dynamic_alloc_tids:a5u_events a5u in
  let def_of_tid sub dtid =
    Term.enum blk_t sub
    |> Seq.concat_map ~f:(Term.enum def_t)
    |> Seq.find ~f:(fun d -> Tid.equal (Term.tid d) dtid)
    |> Base.Option.value_exn
  in
  check "PR-A5: the dynamic-allocation fact rides the def's value through the stamp"
    (Sm.def_is_dyn_alloc (def_of_tid a5_stamped (Term.tid a5_vla)));

  (* A5b: the frailty spellings — the event reads the VALUE, not the
     shape.  The two-temp chain still fires on the SP def. *)
  let a5c_t1 = v64 "pr_a5c_t1" in
  let a5c_t2 = v64 "pr_a5c_t2" in
  let a5c_d1 =
    Def.create a5c_t1 (Bil.BinOp (Bil.MINUS, Bil.Var sp, Bil.Var a5_rcx))
  in
  let a5c_d2 = Def.create a5c_t2 (Bil.Var a5c_t1) in
  let a5c_sp = Def.create sp (Bil.Var a5c_t2) in
  let a5c = straight_sub "pr_a5c_chain" [ a5c_d1; a5c_d2; a5c_sp ] in
  check "PR-A5c: a VLA spelled through TWO temps is still the event (the chain resolves through the sequential state)"
    (Core.Set.equal (Pr.dynamic_alloc_tids_of ~sp ~denote:Hike.Vsa.denote_exp_at a5c)
       (tid_set [ Term.tid a5c_sp ]));

  (* A5d: the plus-form (the lea-computed adjustment: a negative size
     added) is the event — the value is what carries the unbounded
     stack position, not the MINUS spelling. *)
  let a5d_t = v64 "pr_a5d_t" in
  let a5d_d1 =
    Def.create a5d_t (Bil.BinOp (Bil.MINUS, Bil.Int (Cbat_word.to_word (w64 0)), Bil.Var a5_rcx))
  in
  let a5d_sp =
    Def.create sp (Bil.BinOp (Bil.PLUS, Bil.Var sp, Bil.Var a5d_t))
  in
  let a5d = straight_sub "pr_a5d_plus" [ a5d_d1; a5d_sp ] in
  check "PR-A5d: the lea-computed adjustment (a negative size ADDED) is the event"
    (Core.Set.equal (Pr.dynamic_alloc_tids_of ~sp ~denote:Hike.Vsa.denote_exp_at a5d)
       (tid_set [ Term.tid a5d_sp ]));

  (* A5e: N6's direction — the def's VALUE decides.  With real
     environments installed, a provably-above adjustment ([SP + y],
     y's hull [0..63]) is NOT the event: the VLA is a decrement. *)
  let a5e_y = v64 "pr_a5e_y" in
  let a5e_r8 = v64 "pr_a5e_r8" in
  let a5e_y_def =
    Def.create a5e_y
      (Bil.BinOp (Bil.AND, Bil.Var a5e_r8, Bil.Int (Cbat_word.to_word (w64 63))))
  in
  let a5e_sp = Def.create sp (Bil.BinOp (Bil.PLUS, Bil.Var sp, Bil.Var a5e_y)) in
  let a5e = straight_sub "pr_a5e_plus_above" [ a5e_y_def; a5e_sp ] in
  ignore (install_fixture_envs [ a5e ]);
  check "PR-A5e: a provably-above PLUS adjustment is not the VLA event (the value's direction)"
    (Core.Set.is_empty
       (Pr.dynamic_alloc_tids_of ~sp ~denote:Hike.Vsa.denote_exp_at a5e));

  (* A5b: the LOOP-CARRIED VLA — the decrement sits inside a runtime
     loop; the shape test is local to the def, so the loop changes
     nothing. *)
  let a5b_loop = Bil.BinOp (Bil.LT, Bil.Var a5_rcx, Bil.Int (Cbat_word.to_word (w64 5))) in
  let a5b, _ =
    sub_of "pr_a5b_loop_vla"
      [ [], [ (1, mk_goto) ];
        [ Def.create sp (Bil.BinOp (Bil.MINUS, Bil.Var sp, Bil.Var a5_rcx)) ], [ (2, mk_goto) ];
        [], [ (3, fun t -> mk_jmp_to t (Bil.UnOp (Bil.NOT, a5b_loop))); (1, fun t -> mk_jmp_to t a5b_loop) ];
        [], [] ]
  in
  let a5b_events = Pr.dynamic_alloc_tids_of ~sp ~denote:Hike.Vsa.denote_exp_at a5b in
  let a5b_body_sp =
    Term.enum blk_t a5b
    |> Seq.find_map ~f:(fun blk ->
        Term.enum def_t blk
        |> Seq.find_map ~f:(fun d ->
            if Var.same (Def.lhs d) sp then Some (Term.tid d) else None))
    |> Base.Option.value_exn
  in
  check "PR-A5b: the LOOP-CARRIED VLA is the event — the widened head does not hide it"
    (Core.Set.equal a5b_events (tid_set [ a5b_body_sp ]));

  ()
(* Lane B: the layout from the finalized tree ([layout_of_tree]).       *)

let run_layout () =
  (* The Region components' geometry: bytes are the occupied span
     aligned once, no width multiplication (S15); the fallback frame
     (with its 64K unbounded floors) when an identity component
     exists. *)
  let abi = Hike.Abi.x86_64_sysv in
  let entry = Sm.segment_base in
  let m = memv "pr_b_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let mk_ld name off =
    Def.create (v64 name)
      (Bil.Load
         ( Bil.Var m,
           Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (q64 off))),
           LittleEndian, `r64 ))
  in
  let d_rbp = Def.create rbp (Bil.Var rsp) in
  let tree_of sub =
    let ctx = fixture_ctx [ sub ] in
    Base.Option.value_exn
      (Core.Map.find ctx.Hike.Sections.sub_trees (Term.tid sub))
  in
  (* Two reads at [RBP-24]/[RBP-16] occupy [base-24,base-17] and
     [base-16,base-9]: adjacent, not overlapping — two Region
     components with ascending ids, no fallback frame. *)
  let sub1 = straight_sub "pr_b1" [ d_rbp; mk_ld "pr_b1_t1" 24L; mk_ld "pr_b1_t2" 16L ] in
  let l1 = Hike.Sections.layout_of_tree ~word:8 ~entry ~abi ~sub:sub1 (tree_of sub1) in
  check "PR-B1: the precise tree carries its Region components and no residue region"
    (l1.Sm.anchor = Some (1, 8L)
    && l1.Sm.regions =
       [ (1, (pos (-24L), pos (-17L)), 16L); (2, (pos (-16L), pos (-9L)), 16L) ]);
  check "PR-B2: bytes are the occupied span aligned once, never span*width"
    (Base.List.for_all l1.Sm.regions ~f:(fun (_, (lo, hi), b) ->
         (* span 8 bytes, access width 64 bits: align16(8) = 16 — the
            old rule's width multiplication would demand 64. *)
         Int64.equal (Int64.add (Int64.sub hi lo) 1L) 8L
         && Int64.equal b 16L));
  let u = v64 "pr_b_u" in
  let top_store =
    Def.create m
      (Bil.Store (Bil.Var m, Bil.Var u, Bil.Int (Cbat_word.to_word (w64 1)), LittleEndian, `r64))
  in
  (* The plain-TOP store claims the sub-local line as identity: it
     joins the known read's cell into one Frame component, and the
     Args side takes Window — the residue with the unbounded floors. *)
  let sub2 = straight_sub "pr_b3" [ d_rbp; mk_ld "pr_b3_t" 24L; top_store ] in
  let l2 = Hike.Sections.layout_of_tree ~word:8 ~entry ~abi ~sub:sub2 (tree_of sub2) in
  check "PR-B3: a plain-TOP identity member forces the residue region with the 64K unbounded floors"
    ((match l2.Sm.anchor with
      | Some (0, idx) -> Int64.equal idx 65544L
      | _ -> false)
    && Base.List.exists l2.Sm.regions ~f:(fun (id, _, b) ->
           Int.equal id 0 && Int64.equal b 131088L));
  check "PR-B6: a plain-TOP-only residue sub takes the same unbounded floor"
    (let sub3 = straight_sub "pr_b6" [ d_rbp; top_store ] in
     let l3 = Hike.Sections.layout_of_tree ~word:8 ~entry ~abi ~sub:sub3 (tree_of sub3) in
     Base.List.exists l3.Sm.regions ~f:(fun (id, _, b) ->
         Int.equal id 0 && Int64.equal b 131088L))

let run_stl_rewrite () =
  let m = memv "pr_c_m" in
  let mk_store off data (sz : size) : def term =
    Def.create m
      (Bil.Store (Bil.Var m, minus_addr sp off, Bil.Int (Cbat_word.to_word (w64 data)),
                  LittleEndian, sz))
  in
  let def_of_lhs sub (v : var) : def term option =
    Term.enum blk_t sub
    |> Seq.concat_map ~f:(Term.enum def_t)
    |> Seq.find ~f:(fun d -> Var.equal (Def.lhs d) v)
  in
  let def_of_tid sub dtid : def term option =
    Term.enum blk_t sub
    |> Seq.concat_map ~f:(Term.enum def_t)
    |> Seq.find ~f:(fun d -> Tid.equal (Term.tid d) dtid)
  in
  (* C1: the Region conversion — two constant cells ([RSP-24], [RSP-16]),
     each a whole-access store, plus the NESTED load (the -O0 cmp
     pattern) inside a BinOp def.  Every StackOff-proven access
     converts: the memory node re-points at the owning region's mem
     var, the ADDRESS arithmetic is KEPT (the emitter GEPs (position -
     region_lo) into the region's alloca), and a whole-access store's
     lhs rebinds to the region mem. *)
  let c1_st0 = mk_store 24L 1 `r64 in
  let c1_st1 = mk_store 16L 2 `r64 in
  let c1_t = v64 "pr_c1_t" in
  let c1_ld_nested =
    Def.create c1_t
      (Bil.BinOp (Bil.PLUS,
                  Bil.Load (Bil.Var m, minus_addr sp 16L, LittleEndian, `r64),
                  Bil.Int (Cbat_word.to_word (w64 1))))
  in
  let c1 = straight_sub "pr_c1_fission" [ c1_st0; c1_st1; c1_ld_nested ] in
  let c1' = rewrite_one c1 in
  check "PR-C1: the whole-access store rebinds lhs and mem node to the region mem, keeping the SP address arithmetic"
    (match def_of_lhs c1' (Sm.region_mem 1) with
     | Some d ->
        (match Def.rhs d with
         | Bil.Store (Bil.Var mem, Bil.BinOp (Bil.MINUS, Bil.Var b, Bil.Int _), _, _, _) ->
            Var.same mem (Sm.region_mem 1) && Var.same b sp
         | _ -> false)
     | None -> false);
  check "PR-C1: the nested load inside a BinOp def reads the region mem too (the -O0 cmp pattern)"
    (match def_of_lhs c1' c1_t with
     | Some d ->
        (match Def.rhs d with
         | Bil.BinOp (Bil.PLUS, Bil.Load (Bil.Var mem, _, _, _), Bil.Int _) ->
            Var.same mem (Sm.region_mem 2)
         | _ -> false)
     | None -> false);

  (* C2: the Arg_slot byte selection (S20) — args reads wholly inside
     one word cell become [hike_slotN] parameter reads: the full-cell
     read is the bare var, the aligned narrow read splices a LOW cast,
     and the intra-cell read at byte offset d selects bits
     [8d, 8d+bits). *)
  let rbp = v64 "RBP" in
  let d_rbp = Def.create rbp (Bil.Var sp) in
  let args_ld name off (sz : size) : def term =
    Def.create (v64 name)
      (Bil.Load
         ( Bil.Var m,
           Bil.BinOp (Bil.PLUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 off))),
           LittleEndian, sz ))
  in
  let slot0 = Sm.arg_slot ~word:8 0 in
  let c2_full = args_ld "pr_c2_full" 8 `r64 in
  let c2_narrow = args_ld "pr_c2_narrow" 8 `r32 in
  let c2_intra = args_ld "pr_c2_intra" 12 `r32 in
  let c2 = straight_sub "pr_c2_slot" [ d_rbp; c2_full; c2_narrow; c2_intra ] in
  let c2' = rewrite_one c2 in
  check "PR-C2: the full-cell args read (width 64) becomes the bare hike_slot0 var"
    (match def_of_tid c2' (Term.tid c2_full) with
     | Some d ->
        (match Def.rhs d with Bil.Var v -> Var.equal v slot0 | _ -> false)
     | None -> false);
  check "PR-C2: the aligned narrow args read (width 32 at cell start) splices the LOW cast"
    (match def_of_tid c2' (Term.tid c2_narrow) with
     | Some d ->
        (match Def.rhs d with
         | Bil.Cast (Bil.LOW, 32, Bil.Var v) -> Var.equal v slot0
         | _ -> false)
     | None -> false);
  check "PR-C2: the intra-cell args read (width 32 at byte 4) selects bits [32,63]"
    (match def_of_tid c2' (Term.tid c2_intra) with
     | Some d ->
        (match Def.rhs d with
         | Bil.Extract (63, 32, Bil.Var v) -> Var.equal v slot0
         | _ -> false)
     | None -> false);

  (* C3: write-closed Window — an Args cell that also contains a STORE
     takes Window storage on both sides: the read keeps its memory node
     AND its Args tag (never a slot parameter). *)
  let c3_rd = args_ld "pr_c3_rd" 8 `r64 in
  let c3_st =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.PLUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))),
           Bil.Int (Cbat_word.to_word (w64 9)),
           LittleEndian, `r64 ))
  in
  let c3 = straight_sub "pr_c3_abi" [ d_rbp; c3_rd; c3_st ] in
  let c3' = rewrite_one c3 in
  check "PR-C3: an Args read in a stored cell converts with the store to the incoming-window memory (write-closed)"
    (match def_of_tid c3' (Term.tid c3_rd) with
     | Some d ->
        (match Def.rhs d with
         | Bil.Load (Bil.Var mem, _, _, _) -> Var.same mem (Sm.window_mem)
         | _ -> false)
     | None -> false);

  (* N3 (V-F): the split RMW — one read-modify-write def on an Args
     cell fissions into the hoisted read def + the store def;
     write-closure demotes the slot for BOTH sides: the hoisted read
     keeps its memory node in the incoming-window memory (never an
     Arg_slot value), so the read cannot miss the store's write. *)
  let n3_rbp = v64 "RBP" in
  let n3_d_rbp = Def.create n3_rbp (Bil.Var sp) in
  let n3_addr =
    Bil.BinOp (Bil.PLUS, Bil.Var n3_rbp, Bil.Int (Cbat_word.to_word (w64 8)))
  in
  let n3_rmw =
    Def.create (v64 "pr_n3_rmw")
      (Bil.Store
         ( Bil.Var m, n3_addr,
           Bil.BinOp (Bil.PLUS,
                      Bil.Load (Bil.Var m, n3_addr, LittleEndian, `r64),
                      Bil.Int (Cbat_word.to_word (w64 1))),
           LittleEndian, `r64 ))
  in
  let n3 =
    straight_sub "pr_n3_rmw" [ n3_d_rbp; n3_rmw ]
    |> fun sub -> Program.create ~subs:[ sub ] ()
    |> Hike.Split_mem.normalize
    |> Term.first sub_t
    |> Base.Option.value_exn
  in
  let n3' = rewrite_one n3 in
  (* The split fired iff a def besides the two originals exists (the
     hoisted read; fresh vars print under their tid names). *)
  let n3_defs =
    Term.enum blk_t n3'
    |> Seq.concat_map ~f:(Term.enum def_t)
    |> Seq.to_list
  in
  let is_original d =
    Base.List.exists [ rbp; v64 "pr_n3_rmw" ] ~f:(Var.equal (Def.lhs d))
  in
  (* Every memory node of every def is on the incoming-window memory:
     the store's world and the hoisted read's world agree. *)
  let all_window =
    Base.List.for_all n3_defs ~f:(fun d ->
        let vis =
          object
            inherit [ bool ] Exp.visitor
            method! visit_load ~mem ~addr:_ _ _ acc =
              acc
              && (match mem with
                  | Bil.Var v -> Var.same v (Sm.window_mem)
                  | _ -> false)
            method! visit_store ~mem ~addr:_ ~exp:_ _ _ acc =
              acc
              && (match mem with
                  | Bil.Var v -> Var.same v (Sm.window_mem)
                  | _ -> false)
          end
        in
        vis#visit_exp (Def.rhs d) true)
  in
  check "PR-N3: the split RMW's hoisted read converts with the store to the incoming-window memory (write-closed)"
    (Base.List.exists n3_defs ~f:(fun d -> not (is_original d))
    && all_window);

  (* C4: the -O0 guard idiom — the load lives in its own def (the
     lifter materializes every load), the flag def reads the temp, and
     the jcc reads the flag.  hike-jump compiles the guard to a value
     comparison over the temp — no memory node ever rides a cond — and
     the rewrite converts the load def by its own conversion: the guard
     reads the converted temp transitively. *)
  let c4_st = mk_store 16L 7 `r64 in
  let c4_t = v64 "pr_c4_t" in
  let c4_ld =
    Def.create c4_t (Bil.Load (Bil.Var m, minus_addr sp 16L, LittleEndian, `r64))
  in
  let c4_zf = v1 "ZF" in
  let c4_flag =
    Def.create c4_zf
      (Bil.BinOp (Bil.EQ, Bil.Var c4_t, Bil.Int (Cbat_word.to_word (w64 0))))
  in
  let c4_pre, _ =
    sub_of "pr_c4_cond"
      [ [ c4_st; c4_ld; c4_flag ],
        [ (1, fun t -> mk_jmp_to t (Bil.Var c4_zf)); (1, mk_goto) ];
        [], [ (0, mk_ret) ] ]
  in
  let c4 = Hike.Jump.compile_sub jump_target c4_pre in
  let has_load (e : exp) : bool =
    let vis =
      object
        inherit [ bool ] Exp.visitor
        method! visit_load ~mem:_ ~addr:_ _ _ _ = true
      end
    in
    vis#visit_exp e false
  in
  check "PR-C4: the compiled guard is a value comparison — no memory node rides a cond"
    (Term.enum blk_t c4
     |> Seq.concat_map ~f:(Term.enum jmp_t)
     |> Seq.for_all ~f:(fun j -> not (has_load (Jmp.cond j))));
  let c4' = rewrite_one c4 in
  check "PR-C4: the load def converts to the region mem and the guard reads its temp"
    (match def_of_tid c4' (Term.tid c4_ld) with
     | Some d ->
        (match Def.rhs d with
         | Bil.Load (Bil.Var mem, _, _, _) ->
             Var.same mem (Sm.region_mem 1)
             && (Term.enum blk_t c4'
                 |> Seq.concat_map ~f:(Term.enum jmp_t)
                 |> Seq.exists ~f:(fun j ->
                        match Jmp.cond j with
                        | Bil.BinOp (Bil.EQ, Bil.Var v, Bil.Int _) ->
                            Var.equal v c4_t
                        | _ -> false))
         | _ -> false)
     | None -> false);
  ()

(* Lane D: the emitter's alloca shapes — the VLA lane (the dynamic     *)
(* allocation, stack-model hierarchy rule 1), the SP Slot / stack_0   *)
(* anchoring per storage class, and the frame-request clamp (never     *)
(* silent).                                                            *)

(* The fixture stamp: the dyn-alloc facts and the layout tag onto the
   terms; the def's slim tag is stamped at the fixture site (the
   emitter consumes no record). *)
let stamp_shape
    ?(dynamic_alloc_tids : Tid.Set.t option)
    ~(layout : Sm.sub_layout)
    (sub : sub term) : sub term =
  let sub =
    Sm.stamp_dyn_allocs
      ~dynamic_alloc_tids:(Base.Option.value dynamic_alloc_tids
                             ~default:Tid.Set.empty)
      sub
  in
  Sm.set_layout layout sub

(* The storage-free layout: no frame, no regions, no window. *)
let empty_layout : Sm.sub_layout =
  { regions = []; anchor = None; window_param = false }

(* Stamps the production tag onto a fixture def. *)
let tag_def (t : Sm.sec_tag) (d : def term) : def term = Sm.set_sec_tag t d

let run_emitter_shapes () =
  let m = memv "pr_d_m" in

  (* D1: the VLA lane — a non-literal SP decrement becomes a REAL
     runtime-sized alloca; the model RSP binds to its integer. *)
  let d_rbx = Def.create (v64 "pr_d_rbx") (Bil.Int (Cbat_word.to_word (w64 0x80))) in
  let d_vla =
    Def.create sp (Bil.BinOp (Bil.MINUS, Bil.Var sp, Bil.Var (Def.lhs d_rbx)))
  in
  let d_st =
    Def.create m
      (Bil.Store (Bil.Var m, Bil.Var sp, Bil.Int (Cbat_word.to_word (w64 7)),
                  LittleEndian, `r64))
  in
  let d1 = straight_sub "pr_d1_vla" [ d_rbx; d_vla; d_st ] in
  let ir1 =
    emit_ir
      [ stamp_shape ~dynamic_alloc_tids:(tid_set [ Term.tid d_vla ])
          ~layout:empty_layout d1 ]
  in
  check "PR-D1: the VLA def emits a real runtime-sized i8 alloca"
    (contains_substring ir1 "%vla = alloca i8, i64");
  check "PR-D1: the model SP binds to the alloca's integer (vla_i64)"
    (contains_substring ir1 "%vla_i64 = ptrtoint");

  (* D2 (v6): the SP Slot per region class.  The residue region (id 0)
     hosts the anchor; its entry index is the fold's. *)
  let residue_layout bytes idx : Sm.sub_layout =
    { regions = [ (0, (pos (-16L), pos (-9L)), bytes) ];
      anchor = Some (0, idx); window_param = false }
  in
  let d_ld =
    Def.create (v64 "pr_d2_t")
      (Bil.Load (Bil.Var (Sm.region_mem 0), minus_addr sp 16L, LittleEndian, `r64))
    |> tag_def (Sm.Tag.Stack (pos (-16L), pos (-16L)))
  in
  let d2 = straight_sub "pr_d2_residue" [ d_ld ] in
  let ir2 = emit_ir [ stamp_shape ~layout:(residue_layout 32L 8192L) d2 ] in
  check "PR-D2: residue storage anchors through the entry SP Slot (per-invocation stack_0)"
    (contains_substring ir2 "%sp_slot = alloca i64"
    && contains_substring ir2 "%stack_0 = load i64, ptr %sp_slot");
  (* A carved region anchors at the SysV residue (16 - word) when the
     layout names it. *)
  let d2b_ld =
    Def.create (v64 "pr_d2b_t")
      (Bil.Load (Bil.Var (Sm.region_mem 0), minus_addr sp 16L, LittleEndian, `r64))
  in
  let d2b = straight_sub "pr_d2b_region" [ d2b_ld ] in
  let region_layout : Sm.sub_layout =
    { regions = [ (0, (pos (-16L), pos (-9L)), 16L) ];
      anchor = Some (0, 8L); window_param = false }
  in
  let ir2b = emit_ir [ stamp_shape ~layout:region_layout d2b ] in
  check "PR-D2b: region storage anchors the SP Slot at region-0 + 8 (the SysV residue)"
    (contains_substring ir2b "getelementptr i8, ptr %stack_r0, i64 8"
    && contains_substring ir2b "%anchor_i64 = ptrtoint ptr %anchor to i64"
    && contains_substring ir2b "%sp_slot = alloca i64");
  (* Storage-free: no anchor, no SP Slot. *)
  let d2c = straight_sub "pr_d2c_free" [] in
  let ir2c = emit_ir [ stamp_shape ~layout:empty_layout d2c ] in
  check "PR-D2c: a storage-free sub emits no SP Slot and no region"
    (not (contains_substring ir2c "%sp_slot")
    && not (contains_substring ir2c "%stack_r"));

  (* D3: the array-count clamp — a region over the bound (2^31) clamps
     LOUDLY (never silent). *)
  let d3_ld =
    Def.create (v64 "pr_d3_t")
      (Bil.Load (Bil.Var m, minus_addr sp 0x80000000L, LittleEndian, `r64))
    |> tag_def (Sm.Tag.Stack (pos (-0x80000000L), pos (-0x80000000L)))
  in
  let d3 = straight_sub "pr_d3_huge" [ d3_ld ] in
  let clamp_layout : Sm.sub_layout =
    { regions = [ (0, (pos (-16L), pos (-9L)), 0x8000_0000L) ];
      anchor = Some (0, 8192L); window_param = false }
  in
  let d3_err = capture_stderr (fun () ->
      ignore (emit_ir [ stamp_shape ~layout:clamp_layout d3 ])) in
  let ir3 = emit_ir [ stamp_shape ~layout:clamp_layout d3 ] in
  check "PR-D3: an over-bound region request names itself on the channel and clamps"
    (contains_substring d3_err "hike: frame:"
    && contains_substring d3_err "clamped"
    && contains_substring ir3 "alloca [2147483632 x i8]");
  ()

(* Lane E: the register/convention facts (Hike_abi, ADR 0008: SP is    *)
(* the only stack-semantics register, fp an ordinary callee-saved GPR) *)
(* and the KB carrier's table semantics (one producer per slot, whose  *)
(* provide is the whole state).                                        *)

let run_abi_and_kb () =
  let abi = Hike.Abi.x86_64_sysv in
  let named n = Var.create ~is_virtual:false ~fresh:false n (Type.Imm 64) in
  (* The SysV record. *)
  check "PR-E1: the stack pointer is RSP, and only RSP (SP-only, ADR 0008)"
    (Var.equal (Var.base abi.Abi.sp) (Var.base (named "RSP"))
    && Abi.is_sp abi (named "RSP")
    && not (Abi.is_sp abi (named "RBP")));
  check "PR-E1: RBP is an ordinary callee-saved GPR — no frame-pointer fact exists"
    (Abi.is_callee_saved abi (named "RBP")
    && names_are abi.Abi.callee_saved [ "RBX"; "RBP"; "R12"; "R13"; "R14"; "R15" ]);
  check "PR-E1: the SysV lanes — 6 integer args, 8 vector args, RAX/RDX returns"
    (names_are abi.Abi.int_param_regs
       [ "RDI"; "RSI"; "RDX"; "RCX"; "R8"; "R9" ]
    && Base.List.length abi.Abi.vector_param_regs = 8
    && String.equal (Var.name (Base.List.nth_exn abi.Abi.vector_param_regs 0)) "YMM0"
    && names_are abi.Abi.return_regs [ "RAX"; "RDX" ]
    && Base.List.length
         (let unk = Abi.of_target Theory.Target.unknown in
          unk.Abi.int_param_regs @ unk.Abi.vector_param_regs)
       = 14);
  check "PR-E1: the structural predicates partition the lanes"
    (Abi.is_return_reg abi (named "RAX")
    && not (Abi.is_return_reg abi (named "RCX"))
    && Abi.is_vector_param_reg abi (named "YMM3")
    && not (Abi.is_vector_param_reg abi (named "RDI")));
  (* The unknown-target totality: the SysV record serves unit fixtures. *)
  check "PR-E1: an unknown target falls back to the SysV record (total)"
    (Abi.is_sp (Hike.Abi.of_target Theory.Target.unknown) (named "RSP")
    && Hike.Abi.addr_size_bits Theory.Target.unknown = 0);
  (* The real target: the reified SP register. *)
  let x86 = Theory.Target.of_string "x86_64-gnu-elf" in
  check "PR-E1: the x86_64-gnu-elf target reifies RSP as the SP"
    (Theory.Target.matches x86 "x86_64-gnu-elf"
    && Abi.is_sp (Hike.Abi.of_target x86) (Hike.Abi.sp x86));
  (* The word size comes from the Target API (principle 11). *)
  check "PR-E1: the word size — SysV carries the x86-64 word; of_target derives bits/8"
    (abi.Abi.word = 8
    && Hike.Abi.((of_target x86).Abi.word) = Theory.Target.bits x86 / 8);

  (* The KB carrier: one table (the block environments), one producer —
     [install_run] is the whole state, absence is the top identity. *)
  let t1 = Tid.create () in
  let t2 = Tid.create () in
  let present = function Some _ -> true | None -> false in
  Kb.install_run ~block_envs:(Tid.Map.singleton t1 (AI.top, AI.top));
  check "PR-E2: block_env reads back the provided pair; another block reads none"
    (present (Kb.block_env t1) && Kb.block_env t2 = None);
  check "PR-E2: the envs install is the whole state — the run's table replaces, never merges"
    (Kb.block_env t2 = None && present (Kb.block_env t1));
  Kb.install_run ~block_envs:(Tid.Map.singleton t2 (AI.top, AI.top));
  check "PR-E2: the replacement leaves no earlier run's entries"
    (present (Kb.block_env t2) && Kb.block_env t1 = None);
  (* The ONE lookup: absence is the no-constraint identity (the reader
     denotates in [AI.top]). *)
  check "PR-E2: block_env on a never-provided block is none"
    (Kb.block_env (Tid.create ()) = None);
  ()

(* The printable-run rule (the model's one home): a word is string
   text iff a printable run crosses its start boundary. *)
let run_text () =
  let txt = Array.of_list [ 0x63; 0x61; 0x74; 0; 0x61; 0xff; 0x74; 0 ] in
  check "STRING-TEXT: a printable run crossing the start covers the word"
    (Sm.string_text_word ~arr:txt ~off:1);
  check "STRING-TEXT: a NUL directly before the word means no crossing"
    (not (Sm.string_text_word ~arr:txt ~off:4));
  check "STRING-TEXT: pointer bytes before the word mean no crossing"
    (not (Sm.string_text_word ~arr:txt ~off:6));
  check "STRING-TEXT: a non-printable start byte never covers"
    (not (Sm.string_text_word ~arr:txt ~off:5));
  check "STRING-TEXT: the first word of the image never crosses"
    (not (Sm.string_text_word ~arr:txt ~off:0));
  let all_txt = Array.of_list [ 0x63; 0x61; 0x74; 0x20; 0x7e ] in
  check "STRING-TEXT: running off the front crosses iff the prefix is all printable"
    (Sm.string_text_word ~arr:all_txt ~off:4)

let run () =
  run_producer_record ();
  run_layout ();
  run_stl_rewrite ();
  run_emitter_shapes ();
  run_text ();
  run_abi_and_kb ()
