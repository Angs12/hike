(* The attribution pins (T1): the ONE range mechanism's normalization
   table, the section projection, the finalized trees' storage rule,
   the immutable visitor's collection (escapes, TOP members, separate
   sub scopes), and the slim-tag stamping. *)
open Bap.Std
open Bap_core_theory
open Test_common
open Test_fixtures

module A = Hike.Sections
module S = Hike.Stack_model
module Tag = Hike.Sections.Tag
module Hv = Hike.Vsa
module Ws = Cbat_clp_set_composite

let entry = Hike.Stack_model.segment_base
let pos = Int64.add entry

let i2w (x : int64) : Cbat_word.t =
  Cbat_word.of_word (Word.of_int64 ~width:64 x)

let portion_eq (p : A.portion) (sec : A.sec) (lo : int64) (hi : int64) =
  A.equal_sec p.A.pt_sec sec && Int64.equal p.A.pt_lo lo
  && Int64.equal p.A.pt_hi hi

let span_holds (ps : A.portion list) (sec : A.sec) (lo : int64) (hi : int64) =
  Base.List.exists ps ~f:(fun p -> portion_eq p sec lo hi)

(* The pure mechanism over constructed word sets. *)
let rd ?(rip = false) ?(width = 8) (ws : Ws.t) =
  A.range_of_denotation ~word:8 ~entry ~spans:[] ~rip ~width ws

let spans_of () =
  [ { A.ds_sec = S.Data; ds_lo = 0x4000L; ds_hi = 0x403FL; ds_slots = [] };
    { A.ds_sec = S.Rodata; ds_lo = 0x5000L; ds_hi = 0x501FL; ds_slots = [] } ]

let rd_spans ?(rip = false) ?(width = 8) (ws : Ws.t) =
  A.range_of_denotation ~word:8 ~entry ~spans:(spans_of ()) ~rip ~width ws

(* S01/S02/S03: the normalization and projection table. *)
let run_ranges () =
  let stack_off o = Ws.stack_word_i64 o in
  let stack_rng a b = Ws.stack_word (Clp.interval ~width:64 (i2w a) (i2w b)) in
  check "AT1-S01: a 1-byte singleton occupies exactly its byte"
    (match rd ~width:1 (stack_off (-8L)) with
     | _, [ p ] -> portion_eq p S.Stack (pos (-8L)) (pos (-8L))
     | _ -> false);
  check "AT1-S01: an 8-byte singleton at entry-8 occupies [entry-8,entry-1]"
    (match rd ~width:8 (stack_off (-8L)) with
     | _, [ p ] -> portion_eq p S.Stack (pos (-8L)) (pos (-1L))
     | _ -> false);
  check "AT1-S01: a ranged hull [entry-12,entry-8] of width 4 occupies through entry-5"
    (match rd ~width:4 (stack_rng (-12L) (-8L)) with
     | _, [ p ] -> portion_eq p S.Stack (pos (-12L)) (pos (-5L))
     | _ -> false);
  check "AT1-S01: a 4-byte singleton at entry-4 occupies [entry-4,entry-1]"
    (match rd ~width:4 (stack_off (-4L)) with
     | _, [ p ] -> portion_eq p S.Stack (pos (-4L)) (pos (-1L))
     | _ -> false);
  check "AT1-S01: the retaddr read at entry of width 8 occupies [entry,entry+7] (Stack)"
    (match rd ~width:8 (stack_off 0L) with
     | t, [ p ] ->
         portion_eq p S.Stack entry (pos 7L)
         &&
         (match t with
          | Some Tag.Stack (l, h) -> Int64.equal l entry && Int64.equal h entry
          | _ -> false)
     | _ -> false);
  check "AT1-S01: an args read at entry+8 occupies [entry+8,entry+15] (Args)"
    (match rd ~width:8 (stack_off 8L) with
     | t, [ p ] ->
         portion_eq p S.Args (pos 8L) (pos 15L)
         &&
         (match t with
          | Some Tag.Args (l, h) ->
              Int64.equal l (pos 8L) && Int64.equal h (pos 8L)
          | _ -> false)
     | _ -> false);
  check "AT1-S02: bottom yields the Dead tag and no portion"
    (match rd (Ws.of_clp (Clp.bottom 64)) with
     | Some Tag.Dead, [] -> true
     | _ -> false);
  check "AT1-S02: a plain TOP claims the sub-local line, no data span, no tag"
    (match rd (Ws.top 64) with
     | None, [ p1; p2 ] ->
         portion_eq p1 S.Stack (Int64.add entry Stdlib.Int64.min_int) (pos 7L)
         && portion_eq p2 S.Args (pos 8L) Stdlib.Int64.max_int
     | _ -> false);
  check "AT1-S02: a symbolic TOP clamps to [entry-stack_max, entry), below-entry only"
    (match rd (Ws.stack_word (Clp.top 64)) with
     | Some Tag.Stack_unbounded, [ p ] ->
         portion_eq p S.Stack (pos (-65536L)) (pos (-1L))
     | _ -> false);
  check "AT1-S02: a plain TOP claims no data span (imprecision never poisons the spans)"
    (let _, ps = rd_spans (Ws.top 64) in
     Base.List.for_all ps ~f:(fun p ->
         match p.A.pt_sec with S.Stack | S.Args -> true | _ -> false));
  check "AT1-S02: the full data domain [0,2^64-1] is a valid ordered range"
    (A.compare_point { A.p_sec = S.Data; p_pos = 0L }
       { A.p_sec = S.Data; p_pos = (-1L) } < 0);
  check "AT1-S02: the unsigned seam orders the high half above 2^63-1"
    (A.compare_point { A.p_sec = S.Data; p_pos = 0x7fff_ffff_ffff_ffffL }
       { A.p_sec = S.Data; p_pos = (-1L) } < 0);
  check "AT1-S02: an overflowed unsigned expansion saturates at the top, never a wrapped short range"
    (let ws = Ws.of_clp (Clp.interval ~width:64 (i2w (-8L)) (i2w (-1L))) in
     let top_span =
       [ { A.ds_sec = S.Data; ds_lo = (-16L); ds_hi = (-1L); ds_slots = [] } ]
     in
     match
       A.range_of_denotation ~word:8 ~entry ~spans:top_span ~rip:true ~width:8 ws
     with
     | Some Tag.Sec (_, lo, hi), [ p ] ->
         (* The whole occupied range [2^64-8, 2^64-1]: hi+7 wrapped and
            saturated at the domain top, keeping the full coverage. *)
         Int64.equal lo (-8L) && Int64.equal hi (-1L)
         && Int64.unsigned_compare p.A.pt_lo p.A.pt_hi <= 0
         && Int64.equal p.A.pt_hi (-1L)
     | _ -> false);
  check "AT1-S02: a signed expansion at the line's top saturates at the ceiling"
    (let top_off = Int64.sub Stdlib.Int64.max_int entry in
     let ws = Ws.stack_word_i64 top_off in
     match rd ~width:8 ws with
     | _, ps ->
         Base.List.exists ps ~f:(fun p ->
             A.equal_sec p.A.pt_sec S.Args
             && Int64.equal p.A.pt_lo Stdlib.Int64.max_int
             && Int64.equal p.A.pt_hi Stdlib.Int64.max_int));
  check "AT1-S03: a crossing interval splits Stack/Args, both identity"
    (let ws =
       Ws.of_clp (Clp.interval ~width:64 (i2w (pos (-4L))) (i2w (pos 12L)))
     in
     match rd ~width:1 ws with
     | Some Tag.Stack (l, h), [ p1; p2 ] ->
         Int64.equal l (pos (-4L)) && Int64.equal h (pos 12L)
         && portion_eq p1 S.Stack (pos (-4L)) (pos 7L)
         && portion_eq p2 S.Args (pos 8L) (pos 12L)
         && (not p1.A.pt_elig) && (not p2.A.pt_elig)
     | _ -> false);
  check "AT1-S03: a bounded single-space symbolic read stays eligible"
    (match rd ~width:8 (stack_off (-8L)) with
     | _, [ p ] -> p.A.pt_elig
     | _ -> false);
  check "AT1-S03: a plain band hull contributes identity portions (no StackOff proof)"
    (let ws =
       Ws.of_clp (Clp.interval ~width:64 (i2w (pos (-16L))) (i2w (pos (-9L))))
     in
     match rd ~width:8 ws with
     | Some Tag.Stack (l, h), [ p ] ->
         Int64.equal l (pos (-16L)) && Int64.equal h (pos (-9L))
         && (not p.A.pt_elig)
         && portion_eq p S.Stack (pos (-16L)) (pos (-2L))
     | _ -> false);
  check "AT1-S03: a rip-tagged plain access wholly in one span is the Sec proof"
    (let ws = Ws.of_clp (Clp.interval ~width:64 (i2w 0x4010L) (i2w 0x4017L)) in
     match rd_spans ~rip:true ~width:8 ws with
     | Some Tag.Sec (s, lo, hi), [ p ] ->
         (* The Sec bounds are the occupied extent (the width rides in). *)
         A.equal_sec s S.Data && Int64.equal lo 0x4010L && Int64.equal hi 0x401EL
         && p.A.pt_elig
     | _ -> false);
  check "AT1-S03: a symbolic occupied range crossing the retaddr boundary is identity"
    (match rd ~width:8 (stack_off 4L) with
     | _, ps ->
         (* [entry+4,entry+11] crosses into Args: identity both sides. *)
         Base.List.for_all ps ~f:(fun p -> not p.A.pt_elig)
         && Base.List.length ps = 2);
  check "AT1-S03: the same access without the rip tag contributes identity"
    (let ws = Ws.of_clp (Clp.interval ~width:64 (i2w 0x4010L) (i2w 0x4017L)) in
     match rd_spans ~rip:false ~width:8 ws with
     | None, [ p ] -> not p.A.pt_elig
     | _ -> false);
  check "AT1-S03: a plain access straddling a span edge contributes its intersecting portion, identity"
    (let ws = Ws.of_clp (Clp.interval ~width:64 (i2w 0x403CL) (i2w 0x4043L)) in
     match rd_spans ~rip:true ~width:8 ws with
     | None, [ p ] -> portion_eq p S.Data 0x403CL 0x403FL && not p.A.pt_elig
     | _ -> false);
  check "AT1-S03: an interval disjoint from every span contributes no member"
    (let ws = Ws.of_clp (Clp.interval ~width:64 (i2w 0x6000L) (i2w 0x6007L)) in
     match rd_spans ~rip:true ~width:8 ws with
     | None, [] -> true
     | _ -> false)

(* The end-to-end collector: freshly installed fixture environments
   through the sanctioned KB lifecycle, then one attrib pass. *)
let install_envs (subs : sub term list) : bool =
  let all_envs, ok =
    Base.List.fold subs ~init:(Tid.Map.empty, true) ~f:(fun (m, ok) sub ->
        match
          Hv.fixpoint Theory.Target.unknown sp
            ~prog:(Program.create ~subs:[ sub ] ())
            ~images:[] sub
        with
        | None -> (m, false)
        | Some (envs, _) ->
            Core.Map.merge m envs
              ~f:(fun ~key:_ el ->
                match el with
                | `Left v | `Right v | `Both (_, v) -> Some v),
            ok)
  in
  Hike.Kb.install_run ~block_envs:all_envs;
  ok && not (Core.Map.is_empty all_envs)

let attribute_of (subs : sub term list) : A.ctx =
  A.attribute ~word:8 ~entry ~abi:Hike.Abi.x86_64_sysv
    ~spans:(spans_of ()) ~denote:Hv.denote_exp_at
    (Program.create ~subs ())

let storage_at (ctx : A.ctx) (sub : sub term) (sec : A.sec) (lo : int64)
    (hi : int64) : A.storage option =
  match Core.Map.find ctx.A.sub_trees (Term.tid sub) with
  | Some tree ->
      Base.Option.map (A.storage_of_range tree (A.range sec lo hi))
        ~f:(fun rs -> rs.A.storage)
  | None -> None

let mem_rbp () = (memv "at_m", v64 "RSP", v64 "RBP")

let load_at (m : var) (base : var) (off : int64) (bits : int) : def term =
  Def.create (v64 "at_t")
    (Bil.Load
       ( Bil.Var m,
         Bil.BinOp (Bil.MINUS, Bil.Var base, Bil.Int (Cbat_word.to_word (i2w off))),
         LittleEndian,
         Size.of_int_exn bits ))

let ld_plus (m : var) (base : var) (off : int64) (bits : int) : def term =
  Def.create (v64 "at_a")
    (Bil.Load
       ( Bil.Var m,
         Bil.BinOp (Bil.PLUS, Bil.Var base, Bil.Int (Cbat_word.to_word (i2w off))),
         LittleEndian,
         Size.of_int_exn bits ))

let st_plus (m : var) (base : var) (off : int64) (bits : int) : def term =
  Def.create m
    (Bil.Store
       ( Bil.Var m,
         Bil.BinOp (Bil.PLUS, Bil.Var base, Bil.Int (Cbat_word.to_word (i2w off))),
         Bil.Int (Cbat_word.to_word (w64 7)),
         LittleEndian,
         Size.of_int_exn bits ))

let tag_of (sub : sub term) (d : def term) =
  Term.enum blk_t sub |> Seq.concat_map ~f:(Term.enum def_t)
  |> Seq.find_map ~f:(fun dd ->
         if Tid.equal (Term.tid dd) (Term.tid d) then A.sec_tag dd else None)

(* The collection and the storage rule over real fixtures. *)
let run_trees () =
  let m, rsp, rbp = mem_rbp () in
  let def_rbp = Def.create rbp (Bil.Var rsp) in
  let l16 = load_at m rbp 16L 64 in
  let l12 = load_at m rbp 12L 64 in
  let l8 = load_at m rbp 8L 64 in
  let sub1 = straight_sub "at_reads" [ def_rbp; l16; l12; l8 ] in
  check "AT1-ENV: the fixture's environments install (the lifecycle)"
    (install_envs [ sub1 ]);
  let ctx1 = attribute_of [ sub1 ] in
  check "AT1-TREE: the bridged reads merge into one Region over [entry-16,entry-1]"
    (match storage_at ctx1 sub1 S.Stack (pos (-16L)) (pos (-1L)) with
     | Some (A.Stack_region 1) -> true
     | _ -> false);
  check "AT1-TREE: adjacent-only reads stay separate with ascending ids"
    (let sub2 =
       straight_sub "at_adj" [ def_rbp; load_at m rbp 32L 64; load_at m rbp 16L 64 ]
     in
     ignore (install_envs [ sub2 ]);
     let ctx = attribute_of [ sub2 ] in
     match
       ( storage_at ctx sub2 S.Stack (pos (-32L)) (pos (-25L)),
         storage_at ctx sub2 S.Stack (pos (-16L)) (pos (-9L)) )
     with
     | Some (A.Stack_region 1), Some (A.Stack_region 2) -> true
     | _ -> false);
  (* TOP write + known read: shared Frame storage; a different sub's
     trees never merge. *)
  let u = v64 "at_u" in
  let known = load_at m rbp 8L 64 in
  let top_store =
    Def.create m
      (Bil.Store (Bil.Var m, Bil.Var u, Bil.Int (Cbat_word.to_word (w64 42)), LittleEndian, `r64))
  in
  let subw = straight_sub "at_topwrite" [ def_rbp; known; top_store ] in
  let other = straight_sub "at_other" [ def_rbp; load_at m rbp 8L 64 ] in
  check "AT1-ENV: the top-write fixtures' environments install"
    (install_envs [ subw; other ]);
  let ctx = attribute_of [ subw; other ] in
  check "AT1-TOPW: the TOP write and the known read share Frame storage"
    (match storage_at ctx subw S.Stack (pos (-8L)) (pos (-1L)) with
     | Some A.Stack_residue -> true
     | _ -> false);
  check "AT1-TOPW: the TOP write also claims the Args space (Window)"
    (match storage_at ctx subw S.Args (pos 8L) Stdlib.Int64.max_int with
     | Some A.Stack_residue -> true
     | _ -> false);
  check "AT1-SCOPE: a different sub's tree keeps its own Region"
    (match storage_at ctx other S.Stack (pos (-8L)) (pos (-1L)) with
     | Some (A.Stack_region 1) -> true
     | _ -> false);
  (* Escapes: a stored SP-derived value joins as an identity member
     with no def and forces Frame on its component. *)
  let esc_data = v64 "at_esc" in
  let def_esc =
    Def.create esc_data
      (Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 0x30))))
  in
  let esc_store =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 0x20))),
           Bil.Var esc_data,
           LittleEndian,
           `r64 ))
  in
  let clean = load_at m rbp 0x20L 64 in
  let sub3 = straight_sub "at_escape" [ def_rbp; def_esc; clean; esc_store ] in
  check "AT1-ENV: the escape fixture's environments install"
    (install_envs [ sub3 ]);
  let ctx3 = attribute_of [ sub3 ] in
  check "AT1-ESC: the escaped extent's component takes Frame storage"
    (match storage_at ctx3 sub3 S.Stack (pos (-0x30L)) (pos (-0x29L)) with
     | Some A.Stack_residue -> true
     | _ -> false);
  check_bound "AT1-ESC: the escape member survives finalization with no def"
    (Core.Map.find ctx3.A.sub_trees (Term.tid sub3))
    (fun tree ->
       A.Tree.to_sequence tree |> Seq.to_list
       |> Base.List.exists ~f:(fun (_, rs) ->
              Base.List.exists rs.A.members ~f:(fun mm ->
                  Option.is_none mm.A.m_def && mm.A.m_identity)));
  (* The retaddr row. *)
  let ret_read =
    Def.create (v64 "at_ret") (Bil.Load (Bil.Var m, Bil.Var rsp, LittleEndian, `r64))
  in
  let sub4 = straight_sub "at_retaddr" [ ret_read ] in
  check "AT1-ENV: the retaddr fixture's environments install"
    (install_envs [ sub4 ]);
  let ctx4 = attribute_of [ sub4 ] in
  check "AT1-RET: the retaddr bytes' component takes Frame storage"
    (match storage_at ctx4 sub4 S.Stack entry (pos 7L) with
     | Some A.Stack_residue -> true
     | _ -> false);
  (* Args: the intra-slot reads share one Arg_slot; a store demotes its
     cell only; the neighboring cell is unaffected. *)
  let a_full = ld_plus m rbp 8L 64 in
  let a_intra = ld_plus m rbp 12L 32 in
  let sub5 = straight_sub "at_args" [ def_rbp; a_full; a_intra ] in
  check "AT1-ENV: the args fixture's environments install"
    (install_envs [ sub5 ]);
  let ctx5 = attribute_of [ sub5 ] in
  check "AT1-ARGS: the full-cell and intra-cell reads share Arg_slot 0"
    (match storage_at ctx5 sub5 S.Args (pos 8L) (pos 15L) with
     | Some (A.Arg_slot 0) -> true
     | _ -> false);
  let a_cell1 = ld_plus m rbp 16L 64 in
  let sub6 =
    straight_sub "at_args_store"
      [ def_rbp; a_full; st_plus m rbp 8L 64; a_cell1 ]
  in
  check "AT1-ENV: the args-store fixture's environments install"
    (install_envs [ sub6 ]);
  let ctx6 = attribute_of [ sub6 ] in
  check "AT1-ARGS: a store demotes its cell to Window"
    (match storage_at ctx6 sub6 S.Args (pos 8L) (pos 15L) with
     | Some A.Stack_residue -> true
     | _ -> false);
  check "AT1-ARGS: the neighboring cell keeps its own Arg_slot"
    (match storage_at ctx6 sub6 S.Args (pos 16L) (pos 23L) with
     | Some (A.Arg_slot 1) -> true
     | _ -> false);
  (* Stamping: the tags land on the defs' values (present BEFORE any
     removal test). *)
  check "AT1-TAG: the known stack read carries its Stack bounds tag"
    (match tag_of (A.stamp_tags ctx1 sub1) l16 with
     | Some Tag.Stack (l, h) ->
         Int64.equal l (pos (-16L)) && Int64.equal h (pos (-16L))
     | _ -> false);
  check "AT1-TAG: the intra-cell args read carries its Args bounds tag"
    (match tag_of (A.stamp_tags ctx5 sub5) a_intra with
     | Some Tag.Args (l, h) ->
         Int64.equal l (pos 12L) && Int64.equal h (pos 12L)
     | _ -> false);
  check "AT1-TAG: the TOP-addressed store carries no tag (unknown provenance)"
    (match tag_of (A.stamp_tags ctx subw) top_store with None -> true | _ -> false)

(* T3: the data rows of the storage rule (S13) — Global conversion
   through the rip proof, the word hull, the typed-width agreement,
   and the Whole_span identity. *)
let sec_load ?(rip = true) ?(width = 8) (addr : int64) : def term =
  let d =
    Def.create (v64 "at_g")
      (Bil.Load
         ( Bil.Var (memv "at_gm"),
           Bil.Int (Word.of_int64 ~width:64 addr),
           LittleEndian,
           Size.of_int_exn (8 * width) ))
  in
  if rip then
    Def.with_value d
      (Bap_knowledge.Knowledge.Value.put Bap.Std.rip_relative_addr
         (Def.value d) true)
  else d

let data_ctx (defs : def term list) : A.ctx =
  let sub = straight_sub "at_global" defs in
  (* The seam's replay reads the stamped environments: install the
     fixture's block envs through the sanctioned lifecycle. *)
  ignore (install_fixture_envs [ sub ]);
  attribute_of [ sub ]

let data_comps (ctx : A.ctx) : Hike.Stack_model.sec_comp list =
  A.global_comps_of ~word:8 ~spans:(spans_of ()) ctx

let component_is (c : Hike.Stack_model.sec_comp) ~(id : int) ~(lo_w : int)
    ~(hi_w : int) ~(typed_w : int) =
  c.Hike.Stack_model.comp_id = id
  && c.Hike.Stack_model.lo_w = lo_w
  && c.Hike.Stack_model.hi_w = hi_w
  && c.Hike.Stack_model.typed_w = typed_w

let run_data () =
  check "AT3-ENV: the data fixture's environments install"
    (let sub = straight_sub "at_env" [ sec_load 0x4008L ] in
     install_fixture_envs [ sub ]);
  check "AT3-DATA: the rip-proved in-span read's Global component is its word range"
    (match data_comps (data_ctx [ sec_load 0x4008L ]) with
     | [ c ] -> component_is c ~id:0 ~lo_w:1 ~hi_w:1 ~typed_w:8
     | _ -> false);
  check "AT3-DATA: the same read without the rip proof converts to nothing"
    (Base.List.is_empty
       (data_comps (data_ctx [ sec_load ~rip:false 0x4008L ])));
  check "AT3-DATA: a sub-word read's component covers the whole word (the word hull)"
    (match data_comps (data_ctx [ sec_load ~width:4 0x4004L ]) with
     | [ c ] -> component_is c ~id:0 ~lo_w:0 ~hi_w:0 ~typed_w:4
     | _ -> false);
  check "AT3-DATA: same-word reads merge into one component; agreeing widths type the tile"
    (match
       data_comps (data_ctx [ sec_load ~width:4 0x4000L; sec_load ~width:4 0x4004L ])
     with
     | [ c ] -> component_is c ~id:0 ~lo_w:0 ~hi_w:0 ~typed_w:4
     | _ -> false);
  check "AT3-DATA: disagreeing widths collapse the component's type to bytes"
    (match
       data_comps (data_ctx [ sec_load ~width:4 0x4000L; sec_load ~width:2 0x4004L ])
     with
     | [ c ] -> component_is c ~id:0 ~lo_w:0 ~hi_w:0 ~typed_w:1
     | _ -> false);
  check "AT3-DATA: disjoint words keep separate components; ids ascend by (section, position)"
    (match data_comps (data_ctx [ sec_load 0x4008L; sec_load 0x4000L ]) with
     | [ c0; c1 ] ->
       component_is c0 ~id:0 ~lo_w:0 ~hi_w:0 ~typed_w:8
       && component_is c1 ~id:1 ~lo_w:1 ~hi_w:1 ~typed_w:8
     | _ -> false);
  check "AT3-DATA: a copy-reloc span is ONE whole-span region; the slot access keeps the through lane"
    (let slot_spans =
       [ { A.ds_sec = S.Data; ds_lo = 0x4000L; ds_hi = 0x403FL;
           ds_slots = [ 0x4008L ] } ]
     in
     let sub = straight_sub "at_slot" [ sec_load 0x4008L ] in
     let ctx =
       A.attribute ~word:8 ~entry ~abi:Hike.Abi.x86_64_sysv ~spans:slot_spans
         ~denote:Hv.denote_exp_at (Program.create ~subs:[ sub ] ())
     in
     Base.List.is_empty (A.global_comps_of ~word:8 ~spans:slot_spans ctx)
     && (match A.whole_comps_of ~word:8 ~spans:slot_spans ctx with
         | [ (_id, 0x4000L, 0x403FL) ] -> true
         | _ -> false)
     && (match
           A.storage_of_range ctx.A.data_tree
             (A.range S.Data 0x4008L 0x400fL)
         with
         | Some { A.storage = A.Data_region _; _ } -> true
         | _ -> false))

let run () =
  run_ranges ();
  run_trees ();
  run_data ()