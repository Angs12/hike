(* Attribution pins: the ONE range mechanism's normalization table, the
   section projection, the finalized trees' storage rule, the visitor's
   collection (escapes, TOP members, separate sub scopes), the slim-tag
   stamping, the data components, and the Sections-owned regression
   pins (narrow store, escapes, regions, fp-GPR value proof).  One
   Alcotest group per pin; each pin builds its own fixture, so no state
   crosses pins. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

module A = Hike.Sections
module S = Hike.Stack_model
module Tag = Hike.Sections.Tag

let entry = Hike.Stack_model.segment_base

(* An int64 word (the plain denotation literal). *)


let portion_eq (p : A.portion) (sec : A.sec) (lo : int64) (hi : int64) =
  A.equal_sec p.A.pt_sec sec && Int64.equal p.A.pt_lo lo
  && Int64.equal p.A.pt_hi hi

let stack_off (o : int64) : Ws.t = Ws.stack_word_i64 o

let rd ?(rip = false) ?(width = 8) ?(extents = []) (ws : Ws.t) =
  A.range_of_denotation ~extents ~word:8 ~entry ~spans:[] ~rip ~width ws

let spans_of () =
  [ { A.ds_sec = S.Data; ds_lo = 0x4000L; ds_hi = 0x403FL; ds_slots = [] };
    { A.ds_sec = S.Rodata; ds_lo = 0x5000L; ds_hi = 0x501FL; ds_slots = [] } ]

let rd_spans ?(rip = false) ?(width = 8) (ws : Ws.t) =
  A.range_of_denotation ~extents:[] ~word:8 ~entry ~spans:(spans_of ()) ~rip
    ~width ws

(* Fixture stack frame: the mem, the SP and the frame pointer. *)
let mem_rbp () = (memv "at_m", v64 "RSP", v64 "RBP")

(* The fixture's one installed context: the solve, the one install, and
   the stamped subs the seam reads. *)
let tree_ctx (subs : sub term list) : A.ctx =
  fixture_ctx ~spans:(spans_of ()) subs

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
         if Tid.equal (Term.tid dd) (Term.tid d) then Ds.sec_tag dd else None)

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

let storage_at (ctx : A.ctx) (sub : sub term) (sec : A.sec) (lo : int64)
    (hi : int64) : A.storage option =
  Base.Option.bind (Core.Map.find ctx.A.sub_trees (Term.tid sub))
    ~f:(fun tree ->
      Base.Option.map (A.storage_of_range tree (A.range sec lo hi))
        ~f:(fun rs -> rs.A.storage))

(* T3: the data rows of the storage rule — Global conversion through the
   rip proof, the word hull, the typed-width agreement, and the
   Whole_span identity. *)
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
  tree_ctx [ straight_sub "at_global" defs ]

let data_comps (ctx : A.ctx) : Hike.Stack_model.sec_comp list =
  A.global_comps_of ~word:8 ~spans:(spans_of ()) ctx

let component_is (c : Hike.Stack_model.sec_comp) ~(id : int) ~(lo_w : int)
    ~(hi_w : int) ~(typed_w : int) =
  c.Hike.Stack_model.comp_id = id
  && c.Hike.Stack_model.lo_w = lo_w
  && c.Hike.Stack_model.hi_w = hi_w
  && c.Hike.Stack_model.typed_w = typed_w

(* The pre-call state of a two-block escape fixture: the first two
   blocks' defs folded from the anchored entry. *)
let st_pre (sub : sub term) (blk0 : blk term) (blk1 : blk term) : AI.t =
  let blk_of tid =
    match Term.find blk_t sub tid with Some b -> b | None -> assert false
  in
  Vsa.Test_seam.denote_defs
    (blk_of (Term.tid blk1))
    (Vsa.Test_seam.denote_defs (blk_of (Term.tid blk0)) (anchored_entry ()))

let read64 (m : var) (ai : AI.t) (addr : int64) : Ws.t =
  match Mem.Key.of_wordset (Ws.stack_word_i64 addr) with
  | [ k ] ->
      Mem.Val.data
        (Mem.find (64, LittleEndian)
           (AI.find_memory
              { Mem.addr_width = 64; Mem.addressable_width = 8 }
              ai m)
           k)
  | _ -> assert false

(* The full-span claim shapes.  With no VLA live, the tops claim the
   sub-local line only — a VLA's bytes enter a claim solely through
   its recorded extent. *)
let plain (t, ps) =
  match t, ps with
  | None, [ p1; p2 ] ->
      portion_eq p1 S.Stack (Int64.add entry Stdlib.Int64.min_int) (pos 7L)
      && portion_eq p2 S.Args (pos 8L) Stdlib.Int64.max_int
  | _ -> false

let clamped (t, ps) =
  match t, ps with
  | Some Tag.Unbounded, [ p1 ] ->
      portion_eq p1 S.Stack (pos (-65536L)) (pos (-1L))
  | _ -> false

(* S2's shape: a heap-pointing GPR store beside the [RSP-16] cell
   write; the base register is the control (RBP vs RBX). *)
let heap_store_sub name m_name (base : var) : sub term =
  let rsp = v64 "RSP" in
  let m = memv m_name in
  let def_heap =
    Def.create base (Bil.Int (Cbat_word.to_word (w64 0x400000)))
  in
  let def_rsp =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 16)) ),
           Bil.Int (Cbat_word.to_word (w64 1)),
           LittleEndian,
           `r64 ))
  in
  let def_heap_store =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.PLUS, Bil.Var base, Bil.Int (Cbat_word.to_word (w64 0x100)) ),
           Bil.Int (Cbat_word.to_word (w64 9)),
           LittleEndian,
           `r64 ))
  in
  fst (sub_of name [ [ def_heap; def_rsp; def_heap_store ], [ (1, mk_goto) ]; [], [] ])

let tests : unit Alcotest.test list =
  [
    (* S01/S02/S03: the normalization and projection table. *)












    pin "SEC-07" "AT1-S02: bottom yields the Dead tag and no portion"
      (fun () ->
        check "SEC-07"
          (match rd (Ws.of_clp (Clp.bottom 64)) with
           | Some Tag.Dead, [] -> true
           | _ -> false));

    pin "SEC-08" "AT1-S02: a plain TOP claims the sub-local line, no tag"
      (fun () ->
        check "SEC-08"
          (match rd (Ws.top 64) with
           | None, [ p1; p2 ] ->
               portion_eq p1 S.Stack
                 (Int64.add entry Stdlib.Int64.min_int)
                 (pos 7L)
               && portion_eq p2 S.Args (pos 8L) Stdlib.Int64.max_int
           | _ -> false));

    pin "SEC-09"
      "AT1-S02: a symbolic TOP clamps to [entry-stack_max, entry)"
      (fun () ->
        check "SEC-09"
          (match rd (Ws.stack_word (Clp.top 64)) with
           | Some Tag.Unbounded, [ p1 ] ->
               portion_eq p1 S.Stack (pos (-65536L)) (pos (-1L))
           | _ -> false));

    pin "SEC-10"
      "AT1-S02: a plain TOP claims no data span (imprecision never poisons the spans)"
      (fun () ->
        check "SEC-10"
          (let _, ps = rd_spans (Ws.top 64) in
           Base.List.for_all ps ~f:(fun p ->
               match p.A.pt_sec with S.Stack | S.Args | S.Vla -> true | _ -> false)));





    pin "SEC-13"
      "AT1-S02: an overflowed unsigned expansion saturates at the top, never a wrapped short range"
      (fun () ->
        check "SEC-13"
          (let ws = Ws.of_clp (Clp.interval ~width:64 (i2w (-8L)) (i2w (-1L))) in
           let top_span =
             [ { A.ds_sec = S.Data;
                 ds_lo = (-16L);
                 ds_hi = (-1L);
                 ds_slots = [] } ]
           in
           match
             A.range_of_denotation ~extents:[] ~word:8 ~entry ~spans:top_span
               ~rip:true ~width:8 ws
           with
           | None, [ p ] ->
               (* The whole occupied range [2^64-8, 2^64-1]: hi+7 wrapped
                  and saturated at the domain top, keeping the full
                  coverage. *)
               Int64.equal p.A.pt_lo (-8L) && Int64.equal p.A.pt_hi (-1L)
               && Int64.unsigned_compare p.A.pt_lo p.A.pt_hi <= 0
           | _ -> false));

    pin "SEC-14" "AT1-S02: a signed expansion at the line's top saturates at the ceiling"
      (fun () ->
        check "SEC-14"
          (let top_off = Int64.sub Stdlib.Int64.max_int entry in
           let ws = stack_off top_off in
           match rd ~width:8 ws with
           | _, ps ->
               Base.List.exists ps ~f:(fun p ->
                   A.equal_sec p.A.pt_sec S.Args
                   && Int64.equal p.A.pt_lo Stdlib.Int64.max_int
                   && Int64.equal p.A.pt_hi Stdlib.Int64.max_int)));

    pin "SEC-15" "AT1-S03: a crossing interval splits Stack/Args, both identity"
      (fun () ->
        check "SEC-15"
          (let ws =
             Ws.of_clp
               (Clp.interval ~width:64 (i2w (pos (-4L))) (i2w (pos 12L)))
           in
           match rd ~width:1 ws with
           | Some Tag.Range (l, h), [ p1; p2 ] ->
               Int64.equal l (pos (-4L)) && Int64.equal h (pos 12L)
               && portion_eq p1 S.Stack (pos (-4L)) (pos 7L)
               && portion_eq p2 S.Args (pos 8L) (pos 12L)
               && (not p1.A.pt_elig) && not p2.A.pt_elig
           | _ -> false));

    pin "SEC-16" "AT1-S03: a bounded single-space symbolic read stays eligible"
      (fun () ->
        check "SEC-16"
          (match rd ~width:8 (stack_off (-8L)) with
           | _, [ p ] -> p.A.pt_elig
           | _ -> false));

    pin "SEC-17" "AT1-S03: a plain band hull contributes identity portions (no StackOff proof)"
      (fun () ->
        check "SEC-17"
          (let ws =
             Ws.of_clp
               (Clp.interval ~width:64 (i2w (pos (-16L))) (i2w (pos (-9L))))
           in
           match rd ~width:8 ws with
           | Some Tag.Range (l, h), [ p ] ->
               Int64.equal l (pos (-16L)) && Int64.equal h (pos (-9L))
               && (not p.A.pt_elig)
               && portion_eq p S.Stack (pos (-16L)) (pos (-2L))
           | _ -> false));

    pin "SEC-18" "AT1-S03: a rip-tagged plain access wholly in one span proves its portion"
      (fun () ->
        check "SEC-18"
          (let ws =
             Ws.of_clp (Clp.interval ~width:64 (i2w 0x4010L) (i2w 0x4017L))
           in
           match rd_spans ~rip:true ~width:8 ws with
           | None, [ p ] ->
               (* The portion's bounds are the occupied extent (the width
                  rides in). *)
               Int64.equal p.A.pt_lo 0x4010L
               && Int64.equal p.A.pt_hi 0x401EL
               && p.A.pt_elig
           | _ -> false));

    pin "SEC-19"
      "AT1-S03: a symbolic occupied range crossing the retaddr boundary is identity"
      (fun () ->
        check "SEC-19"
          (match rd ~width:8 (stack_off 4L) with
           | _, ps ->
               (* [entry+4,entry+11] crosses into Args: identity both
                  sides. *)
               Base.List.for_all ps ~f:(fun p -> not p.A.pt_elig)
               && Base.List.length ps = 2));

    pin "SEC-20" "AT1-S03: the same access without the rip tag contributes identity"
      (fun () ->
        check "SEC-20"
          (let ws =
             Ws.of_clp (Clp.interval ~width:64 (i2w 0x4010L) (i2w 0x4017L))
           in
           match rd_spans ~rip:false ~width:8 ws with
           | None, [ p ] -> not p.A.pt_elig
           | _ -> false));

    pin "SEC-21"
      "AT1-S03: a plain access straddling a span edge contributes its intersecting portion, identity"
      (fun () ->
        check "SEC-21"
          (let ws =
             Ws.of_clp (Clp.interval ~width:64 (i2w 0x403CL) (i2w 0x4043L))
           in
           match rd_spans ~rip:true ~width:8 ws with
           | None, [ p ] ->
               portion_eq p S.Data 0x403CL 0x403FL && not p.A.pt_elig
           | _ -> false));



    (* The collection and the storage rule over real fixtures. *)








    pin "SEC-27" "AT1-TOPW: the TOP write and the known read share Frame storage"
      (fun () ->
        let m, rsp, rbp = mem_rbp () in
        let def_rbp = Def.create rbp (Bil.Var rsp) in
        let u = v64 "at_u" in
        let known = load_at m rbp 8L 64 in
        let top_store =
          Def.create m
            (Bil.Store
               ( Bil.Var m,
                 Bil.Var u,
                 Bil.Int (Cbat_word.to_word (w64 42)),
                 LittleEndian,
                 `r64 ))
        in
        let subw =
          straight_sub "at_topwrite" [ def_rbp; known; top_store ]
        in
        let other = straight_sub "at_other" [ def_rbp; load_at m rbp 8L 64 ] in
        let ctx = tree_ctx [ subw; other ] in
        check "SEC-27"
          (match storage_at ctx subw S.Stack (pos (-8L)) (pos (-1L)) with
           | Some A.Stack_residue -> true
           | _ -> false));

    pin "SEC-28" "AT1-TOPW: the TOP write also claims the Args space (Window)"
      (fun () ->
        let m, rsp, rbp = mem_rbp () in
        let def_rbp = Def.create rbp (Bil.Var rsp) in
        let u = v64 "at_u" in
        let known = load_at m rbp 8L 64 in
        let top_store =
          Def.create m
            (Bil.Store
               ( Bil.Var m,
                 Bil.Var u,
                 Bil.Int (Cbat_word.to_word (w64 42)),
                 LittleEndian,
                 `r64 ))
        in
        let subw =
          straight_sub "at_topwrite" [ def_rbp; known; top_store ]
        in
        let other = straight_sub "at_other" [ def_rbp; load_at m rbp 8L 64 ] in
        let ctx = tree_ctx [ subw; other ] in
        check "SEC-28"
          (match storage_at ctx subw S.Args (pos 8L) Stdlib.Int64.max_int with
           | Some A.Stack_residue -> true
           | _ -> false));

    pin "SEC-29" "AT1-SCOPE: a different sub's tree keeps its own Region"
      (fun () ->
        let m, rsp, rbp = mem_rbp () in
        let def_rbp = Def.create rbp (Bil.Var rsp) in
        let u = v64 "at_u" in
        let known = load_at m rbp 8L 64 in
        let top_store =
          Def.create m
            (Bil.Store
               ( Bil.Var m,
                 Bil.Var u,
                 Bil.Int (Cbat_word.to_word (w64 42)),
                 LittleEndian,
                 `r64 ))
        in
        let subw =
          straight_sub "at_topwrite" [ def_rbp; known; top_store ]
        in
        let other = straight_sub "at_other" [ def_rbp; load_at m rbp 8L 64 ] in
        let ctx = tree_ctx [ subw; other ] in
        check "SEC-29"
          (match storage_at ctx other S.Stack (pos (-8L)) (pos (-1L)) with
           | Some (A.Stack_region 1) -> true
           | _ -> false));



    pin "SEC-31" "AT1-ESC: the escaped extent's component takes Frame storage"
      (fun () ->
        let m, rsp, rbp = mem_rbp () in
        let def_rbp = Def.create rbp (Bil.Var rsp) in
        let esc_data = v64 "at_esc" in
        let def_esc =
          Def.create esc_data
            (Bil.BinOp
               ( Bil.MINUS,
                 Bil.Var rbp,
                 Bil.Int (Cbat_word.to_word (w64 0x30)) ))
        in
        let esc_store =
          Def.create m
            (Bil.Store
               ( Bil.Var m,
                 Bil.BinOp
                   ( Bil.MINUS,
                     Bil.Var rbp,
                     Bil.Int (Cbat_word.to_word (w64 0x20)) ),
                 Bil.Var esc_data,
                 LittleEndian,
                 `r64 ))
        in
        let clean = load_at m rbp 0x20L 64 in
        let sub3 =
          straight_sub "at_escape" [ def_rbp; def_esc; clean; esc_store ]
        in
        let ctx3 = tree_ctx [ sub3 ] in
        check "SEC-31"
          (match storage_at ctx3 sub3 S.Stack (pos (-0x30L)) (pos (-0x29L)) with
           | Some A.Stack_residue -> true
           | _ -> false));

    pin "SEC-32" "AT1-ESC: the escape member survives finalization with no def"
      (fun () ->
        let m, rsp, rbp = mem_rbp () in
        let def_rbp = Def.create rbp (Bil.Var rsp) in
        let esc_data = v64 "at_esc" in
        let def_esc =
          Def.create esc_data
            (Bil.BinOp
               ( Bil.MINUS,
                 Bil.Var rbp,
                 Bil.Int (Cbat_word.to_word (w64 0x30)) ))
        in
        let esc_store =
          Def.create m
            (Bil.Store
               ( Bil.Var m,
                 Bil.BinOp
                   ( Bil.MINUS,
                     Bil.Var rbp,
                     Bil.Int (Cbat_word.to_word (w64 0x20)) ),
                 Bil.Var esc_data,
                 LittleEndian,
                 `r64 ))
        in
        let clean = load_at m rbp 0x20L 64 in
        let sub3 =
          straight_sub "at_escape" [ def_rbp; def_esc; clean; esc_store ]
        in
        let ctx3 = tree_ctx [ sub3 ] in
        check_bound "SEC-32"
          (Core.Map.find ctx3.A.sub_trees (Term.tid sub3))
          (fun tree ->
            A.Tree.to_sequence tree |> Seq.to_list
            |> Base.List.exists ~f:(fun (_, rs) ->
                   Base.List.exists rs.A.members ~f:(fun mm ->
                       Option.is_none mm.A.m_def && mm.A.m_identity))));



    pin "SEC-34" "AT1-RET: the retaddr bytes' component takes Frame storage"
      (fun () ->
        let m, _rsp, _rbp = mem_rbp () in
        let ret_read =
          Def.create (v64 "at_ret")
            (Bil.Load (Bil.Var m, Bil.Var sp, LittleEndian, `r64))
        in
        let sub4 = straight_sub "at_retaddr" [ ret_read ] in
        let ctx4 = tree_ctx [ sub4 ] in
        check "SEC-34"
          (match storage_at ctx4 sub4 S.Stack entry (pos 7L) with
           | Some A.Stack_residue -> true
           | _ -> false));







    pin "SEC-38" "AT1-ARGS: a store demotes its cell to Window"
      (fun () ->
        let m, rsp, rbp = mem_rbp () in
        let def_rbp = Def.create rbp (Bil.Var rsp) in
        let a_full = ld_plus m rbp 8L 64 in
        let a_cell1 = ld_plus m rbp 16L 64 in
        let sub6 =
          straight_sub "at_args_store"
            [ def_rbp; a_full; st_plus m rbp 8L 64; a_cell1 ]
        in
        let ctx6 = tree_ctx [ sub6 ] in
        check "SEC-38"
          (match storage_at ctx6 sub6 S.Args (pos 8L) (pos 15L) with
           | Some A.Stack_residue -> true
           | _ -> false));

    pin "SEC-39" "AT1-ARGS: the neighboring cell keeps its own Arg_slot"
      (fun () ->
        let m, rsp, rbp = mem_rbp () in
        let def_rbp = Def.create rbp (Bil.Var rsp) in
        let a_full = ld_plus m rbp 8L 64 in
        let a_cell1 = ld_plus m rbp 16L 64 in
        let sub6 =
          straight_sub "at_args_store"
            [ def_rbp; a_full; st_plus m rbp 8L 64; a_cell1 ]
        in
        let ctx6 = tree_ctx [ sub6 ] in
        check "SEC-39"
          (match storage_at ctx6 sub6 S.Args (pos 16L) (pos 23L) with
           | Some (A.Arg_slot 1) -> true
           | _ -> false));

    (* Stamping: the tags land on the defs' values (present BEFORE any
       removal test). *)
    pin "SEC-40" "AT1-TAG: the known stack read carries its Stack bounds tag"
      (fun () ->
        let m, rsp, rbp = mem_rbp () in
        let def_rbp = Def.create rbp (Bil.Var rsp) in
        let l16 = load_at m rbp 16L 64 in
        let sub1 =
          straight_sub "at_reads"
            [ def_rbp; l16; load_at m rbp 12L 64; load_at m rbp 8L 64 ]
        in
        let ctx1 = tree_ctx [ sub1 ] in
        check "SEC-40"
          (match tag_of (A.stamp_tags ctx1 sub1) l16 with
           | Some Tag.Range (l, h) ->
               Int64.equal l (pos (-16L)) && Int64.equal h (pos (-16L))
           | _ -> false));

    pin "SEC-41" "AT1-TAG: the intra-cell args read carries its Args bounds tag"
      (fun () ->
        let m, rsp, rbp = mem_rbp () in
        let def_rbp = Def.create rbp (Bil.Var rsp) in
        let a_intra = ld_plus m rbp 12L 32 in
        let sub5 =
          straight_sub "at_args" [ def_rbp; ld_plus m rbp 8L 64; a_intra ]
        in
        let ctx5 = tree_ctx [ sub5 ] in
        check "SEC-41"
          (match tag_of (A.stamp_tags ctx5 sub5) a_intra with
           | Some Tag.Range (l, h) ->
               Int64.equal l (pos 12L) && Int64.equal h (pos 12L)
           | _ -> false));

    pin "SEC-42" "AT1-TAG: the TOP-addressed store carries no tag (unknown provenance)"
      (fun () ->
        let m, rsp, rbp = mem_rbp () in
        let def_rbp = Def.create rbp (Bil.Var rsp) in
        let u = v64 "at_u" in
        let known = load_at m rbp 8L 64 in
        let top_store =
          Def.create m
            (Bil.Store
               ( Bil.Var m,
                 Bil.Var u,
                 Bil.Int (Cbat_word.to_word (w64 42)),
                 LittleEndian,
                 `r64 ))
        in
        let subw =
          straight_sub "at_topwrite" [ def_rbp; known; top_store ]
        in
        let other = straight_sub "at_other" [ def_rbp; load_at m rbp 8L 64 ] in
        let ctx = tree_ctx [ subw; other ] in
        check "SEC-42"
          (match tag_of (A.stamp_tags ctx subw) top_store with
           | None -> true
           | _ -> false));

    (* T3: the data rows of the storage rule. *)


    pin "SEC-44" "AT3-DATA: the rip-proved in-span read's Global component is its word range"
      (fun () ->
        check "SEC-44"
          (match data_comps (data_ctx [ sec_load 0x4008L ]) with
           | [ c ] -> component_is c ~id:0 ~lo_w:1 ~hi_w:1 ~typed_w:8
           | _ -> false));

    pin "SEC-45" "AT3-DATA: the same read without the rip proof converts to nothing"
      (fun () ->
        check "SEC-45"
          (Base.List.is_empty
             (data_comps (data_ctx [ sec_load ~rip:false 0x4008L ]))));

    pin "SEC-46" "AT3-DATA: a sub-word read's component covers the whole word (the word hull)"
      (fun () ->
        check "SEC-46"
          (match data_comps (data_ctx [ sec_load ~width:4 0x4004L ]) with
           | [ c ] -> component_is c ~id:0 ~lo_w:0 ~hi_w:0 ~typed_w:4
           | _ -> false));

    pin "SEC-47"
      "AT3-DATA: same-word reads merge into one component; agreeing widths type the tile"
      (fun () ->
        check "SEC-47"
          (match
             data_comps
               (data_ctx [ sec_load ~width:4 0x4000L; sec_load ~width:4 0x4004L ])
           with
           | [ c ] -> component_is c ~id:0 ~lo_w:0 ~hi_w:0 ~typed_w:4
           | _ -> false));

    pin "SEC-48" "AT3-DATA: disagreeing widths collapse the component's type to bytes"
      (fun () ->
        check "SEC-48"
          (match
             data_comps
               (data_ctx [ sec_load ~width:4 0x4000L; sec_load ~width:2 0x4004L ])
           with
           | [ c ] -> component_is c ~id:0 ~lo_w:0 ~hi_w:0 ~typed_w:1
           | _ -> false));

    pin "SEC-49"
      "AT3-DATA: disjoint words keep separate components; ids ascend by (section, position)"
      (fun () ->
        check "SEC-49"
          (match data_comps (data_ctx [ sec_load 0x4008L; sec_load 0x4000L ]) with
           | [ c0; c1 ] ->
               component_is c0 ~id:0 ~lo_w:0 ~hi_w:0 ~typed_w:8
               && component_is c1 ~id:1 ~lo_w:1 ~hi_w:1 ~typed_w:8
           | _ -> false));

    pin "SEC-50"
      "AT3-DATA: a copy-reloc span is ONE whole-span region; the slot access keeps the through lane"
      (fun () ->
        check "SEC-50"
          (let slot_spans =
             [ { A.ds_sec = S.Data;
                 ds_lo = 0x4000L;
                 ds_hi = 0x403FL;
                 ds_slots = [ 0x4008L ] } ]
           in
           let sub = straight_sub "at_slot" [ sec_load 0x4008L ] in
           let ctx =
             A.attribute ~facts:top_facts ~word:8 ~entry ~spans:slot_spans
               (Program.create ~subs:[ sub ] ())
           in
           Base.List.is_empty (A.global_comps_of ~word:8 ~spans:slot_spans ctx)
           && (match A.whole_comps_of ctx with
               | [ (_id, 0x4000L, 0x403FL) ] -> true
               | _ -> false)
           && (match
                 A.storage_of_range ctx.A.data_tree
                   (A.range S.Data 0x4008L 0x400fL)
               with
               | Some { A.storage = A.Data_region _; _ } -> true
               | _ -> false)));

    (* The full-span claim. *)
    pin "SEC-51" "AT1-TC1: the query-failed claim is the plain full-line claim"
      (fun () ->
        check "SEC-51"
          (plain (A.top_claim ~extents:[] ~cause:A.Query_failed ~entry ~word:8)));

    pin "SEC-52" "AT1-TC2: the foreign claim is the plain full-line claim"
      (fun () ->
        check "SEC-52" (plain (A.top_claim ~extents:[] ~cause:A.Foreign ~entry ~word:8)));

    pin "SEC-53" "AT1-TC3: the unbounded-stack claim clamps below the entry"
      (fun () ->
        check "SEC-53"
          (clamped (A.top_claim ~extents:[] ~cause:A.Unbounded_stack ~entry ~word:8)));



    (* The Sections-owned regression pins. *)
    pin "SEC-55"
      "C1: the narrow r16 store converts to the region mem, keeping its address and width"
      (fun () ->
        let rsp = v64 "RSP" in
        let m = memv "c1_m" in
        let def_wide =
          Def.create m
            (Bil.Store
               ( Bil.Var m,
                 Bil.BinOp
                   ( Bil.MINUS,
                     Bil.Var rsp,
                     Bil.Int (Cbat_word.to_word (w64 16)) ),
                 Bil.Int (Cbat_word.to_word (q64 0x1122334455667788L)),
                 LittleEndian,
                 `r64 ))
        in
        let def_narrow =
          Def.create m
            (Bil.Store
               ( Bil.Var m,
                 Bil.BinOp
                   ( Bil.MINUS,
                     Bil.Var rsp,
                     Bil.Int (Cbat_word.to_word (w64 16)) ),
                 Bil.Int (Cbat_word.to_word (Cbat_word.of_int ~width:16 0xABCD)),
                 LittleEndian,
                 `r16 ))
        in
        let sub, _ =
          sub_of "c1_mask" [ [ def_wide; def_narrow ], [ (1, mk_goto) ]; [], [] ]
        in
        let sub' = rewrite_one sub in
        let narrow' =
          Term.enum blk_t sub'
          |> Seq.concat_map ~f:(Term.enum def_t)
          |> Seq.find ~f:(fun d ->
                 Tid.equal (Term.tid d) (Term.tid def_narrow))
        in
        check "SEC-55"
          (match narrow' with
           | Some d -> (
               match Def.rhs d with
               | Bil.Store (Bil.Var mem, Bil.Var b, _, _, `r16) ->
                   Var.same mem (Sm.region_mem ~addr_bits:64 1)
                   && Sm.region_ptr_id_of b = Some 1
                   && Var.equal (Def.lhs d) mem
               | _ -> false)
           | None -> false));

    pin "SEC-56" "C3: pre-call the caller-frame cell [RSP-8] holds {0xAA} (non-vacuous pin)"
      (fun () ->
        let fx = mk_escape_caller ~pfx:"c3" ~fp_off:8 ~seed:0xAA ~outs:[ (16, C 0xBB) ] () in
        let st = st_pre fx.es_sub fx.es_blk0 fx.es_blk1 in
        check "SEC-56"
          (Ws.equal (read64 fx.es_m st (-8L)) (Ws.singleton (w64 0xAA))));

    pin "SEC-57" "C3: pre-call the outgoing slot [RSP+16] holds {0xBB} (non-vacuous pin)"
      (fun () ->
        let fx = mk_escape_caller ~pfx:"c3" ~fp_off:8 ~seed:0xAA ~outs:[ (16, C 0xBB) ] () in
        let st = st_pre fx.es_sub fx.es_blk0 fx.es_blk1 in
        check "SEC-57"
          (Ws.equal (read64 fx.es_m st (-16L)) (Ws.singleton (w64 0xBB))));

    pin "SEC-58"
      "C3: the caller-frame cell [RSP-8] survives the call with its value (frame not whole-memory-topped)"
      (fun () ->
        let fx = mk_escape_caller ~pfx:"c3" ~fp_off:8 ~seed:0xAA ~outs:[ (16, C 0xBB) ] () in
        let sol = run_anchored fx.es_sub in
        let post_ai = Graphlib.Std.Solution.get sol fx.es_post_tid in
        check "SEC-58"
          (Ws.equal (read64 fx.es_m post_ai (-8L)) (Ws.singleton (w64 0xAA))));



    pin "SEC-60" "C4b: the widened member's component takes Frame storage, never Region"
      (fun () ->
        let sub_mixed, def_idx_store = mk_indexed_loop ~pfx:"c4b" in
        let ctx_mixed = fixture_ctx [ sub_mixed ] in
        check_bound "SEC-60"
          (storage_of_def ctx_mixed sub_mixed (Term.tid def_idx_store))
          (fun rs -> rs.A.storage = A.Stack_residue));

    pin "SEC-61"
      "C4b: the constant cell joins the widened member's Frame component (together, not Region)"
      (fun () ->
        let sub_mixed, _def_idx_store = mk_indexed_loop ~pfx:"c4b" in
        let ctx_mixed = fixture_ctx [ sub_mixed ] in
        check "SEC-61"
          (match Core.Map.find ctx_mixed.A.sub_trees (Term.tid sub_mixed) with
           | Some tree -> (
               match
                 A.storage_of_range tree (A.range Sm.Stack (pos (-16L)) (pos (-9L)))
               with
               | Some rs -> rs.A.storage = A.Stack_residue
               | None -> false)
           | None -> false));







    pin "SEC-65"
      "R12: a Region binding of occupied span 8 bytes allocates 16 (aligned once, no width factor)"
      (fun () ->
        let m = memv "r12_m" in
        let rsp = v64 "RSP" in
        let rbp = v64 "RBP" in
        let d_rbp = Def.create rbp (Bil.Var rsp) in
        let d =
          Def.create (v64 "r12_t")
            (Bil.Load
               ( Bil.Var m,
                 Bil.BinOp
                   ( Bil.MINUS,
                     Bil.Var rbp,
                     Bil.Int (Cbat_word.to_word (w64 8)) ),
                 LittleEndian,
                 `r64 ))
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
        check "SEC-65"
        (l.Sm.regions
        = [ { Sm.r_id = 1;
              r_lo = pos (-8L);
              r_hi = pos (-1L);
              r_bytes = 16L } ]));

    pin "SEC-71"
      "B2a: the residue's window reserve is the def-backed members' proven reach — the call escape does not size it"
      (fun () ->
        let m = memv "b2a_m" in
        let rsp = v64 "RSP" in
        let callee = mk_selfloop_callee "b2a_callee" in
        let callee_tid = Term.tid callee in
        let def_out =
          Def.create m
            (Bil.Store
               ( Bil.Var m,
                 Bil.BinOp
                   ( Bil.PLUS,
                     Bil.Var rsp,
                     Bil.Int (Cbat_word.to_word (w64 0x10)) ),
                 Bil.Int (Cbat_word.to_word (w64 0xBB)),
                 LittleEndian,
                 `r64 ))
        in
        let sub, _ =
          sub_of "b2a_caller"
            [ [ def_out ], [ (1, fun t -> mk_call_jmp t callee_tid) ]; [], [] ]
        in
        let ctx = fixture_ctx [ sub ] in
        let tree =
          Base.Option.value_exn (Core.Map.find ctx.A.sub_trees (Term.tid sub))
        in
        let l =
          A.layout_of_tree ~word:8 ~entry:Hike.Stack_model.segment_base
            ~abi:Hike.Abi.x86_64_sysv ~sub tree
        in
        check "SEC-71"
          (match
             Base.List.find l.Sm.regions ~f:(fun { Sm.r_id = id; _ } -> Int.equal id 0)
           with
           | Some { Sm.r_hi = rhi; _ } ->
             let window =
               Stdlib.Int64.add
                 (Stdlib.Int64.sub rhi Hike.Stack_model.segment_base)
                 1L
             in
             (* The outgoing store at RSP+0x10 is the only def-backed
                Args member: the reserve is its 24-byte reach, never the
                64 KiB the call escape alone would claim. *)
             Stdlib.Int64.equal window 24L
           | None -> false));

    pin "SEC-66"
      "S2 (fp-GPR): an untagged heap-RBP store does NOT degrade the sub (the rsp cell keeps Region storage — stack-ness is the value proof alone)"
      (fun () ->
        let sub = heap_store_sub "s2_heap_rbp" "s2_m" (v64 "RBP") in
        let ctx = fixture_ctx [ sub ] in
        check "SEC-66"
          (storage_at ctx sub Sm.Stack (pos (-16L)) (pos (-9L))
          = Some (A.Stack_region 1)));





    pin "SEC-69"
      "AT4-VLA: the extent claims bind nowhere — the static frame carves beside a live VLA"
      (fun () ->
        let m, rsp, rbp = mem_rbp () in
        let rax = v64 "at_vla_rax" in
        let at_vla_n = v64 "at_vla_n" in
        let def_rbp = Def.create rbp (Bil.Var rsp) in
        (* The literal frame decrement: the static slots [rbp-12, rbp-1]
           sit at/above the cut, the VLA strictly below it. *)
        let def_frame =
          Def.create rsp
            (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 16))))
        in
        let def_n_cell =
          Def.create m
            (Bil.Store
               ( Bil.Var m,
                 Bil.BinOp
                   (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 12))),
                 Bil.Var at_vla_n,
                 LittleEndian,
                 `r64 ))
        in
        let def_load =
          Def.create rax
            (Bil.Load
               ( Bil.Var m,
                 Bil.BinOp
                   (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 12))),
                 LittleEndian,
                 `r64 ))
        in
        let def_sub =
          Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Var rax))
        in
        let def_ptr = Def.create rax (Bil.Var rsp) in
        let def_align =
          Def.create rax
            (Bil.BinOp
               (Bil.AND, Bil.Var rax,
                Bil.Int (Cbat_word.to_word (Cbat_word.of_int64 ~width:64 (-4L)))))
        in
        let def_save =
          Def.create m
            (Bil.Store
               ( Bil.Var m,
                 Bil.BinOp
                   (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))),
                 Bil.Var rax,
                 LittleEndian,
                 `r64 ))
        in
        let def_band =
          Def.create m
            (Bil.Store
               ( Bil.Var m,
                 Bil.BinOp
                   (Bil.PLUS, Bil.Var rax, Bil.Int (Cbat_word.to_word (w64 12))),
                 Bil.Int (Cbat_word.to_word (Cbat_word.of_int ~width:32 1)),
                 LittleEndian,
                 `r32 ))
        in
        let sub =
          straight_sub "vla_frame"
            [ def_rbp; def_frame; def_n_cell; def_load; def_sub; def_ptr;
              def_align; def_save; def_band ]
        in
        let ctx = fixture_ctx [ sub ] in
        let projection d =
          match Core.Map.find ctx.A.projections (Term.tid d) with
          | Some (Some p) -> Some p
          | _ -> None
        in
        check "SEC-69"
          ((match projection def_band with
            | Some p ->
                (* The frame fact rides the projection's origin, named by
                   the decrement def's own tid; a VLA claim binds nowhere
                   in the tree. *)
                Option.equal Hike_origin.equal p.A.origin
                  (Some (Hike_origin.Vla (Term.tid def_sub)))
                && p.A.portions = []
            | None -> false)
           && (match storage_at ctx sub Sm.Stack (pos (-8L)) (pos (-1L)) with
               | Some (A.Stack_region _) -> true
               | _ -> false)
           && (match storage_at ctx sub Sm.Stack (pos (-12L)) (pos (-9L)) with
               | Some (A.Stack_region _) -> true
               | _ -> false)));

    pin "SEC-70"
      "AT4-VLA: a frame claim is not cut around the extent — it binds on its own line"
      (fun () ->
        let m, rsp, rbp = mem_rbp () in
        let rax = v64 "at_vla_rax" in
        let at_vla_n = v64 "at_vla_n" in
        let def_rbp = Def.create rbp (Bil.Var rsp) in
        let def_frame =
          Def.create rsp
            (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 16))))
        in
        let def_n_cell =
          Def.create m
            (Bil.Store
               ( Bil.Var m,
                 Bil.BinOp
                   (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 12))),
                 Bil.Var at_vla_n,
                 LittleEndian,
                 `r64 ))
        in
        let def_load =
          Def.create rax
            (Bil.Load
               ( Bil.Var m,
                 Bil.BinOp
                   (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 12))),
                 LittleEndian,
                 `r64 ))
        in
        let def_sub =
          Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Var rax))
        in
        (* A frame-pointer store whose occupied window once straddled the
           extent's top: with the cut deleted it binds on the stack line
           as one portion. *)
        let def_straddle =
          Def.create m
            (Bil.Store
               ( Bil.Var m,
                 Bil.BinOp
                   (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 20))),
                 Bil.Int (Cbat_word.to_word (w64 7)),
                 LittleEndian,
                 `r64 ))
        in
        let sub =
          straight_sub "vla_cut"
            [ def_rbp; def_frame; def_n_cell; def_load; def_sub; def_straddle ]
        in
        let ctx = fixture_ctx [ sub ] in
        check "SEC-70"
          (match
             Core.Map.find ctx.A.projections (Term.tid def_straddle)
           with
           | Some (Some p) ->
               Base.List.exists p.A.portions ~f:(fun q ->
                   portion_eq q S.Stack (pos (-20L)) (pos (-13L)))
               && Base.List.length p.A.portions = 1
           | _ -> false));
]

let () = run "sections" tests
