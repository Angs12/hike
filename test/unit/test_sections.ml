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

let resolved_addr resolved =
  if resolved then
    let synth, v = Hike_synth.mint_module_addr ~addr_bits:64 0x4000L Hike_synth.empty in
    synth, Bil.Var v
  else Hike_synth.empty, Bil.Int (Word.zero 64)

let rd ?(resolved = false) ?(width = 8) (ws : Ws.t) =
  let synth, address = resolved_addr resolved in
  A.range_of_denotation ~word:8 ~entry ~spans:[] ~synth
    ~address ~width ws

let spans_of () =
  [ { A.ds_sec = S.Data; ds_lo = 0x4000L; ds_hi = 0x403FL; ds_slots = [] };
    { A.ds_sec = S.Rodata; ds_lo = 0x5000L; ds_hi = 0x501FL; ds_slots = [] } ]

let rd_spans ?(resolved = false) ?(width = 8) (ws : Ws.t) =
  let synth, address = resolved_addr resolved in
  A.range_of_denotation ~word:8 ~entry ~spans:(spans_of ()) ~synth
    ~address ~width ws

(* Fixture stack frame: the mem, the SP and the frame pointer. *)
let mem_rbp () = (memv "at_m", sp, frame_ptr)

(* The fixture's one installed context: the solve, the one install, and
   the stamped subs the seam reads. *)
let tree_ctx (subs : sub term list) : A.ctx =
  fixture_ctx ~synth:Hike.Synth.empty ~spans:(spans_of ()) subs

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
   resolved proof, the word hull, the typed-width agreement, and the
   Whole_span identity. *)
let sec_load ?(resolved = true) ?(width = 8) (addr : int64) =
  let d =
    Def.create (v64 "at_g")
      (Bil.Load
         ( Bil.Var (memv "at_gm"),
           Bil.Int (Word.of_int64 ~width:64 addr),
           LittleEndian,
           Size.of_int_exn (8 * width) ))
  in
  if resolved then
    let synth, v = Hike_synth.mint_module_addr ~addr_bits:64 addr Hike_synth.empty in
    synth, Def.map_exp d ~f:(Exp.substitute
      (Bil.Int (Word.of_int64 ~width:64 addr)) (Bil.Var v))
  else Hike_synth.empty, d

let data_ctx defs : A.ctx =
  let synth = Base.List.fold defs ~init:Hike_synth.empty
      ~f:(fun synth (table, _) -> Hike_synth.union synth table) in
  fixture_ctx ~synth ~spans:(spans_of ())
    [ straight_sub "at_global" (Base.List.map defs ~f:snd) ]

let data_comps (ctx : A.ctx) : Hike.Stack_model.sec_comp list =
  A.global_comps_of ~word:8 ~spans:(spans_of ()) ctx

let component_is (c : Hike.Stack_model.sec_comp) ~(id : int) ~(lo_w : int)
    ~(hi_w : int) ~(typed_w : int) =
  c.Hike.Stack_model.comp_id = id
  && c.Hike.Stack_model.lo_w = lo_w
  && c.Hike.Stack_model.hi_w = hi_w
  && c.Hike.Stack_model.typed_w = typed_w

(* The pre-call state of a two-block escape fixture: the call block's
   end state — the block's phis applied, its defs folded — from the
   anchored run. *)
let st_pre (sub : sub term) (call_blk : blk term) : AI.t =
  let sol = run_anchored sub in
  let _, after =
    Vsa.fold_block_states ~synth:Hike.Synth.empty ~sol call_blk ~init:()
      ~f:(fun _ _ _ () -> ())
  in
  after

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

(* The full-span claim shapes: the tops claim the sub-local line only. *)
let plain (t, ps) =
  match t, ps with
  | None, [ p1; p2 ] ->
      portion_eq p1 S.Stack (Int64.add entry Stdlib.Int64.min_int) (pos 7L)
      && portion_eq p2 S.Args (pos 8L) Stdlib.Int64.max_int
  | _ -> false

let to_floor (t, ps) =
  match t, ps with
  | Some Tag.Unbounded, [ p1 ] ->
      portion_eq p1 S.Stack (Int64.add entry Stdlib.Int64.min_int) (pos (-1L))
  | _ -> false

(* S2's shape: a heap-pointing GPR store beside the [RSP-16] cell
   write; the base register is the control (RBP vs RBX). *)
let heap_store_sub name m_name (base : var) : sub term =
  let rsp = sp in
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

(* Storage selection: the residue's below-entry extent is its proven
   depth when it fits an alloca, and the runtime stack otherwise. The
   variable store reaches the return cell, so it lives in the residue. *)
let residue_layout name (mask : int64) =
  let m = memv (name ^ "_m") in
  let rsp = sp in
  let u = v64 (name ^ "_u") and n = v64 (name ^ "_n") in
  let def_n =
    Def.create n
      (Bil.BinOp
         (Bil.AND, Bil.Var u, Bil.Int (Cbat_word.to_word (i2w mask))))
  in
  let def_st =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp
             ( Bil.MINUS,
               Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Var n),
               Bil.Int (Cbat_word.to_word (w64 4)) ),
           Bil.Int (Cbat_word.to_word (w64 7)),
           LittleEndian,
           `r64 ))
  in
  let sub = straight_sub name [ def_n; def_st ] in
  let ctx = fixture_ctx ~synth:Hike.Synth.empty [ sub ] in
  let tree =
    Base.Option.value_exn (Core.Map.find ctx.A.sub_trees (Term.tid sub))
  in
  A.layout_of_tree ~word:8 ~entry:Hike.Stack_model.segment_base
    ~abi:Hike.Abi.x86_64_sysv ~sub tree

let residue_depth (l : Sm.sub_layout) =
  Base.List.find_map l.Sm.regions ~f:(fun { Sm.r_id = id; r_lo; _ } ->
      if Int.equal id 0 then Some (Int64.sub Hike.Stack_model.segment_base r_lo)
      else None)

let tests : unit Alcotest.test list =
  [
    (* S01/S02/S03: the normalization and projection table. *)












    pin "SEC-07"
      "AT1-S02: bottom claims like a failed query - no tag, full-range portions"
      (fun () ->
        check "SEC-07"
          (match rd (Ws.of_clp (Clp.bottom 64)) with
           | None, ps -> not (Base.List.is_empty ps)
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
      "AT1-S02: a symbolic TOP claims [floor, entry)"
      (fun () ->
        check "SEC-09"
          (match rd (Ws.stack_word (Clp.top 64)) with
           | Some Tag.Unbounded, [ p1 ] ->
               portion_eq p1 S.Stack
                 (Int64.add entry Stdlib.Int64.min_int) (pos (-1L))
           | _ -> false));

    pin "SEC-10"
      "AT1-S02: a plain TOP claims no data span (imprecision never poisons the spans)"
      (fun () ->
        check "SEC-10"
          (let _, ps = rd_spans (Ws.top 64) in
           Base.List.for_all ps ~f:(fun p ->
               match p.A.pt_sec with S.Stack | S.Args -> true | _ -> false)));





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
           let synth, address = Hike_synth.mint_module_addr ~addr_bits:64 (-8L) Hike_synth.empty in
           match
             A.range_of_denotation ~word:8 ~entry ~spans:top_span
               ~synth ~address:(Bil.Var address) ~width:8 ws
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
             Ws.stack_word (Clp.interval ~width:64 (i2w 4L) (i2w 12L))
           in
           match rd ~width:1 ws with
           | Some Tag.Range (l, h), [ p1; p2 ] ->
               Int64.equal l (pos 4L) && Int64.equal h (pos 12L)
               && portion_eq p1 S.Stack (pos 4L) (pos 7L)
               && portion_eq p2 S.Args (pos 8L) (pos 12L)
               && (not p1.A.pt_elig) && not p2.A.pt_elig
           | _ -> false));

    pin "SEC-16" "AT1-S03: a bounded single-space symbolic read stays eligible"
      (fun () ->
        check "SEC-16"
          (match rd ~width:8 (stack_off (-8L)) with
           | _, [ p ] -> p.A.pt_elig
           | _ -> false));

    pin "SEC-17" "a plain numeric stack-band hull has no stack attribution"
      (fun () ->
        check "SEC-17"
          (let ws =
             Ws.of_clp
               (Clp.interval ~width:64 (i2w (pos (-16L))) (i2w (pos (-9L))))
           in
           match rd ~width:8 ws with
           | None, [] -> true
           | _ -> false));

    pin "SEC-18" "AT1-S03: a resolved-tagged plain access wholly in one span proves its portion"
      (fun () ->
        check "SEC-18"
          (let ws =
             Ws.of_clp (Clp.interval ~width:64 (i2w 0x4010L) (i2w 0x4017L))
           in
           match rd_spans ~resolved:true ~width:8 ws with
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

    pin "SEC-20" "AT1-S03: the same access without the resolved tag contributes identity"
      (fun () ->
        check "SEC-20"
          (let ws =
             Ws.of_clp (Clp.interval ~width:64 (i2w 0x4010L) (i2w 0x4017L))
           in
           match rd_spans ~resolved:false ~width:8 ws with
           | None, [ p ] -> not p.A.pt_elig
           | _ -> false));

    pin "SEC-21"
      "AT1-S03: a plain access straddling a span edge contributes its intersecting portion, identity"
      (fun () ->
        check "SEC-21"
          (let ws =
             Ws.of_clp (Clp.interval ~width:64 (i2w 0x403CL) (i2w 0x4043L))
           in
           match rd_spans ~resolved:true ~width:8 ws with
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







    pin "SEC-38" "AT1-ARGS: a stored cell is a slot too (the pointer convention)"
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
           | Some A.Arg_slot -> true
           | _ -> false));

    pin "SEC-39" "AT1-ARGS: the neighboring cell is its own slot"
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
           | Some A.Arg_slot -> true
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


    pin "SEC-44" "AT3-DATA: the resolved-proved in-span read's Global component is its word range"
      (fun () ->
        check "SEC-44"
          (match data_comps (data_ctx [ sec_load 0x4008L ]) with
           | [ c ] -> component_is c ~id:0 ~lo_w:1 ~hi_w:1 ~typed_w:8
           | _ -> false));

    pin "SEC-45" "AT3-DATA: the same read without the resolved proof converts to nothing"
      (fun () ->
        check "SEC-45"
          (Base.List.is_empty
             (data_comps (data_ctx [ sec_load ~resolved:false 0x4008L ]))));

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
           let synth, def = sec_load 0x4008L in
           let sub = straight_sub "at_slot" [ def ] in
           let facts = top_facts () in
           let facts = Hike.Kb.with_synth facts (Hike.Synth.union facts.synth synth) in
           let ctx =
             A.attribute ~facts ~word:8 ~entry ~spans:slot_spans
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
          (plain (A.top_claim ~cause:A.Query_failed ~entry ~word:8)));

    pin "SEC-52" "AT1-TC2: the foreign claim is the plain full-line claim"
      (fun () ->
        check "SEC-52" (plain (A.top_claim ~cause:A.Foreign ~entry ~word:8)));

    pin "SEC-53" "AT1-TC3: the unbounded-stack claim reaches the floor below the entry"
      (fun () ->
        check "SEC-53"
          (to_floor (A.top_claim ~cause:A.Unbounded_stack ~entry ~word:8)));



    (* The Sections-owned regression pins. *)
    pin "SEC-55"
      "C1: the narrow r16 store converts to the region mem, keeping its address and width"
      (fun () ->
        let rsp = sp in
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
        let synth, sub' = rewrite_one_synth ~synth:Hike.Synth.empty sub in
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
                   && Sm.region_ptr_id_of synth b = Some 1
                   && Var.equal (Def.lhs d) mem
               | _ -> false)
           | None -> false));

    pin "SEC-56" "C3: pre-call the caller-frame cell [RSP-8] holds {0xAA} (non-vacuous pin)"
      (fun () ->
        let fx = mk_escape_caller ~pfx:"c3" ~fp_off:8 ~seed:0xAA ~outs:[ (16, C 0xBB) ] () in
        let st = st_pre fx.es_sub fx.es_blk1 in
        check "SEC-56"
          (Ws.equal (read64 fx.es_m st (-8L)) (Ws.singleton (w64 0xAA))));

    pin "SEC-57" "C3: pre-call the outgoing slot [RSP+16] holds {0xBB} (non-vacuous pin)"
      (fun () ->
        let fx = mk_escape_caller ~pfx:"c3" ~fp_off:8 ~seed:0xAA ~outs:[ (16, C 0xBB) ] () in
        let st = st_pre fx.es_sub fx.es_blk1 in
        check "SEC-57"
          (Ws.equal (read64 fx.es_m st (-16L)) (Ws.singleton (w64 0xBB))));

    pin "SEC-58"
      "C3: the stack address read in RDI clears the whole retained caller frame"
      (fun () ->
        let fx = mk_escape_caller ~pfx:"c3" ~fp_off:8 ~seed:0xAA ~outs:[ (16, C 0xBB) ] () in
        let sol = run_anchored fx.es_sub in
        let post_ai = Graphlib.Std.Solution.get sol fx.es_post_tid in
        check "SEC-58"
          (Ws.is_top (read64 fx.es_m post_ai (-8L))
          && Ws.is_top (read64 fx.es_m post_ai (-16L))));



    pin "SEC-60" "C4b: the widened member's component takes Frame storage, never Region"
      (fun () ->
        let sub_mixed, def_idx_store = mk_indexed_loop ~pfx:"c4b" in
        let ctx_mixed = fixture_ctx ~synth:Hike.Synth.empty [ sub_mixed ] in
        check_bound "SEC-60"
          (storage_of_def ctx_mixed sub_mixed (Term.tid def_idx_store))
          (fun rs -> rs.A.storage = A.Stack_residue));

    pin "SEC-61"
      "C4b: the constant cell joins the widened member's Frame component (together, not Region)"
      (fun () ->
        let sub_mixed, _def_idx_store = mk_indexed_loop ~pfx:"c4b" in
        let ctx_mixed = fixture_ctx ~synth:Hike.Synth.empty [ sub_mixed ] in
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
        let rsp = sp in
        let rbp = frame_ptr in
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
        let ctx = fixture_ctx ~synth:Hike.Synth.empty [ sub ] in
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
        let rsp = sp in
        let callee = mk_selfloop_callee "b2a_callee" in
        let callee_tid = Term.tid callee in
        let def_out =
          Def.create m
            (Bil.Store
               ( Bil.Var m,
                 Bil.BinOp
                   ( Bil.PLUS,
                     Bil.Var rsp,
                     Bil.Int (Cbat_word.to_word (w64 0xC)) ),
                 Bil.Int (Cbat_word.to_word (w64 0xBB)),
                 LittleEndian,
                 `r64 ))
        in
        let sub, _ =
          sub_of "b2a_caller"
            [ [ def_out ], [ (1, fun t -> mk_call_jmp t callee_tid) ]; [], [] ]
        in
        let ctx = fixture_ctx ~synth:Hike.Synth.empty [ sub ] in
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
             (* The unaligned store at RSP+0xC is the only def-backed Args
                member and crosses two word cells, so it is not a slot:
                the reserve is its 20-byte reach, never the 64 KiB the
                call escape alone would claim. *)
             Stdlib.Int64.equal window 20L
           | None -> false));

    pin "SEC-76" "two outgoing stack stores define the exact call-window hull" (fun () ->
        let m = memv "w_exact_m" in
        let store off value =
          Def.create m
            (Bil.Store
               (Bil.Var m,
                Bil.BinOp
                  (Bil.PLUS, Bil.Var sp,
                   Bil.Int (Cbat_word.to_word (w64 off))),
                Bil.Int (Cbat_word.to_word (w64 value)),
                LittleEndian, `r64))
        in
        let callee = mk_selfloop_callee "w_exact_callee" in
        let sub, _ =
          sub_of "w_exact_caller"
            [ [ store 8 11; store 16 22 ],
              [ (1, fun t -> mk_call_jmp t (Term.tid callee)) ];
              [], [ (0, mk_ret) ] ]
        in
        let ctx = fixture_ctx ~synth:Hike.Synth.empty [ sub ] in
        let tree = Base.Option.value_exn (Core.Map.find ctx.A.sub_trees (Term.tid sub)) in
        let identity =
          A.Tree.to_sequence tree |> Seq.to_list
          |> Base.List.concat_map ~f:(fun (_, rs) -> rs.A.members)
          |> Base.List.filter ~f:(fun m ->
                 m.A.m_identity && Option.is_none m.A.m_def
                 && A.equal_sec m.A.m_sec Sm.Args)
        in
        check "SEC-76"
          (match identity with
           | [ m ] ->
             Int64.equal m.A.m_lo (pos 8L)
             && Int64.equal m.A.m_hi (pos 23L)
           | _ -> false));

    pin "SEC-77" "two locals and a call without stack arguments keep separate regions" (fun () ->
        let m = memv "w_locals_m" in
        let store off value =
          Def.create m
            (Bil.Store
               (Bil.Var m,
                Bil.BinOp
                  (Bil.MINUS, Bil.Var sp,
                   Bil.Int (Cbat_word.to_word (w64 off))),
                Bil.Int (Cbat_word.to_word (w64 value)),
                LittleEndian, `r64))
        in
        let callee = mk_selfloop_callee "w_locals_callee" in
        let sub, _ =
          sub_of "w_locals_caller"
            [ [ store 8 11; store 16 22 ],
              [ (1, fun t -> mk_call_jmp t (Term.tid callee)) ];
              [], [ (0, mk_ret) ] ]
        in
        let ctx = fixture_ctx ~synth:Hike.Synth.empty [ sub ] in
        let tree = Base.Option.value_exn (Core.Map.find ctx.A.sub_trees (Term.tid sub)) in
        let layout =
          A.layout_of_tree ~word:8 ~entry ~abi:Hike.Abi.x86_64_sysv ~sub tree
        in
        check "SEC-77"
          (List.length layout.Sm.regions = 2 && not layout.Sm.window_param));

    pin "SEC-78"
      "a stack pointer passed in a lane keeps the caller frame in shared storage"
      (fun () ->
        let m = memv "w_escape_m" in
        let rdi = int_param 0 in
        let store off value =
          Def.create m
            (Bil.Store
               (Bil.Var m,
                Bil.BinOp
                  (Bil.MINUS, Bil.Var sp,
                   Bil.Int (Cbat_word.to_word (w64 off))),
                Bil.Int (Cbat_word.to_word (w64 value)),
                LittleEndian, `r64))
        in
        let set_rdi =
          Def.create rdi
            (Bil.BinOp
               (Bil.MINUS, Bil.Var sp,
                Bil.Int (Cbat_word.to_word (w64 24))))
        in
        let callee = mk_selfloop_callee "w_escape_callee" in
        let sub, _ =
          sub_of "w_escape_caller"
            [ [ store 24 11; store 16 22; set_rdi ],
              [ (1, fun t -> mk_call_jmp t (Term.tid callee)) ];
              [], [ (0, mk_ret) ] ]
        in
        let ctx = fixture_ctx ~synth:Hike.Synth.empty [ sub ] in
        check "SEC-78"
          (storage_at ctx sub Sm.Stack (pos (-24L)) (pos (-17L))
           = Some A.Stack_residue
          && storage_at ctx sub Sm.Stack (pos (-16L)) (pos (-9L))
             = Some A.Stack_residue));

    pin "SEC-66"
      "S2 (fp-GPR): an untagged heap-RBP store does NOT degrade the sub (the rsp cell keeps Region storage — stack-ness is the value proof alone)"
      (fun () ->
        let sub = heap_store_sub "s2_heap_rbp" "s2_m" frame_ptr in
        let ctx = fixture_ctx ~synth:Hike.Synth.empty [ sub ] in
        check "SEC-66"
          (storage_at ctx sub Sm.Stack (pos (-16L)) (pos (-9L))
          = Some (A.Stack_region 1)));





    pin "SEC-69"
      "a runtime-sized allocation is ordinary stack arithmetic: its stores claim the stack down to the floor, so the sub selects the runtime stack and the frame cells share the residue"
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
        let ctx = fixture_ctx ~synth:Hike.Synth.empty [ sub ] in
        let projection d =
          match Core.Map.find ctx.A.projections (Term.tid d) with
          | Some (Some p) -> Some p
          | _ -> None
        in
        let tree =
          Base.Option.value_exn (Core.Map.find ctx.A.sub_trees (Term.tid sub))
        in
        let layout =
          A.layout_of_tree ~word:8 ~entry ~abi:Hike.Abi.x86_64_sysv ~sub tree
        in
        ignore def_sub;
        check "SEC-69"
          ((match projection def_band with
            | Some p ->
                Option.equal Hike_origin.equal p.A.origin (Some Hike_origin.Stack)
                && (match p.A.portions with
                    | [ q ] ->
                        Int64.equal q.A.pt_lo (Int64.add entry Stdlib.Int64.min_int)
                    | _ -> false)
            | None -> false)
           && layout.Sm.runtime_residue
           && (match storage_at ctx sub Sm.Stack (pos (-8L)) (pos (-1L)) with
               | Some A.Stack_residue -> true
               | _ -> false)));

    pin "SEC-70"
      "a frame store beside a runtime-sized allocation keeps its one exact portion"
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
        let ctx = fixture_ctx ~synth:Hike.Synth.empty [ sub ] in
        check "SEC-70"
          (match
             Core.Map.find ctx.A.projections (Term.tid def_straddle)
           with
           | Some (Some p) ->
               Base.List.exists p.A.portions ~f:(fun q ->
                   portion_eq q S.Stack (pos (-20L)) (pos (-13L)))
               && Base.List.length p.A.portions = 1
           | _ -> false));
    pin "SEC-72"
      "storage selection: a proven depth above 64 KiB sizes the residue exactly, with no runtime stack"
      (fun () ->
        let l = residue_layout "sel_deep" 0x3FFFFL in
        check "SEC-72"
          ((not l.Sm.runtime_residue)
           && (match residue_depth l with
               | Some d -> Int64.compare d 0x40003L >= 0
                           && Int64.compare d 0x40043L < 0
               | None -> false)));

    pin "SEC-73"
      "storage selection: a depth beyond the alloca limit selects the runtime stack"
      (fun () ->
        check "SEC-73"
          (residue_layout "sel_huge" 0xFFFFFFFL).Sm.runtime_residue);

    pin "SEC-74"
      "storage selection: an unbounded stack extent selects the runtime stack"
      (fun () ->
        let m = memv "sel_top_m" in
        let rsp = sp and u = v64 "sel_top_u" in
        let def_st =
          Def.create m
            (Bil.Store
               ( Bil.Var m,
                 Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Var u),
                 Bil.Int (Cbat_word.to_word (w64 7)),
                 LittleEndian,
                 `r64 ))
        in
        let sub = straight_sub "sel_top" [ def_st ] in
        let ctx = fixture_ctx ~synth:Hike.Synth.empty [ sub ] in
        let tree =
          Base.Option.value_exn (Core.Map.find ctx.A.sub_trees (Term.tid sub))
        in
        let l =
          A.layout_of_tree ~word:8 ~entry:Hike.Stack_model.segment_base
            ~abi:Hike.Abi.x86_64_sysv ~sub tree
        in
        check "SEC-74" l.Sm.runtime_residue);

    pin "SEC-75"
      "storage selection: a bounded frame keeps allocas"
      (fun () ->
        check "SEC-75" (not (residue_layout "sel_small" 0xFFL).Sm.runtime_residue));
]

let () = run "sections" tests
