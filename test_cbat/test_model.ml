(* The model/producer surface pins: the coverage-lane gaps closed.

   - [run_producer_record]: [Hike.Vsa.offsets_of_sub] end-to-end — the
     promotion-fact derivation ([callee_side]/[caller_side]), the VLA
     detection, and the degraded arm, through the REAL fixpoint (the
     entry seeds RSP at the symbolic segment base, the production
     universe).  Previously only the probes touched this surface and
     the unit suite pinned [promote_sub]/[resolve_target] with
     hand-built records.
   - Later lanes (layout/frame geometry, stack-to-locals fission,
     emitter VLA/SP-Slot shapes, Abi/Kb domains) follow. *)

open Test_common
open Test_fixtures
open Bap.Std
open Bap_core_theory

module Sm = Hike.Stack_model
module Hv = Hike.Vsa
(* The consumer-side one-line alias (the src convention). *)
module Abi = Hike.Abi

(* A register list names exactly [names]. *)
let names_are (vs : var list) (names : string list) : bool =
  Base.List.map vs ~f:(fun v -> Var.name v) = names

(* 64-bit literal word (native-int [w64] covers 63 bits only). *)
let q64 (v : int64) : Cbat_word.t = Cbat_word.of_int64 ~width:64 v

(* [sp + off] — the caller-window address shape (entry RSP = segment
   base + 0, so the BIL offset IS the SysV slot space). *)
let plus_addr sp (off : int64) : exp =
  Bil.BinOp (Bil.PLUS, Bil.Var sp, Bil.Int (Cbat_word.to_word (w64 (Int64.to_int off))))

let minus_addr sp (off : int64) : exp =
  Bil.BinOp (Bil.MINUS, Bil.Var sp, Bil.Int (Cbat_word.to_word (w64 (Int64.to_int off))))

(* A one-entry sub over the defs, exiting through a real terminal
   block (CFG-honest: the Goto target is built first). *)
let straight_sub (name : string) (defs : def term list) : sub term =
  let exit_blk = mk_exit_blk () in
  let bb = blk_of_defs defs in
  let body = with_jmps bb [ mk_goto (Term.tid exit_blk) ] in
  let sb = Sub.Builder.create ~name () in
  Sub.Builder.add_blk sb body;
  Sub.Builder.add_blk sb exit_blk;
  Sub.Builder.result sb

let tid_set (tids : tid list) : Tid.Set.t =
  List.fold_left (fun s t -> Core.Set.add s t) Tid.Set.empty tids

(* ------------------------------------------------------------------ *)
(* Lane A: the producer record ([offsets_of_sub] end-to-end).          *)
(* ------------------------------------------------------------------ *)

let run_producer_record () =
  let m = memv "pr_m" in

  (* A1: the proven incoming-slot read promotes (the SysV slot 0 at
     [entry RSP + 8]). *)
  let a1_t = v64 "pr_a1_t" in
  let a1_ld = Def.create a1_t (Bil.Load (Bil.Var m, plus_addr sp 8L, LittleEndian, `r64)) in
  let a1 = straight_sub "pr_a1_callee" [ a1_ld ] in
  let a1_info =
    Hv.offsets_of_sub Theory.Target.unknown sp ~symtab:None
      ~prog:(Program.create ~subs:[ a1 ] ()) a1
  in
  check "PR-A1: the [RSP+8] load tags Caller(8,8) through the real extraction"
    (Core.Map.find a1_info.Sm.offsets (Term.tid a1_ld)
     = Some (Sm.Caller (8L, 8L)));
  check "PR-A1: the slot read promotes to slot 0, arity 1, no window"
    (Core.Map.find a1_info.Sm.prom_slots (Term.tid a1_ld) = Some 0
    && a1_info.Sm.prom_arity = 1
    && not a1_info.Sm.prom_window
    && Core.Set.is_empty a1_info.Sm.prom_retaddr);

  (* A2: the return-address cell ([RSP+0] load, within the cell width)
     dies into prom_retaddr — it never forces a window parameter. *)
  let a2_ra = v64 "pr_a2_ra" in
  let a2_ld = Def.create a2_ra (Bil.Load (Bil.Var m, Bil.Var sp, LittleEndian, `r64)) in
  let a2 = straight_sub "pr_a2_retaddr" [ a2_ld ] in
  let a2_info =
    Hv.offsets_of_sub Theory.Target.unknown sp ~symtab:None
      ~prog:(Program.create ~subs:[ a2 ] ()) a2
  in
  check "PR-A2: the [RSP+0] read is the retaddr cell (retaddr set, no window, no slots)"
    (Core.Set.mem a2_info.Sm.prom_retaddr (Term.tid a2_ld)
    && not a2_info.Sm.prom_window
    && Core.Map.is_empty a2_info.Sm.prom_slots);

  (* A4: the written-slot demotion (T4b): a store into the caller
     window writes REAL memory — the slot it touches leaves the
     promoted map, so the read after the write observes the store. *)
  let a4_t = v64 "pr_a4_t" in
  let a4_st =
    Def.create m
      (Bil.Store (Bil.Var m, plus_addr sp 8L, Bil.Int (Cbat_word.to_word (w64 5)),
                  LittleEndian, `r64))
  in
  let a4_ld = Def.create a4_t (Bil.Load (Bil.Var m, plus_addr sp 8L, LittleEndian, `r64)) in
  let a4 = straight_sub "pr_a4_storing" [ a4_st; a4_ld ] in
  let a4_info =
    Hv.offsets_of_sub Theory.Target.unknown sp ~symtab:None
      ~prog:(Program.create ~subs:[ a4 ] ()) a4
  in
  check "PR-A4: a window store forces the Caller-Window Parameter"
    a4_info.Sm.prom_window;
  check "PR-A4: the slot the store touches demotes (its read takes the window)"
    (not (Core.Map.mem a4_info.Sm.prom_slots (Term.tid a4_ld)));


(* A5: the VLA detection (the non-literal SP decrement) and the
     def-kind stamp round-trip. *)
  let a5_rbx = v64 "pr_a5_rbx" in
  let a5_lit = Def.create sp (Bil.BinOp (Bil.MINUS, Bil.Var sp, Bil.Int (Cbat_word.to_word (w64 0x28)))) in
  let a5_rbx_def = Def.create a5_rbx (Bil.Int (Cbat_word.to_word (w64 0x80))) in
  let a5_vla =
    Def.create sp (Bil.BinOp (Bil.MINUS, Bil.Var sp, Bil.Var a5_rbx))
  in
  let a5 = straight_sub "pr_a5_vla" [ a5_lit; a5_rbx_def; a5_vla ] in
  let a5_info =
    Hv.offsets_of_sub Theory.Target.unknown sp ~symtab:None
      ~prog:(Program.create ~subs:[ a5 ] ()) a5
  in
  check "PR-A5: the non-literal SP decrement is the VLA def; the literal decrement is not"
    (Core.Set.equal a5_info.Sm.vla_alloc_tids (tid_set [ Term.tid a5_vla ]));
  let a5_stamped = Sm.stamp_def_kinds a5_info a5 in
  let kind_of_tid sub dtid =
    Term.enum blk_t sub
    |> Seq.concat_map ~f:(Term.enum def_t)
    |> Seq.find_map ~f:(fun d ->
           if Tid.equal (Term.tid d) dtid then Some (Sm.def_kind d) else None)
    |> Base.Option.join
  in
  check "PR-A5: the VLA kind rides the def's value through the stamp"
    (kind_of_tid a5_stamped (Term.tid a5_vla) = Some (Sm.VLA (Term.tid a5_vla))
    && kind_of_tid a5_stamped (Term.tid a5_lit) = None);

  (* A6: the caller side — an outgoing store at [RSP+16] feeds callee
     slot 1 (last-wins on a same-slot re-store). *)
  let a6_st1 =
    Def.create m
      (Bil.Store (Bil.Var m, plus_addr sp 16L, Bil.Int (Cbat_word.to_word (w64 7)),
                  LittleEndian, `r64))
  in
  let a6_st2 =
    Def.create m
      (Bil.Store (Bil.Var m, plus_addr sp 16L, Bil.Int (Cbat_word.to_word (w64 9)),
                  LittleEndian, `r64))
  in
  let exit_blk = mk_exit_blk () in
  let cont0 = blk_of_defs [] in
  let cont = with_jmps cont0 [ mk_goto (Term.tid exit_blk) ] in
  let body0 = blk_of_defs [ a6_st1; a6_st2 ] in
  let j =
    Jmp.create
      (Call
         (Call.create ~return:(Direct (Term.tid cont))
            ~target:(Indirect (Bil.Var (v64 "pr_a6_tptr"))) ()))
  in
  let body = with_jmps body0 [ j ] in
  let sb = Sub.Builder.create ~name:"pr_a6_caller" () in
  Sub.Builder.add_blk sb body;
  Sub.Builder.add_blk sb cont;
  Sub.Builder.add_blk sb exit_blk;
  let a6 = Sub.Builder.result sb in
  let a6_info =
    Hv.offsets_of_sub Theory.Target.unknown sp ~symtab:None
      ~prog:(Program.create ~subs:[ a6 ] ()) a6
  in
  let site = Core.Map.find a6_info.Sm.prom_sites (Term.tid body) in
  check "PR-A6: the site's outgoing stores map to SysV slots, last store wins"
    (match site with
     | Some { Sm.site_slots = [ (1, dtid) ] } -> Tid.equal dtid (Term.tid a6_st2)
     | _ -> false);
  check "PR-A6: the unresolvable indirect target records no resolution (symtab-free)"
    (Core.Map.find a6_info.Sm.prom_resolved (Term.tid j) = Some None);

  (* A8: the escape-extent rule (T14): only a StackOff proof — an
     SP-formed value — records an extent; a plain in-band integer (the
     spill_many class, [2^62, 2^63)) contributes NOTHING. *)
  let a8_rdi = v64 "RDI" in
  let a8_off = Def.create a8_rdi (Bil.BinOp (Bil.MINUS, Bil.Var sp, Bil.Int (Cbat_word.to_word (w64 0x10)))) in
  let a8_band =
    Def.create (v64 "pr_a8_rsi")
      (Bil.Int (Cbat_word.to_word (q64 0x4000000000000005L)))
  in
  let a8 = straight_sub "pr_a8_escape" [ a8_off; a8_band ] in
  let a8_info =
    Hv.offsets_of_sub Theory.Target.unknown sp ~symtab:None
      ~prog:(Program.create ~subs:[ a8 ] ()) a8
  in
  check "PR-A8: the SP-formed arg value records the (-16,-16) extent; the in-band plain integer records nothing (T14)"
    (List.mem (-16L, -16L) a8_info.Sm.sp_extents
    (* No extent reaches into the band: the plain in-band integer and
       the never-defined registers contribute nothing (an escape is
       noted once per block end, so the list may repeat). *)
    && List.for_all
         (fun (l, h) -> Int64.compare l 0x4000000000000000L < 0
                        && Int64.compare h 0x4000000000000000L < 0)
         a8_info.Sm.sp_extents);

  (* A9: the degraded arm — an indirect jump leaves the CFG
     incomplete; the sub degrades (no tags) without a refusal. *)
  let a9_tptr = v64 "pr_a9_tptr" in
  let a9_exit = mk_exit_blk () in
  let a9_body0 = blk_of_defs [] in
  let a9_body = with_jmps a9_body0 [ Jmp.create (Goto (Indirect (Bil.Var a9_tptr))) ] in
  let sb9 = Sub.Builder.create ~name:"pr_a9_indirect" () in
  Sub.Builder.add_blk sb9 a9_body;
  Sub.Builder.add_blk sb9 a9_exit;
  let a9 = Sub.Builder.result sb9 in
  let a9_info =
    Hv.offsets_of_sub Theory.Target.unknown sp ~symtab:None
      ~prog:(Program.create ~subs:[ a9 ] ()) a9
  in
  check "PR-A9: an indirect jump degrades the sub (CFG incomplete), not a refusal"
    (a9_info.Sm.degraded && Core.Map.is_empty a9_info.Sm.offsets);

  (* A10: the below-entry frame lane — a store at [RSP-16] tags
     Range(-16,-16), the sub's own proven-constant cell. *)
  let a10_st =
    Def.create m
      (Bil.Store (Bil.Var m, minus_addr sp 16L, Bil.Int (Cbat_word.to_word (w64 3)),
                  LittleEndian, `r64))
  in
  let a10 = straight_sub "pr_a10_frame" [ a10_st ] in
  let a10_info =
    Hv.offsets_of_sub Theory.Target.unknown sp ~symtab:None
      ~prog:(Program.create ~subs:[ a10 ] ()) a10
  in
  check "PR-A10: the [RSP-16] store tags Range(-16,-16) (the sub's own cell)"
    (Core.Map.find a10_info.Sm.offsets (Term.tid a10_st)
     = Some (Sm.Range (-16L, -16L)));
  ()

(* ------------------------------------------------------------------ *)
(* Lane B: the frame geometry ([layout_of_sub] -> [frame_dims]) and    *)
(* the split-plan cap.  T14's contract: only a StackOff proof sizes    *)
(* the frame; absurd spans degrade to the bounded 64K arm with a       *)
(* named diagnostic; the no-tags walk sizes from the SP decrement.     *)
(* ------------------------------------------------------------------ *)

let info_of ~(offsets : (tid * Sm.vsa_kind) list)
    ?(sp_extents : (int64 * int64) list = [])
    ?(regions : Sm.region list = []) ?(plan : Sm.split_plan = [])
    ?(degraded = false) () : Sm.vsa_info =
  Sm.mk_vsa_info ~offsets ~sp_extents ~regions ~stack_plan:plan
    ~degraded ~vla_alloc_tids:Tid.Set.empty ()

let run_layout () =
  let abi = Hike.Abi.x86_64_sysv in
  let layout_of info =
    let sub = straight_sub "pr_layout" [] in
    Sm.layout_of_sub sub ~abi info
  in
  (* B1: the precise arm — the plan's regions are the layout, no frame. *)
  let region : Sm.region =
    { id = 0; span = (-24L, -16L); members = []; convertible = true; max_width = 64 }
  in
  let b1 = layout_of (info_of ~offsets:[] ~regions:[ region ] ~plan:[ region ] ()) in
  check "PR-B1: the precise sub carries its region geometry and no fallback frame"
    (b1.frame_bytes = None
    && b1.regions = [ (0, (-24L, -16L), Sm.region_bytes region) ]);
  (* B2: the storage-free arm — no tags, not degraded: no stack storage. *)
  let b2 = layout_of (info_of ~offsets:[] ()) in
  check "PR-B2: a tag-free non-degraded sub owns no stack storage"
    (b2.frame_bytes = None && b2.regions = []);
  (* B3: the tags arm — extents size the frame: Range(-32,-8) ->
     need = max(8-(-32), 25) = 40 -> align16 = 48. *)
  let d_b3 = Tid.create () in
  let b3 =
    layout_of (info_of ~offsets:[ (d_b3, Sm.Range (-32L, -8L)) ] ())
  in
  check "PR-B3: the tagged frame sizes to the extent span (Range(-32,-8) -> 48 bytes)"
    (b3.frame_bytes = Some 48L && b3.regions = []);
  (* B4: the unbounded arm — Unbounded widens to the 64K window:
     max_hi -> 65536, need = 65537 -> align16 = 65552. *)
  let d_b4 = Tid.create () in
  let b4 = layout_of (info_of ~offsets:[ (d_b4, Sm.Unbounded) ] ()) in
  check "PR-B4: an Unbounded tag takes the bounded 64K arm (65552 bytes)"
    (b4.frame_bytes = Some 65552L);
  (* B5: the absurd-extent rule (T14, the spill_many class): a span
     >= 2^31 (here the [2^61, 2^62) band hull) never sizes the frame —
     it degrades to the bounded arm and names itself on the channel. *)
  let d_b5 = Tid.create () in
  let absurd_span = (0x2000000000000000L, 0x4000000000000000L) in
  let b5_err =
    capture_stderr (fun () ->
        ignore (layout_of (info_of ~offsets:[ (d_b5, Sm.Range (fst absurd_span, snd absurd_span)) ] ())))
  in
  let b5 = layout_of (info_of ~offsets:[ (d_b5, Sm.Range (fst absurd_span, snd absurd_span)) ] ()) in
  check "PR-B5: the absurd extent warns through the Hike_diag channel"
    (contains_substring b5_err "hike: frame:"
    && contains_substring b5_err "absurd");
  check "PR-B5: the absurd span takes the bounded arm, never a multi-exabyte frame"
    (b5.frame_bytes = Some 65552L);
  (* B5b: the wrapped pair reads absurd too (overflow-safe). *)
  let b5b_err =
    capture_stderr (fun () ->
        ignore (layout_of
                  (info_of ~offsets:[] ~sp_extents:[ (Int64.max_int, Int64.min_int) ] ())))
  in
  check "PR-B5b: a wrapped extent span is absurd (the sound unbounded reading)"
    (contains_substring b5b_err "absurd");
  (* B6: the degraded walk — no tags: the deepest SP decrement sizes
     the frame, floored at 8192. *)
  let rsp_dec n = Def.create sp (Bil.BinOp (Bil.MINUS, Bil.Var sp, Bil.Int (Cbat_word.to_word (w64 n)))) in
  let small = straight_sub "pr_b6_small" [ rsp_dec 0x80 ] in
  let big = straight_sub "pr_b6_big" [ rsp_dec 0x4000 ] in
  let b6_small = Sm.layout_of_sub small ~abi (info_of ~offsets:[] ~degraded:true ()) in
  let b6_big = Sm.layout_of_sub big ~abi (info_of ~offsets:[] ~degraded:true ()) in
  check "PR-B6: the no-tags walk floors at the 8192-byte degraded minimum"
    (b6_small.frame_bytes = Some 8192L);
  check "PR-B6: a deep SP decrement sizes the degraded frame above the floor (0x4000 -> 16400)"
    (b6_big.frame_bytes = Some 16400L);
  (* B7: the split-plan cap — a region whose alloca exceeds 64 MiB
     joins to Frame storage (excluded from the plan) with a named
     diagnostic; the control region stays. *)
  let big_region : Sm.region =
    { id = 0; span = (0L, 0x1000000L); members = []; convertible = true; max_width = 64 }
  in
  let ok_region : Sm.region =
    { id = 1; span = (-16L, -16L); members = []; convertible = true; max_width = 64 }
  in
  let sub_b7 = straight_sub "pr_b7_cap" [] in
  let info_b7 = info_of ~offsets:[] ~regions:[ big_region; ok_region ] () in
  let b7_err =
    capture_stderr (fun () -> ignore (Sm.split_plan sub_b7 info_b7))
  in
  let plan = Sm.split_plan sub_b7 info_b7 in
  check "PR-B7: the oversized region names itself and leaves the plan (storage Frame)"
    (contains_substring b7_err "hike: region:"
    && contains_substring b7_err "storage Frame"
    && plan = [ ok_region ]);
  ()

(* ------------------------------------------------------------------ *)
(* Lane C: the stack-to-locals rewrite's deep arms — the multi-cell    *)
(* region fission (region mem + base), the entry zero-init, the        *)
(* narrow-read splice, the ABI-visible exception, and the write-closed *)
(* rule at the rewrite level.  (Only the slot OR-mask form was pinned
   before: C1/A4 in test_regression.) *)
(* ------------------------------------------------------------------ *)

let run_stl_rewrite () =
  let m = memv "pr_c_m" in
  let mk_store off data (sz : size) : def term =
    Def.create m
      (Bil.Store (Bil.Var m, minus_addr sp off, Bil.Int (Cbat_word.to_word (w64 data)),
                  LittleEndian, sz))
  in
  (* C1: the fission arm — two singleton cells (-24, -16) in one
     convertible region whose span is NOT singleton: both accesses take
     the Region shape (region mem + base), including the NESTED load
     (the -O0 cmp pattern) inside a BinOp def. *)
  let c1_st0 = mk_store 24L 1 `r64 in
  let c1_st1 = mk_store 16L 2 `r64 in
  let c1_t = v64 "pr_c1_t" in
  let c1_ld_nested =
    Def.create c1_t
      (Bil.BinOp (Bil.PLUS,
                  Bil.Load (Bil.Var m, minus_addr sp 16L, LittleEndian, `r64),
                  Bil.Int (Cbat_word.to_word (w64 1))))
  in
  (* The write-closed control: a member of a NON-convertible region
     stays memory (together or not at all). *)
  let c1_ctl = mk_store 8L 3 `r64 in
  let c1 = straight_sub "pr_c1_fission"
      [ c1_st0; c1_st1; c1_ld_nested; c1_ctl ] in
  let region0 : Sm.region =
    { id = 0;
      span = (-24L, -16L);
      members =
        [ (Term.tid c1_st0, (-24L, -24L)); (Term.tid c1_st1, (-16L, -16L));
          (Term.tid c1_ld_nested, (-16L, -16L)) ];
      convertible = true;
      max_width = 64 }
  in
  let region1 : Sm.region =
    { id = 1; span = (-8L, -8L); members = [ (Term.tid c1_ctl, (-8L, -8L)) ];
      convertible = false; max_width = 64 }
  in
  let c1_info =
    info_of ~offsets:[]
      ~regions:[ region0; region1 ] ()
  in
  let c1_info =
    { c1_info with
      Sm.offsets =
        Core.Map.set
          (Core.Map.set
             (Core.Map.set
                (Core.Map.set Tid.Map.empty
                   ~key:(Term.tid c1_st0) ~data:(Sm.Range (-24L, -24L)))
                ~key:(Term.tid c1_st1) ~data:(Sm.Range (-16L, -16L)))
             ~key:(Term.tid c1_ld_nested) ~data:(Sm.Range (-16L, -16L)))
          ~key:(Term.tid c1_ctl) ~data:(Sm.Caller (8L, 8L)) }
  in
  Kb.provide (Tid.Map.singleton (Term.tid c1) c1_info);
  let c1' = Stl.stack_to_locals Theory.Target.unknown sp c1 in
  let def_of_lhs sub (n : string) : def term option =
    Term.enum blk_t sub
    |> Seq.concat_map ~f:(Term.enum def_t)
    |> Seq.find ~f:(fun d -> String.equal (Var.name (Def.lhs d)) n)
  in
  (* The COMPOUND-address shape (the lifted -O0 [mem[RSP - k]]): the mem
     operand names the region and the SP index arithmetic is KEPT — it
     materializes at emission through the anchor (= region-0 for
     precise subs). *)
  let st0' = def_of_lhs c1' (Var.name (Sm.region_mem 0)) in
  check "PR-C1: the whole-access store rebinds to the region mem, keeping the SP index arithmetic"
    (match st0' with
     | Some d ->
        (match Def.rhs d with
         | Bil.Store (Bil.Var mem, Bil.BinOp (Bil.MINUS, Bil.Var b, Bil.Int _), _, _, _) ->
            Var.same mem (Sm.region_mem 0) && Var.same b sp
         | _ -> false)
     | None -> false);
  let c1_t' =
    Term.enum blk_t c1'
    |> Seq.concat_map ~f:(Term.enum def_t)
    |> Seq.find ~f:(fun d -> Var.equal (Def.lhs d) c1_t)
  in
  check "PR-C1: the nested load inside a BinOp def reads the region mem too (the -O0 cmp pattern)"
    (match c1_t' with
     | Some d ->
        (match Def.rhs d with
         | Bil.BinOp (Bil.PLUS, Bil.Load (Bil.Var mem, _, _, _), Bil.Int _) ->
            Var.same mem (Sm.region_mem 0)
         | _ -> false)
     | None -> false);

  (* C1b: the BARE-VAR-address shape (the lifted indirect/[t] form):
     the address temp names the region base — [stack_rN_base] replaces
     it, both operands name the region (the split-storage rule). *)
  let c1b_t = v64 "pr_c1b_t" in
  let c1b_addr = Def.create c1b_t (Bil.BinOp (Bil.MINUS, Bil.Var sp, Bil.Int (Cbat_word.to_word (w64 16)))) in
  let c1b_st =
    Def.create m
      (Bil.Store (Bil.Var m, Bil.Var c1b_t, Bil.Int (Cbat_word.to_word (w64 5)),
                  LittleEndian, `r64))
  in
  let c1b = straight_sub "pr_c1b_barevar" [ c1b_addr; c1b_st ] in
  let c1b_info =
    info_of ~offsets:[] ~regions:[ { region0 with members = [ (Term.tid c1b_st, (-16L, -16L)) ] } ] ()
  in
  let c1b_info =
    { c1b_info with
      Sm.offsets =
        Core.Map.set Tid.Map.empty
          ~key:(Term.tid c1b_st) ~data:(Sm.Range (-16L, -16L)) }
  in
  Kb.provide (Tid.Map.singleton (Term.tid c1b) c1b_info);
  let c1b' = Stl.stack_to_locals Theory.Target.unknown sp c1b in
  let st0b' = def_of_lhs c1b' (Var.name (Sm.region_mem 0)) in
  check "PR-C1b: the bare-var address store rebinds to the region mem and names the region base"
    (match st0b' with
     | Some d ->
        (match Def.rhs d with
         | Bil.Store (Bil.Var mem, Bil.Var b, _, _, _) ->
            Var.same mem (Sm.region_mem 0) && Var.same b (Sm.region_base 0)
         | _ -> false)
     | None -> false);
  let ctl' = def_of_lhs c1' (Var.name m) in
  check "PR-C1: the non-convertible region's member keeps its memory store (write-closed)"
    (match ctl' with
     | Some d ->
        (match Def.rhs d with
         | Bil.Store (Bil.Var mem, _, _, _, _) -> Var.same mem m
         | _ -> false)
     | None -> false);

  (* C2: the slot arms — a singleton region converts to a named local:
     the entry zero-init, and the narrow read splices a LOW cast. *)
  let c2_st = mk_store 16L 7 `r64 in
  let c2_t = v64 "pr_c2_t" in
  let c2_ld =
    Def.create c2_t (Bil.Load (Bil.Var m, minus_addr sp 16L, LittleEndian, `r32))
  in
  let c2 = straight_sub "pr_c2_slot" [ c2_st; c2_ld ] in
  let c2_region : Sm.region =
    { id = 0; span = (-16L, -16L);
      members = [ (Term.tid c2_st, (-16L, -16L)); (Term.tid c2_ld, (-16L, -16L)) ];
      convertible = true; max_width = 64 }
  in
  let c2_info =
    info_of ~offsets:[] ~regions:[ c2_region ] ()
  in
  let c2_info =
    { c2_info with
      Sm.offsets =
        Core.Map.set
          (Core.Map.set Tid.Map.empty
             ~key:(Term.tid c2_st) ~data:(Sm.Range (-16L, -16L)))
          ~key:(Term.tid c2_ld) ~data:(Sm.Range (-16L, -16L)) }
  in
  Kb.provide (Tid.Map.singleton (Term.tid c2) c2_info);
  let c2' = Stl.stack_to_locals Theory.Target.unknown sp c2 in
  let entry = Base.Option.value_exn (Term.first blk_t c2') in
  let defs = Term.enum def_t entry |> Seq.to_list in
  (* The slot var is minted by the model's deterministic grammar
     ("slot_<abs-lo>", the cell width); [slot_of] itself is not on the
     mli surface, so the pin reads the grammar off the rewrite. *)
  let is_slot_var v = String.equal (Var.name v) "slot_16" in
  check "PR-C2: the converted slot zero-initializes at entry (the width travels with the cell)"
    (match defs with
     | d :: _ ->
        is_slot_var (Def.lhs d)
        && (match Def.rhs d with Bil.Int w -> Word.equal w (Word.zero 64) | _ -> false)
     | [] -> false);
  let c2_ld' =
    List.find_opt (fun d -> Var.equal (Def.lhs d) c2_t) defs
  in
  check "PR-C2: the narrow (r32) read of a 64-bit slot splices the LOW cast"
    (match c2_ld' with
     | Some d ->
        (match Def.rhs d with
         | Bil.Cast (Bil.LOW, 32, Bil.Var v) -> is_slot_var v
         | _ -> false)
     | None -> false);

  (* C3: the ABI-visible exception - a Caller-tagged access stays
     memory even inside a convertible region (the cross-sub
     consistency rule outranks the region). *)
  let c3_st = mk_store 8L 9 `r64 in
  let c3 = straight_sub "pr_c3_abi" [ c3_st ] in
  let c3_region : Sm.region =
    { id = 0; span = (-8L, -8L); members = [ (Term.tid c3_st, (-8L, -8L)) ];
      convertible = true; max_width = 64 }
  in
  let c3_info = info_of ~offsets:[] ~regions:[ c3_region ] () in
  let c3_info =
    { c3_info with
      Sm.offsets =
        Core.Map.set Tid.Map.empty
          ~key:(Term.tid c3_st) ~data:(Sm.Caller (8L, 8L)) }
  in
  Kb.provide (Tid.Map.singleton (Term.tid c3) c3_info);
  let c3' = Stl.stack_to_locals Theory.Target.unknown sp c3 in
  let c3_st' =
    Term.enum blk_t c3'
    |> Seq.concat_map ~f:(Term.enum def_t)
    |> Seq.find ~f:(fun d -> Tid.equal (Term.tid d) (Term.tid c3_st))
  in
  check "PR-C3: the Caller-tagged access keeps its memory store (ABI-visible)"
    (match c3_st' with
     | Some d ->
        (match Def.rhs d with
         | Bil.Store (Bil.Var mem, _, _, _, _) -> Var.same mem m
         | _ -> false)
     | None -> false);
  ()

(* ------------------------------------------------------------------ *)
(* Lane D: the emitter's alloca shapes — the VLA lane (the dynamic     *)
(* allocation, stack-model hierarchy rule 1), the SP Slot / stack_0   *)
(* anchoring per storage class, and the frame-request clamp (the       *)
(* silent-truncation lesson, loud now).                                *)
(* ------------------------------------------------------------------ *)

(* The T10 fixture stamp: per-def kinds + the layout tag onto the terms
   (the emitter consumes no record). *)
let stamp_shape (info : Sm.vsa_info) (sub : sub term) : sub term =
  let sub = Sm.stamp_def_kinds info sub in
  Sm.set_layout (Sm.layout_of_sub sub ~abi:Hike.Abi.x86_64_sysv info) sub

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
  let d1_info =
    info_of ~offsets:[] ~degraded:false ()
    |> fun i ->
    { i with Sm.vla_alloc_tids = tid_set [ Term.tid d_vla ] }
  in
  let ir1 = emit_ir [ stamp_shape d1_info d1 ] in
  check "PR-D1: the VLA def emits a real runtime-sized i8 alloca"
    (contains_substring ir1 "%vla = alloca i8, i64");
  check "PR-D1: the model SP binds to the alloca's integer (vla_i64)"
    (contains_substring ir1 "%vla_i64 = ptrtoint");

  (* D2: the SP Slot per storage class. *)
  (* Frame storage: %frame + the anchor GEP + the entry sp_slot. *)
  let d_ld =
    Def.create (v64 "pr_d2_t")
      (Bil.Load (Bil.Var m, minus_addr sp 16L, LittleEndian, `r64))
  in
  let d2 = straight_sub "pr_d2_frame" [ d_ld ] in
  let d2_info =
    info_of ~offsets:[ (Term.tid d_ld, Sm.Range (-16L, -16L)) ] ()
  in
  let ir2 = emit_ir [ stamp_shape d2_info d2 ] in
  check "PR-D2: frame storage emits the %frame alloca"
    (contains_substring ir2 "%frame = alloca [");
  check "PR-D2: frame storage anchors through the entry SP Slot (per-invocation stack_0)"
    (contains_substring ir2 "%sp_slot = alloca i64"
    && contains_substring ir2 "%stack_0 = load i64, ptr %sp_slot");
  (* Region storage: the anchor is region-0 (the precise sub's base). *)
  let region : Sm.region =
    { id = 0; span = (-16L, -16L); members = []; convertible = true; max_width = 64 }
  in
  let d2b = straight_sub "pr_d2b_region" [ d_ld ] in
  let d2b_info =
    info_of ~offsets:[ (Term.tid d_ld, Sm.Range (-16L, -16L)) ]
      ~regions:[ region ] ~plan:[ region ] ()
  in
  let ir2b = emit_ir [ stamp_shape d2b_info d2b ] in
  check "PR-D2b: region storage anchors the SP Slot at region-0 (the ptrtoint base)"
    (contains_substring ir2b "%anchor_i64 = ptrtoint ptr %stack_r0"
    && contains_substring ir2b "%sp_slot = alloca i64");
  (* Storage-free: no anchor, no SP Slot. *)
  let d2c = straight_sub "pr_d2c_free" [] in
  let ir2c = emit_ir [ stamp_shape (info_of ~offsets:[] ()) d2c ] in
  check "PR-D2c: a storage-free sub emits no SP Slot and no frame"
    (not (contains_substring ir2c "%sp_slot")
    && not (contains_substring ir2c "%frame"));

  (* D3: the frame-request clamp — a layout over the array-count bound
     (2^31) clamps LOUDLY (the silent-truncation lesson). *)
  let d3 = straight_sub "pr_d3_huge" [ d_ld ] in
  let d3_info =
    info_of ~offsets:[ (Tid.create (), Sm.Range (-0x80000000L, -0x80000000L)) ] ()
  in
  let d3_sub = stamp_shape d3_info d3 in
  let d3_err, ir3 =
    capture_stderr (fun () -> ignore (emit_ir [ d3_sub ]))
    |> fun err -> (err, emit_ir [ stamp_shape d3_info d3 ])
  in
  check "PR-D3: an over-bound frame request names itself on the channel and clamps"
    (contains_substring d3_err "hike: frame:"
    && contains_substring d3_err "clamped"
    && contains_substring ir3 "alloca [2147483647 x i8]");
  ()

(* ------------------------------------------------------------------ *)
(* Lane E: the register/convention facts (Hike_abi, ADR 0008: SP is    *)
(* the only stack-semantics register, fp an ordinary callee-saved GPR) *)
(* and the KB domain's join/order semantics (the pipeline-only store). *)
(* ------------------------------------------------------------------ *)

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
    && Base.List.length (Abi.param_regs Theory.Target.unknown) = 14);
  check "PR-E1: the structural predicates partition the lanes"
    (Abi.is_return_reg abi (named "RAX")
    && not (Abi.is_return_reg abi (named "RCX"))
    && Abi.is_vector_param_reg abi (named "YMM3")
    && not (Abi.is_vector_param_reg abi (named "RDI")));
  (* The unknown-target totality: the SysV record serves unit fixtures. *)
  check "PR-E1: an unknown target falls back to the SysV record (total)"
    (Hike.Abi.of_target_opt Theory.Target.unknown = None
    && Abi.is_sp (Hike.Abi.of_target Theory.Target.unknown) (named "RSP")
    && Hike.Abi.addr_size_bits Theory.Target.unknown = 0);
  (* The real target: the reified SP register. *)
  let x86 = Theory.Target.of_string "x86_64-gnu-elf" in
  check "PR-E1: the x86_64-gnu-elf target reifies RSP as the SP"
    (Theory.Target.matches x86 "x86_64-gnu-elf"
    && (match Hike.Abi.of_target_opt x86 with
        | Some a -> Abi.is_sp a (Hike.Abi.sp x86)
        | None -> false));

  (* The KB domain: extension order, union join, conflicts refuse. *)
  let t1 = Tid.create () in
  let t2 = Tid.create () in
  let mk_info ks = Sm.mk_vsa_info ~offsets:ks ~regions:[] ~stack_plan:[]
      ~degraded:false ~vla_alloc_tids:Tid.Set.empty () in
  let i_a = mk_info [ (t1, Sm.Range (-8L, -8L)) ] in
  let i_a' = mk_info [ (t1, Sm.Range (-8L, -8L)) ] in
  let i_ab = mk_info [ (t1, Sm.Range (-8L, -8L)); (t2, Sm.Unbounded) ] in
  let i_b = mk_info [ (t2, Sm.Range (-16L, -16L)) ] in
  let i_c = mk_info [ (t1, Sm.Range (-24L, -24L)) ] in
  let m1 = Tid.Map.singleton t1 i_a in
  let m2 = Tid.Map.singleton t1 i_a' in
  let big = Core.Map.set (Tid.Map.singleton t1 i_a) ~key:t2 ~data:i_ab in
  let other = Tid.Map.singleton (Tid.create ()) i_b in
  let open Kb in
  check "PR-E2: the info order is extension (EQ / LT / GT / NC over the maps)"
    (map_order m1 m2 = KB.Order.EQ
    && map_order m1 big = KB.Order.LT
    && map_order big m1 = KB.Order.GT
    && map_order m1 other = KB.Order.NC);
  check "PR-E2: joining a subset takes the bigger"
    (match map_join m1 big with
     | Ok j -> Core.Map.equal Sm.equal_vsa_info j big
     | Error _ -> false);
  check "PR-E2: joining disjoint maps unions (both entries survive)"
    (match map_join m1 other with
     | Ok j -> Core.Map.mem j t1 && Core.Map.mem j (fst (Base.Option.value_exn (Core.Map.nth other 0)))
     | Error _ -> false);
  check "PR-E2: two different infos for one sub CONFLICT (never silently dropped)"
    (match map_join m1 (Tid.Map.singleton t1 i_c) with
     | Error (Vsa_info_conflict _) -> true
     | _ -> false);
  check "PR-E2: info_join accepts equal infos and refuses differing ones"
    ((match info_join t1 i_a i_a' with Ok _ -> true | Error _ -> false)
    && (match info_join t1 i_a i_c with Error _ -> true | Ok _ -> false));
  (* The ONE lookup: absence is the empty info (the identity record). *)
  check "PR-E2: info_of_sub on a never-provided sub is the empty record"
    (Sm.equal_vsa_info (Kb.info_of_sub (Tid.create ())) Sm.empty_vsa_info)


let run () =
  run_producer_record ();
  run_layout ();
  run_stl_rewrite ();
  run_emitter_shapes ();
  run_abi_and_kb ()
