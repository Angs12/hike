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

let run () = run_producer_record ()
