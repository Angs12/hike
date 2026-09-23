(* Stack-arg promotion pins: the promotion-fact derivation through the REAL
   fixpoint ([Hike.Vsa.fixpoint] / [fixture_ctx]), the promotion as a BIR
   rewrite ([Hike.Promote.promote_sub] / [rewrite_program]), and the
   promotion's emitted shape.  One Alcotest group per pin; each pin builds
   its own fixture, so no state crosses pins. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

(* [sp + off] — the caller-window address shape (entry RSP = segment base,
   so the BIL offset IS the SysV slot space). *)
let plus_addr sp (off : int64) : exp =
  Bil.BinOp (Bil.PLUS, Bil.Var sp, Bil.Int (Cbat_word.to_word (w64 (Int64.to_int off))))

(* The fixture stamps the producer's facts onto the terms, then runs the
   promotion as a BIR rewrite — what the pipeline's vsa pass does. *)
let stamp (facts : Hike.Promote.facts) (sub : sub term) : sub term =
  let sub =
    Cu.stamp_dyn_allocs
      ~dynamic_alloc_tids:(Hike.Promote.dynamic_alloc_tids_of ~facts:top_facts sub) sub
  in
  Hike.Promote.promote_sub ~abi:Hike.Abi.x86_64_sysv facts sub

(* Family 8: stack-arg promotion emission.  A promoted callee (two proven
   slots) and two callers — one resolved indirect site with the outgoing
   stores the slots feed, one unresolvable.  Returns the callee and the
   emitted IR for each caller. *)
let t4_fixture () : sub term * string * string =
  let m = memv "prom_m" in
  let rsp = v64 "RSP" in
  let slot0 = ivar64 "hike_slot0" in
  let slot1 = ivar64 "hike_slot1" in
  let acc = v64 "prom_acc" in
  let rdi = v64 "RDI" in
  let rsi = v64 "RSI" in
  let ld0 =
    Def.create (v64 "prom_ld0")
      (Bil.Load (Bil.Var m, Bil.Var slot0, LittleEndian, `r64))
  in
  let callee, _ =
    sub_of "prom_callee"
      [ [ ld0;
          Def.create acc
            (Bil.BinOp (Bil.PLUS, Bil.Var rdi,
                        Bil.BinOp (Bil.PLUS, Bil.Var rsi,
                                   Bil.BinOp (Bil.PLUS, Bil.Var slot0, Bil.Var slot1)))) ],
        [ (1, mk_goto) ];
        [], [ (0, mk_ret) ] ]
  in
  let store1 =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 24))),
           Bil.Int (Cbat_word.to_word (w64 7)),
           LittleEndian,
           `r64 ))
  in
  let store2 =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 32))),
           Bil.Int (Cbat_word.to_word (w64 9)),
           LittleEndian,
           `r64 ))
  in
  let caller, _ =
    sub_of "prom_caller"
      [ [ store1; store2 ],
        [ (1, fun t -> Jmp.create (Call (Call.create ~return:(Direct t) ~target:(Indirect (Bil.Var (v64 "prom_tptr"))) ()))) ];
        [], [ (0, mk_ret) ] ]
  in
  let j = sub_jmp caller 0 0 in
  let callee_facts : Hike.Promote.facts = mk_facts ~prom_arity:2 () in
  let caller_facts : Hike.Promote.facts =
    mk_facts
      ~prom_resolved:(Tid.Map.singleton (Term.tid j) (Some (Term.tid callee)))
      ()
  in
  let callee = stamp callee_facts callee in
  let caller = stamp caller_facts caller in
  let ir = emit_ir [ caller; callee ] in
  let caller2, _ =
    sub_of "prom_caller2"
      [ [],
        [ (1,
           fun t ->
             Jmp.create
               (Call (Call.create ~return:(Direct t) ~target:(Indirect (Bil.Var (v64 "prom_tptr2"))) ()))) ];
        [], [ (0, mk_ret) ] ]
  in
  let j2 = sub_jmp caller2 0 0 in
  let caller2_facts : Hike.Promote.facts =
    mk_facts ~prom_resolved:(Tid.Map.singleton (Term.tid j2) None) ()
  in
  let caller2 = stamp caller2_facts caller2 in
  let ir2 = emit_ir [ caller2; callee ] in
  (callee, ir, ir2)

(* Family 9: the promotion as a BIR rewrite — the sub's structure is the
   emitter's only input. *)

(* The promoted callee with one proven incoming-slot read.  Returns the
   original sub and its rewrite. *)
let t10_promoted () : sub term * sub term =
  let m = memv "t10_m" in
  let addr =
    Bil.BinOp (Bil.PLUS, Bil.Var (v64 "RSP"), Cbat_word.to_word (w64 8) |> fun w -> Bil.Int w)
  in
  let d_ld =
    Def.create (ivar64 "t10_t")
      (Bil.Load (Bil.Var m, addr, LittleEndian, `r64))
  in
  let sub, _ =
    sub_of "t10_callee"
      [ [ d_ld ], [ (1, mk_goto) ];
        [], [ (0, mk_ret) ] ]
  in
  let facts = mk_facts ~prom_arity:1 () in
  (sub, Hike.Promote.promote_sub ~abi:Hike.Abi.x86_64_sysv facts sub)

let t10_find_def sub' dtid =
  Term.enum blk_t sub'
  |> Seq.find_map ~f:(fun b ->
         Base.List.find_map
           (Term.enum def_t b |> Seq.to_list)
           ~f:(fun d -> if Tid.equal (Term.tid d) dtid then Some d else None))

(* The caller side: the site's store gains its call-arg def right after it
   (found through the chain replica's rewrite).  Returns the storing def
   and the bound call-arg def, when present. *)
let t10_site () : def term * def term option =
  let m2 = memv "t10_m2" in
  let store =
    Def.create m2
      (Bil.Store
         ( Bil.Var m2,
           Bil.BinOp (Bil.PLUS, Bil.Var (v64 "RSP"), Cbat_word.to_word (w64 16) |> fun w -> Bil.Int w),
           Bil.Int (Cbat_word.to_word (w64 7)),
           LittleEndian,
           `r64 ))
  in
  let caller, _ =
    sub_of "t10_caller"
      [ [ store ],
        [ (1,
           fun t ->
             Jmp.create
               (Call (Call.create ~return:(Direct t) ~target:(Indirect (Bil.Var (ivar64 "t10_tptr"))) ()))) ];
        [], [ (0, mk_ret) ] ]
  in
  let caller' = rewrite_one caller in
  let cblk = Base.List.hd_exn (Term.enum blk_t caller' |> Seq.to_list) in
  let cdefs = Term.enum def_t cblk |> Seq.to_list in
  let pos dtid = Base.List.findi cdefs ~f:(fun _ d -> Tid.equal (Term.tid d) dtid) in
  let arg_at =
    match pos (Term.tid store) with
    | Some (i_store, _) -> (
        match cdefs |> Base.List.findi ~f:(fun _ d -> Cu.is_call_arg (Def.lhs d)) with
        | Some (i_arg, arg_def) when Base.Int.equal i_arg (i_store + 1) -> Some arg_def
        | _ -> None)
    | None -> None
  in
  (store, arg_at)

(* Family 9b: the producer record's promotion lanes, through the REAL
   fixpoint. *)

(* The A4 storing sub: a store at [RSP+8] then reads at [RSP+8] and
   [RSP+16]. *)
let pr_a4_sub () : sub term =
  let m = memv "pr_m" in
  let a4_t = v64 "pr_a4_t" in
  let a4_st =
    Def.create m
      (Bil.Store
         ( Bil.Var m, plus_addr sp 8L, Bil.Int (Cbat_word.to_word (w64 5)),
           LittleEndian, `r64 ))
  in
  let a4_ld = Def.create a4_t (Bil.Load (Bil.Var m, plus_addr sp 8L, LittleEndian, `r64)) in
  let a4_ld1 =
    Def.create (v64 "pr_a4_t1")
      (Bil.Load (Bil.Var m, plus_addr sp 16L, LittleEndian, `r64))
  in
  let a4 = straight_sub "pr_a4_storing" [ a4_st; a4_ld; a4_ld1 ] in
  ignore (produce Theory.Target.unknown (Program.create ~subs:[ a4 ] ()) a4);
  a4

(* The A4 sub's storage over [sec; lo, hi], read through its tree. *)
let pr_a4_storage (a4 : sub term) (sec : Hike.Stack_model.sec) (lo : int64) (hi : int64) :
    Hike.Sections.storage option =
  let ctx = fixture_ctx [ a4 ] in
  Base.Option.bind (Core.Map.find ctx.Hike.Sections.sub_trees (Term.tid a4))
    ~f:(fun tree ->
      Base.Option.map
        (Hike.Sections.storage_of_range tree (Hike.Sections.range sec lo hi))
        ~f:(fun rs -> rs.Hike.Sections.storage))

(* The A6 caller: two stores at [RSP+16] then an indirect call.  Returns the
   sub, its entry block, the call jmp, and the second (last) store def. *)
let pr_a6_sub () : sub term * blk term * jmp term * def term =
  let m = memv "pr_m" in
  let a6_st1 =
    Def.create m
      (Bil.Store
         ( Bil.Var m, plus_addr sp 16L, Bil.Int (Cbat_word.to_word (w64 7)),
           LittleEndian, `r64 ))
  in
  let a6_st2 =
    Def.create m
      (Bil.Store
         ( Bil.Var m, plus_addr sp 16L, Bil.Int (Cbat_word.to_word (w64 9)),
           LittleEndian, `r64 ))
  in
  let a6, _ =
    sub_of "pr_a6_caller"
      [ [ a6_st1; a6_st2 ],
        [ (1,
           fun t ->
             Jmp.create
               (Call (Call.create ~return:(Direct t) ~target:(Indirect (Bil.Var (v64 "pr_a6_tptr"))) ()))) ];
        [], [ (2, mk_goto) ];
        [], [ (0, mk_ret) ] ]
  in
  let body = Base.List.hd_exn (Term.enum blk_t a6 |> Seq.to_list) in
  let j = sub_jmp a6 0 0 in
  (a6, body, j, a6_st2)

(* Family 10: the window class's stored-value channel.  The fixture is the
   va_start triangle: the middle sub takes six GP args (no incoming
   stack-arg read), produces the overflow pointer (RAX := RBP + 8) and
   stores it (mem[RBP-0xC0] := RAX) in one straight-line block. *)
let prwc_mk_defs () : def term * def term * def term * def term * def term * var list =
  let m = memv "prwc_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let rax = v64 "RAX" in
  let gp_args = Base.List.map ~f:v64 [ "RDI"; "RSI"; "RDX"; "RCX"; "R8"; "R9" ] in
  ( Def.create rbp (Bil.Var rsp),
    Def.create rax (Bil.Var (List.nth gp_args 0)),
    Def.create rax (Bil.BinOp (Bil.PLUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8)))),
    Def.create (v64 "prwc_t") (Bil.Var (List.nth gp_args 1)),
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 0xc0))),
           Bil.Var rax,
           LittleEndian,
           `r64 )),
    gp_args )

let tests : unit Alcotest.test list =
  [
    (* PR-01: the promoted signature carries the register lanes then the
       positional slots. *)
    pin "PR-01" "the promoted signature carries the positional slots" (fun () ->
        let _, ir, _ = t4_fixture () in
        check_ir "PR-01"
          "(i64 %RDI, i64 %RSI, i64 %hike_slot0, i64 %hike_slot1)" ir);

    (* PR-02: the resolved site is a DIRECT call through the promoted
       signature; the unpassed slots stay undef. *)
    pin "PR-02" "the resolved site calls the promoted body directly" (fun () ->
        let callee, ir, _ = t4_fixture () in
        check "PR-02"
          (contains_substring ir
             (Printf.sprintf "call void @\"%s\"("
                (Hike.Bil2llvm.sanitize_name (Tid.name (Term.tid callee))))
          && contains_substring ir ", i64 undef, i64 undef)"));

    (* PR-03: the memory-convention twin is internal. *)
    pin "PR-03" "the memory-convention twin is emitted with internal linkage" (fun () ->
        let callee, ir, _ = t4_fixture () in
        check_ir "PR-03"
          (Printf.sprintf "define internal void @\"%s_hike_thunk\""
             (Hike.Bil2llvm.sanitize_name (Tid.name (Term.tid callee))))
          ir);

    (* PR-04: the twin's synthetic indirect convention carries the window
       base, never SP. *)
    pin "PR-04"
      "the twin carries the synthetic indirect convention (the window base, never SP)"
      (fun () ->
        let _, ir, _ = t4_fixture () in
        check_ir "PR-04"
          ("_hike_thunk\"(i64 %RDI, i64 %RSI, i64 %RDX, i64 %RCX, i64 %R8, "
          ^ "i64 %R9, i256 %YMM0, i256 %YMM1, i256 %YMM2, i256 %YMM3, "
          ^ "i256 %YMM4, i256 %YMM5, i256 %YMM6, i256 %YMM7, ptr %hike_window)")
          ir);

    (* PR-05: the twin unpacks the window slots into the promoted body. *)
    pin "PR-05" "the twin unpacks the window slots into the promoted body" (fun () ->
        let callee, ir, _ = t4_fixture () in
        check_ir "PR-05"
          (Printf.sprintf "call void @\"%s\"(i64 %%RDI, i64 %%RSI, i64 %%"
             (Hike.Bil2llvm.sanitize_name (Tid.name (Term.tid callee))))
          ir);

    (* PR-06: the twin reads the slots through the window pointer. *)
    pin "PR-06" "the twin reads the slots through the window pointer" (fun () ->
        let _, ir, _ = t4_fixture () in
        check_ir "PR-06" "getelementptr i8, ptr %hike_window" ir);

    (* PR-07: the unresolved site takes the pointer call through the
       synthetic signature. *)
    pin "PR-07" "the unresolvable site takes the pointer call (never the promoted body)"
      (fun () ->
        let _, _, ir2 = t4_fixture () in
        check_ir "PR-07" "call { i64, i64 } %" ir2);

    (* PR-08: the pointer call never lands on the promoted body directly. *)
    pin "PR-08" "the pointer call never lands on the promoted body directly" (fun () ->
        let _, _, ir2 = t4_fixture () in
        check "PR-08" (not (contains_substring ir2 "call { i64, i64 } @prom_callee(")));

    (* PR-09: the synthetic indirect signature carries the window base. *)
    pin "PR-09" "the synthetic indirect signature carries the window base" (fun () ->
        let _, _, ir2 = t4_fixture () in
        check_ir "PR-09"
          "@indirect_call(i64, i64, i64, i64, i64, i64, i256, i256, i256, i256, \
           i256, i256, i256, i256, ptr)"
          ir2);

    (* PR-10: the sub gains its promoted parameter as a real BIR arg. *)
    pin "PR-10" "the sub gains its promoted parameter as a real BIR arg" (fun () ->
        let _, sub' = t10_promoted () in
        check "PR-10"
          (Base.List.exists
             (Term.enum arg_t sub' |> Seq.to_list)
             ~f:(fun a -> Var.equal (Arg.lhs a) (Cu.arg_slot ~word:8 0))));

    (* PR-11: the sub keeps its tid through the arg-term rewrite. *)
    pin "PR-11" "the sub keeps its tid through the arg-term rewrite" (fun () ->
        let sub, sub' = t10_promoted () in
        check "PR-11" (Tid.equal (Term.tid sub') (Term.tid sub)));

    (* PR-12: an identity access keeps its tag through the stamp. *)
    pin "PR-12" "an identity access keeps its tag through the stamp" (fun () ->
        let keep_m = memv "t10_km" in
        let keep =
          Def.create (v64 "t10_keep")
            (Bil.Load
               ( Bil.Var keep_m,
                 Bil.BinOp
                   ( Bil.PLUS,
                     Bil.Var (v64 "RSP"),
                     Cbat_word.to_word (w64 8) |> fun w -> Bil.Int w ),
                 LittleEndian,
                 `r64 ))
        in
        let keep_st =
          Def.create keep_m
            (Bil.Store
               ( Bil.Var keep_m,
                 Bil.BinOp
                   ( Bil.PLUS,
                     Bil.Var (v64 "RSP"),
                     Cbat_word.to_word (w64 8) |> fun w -> Bil.Int w ),
                 Bil.Int (Cbat_word.to_word (w64 3)),
                 LittleEndian,
                 `r64 ))
        in
        let keep_sub0 = straight_sub "t10_keep" [ keep; keep_st ] in
        let keep_ctx = fixture_ctx [ keep_sub0 ] in
        let keep_sub = Hike.Sections.stamp_tags keep_ctx keep_sub0 in
        let keep' = Sm.stamp_dyn_allocs ~dynamic_alloc_tids:Tid.Set.empty keep_sub in
        let keep_def = Base.Option.value_exn (t10_find_def keep' (Term.tid keep)) in
        check "PR-12" (Sm.sec_tag keep_def <> None));

    (* PR-13: the call-arg def is bound right after the storing def. *)
    pin "PR-13" "the call-arg def is bound right after the storing def" (fun () ->
        let _, arg_at = t10_site () in
        check "PR-13" (Option.is_some arg_at));

    (* PR-14: the call-arg def reads the storing def's written bytes (7). *)
    pin "PR-14" "the call-arg def reads the storing def's written bytes" (fun () ->
        let _, arg_at = t10_site () in
        check_bound "PR-14" arg_at (fun arg_def ->
            match Def.rhs arg_def with
            | Bil.Int w -> Word.to_int64_exn w = 7L
            | _ -> false));

    (* PR-15: the proven incoming-slot read promotes — the read's cell is
       Arg_slot 0 in the finalized tree (arity 1, no window). *)
    pin "PR-15" "the read's cell is Arg_slot 0 in the finalized tree (arity 1, no window)"
      (fun () ->
        let m = memv "pr_m" in
        let a1_t = v64 "pr_a1_t" in
        let a1_ld =
          Def.create a1_t (Bil.Load (Bil.Var m, plus_addr sp 8L, LittleEndian, `r64))
        in
        let a1 = straight_sub "pr_a1_callee" [ a1_ld ] in
        check "PR-15"
          (let ctx = fixture_ctx [ a1 ] in
           match Core.Map.find ctx.Hike.Sections.sub_trees (Term.tid a1) with
           | None -> false
           | Some tree ->
               let bs = Hike.Sections.Tree.to_sequence tree |> Seq.to_list in
               let argslots =
                 Base.List.filter_map bs ~f:(fun (_, rs) ->
                     match rs.Hike.Sections.storage with
                     | Hike.Sections.Arg_slot i -> Some i
                     | _ -> None)
               in
               argslots = [ 0 ]));

    (* PR-16: the return-address cell ([RSP+0] load) dies into the retaddr
       set — it never forces a window parameter. *)
    pin "PR-16" "the [RSP+0] read is the retaddr cell (the retaddr set)" (fun () ->
        let m = memv "pr_m" in
        let a2_ra = v64 "pr_a2_ra" in
        let a2_ld =
          Def.create a2_ra (Bil.Load (Bil.Var m, Bil.Var sp, LittleEndian, `r64))
        in
        let a2 = straight_sub "pr_a2_retaddr" [ a2_ld ] in
        let a2_retaddr =
          let sol =
            Cbat_vsa.static_graph_vsa
              ~abi:Hike_abi.x86_64_sysv
              ~resolved:Tid.Map.empty (Program.create ~subs:[ a2 ] ()) a2
              (Cbat_vsa.init_sol ~abi:Hike_abi.x86_64_sysv a2)
          in
          Hike.Cfg_complete.retaddr_defs ~abi:Hike.Abi.x86_64_sysv ~sol a2
        in
        check "PR-16" (Core.Set.mem a2_retaddr (Term.tid a2_ld)));

    (* PR-17: the written slot demotes to Window (write-closed). *)
    pin "PR-17" "the written cell is Window (write-closed; its reads take the window)"
      (fun () ->
        let a4 = pr_a4_sub () in
        check "PR-17"
          (pr_a4_storage a4 Sm.Args (pos 8L) (pos 15L) = Some Hike.Sections.Stack_residue));

    (* PR-18: the demotion is EXACT — an 8-byte store at [RSP+8] touches slot
       0's cell only; slot 1 stays Arg_slot. *)
    pin "PR-18"
      "the demotion is EXACT — an 8-byte store at [RSP+8] leaves slot 1 Arg_slot"
      (fun () ->
        let a4 = pr_a4_sub () in
        check "PR-18"
          (pr_a4_storage a4 Sm.Args (pos 16L) (pos 23L)
          = Some (Hike.Sections.Arg_slot 1)));

    (* PR-19: the site's outgoing stores map to SysV slots, last store wins. *)
    pin "PR-19" "the site's outgoing stores map to SysV slots, last store wins"
      (fun () ->
        let a6, body, _, a6_st2 = pr_a6_sub () in
        check "PR-19"
          (let fa6, a6 = fixture_facts_sub a6 in
           let bindings =
             Hike.Promote.stage_a ~word:8 ~abi:Hike.Abi.x86_64_sysv ~sp
               ~denote:fa6.denote a6
           in
           match Core.Map.find bindings (Term.tid body) with
           | Some [ b ] ->
               Base.Int.equal b.Hike.Promote.sb_slot 1
               && Tid.equal (Term.tid b.Hike.Promote.sb_def) (Term.tid a6_st2)
           | _ -> false));

    (* PR-20: the unresolvable indirect target records no resolution. *)
    pin "PR-20" "the unresolvable indirect target records no resolution (symtab-free)"
      (fun () ->
        let a6, _, j, _ = pr_a6_sub () in
        check "PR-20"
          (let fa6, a6 = fixture_facts_sub a6 in
           let resolved =
             Hike.Promote.call_resolution ~denote:fa6.denote ~symtab:None
               ~name_tid:[] a6
           in
           Core.Map.find resolved (Term.tid j) = Some None));

    (* PR-21: the window class keeps every slot unbound (arity 0) — the
       window lane serves. *)
    pin "PR-21" "the window class keeps every slot unbound (arity 0) — the window lane serves"
      (fun () ->
        let prologue, al, ptr, filler, store, gp_args = prwc_mk_defs () in
        let mid, _ =
          sub_of
            ~args:(Base.List.map gp_args ~f:(fun v -> Arg.create v (Bil.Var v)))
            "prwc_va_middle"
            [ [ prologue; al; ptr; filler; store ], [ (1, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        check "PR-21"
          (let ctx = fixture_ctx [ mid ] in
           match Core.Map.find ctx.Hike.Sections.sub_trees (Term.tid mid) with
           | None -> false
           | Some tree ->
               let bs = Hike.Sections.Tree.to_sequence tree |> Seq.to_list in
               Base.List.for_all bs ~f:(fun (_, rs) ->
                   match rs.Hike.Sections.storage with
                   | Hike.Sections.Arg_slot _ -> false
                   | _ -> true)
               && Base.List.exists bs ~f:(fun (k, rs) ->
                      (match k.Hike.Sections.lo.Hike.Sections.p_sec with
                       | Sm.Args -> true
                       | _ -> false)
                      && (match rs.Hike.Sections.storage with
                          | Hike.Sections.Stack_residue -> true
                          | _ -> false))));

    (* PR-22: the boundary-visible twin — the pointer is produced in a
       previous block, so the store's data is SP-derived at the storing
       block's entry; the anchor's pointer cell is Window-served. *)
    pin "PR-22" "the anchor's pointer cell is Window-served in the tree" (fun () ->
        let prologue, al, ptr, _filler, store, _gp_args = prwc_mk_defs () in
        let twin, _ =
          sub_of "prwc_va_twin"
            [ [ prologue; al; ptr ], [ (1, mk_goto) ];
              [ store ], [ (0, mk_ret) ] ]
        in
        ignore (produce Theory.Target.unknown (Program.create ~subs:[ twin ] ()) twin);
        check "PR-22"
          (let ctx = fixture_ctx [ twin ] in
           match Core.Map.find ctx.Hike.Sections.sub_trees (Term.tid twin) with
           | None -> false
           | Some tree ->
               Base.List.exists (Hike.Sections.Tree.to_sequence tree |> Seq.to_list)
                 ~f:(fun (_, rs) ->
                     match rs.Hike.Sections.storage with
                     | Hike.Sections.Stack_residue -> true
                     | _ -> false)));
  ]

let () = run "promote" tests
