(* The stack-arg promotion's pins: the promotion-fact derivation through
   the REAL fixpoint ([Hike.Vsa.fixpoint]) and the tree's promotion facts
   ([prom_arity] / [prom_resolved] — the producer's promotion product),
   the promotion as a BIR rewrite ([Hike.Sections.promote_sub] — real
   args, parameter reads, call-arg
   defs, direct resolved targets), and the promotion's emitted shape
   (the promoted signature, the memory-convention twin, the pointer
   call).  Fixtures stamp the producer's facts onto BIR terms; the
   checks read the promotion's own output. *)

open Printf
open Test_common
open Test_fixtures
open Bap.Std
open Bap_core_theory

module Cu = Hike.Stack_model
module Sm = Hike.Stack_model
module Pr = Hike.Sections
(* The producer-record pins spell the model [Sm] and the driver [Hv]
   (the aliases they carried in the producer-record suite). *)
module Hv = Hike.Vsa

(* [sp + off] — the caller-window address shape (entry RSP = segment
   base + 0, so the BIL offset IS the SysV slot space). *)
let plus_addr sp (off : int64) : exp =
  Bil.BinOp (Bil.PLUS, Bil.Var sp, Bil.Int (Cbat_word.to_word (w64 (Int64.to_int off))))

(* A one-entry sub over the defs, exiting through a real terminal
   block (CFG-honest: the Goto target is built first). *)
let straight_sub (name : string) (defs : def term list) : sub term =
  fst (sub_of name [ defs, [ (1, mk_goto) ]; [], [ (0, mk_ret) ] ])

(* The emitter consumes NO record — the fixture stamps the
   producer's facts onto the terms (what the pipeline's vsa pass does:
   per-def kinds, the layout tag, and the promotion's BIR structure).
   [Kb.provide] stays a pipeline-pass concern and is not used here. *)
let stamp_tag
 (d : def term) (t : Sm.sec_tag option) : def term =
  match t with Some t -> Sm.set_sec_tag t d | None -> d

let stamp (facts : Pr.facts) (sub : sub term) : sub term =
  let sub =
    Cu.stamp_dyn_allocs
      ~dynamic_alloc_tids:(Pr.dynamic_alloc_tids_of ~sp ~denote:Hike.Vsa.denote_exp_at sub) sub
  in
  Hike.Sections.promote_sub ~abi:Hike.Abi.x86_64_sysv facts sub

(* Family 8: stack-arg promotion emission.                             *)

(* A promoted callee (two proven slots) and a caller with one resolved
   indirect site and the outgoing stores the slots feed. *)
let run_promotion () =
  let m = memv "prom_m" in
  let rsp = v64 "RSP" in
  let slot0 = ivar64 "hike_slot0" in
  let slot1 = ivar64 "hike_slot1" in
  (* The callee: reads its two promoted slots (the production Caller
     reads) and returns through the model ret lane. *)
  let acc = v64 "prom_acc" in
  (* The callee also reads RDI/RSI (never defines them): the register
     lanes of the signature, the realistic promoted shape. *)
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
  (* The caller: pushes two outgoing stores, then an indirect call the
     VSA resolves (the volatile-singleton class). *)
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
  let callee_facts : Pr.facts = mk_facts ~prom_arity:2 () in
  let caller_facts : Pr.facts =
    mk_facts
      ~prom_resolved:(Tid.Map.singleton (Term.tid j) (Some (Term.tid callee)))
      ()
  in
  let callee = stamp callee_facts callee in
  let caller = stamp caller_facts caller in
  let ir = emit_ir [ caller; callee ] in
  (try
     let oc = open_out "/tmp/t10_prom_ir.txt" in
     output_string oc ir; close_out oc
   with _ -> ());
  (* The callee's promoted signature carries the register lanes then
     the positional slots. *)
  check_ir "T4-PROM: the promoted signature carries the positional slots"
    "(i64 %RDI, i64 %RSI, i64 %hike_slot0, i64 %hike_slot1)" ir;
  (* The resolved site is a DIRECT call through the promoted
     signature (the producer rewrote the target); the unpassed slots
     stay undef.  The register lanes carry the caller's own signature
     values (the direct call frees the caller of its indirect-target
     var, so the lanes are real parameters, not undefs). *)
  check
    "T4-PROM: the resolved site calls the promoted body directly"
    (contains_substring ir
       (sprintf "call void @\"%s\"("
          (Hike.Bil2llvm.sanitize_name (Tid.name (Term.tid callee))))
     && contains_substring ir ", i64 undef, i64 undef)");
  (* The Thunk: internal linkage, the memory-path signature. *)
  check_ir "T4-THUNK: the memory-convention twin is emitted with internal linkage"
    (sprintf "define internal void @\"%s_hike_thunk\""
       (Hike.Bil2llvm.sanitize_name (Tid.name (Term.tid callee))))
    ir;
  check_ir "T4-THUNK: the twin carries the synthetic indirect convention (the window base, never SP)"
    ("_hike_thunk\"(i64 %RDI, i64 %RSI, i64 %RDX, i64 %RCX, i64 %R8, "
    ^ "i64 %R9, i256 %YMM0, i256 %YMM1, i256 %YMM2, i256 %YMM3, "
    ^ "i256 %YMM4, i256 %YMM5, i256 %YMM6, i256 %YMM7, i64 %hike_window)")
    ir;
  check_ir "T4-THUNK: the twin unpacks the window slots into the promoted body"
    (sprintf "call void @\"%s\"(i64 %%RDI, i64 %%RSI, i64 %%"
       (Hike.Bil2llvm.sanitize_name (Tid.name (Term.tid callee))))
    ir;
  check_ir "T4-THUNK: the twin loads the slots from the window memory"
    "load i64, ptr %1" ir;
  (* The unresolved site: the pointer call through the synthetic
     signature (which carries the window base). *)
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
  let caller2_facts : Pr.facts =
    mk_facts ~prom_resolved:(Tid.Map.singleton (Term.tid j2) None) ()
  in
  let caller2 = stamp caller2_facts caller2 in
  let ir2 = emit_ir [ caller2; callee ] in
  check_ir
    "T4-PTR: the unresolvable site takes the pointer call (never the promoted body)"
    "call { i64, i64 } %" ir2;
  check
    "T4-PTR: the pointer call never lands on the promoted body directly"
    (not (contains_substring ir2 "call { i64, i64 } @prom_callee("));
  check_ir "T4-PTR: the synthetic indirect signature carries the window base"
    "@indirect_call(i64, i64, i64, i64, i64, i64, i256, i256, i256, i256, \
                    i256, i256, i256, i256, i64)"
    ir2;
  ()

(* Family 9: the promotion as a BIR rewrite — the sub's structure *)
(* is the emitter's only input.                                         *)

let run_t10_rewrite () =
  (* A Caller(8,8) load def: the proven incoming slot read. *)
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
  let sub' = Hike.Sections.promote_sub ~abi:Hike.Abi.x86_64_sysv facts sub in
  check "T10-PROMOTE: the sub gains its promoted parameter as a real BIR arg"
    (Base.List.exists
       (Term.enum arg_t sub' |> Seq.to_list)
       ~f:(fun a -> Var.equal (Arg.lhs a) (Cu.arg_slot ~word:8 0)));
  check "T10-PROMOTE: the sub keeps its tid through the arg-term rewrite"
    (Tid.equal (Term.tid sub') (Term.tid sub));
  let find_def sub' dtid =
    Term.enum blk_t sub'
    |> Seq.find_map ~f:(fun b ->
           Base.List.find_map
             (Term.enum def_t b |> Seq.to_list)
             ~f:(fun d ->
                 if Tid.equal (Term.tid d) dtid then Some d else None))
  in
  let keep_m = memv "t10_km" in
  let keep =
    Def.create (v64 "t10_keep")
      (Bil.Load
         ( Bil.Var keep_m,
           Bil.BinOp (Bil.PLUS, Bil.Var (v64 "RSP"), Cbat_word.to_word (w64 8) |> fun w -> Bil.Int w),
           LittleEndian, `r64 ))
  in
  let keep_st =
    Def.create keep_m
      (Bil.Store
         ( Bil.Var keep_m,
           Bil.BinOp (Bil.PLUS, Bil.Var (v64 "RSP"), Cbat_word.to_word (w64 8) |> fun w -> Bil.Int w),
           Bil.Int (Cbat_word.to_word (w64 3)), LittleEndian, `r64 ))
  in
  let keep_sub0 = straight_sub "t10_keep" [ keep; keep_st ] in
  let keep_ctx = fixture_ctx [ keep_sub0 ] in
  let keep_sub = Hike.Sections.stamp_tags keep_ctx keep_sub0 in
  let keep' = Sm.stamp_dyn_allocs ~dynamic_alloc_tids:Tid.Set.empty keep_sub in
  let keep_def = Base.Option.value_exn (find_def keep' (Term.tid keep)) in
  check "T10-PROMOTE: an identity access keeps its tag through the stamp"
    (Sm.sec_tag keep_def <> None);
  (* The caller side: the site's store gains its call-arg def, and the
     resolved indirect target becomes a direct call. *)
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
  (* T10-SITE migrated to the REAL composition (Stage C's single
     insertion site: bind_site_args inside rewrite_program; the
     promote_sub 3b recipe died as its duplicate). *)
  let caller' = rewrite_one caller in
  let cblk = Base.List.hd_exn (Term.enum blk_t caller' |> Seq.to_list) in
  let cdefs = Term.enum def_t cblk |> Seq.to_list in
  let pos dtid =
    Base.List.findi cdefs ~f:(fun _ d -> Tid.equal (Term.tid d) dtid)
  in
  (* The call-arg def (the store's slot, computed from the store's own
     start address) sits right after the storing def and binds its
     WRITTEN bytes (7).  The resolved-target rewrite is covered by the
     resolve_target pins (test_resolve) and the corpus battery. *)
  let arg_at =
    match pos (Term.tid store) with
    | Some (i_store, _) -> (
        match cdefs |> Base.List.findi ~f:(fun _ d -> Cu.is_call_arg (Def.lhs d)) with
        | Some (i_arg, arg_def) when Int.equal i_arg (i_store + 1) -> Some arg_def
        | _ -> None)
    | None -> None
  in
  check "T10-SITE: the call-arg def is bound right after the storing def"
    (match arg_at with Some _ -> true | None -> false);
  check "T10-SITE: the call-arg def reads the storing def's written bytes"
    (match arg_at with
     | Some arg_def ->
       (match Def.rhs arg_def with
        | Bil.Int w -> Word.to_int64_exn w = 7L
        | _ -> false)
     | None -> false)

(* The producer record's promotion lanes, through the REAL fixpoint
   (the entry seeds RSP at the symbolic segment base, the production
   universe). *)

let run_producer_promotion () =
  let m = memv "pr_m" in

  (* A1: the proven incoming-slot read promotes (the SysV slot 0 at
     [entry RSP + 8]). *)
  let a1_t = v64 "pr_a1_t" in
  let a1_ld = Def.create a1_t (Bil.Load (Bil.Var m, plus_addr sp 8L, LittleEndian, `r64)) in
  let a1 = straight_sub "pr_a1_callee" [ a1_ld ] in
  check "PR-A1: the read's cell is Arg_slot 0 in the finalized tree (arity 1, no window)"
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
         argslots = [ 0 ]);

  (* A2: the return-address cell ([RSP+0] load, within the cell width)
     dies into prom_retaddr — it never forces a window parameter. *)
  let a2_ra = v64 "pr_a2_ra" in
  let a2_ld = Def.create a2_ra (Bil.Load (Bil.Var m, Bil.Var sp, LittleEndian, `r64)) in
  let a2 = straight_sub "pr_a2_retaddr" [ a2_ld ] in
  let a2_retaddr =
    let sol =
      Cbat_vsa.static_graph_vsa
        ~abi:Hike_abi.x86_64_sysv
        ~resolved:Tid.Map.empty []
        (Program.create ~subs:[ a2 ] ()) a2
        (Cbat_vsa.init_sol ~abi:Hike_abi.x86_64_sysv a2)
    in
    Hike.Cfg_complete.retaddr_defs ~abi:Hike.Abi.x86_64_sysv ~sol a2
  in
  check "PR-A2: the [RSP+0] read is the retaddr cell (the retaddr set)"
    (Core.Set.mem a2_retaddr (Term.tid a2_ld));

  (* A4: the written-slot demotion: a store into the caller
     window writes REAL memory — the slot it touches leaves the
     promoted map, so the read after the write observes the store.
     The demotion is EXACT: slot i spans [entry_rsp+8+8i, +8), so an
     8-byte store at [RSP+8] touches slot 0's cell ONLY — the next
     slot's read stays promoted. *)
  let a4_t = v64 "pr_a4_t" in
  let a4_st =
    Def.create m
      (Bil.Store (Bil.Var m, plus_addr sp 8L, Bil.Int (Cbat_word.to_word (w64 5)),
                  LittleEndian, `r64))
  in
  let a4_ld = Def.create a4_t (Bil.Load (Bil.Var m, plus_addr sp 8L, LittleEndian, `r64)) in
  let a4_ld1 =
    Def.create (v64 "pr_a4_t1")
      (Bil.Load (Bil.Var m, plus_addr sp 16L, LittleEndian, `r64))
  in
  let a4 = straight_sub "pr_a4_storing" [ a4_st; a4_ld; a4_ld1 ] in
  ignore (produce Theory.Target.unknown (Program.create ~subs:[ a4 ] ()) a4);
  let a4_storage (sec : Hike.Stack_model.sec) (lo : int64) (hi : int64) :
      Hike.Sections.storage option =
    let ctx = fixture_ctx [ a4 ] in
    match Core.Map.find ctx.Hike.Sections.sub_trees (Term.tid a4) with
    | None -> None
    | Some tree ->
        Base.Option.map
          (Hike.Sections.storage_of_range tree (Hike.Sections.range sec lo hi))
          ~f:(fun rs -> rs.Hike.Sections.storage)
  in
  check "PR-A4: the written cell is Window (write-closed; its reads take the window)"
    (a4_storage Sm.Args (pos 8L) (pos 15L) = Some Hike.Sections.Stack_residue);
  check "PR-A4: the demotion is EXACT — an 8-byte store at [RSP+8] leaves slot 1 Arg_slot"
    (a4_storage Sm.Args (pos 16L) (pos 23L) = Some (Hike.Sections.Arg_slot 1));

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
  let body = List.nth (Term.enum blk_t a6 |> Seq.to_list) 0 in
  let j = sub_jmp a6 0 0 in
  check "PR-A6: the site's outgoing stores map to SysV slots, last store wins"
    (ignore (install_fixture_envs [ a6 ]);
     let bindings = Hike.Sections.stage_a ~word:8 ~abi:Hike.Abi.x86_64_sysv ~sp
        ~denote:Hv.denote_exp_at a6 in
     match Core.Map.find bindings (Term.tid body) with
     | Some [ b ] ->
         Int.equal b.Hike.Sections.sb_slot 1
         && Tid.equal (Term.tid b.Hike.Sections.sb_def) (Term.tid a6_st2)
     | _ -> false);
  check "PR-A6: the unresolvable indirect target records no resolution (symtab-free)"
    (ignore (install_fixture_envs [ a6 ]);
     let resolved =
       Hike.Sections.call_resolution ~denote:Hv.denote_exp_at ~symtab:None
         ~name_tid:[] a6
     in
     Core.Map.find resolved (Term.tid j) = Some None);
  ()

(* Family 10: the window class's stored-value channel.  The escape
   notes at the STORE DEF's own pre-state — never at a block boundary.
   The fixture is the va_start triangle: the middle sub takes six GP
   args (no incoming stack-arg read exists), produces the overflow
   pointer (RAX := RBP + 8) and stores it (mem[RBP-0xC0] := RAX) in one
   straight-line block — at the block's entry RAX holds no SP-derived
   value, so only the at-def evaluation sees the escape. *)

let run_window_escape () =
  let m = memv "prwc_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let rax = v64 "RAX" in
  let gp_args = Base.List.map ~f:v64 [ "RDI"; "RSI"; "RDX"; "RCX"; "R8"; "R9" ] in
  (* Fresh def terms per sub (the tids are per-sub keys in the record). *)
  let mk_defs () =
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
             `r64 )) )
  in
  let prologue, al, ptr, filler, store = mk_defs () in
  let mid, _ =
    sub_of
      ~args:(Base.List.map gp_args ~f:(fun v -> Arg.create v (Bil.Var v)))
      "prwc_va_middle"
      [ [ prologue; al; ptr; filler; store ], [ (1, mk_goto) ];
        [], [ (0, mk_ret) ] ]
  in
  check "PR-WC1: the window class keeps every slot unbound (arity 0) — the window lane serves"
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
                 | Sm.Args -> true | _ -> false)
                && (match rs.Hike.Sections.storage with
                    | Hike.Sections.Stack_residue -> true | _ -> false)));
  (* The boundary-visible twin: the pointer is produced in a previous
     block, so the store's data is SP-derived at the storing block's
     entry — every evaluation sees it. *)
  let prologue, al, ptr, _filler, store = mk_defs () in
  let twin, _ =
    sub_of "prwc_va_twin"
      [ [ prologue; al; ptr ], [ (1, mk_goto) ];
        [ store ], [ (0, mk_ret) ] ]
  in
  ignore (produce Theory.Target.unknown (Program.create ~subs:[ twin ] ()) twin);
  check "PR-WC2: the anchor's pointer cell is Window-served in the tree"
    (let ctx = fixture_ctx [ twin ] in
     match Core.Map.find ctx.Hike.Sections.sub_trees (Term.tid twin) with
     | None -> false
     | Some tree ->
         Base.List.exists (Hike.Sections.Tree.to_sequence tree |> Seq.to_list)
           ~f:(fun (_, rs) ->
               match rs.Hike.Sections.storage with
               | Hike.Sections.Stack_residue -> true | _ -> false))

let run () =
  run_promotion ();
  run_t10_rewrite ();
  run_producer_promotion ();
  run_window_escape ()
