(* Emitter tests: the first seam over bil2llvm (emit_program).
   Each fixture builds a BIR sub, emits it via emit_program with
   Theory.Target.unknown + ptrsize:64, and asserts on the textual IR
   (Llvm.print_module) — the same idiom check_allocas.sh uses. *)

open Printf
open Test_common
open Test_fixtures
open Bap.Std
open Bap_core_theory

module Cu = Hike.Stack_model
module Sm = Hike.Stack_model

(* The emitter consumes NO record — the fixture stamps the
   producer's facts onto the terms (what the pipeline's vsa pass does:
   per-def kinds, the layout tag, and the promotion's BIR structure).
   [Kb.provide] stays a pipeline-pass concern and is not used here. *)
let stamp_tag (d : def term) (t : Sm.sec_tag option) : def term =
  match t with Some t -> Sm.set_sec_tag t d | None -> d

(* The fixture stamp: the PRODUCTION tags, hand-stated per fixture
   (the same sec_tag the attribution stamps); then the promotion. *)
let stamp (tags : (Tid.t * Sm.sec_tag) list) (sub : sub term) : sub term =
  let tags =
    Base.List.fold tags ~init:Tid.Map.empty
      ~f:(fun m (tid, t) -> Core.Map.set m ~key:tid ~data:t)
  in
  let sub =
    Term.map blk_t sub ~f:(fun blk ->
        Term.map def_t blk ~f:(fun d ->
            match Core.Map.find tags (Term.tid d) with
            | Some t -> stamp_tag d (Some t)
            | None -> d))
  in
  Hike.Sections.promote_sub ~abi:Hike.Abi.x86_64_sysv (mk_facts ()) sub

let run_poison () =
  (* The warned-poison class, pinned: an unbounded-span access (the
     fully-infinite kind) warns through Hike_diag and still emits
     (create_exp); a Dead-tagged access emits a poison value. *)
  let rsp = v64 "RSP" in
  let m = memv "poison_m" in
  let t = v64 "poison_t" in
  let addr = Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 16))) in
  let ld = Def.create t (Bil.Load (Bil.Var m, addr, LittleEndian, `r64)) in
  (* The store consumes the LOAD result: the poison is textually live. *)
  let st =
    Def.create m (Bil.Store (Bil.Var m, addr, Bil.Var t, LittleEndian, `r64))
  in
  (* The unbounded span on the load/store; Dead on the second pair. *)
  let dead_sub = mk_lds_sub "poison_dead" [ ld; st ] in
  let dead_sub =
    stamp [ (Term.tid ld, Sm.Tag.Dead) ] dead_sub
  in

  let ir_holder2 = ref "" in
  let err_dead =
    capture_stderr (fun () -> ir_holder2 := emit_ir [ dead_sub ])
  in
  check "POISON: the Dead-tagged access emits a poison value"
    (contains_substring !ir_holder2 "poison");
  (* The Dead arm warns through the Hike_diag channel (the L1 lane, 2026-09-09):
     a Dead tag is a provably-empty range — it must be loud, never silent. *)
  check "POISON: the Dead-tagged access warns through the Hike_diag channel"
    (contains_substring err_dead "hike: guarded: sub");
  (* The undef-read lane: reading a never-defined register warns and the
     value becomes undef. *)
  let rax = v64 "RAX" in
  let sub, _ =
    sub_of "undef_read_sub"
      [ [],
        [ (1, fun t -> mk_jmp_to t (Bil.BinOp (Bil.EQ, Bil.Var rax, Bil.Int (Cbat_word.to_word (w64 0)))));
          (1, mk_goto) ];
        [], [ (0, mk_ret) ] ]
  in
  let ir_holder3 = ref "" in
  let err_und =
    capture_stderr (fun () -> ir_holder3 := emit_ir [ sub ])
  in
  check "UNDEF: a never-defined register read warns through Hike_diag"
    (contains_substring err_und "hike: undef-read:");
  check "UNDEF: the never-defined read becomes a frozen undef"
    (contains_substring !ir_holder3 "freeze i64 undef")

(* Family: the never-defined register's frozen entry value (the
   self-comparison class).                                   *)

let run_frozen_undef () =
  (* The pcmpeqd-self lift: two defs extract the SAME lane of one
     never-defined vector register and a guard compares them — at the
     machine the comparison is deterministically equal, so both reads
     must observe the SAME frozen value (a bare per-use undef folds
     the tautology to undef under opt). *)
  let ymm =
    Var.create ~is_virtual:false ~fresh:false "YMM3" (Type.Imm 256)
  in
  let lane () = Bil.Extract (31, 0, Bil.Extract (127, 0, Bil.Var ymm)) in
  let t1 = Var.create ~is_virtual:true ~fresh:false "sc_t1" (Type.Imm 32) in
  let t2 = Var.create ~is_virtual:true ~fresh:false "sc_t2" (Type.Imm 32) in
  let eq = Bil.BinOp (Bil.EQ, Bil.Var t1, Bil.Var t2) in
  let sub, _ =
    sub_of "selfcmp_sub"
      [ [ Def.create t1 (lane ()); Def.create t2 (lane ()) ],
        [ (1, fun t -> mk_jmp_to t eq);
          (1, fun t -> mk_jmp_to t (Bil.UnOp (Bil.NOT, eq))) ];
        [], [ (0, mk_ret) ] ]
  in
  let ir = emit_ir [ sub ] in
  check "FRZ: the never-defined register's entry value is one freeze"
    (contains_substring ir "freeze i256 undef");
  check "FRZ: the register-file phi reads the frozen entry value"
    (contains_substring ir "[ %hike_undef,");
  check "FRZ: no bare undef remains as an entry phi incoming"
    (not (contains_substring ir "[ undef,"))

(* Family 3: restore_sp_after_call idempotence (the L-E1e class).     *)

let run_sp_restore () =
  (* A direct call: after it, the sp local rebinds to post-push + 8. *)
  let rsp = v64 "RSP" in
  let m = memv "sp_m" in
  let callee_tid = Tid.for_name "sp_callee" in
  (* The push: RSP := RSP - 8; mem[RSP] := retaddr — the lifted call shape. *)
  let caller, _ =
    sub_of "sp_caller"
      [ [ Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 8))));
          Def.create m (Bil.Store (Bil.Var m, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 1234)), LittleEndian, `r64)) ],
        [ (1, fun t -> Jmp.create (Call (Call.create ~return:(Direct t) ~target:(Direct callee_tid) ()))) ];
        [], [ (0, mk_ret) ] ]
  in
  let callee = fst (sub_of "sp_callee" [ [], [ (0, mk_ret) ] ]) in
  let ir = emit_ir [ caller; callee ] in
  (* The restore rebinds sp to post-push + 8, by name. *)
  check "SP-RESTORE: the named sp_restored = add <pushed>, 8 is emitted"
    (contains_substring ir "%sp_restored = add i64 ");
  check "SP-RESTORE: the continuation's sp phi reads the restore (no net drift)"
    (contains_substring ir "[ %sp_restored,");
  (* The regioned twin: a sub with a split layout restores too.  The
     store at [SP+8] before the call and the reload at [SP+8] on the
     continuation must hit the same cell — the callee's ret popped the
     pushed retaddr, so the return edge restores the SP. *)
  let rsp2 = v64 "RSP" in
  let m2 = memv "sp_m2" in
  let callee2_tid = Tid.for_name "sp_callee2" in
  let t2 = v64 "sp_t2" in
  let w8 = Bil.Int (Cbat_word.to_word (w64 8)) in
  let caller2, _ =
    sub_of "sp_caller2"
      [ [ Def.create rsp2 (Bil.BinOp (Bil.MINUS, Bil.Var rsp2, w8));
          Def.create m2
            (Bil.Store
               ( Bil.Var m2,
                 Bil.BinOp (Bil.PLUS, Bil.Var rsp2, w8),
                 Bil.Int (Cbat_word.to_word (w64 7)),
                 LittleEndian, `r64 )) ],
        [ (1, fun t ->
              Jmp.create
                (Call
                   (Call.create ~return:(Direct t)
                      ~target:(Direct callee2_tid) ()))) ] ;
        [ Def.create t2
            (Bil.Load
               ( Bil.Var m2,
                 Bil.BinOp (Bil.PLUS, Bil.Var rsp2, w8),
                 LittleEndian, `r64 )) ],
        [ (0, mk_ret) ] ]
  in
  let caller2 =
    Cu.set_layout
      { Cu.regions = [ (0, (pos (-24L), pos (-16L)), 16L) ];
        Cu.anchor = Some (0, 8192L); Cu.window_param = false }
      caller2
  in
  let callee2 = fst (sub_of "sp_callee2" [ [], [ (0, mk_ret) ] ]) in
  let ir2 = emit_ir [ caller2; callee2 ] in
  check "SP-RESTORE: the regioned sub's return edge restores too"
    (contains_substring ir2 "%sp_restored = add i64 ");
  check "SP-RESTORE: the regioned continuation's sp phi reads the restore"
    (contains_substring ir2 "[ %sp_restored,")

(* Family 4: cast preservation at BIL type boundaries.                 *)

let run_casts () =
  (* A tagged (singleton Range) stack store whose DATA is a narrower cast:
     the zext/trunc sits at the store, not dropped or promoted. *)
  let rsp = v64 "RSP" in
  let m = memv "cast_m" in
  let src = v64 "cast_src" in
  let addr = Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 16))) in
  let d_src = Def.create src (Bil.Int (Cbat_word.to_word (w64 0x7B))) in
  let d_st =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           addr,
           Bil.Cast (Bil.UNSIGNED, 32, Bil.Var src),
           LittleEndian,
           `r64 ))
  in
  let sub, _ =
    sub_of "cast_sub"
      [ [ d_src; d_st ],
        [ (1, fun t -> mk_jmp_to t (Bil.BinOp (Bil.EQ, Bil.Var src, Bil.Int (Cbat_word.to_word (w64 0x7B))))) ];
        [], [ (0, mk_ret) ] ]
  in
  (* Singleton Range tag on the store: the converted-cell shape. *)
  let sub = stamp [ (Term.tid d_st, Sm.Tag.Stack (pos (-16L), pos (-16L))) ] sub in
  let ir = emit_ir [ sub ] in
  check "CAST: the tagged store reaches memory with its narrowing cast intact"
    (contains_substring ir "store" && contains_substring ir "trunc")

(* Family 5: the substring-complete golden (singleton slot + one      *)
(* fission region).                                                   *)

let run_golden () =
  (* The golden sub: an entry, a stack load and store (singleton Range
     tags via Kb.provide, the D4 fixture shape), and a ret. *)
  let rsp = v64 "RSP" in
  let m = memv "gold_m" in
  let ld_var = v64 "gold_ld" in
  let st_val = v64 "gold_st" in
  let ld_addr = Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 16))) in
  let st_addr = Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 24))) in
  let d_ld = Def.create ld_var (Bil.Load (Bil.Var m, ld_addr, LittleEndian, `r64)) in
  let d_st = Def.create m (Bil.Store (Bil.Var m, st_addr, Bil.Var ld_var, LittleEndian, `r64)) in
  let d_val = Def.create st_val (Bil.BinOp (Bil.PLUS, Bil.Var ld_var, Bil.Int (Cbat_word.to_word (w64 1)))) in
  let sub, _ =
    sub_of "golden_sub"
      [ [ d_ld; d_st; d_val ],
        [ (1, fun t -> mk_jmp_to t (Bil.BinOp (Bil.EQ, Bil.Var st_val, Bil.Int (Cbat_word.to_word (w64 0)))));
          (1, mk_goto) ];
        [], [ (0, mk_ret) ] ]
  in
  (* The vsa_info: singleton Range tags on both accesses + the split
     layout, the write-closed fission shape. *)
  let sub =
    stamp
      [ (Term.tid d_ld, Sm.Tag.Stack (pos (-16L), pos (-16L)));
        (Term.tid d_st, Sm.Tag.Stack (pos (-24L), pos (-24L))) ]
      sub
  in
  let sub =
    Cu.set_layout
      { Cu.regions = [ (0, (pos (-24L), pos (-16L)), 16L) ];
        Cu.anchor = Some (0, 8192L); Cu.window_param = false }
      sub
  in
  let ir = emit_ir [ sub ] in
  check_ir "GOLDEN: the golden sub emits a function define" "define" ir;
  check_ir "GOLDEN: the fission region alloca is built by name" "stack_r0" ir;
  check_ir "GOLDEN: the region base GEP lane is present" "getelementptr" ir;
  check_ir "GOLDEN: a load reaches the frame" "load" ir;
  check_ir "GOLDEN: a store reaches the frame" "store" ir;
  check_ir "GOLDEN: the jmp cond comparison emitted" "icmp" ir;
  check_ir "GOLDEN: a branch on the cond" "br " ir;
  check_ir "GOLDEN: a return is emitted" "ret" ir;
  check_ir "GOLDEN: i64 lanes (ptrsize 64)" "i64" ir;
  (* The anchor residue invariant: the SP Slot word ≡ 8 (mod 16) — the
     SysV entry residue the lifted word arithmetic must reproduce. *)
  check_ir "GOLDEN: the anchor word is the region GEP at the SysV residue"
    "getelementptr i8, ptr %stack_r0, i64 8" ir;
  check_ir "GOLDEN: the SP Slot stores that anchor word"
    "%anchor_i64 = ptrtoint ptr %anchor to i64" ir

(* Family 6: the fp-GPR lane (ADR 0008) — the emitter never invents a   *)
(* register value.                                                      *)

let run_fp_gpr () =
  (* The -O2 GPR-RBP shape: a def READS RBP without ever defining it (no
     prologue). The true value is the caller's RBP (a heap pointer); the
     emitter must not substitute the model frame for it. *)
  let rbp = v64 "RBP" in
  let rdi = v64 "RDI" in
  let v = v64 "fpg_v" in
  (* Reads RBP (never defined in this sub) and passes the value out. *)
  let rsp = v64 "RSP" in
  let mm = memv "fpg_m" in
  let d_st =
    Def.create mm
      (Bil.Store
         ( Bil.Var mm,
           Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 16))),
           Bil.Int (Cbat_word.to_word (w64 1)),
           LittleEndian,
           `r64 ))
  in
  let d_v = Def.create v (Bil.Var rbp) in
  let d_arg = Def.create rdi (Bil.Var rbp) in
  let callee_tid = Tid.for_name "fpg_callee" in
  let caller_sub, _ =
    sub_of "fpg_read_rbp"
      [ [ d_st; d_v; d_arg ],
        [ (1, fun t -> Jmp.create (Call (Call.create ~return:(Direct t) ~target:(Direct callee_tid) ()))) ];
        [], [ (0, mk_ret) ] ]
  in
  let callee = fst (sub_of "fpg_callee" [ [], [ (0, mk_ret) ] ]) in
  let caller_sub =
    stamp [ (Term.tid d_st, Sm.Tag.Stack (pos (-16L), pos (-16L))) ] caller_sub in
  let ir_holder = ref "" in
  let err = capture_stderr (fun () -> ir_holder := emit_ir [ caller_sub; callee ]) in
  let ir = !ir_holder in
  check
    "FP-GPR: a never-defined RBP read warns through the undef-read lane \
     (the RBX treatment)"
    (contains_substring err "hike: undef-read:");
  (* The invented binding would be [fp := anchor - 8] — `sub i64
     %anchor_i64, 8` (SP takes [anchor_i64] itself; the call-restore is
     an [add]) — so the never-defined read would resolve to a
     frame-relative constant instead of the caller's RBP. Its absence is
     the positive half. *)
  check
    "FP-GPR: no invented [fp := anchor - 8] binding is emitted for RBP \
     (the emitter does not invent a register value)"
    (not (contains_substring ir "sub i64 %anchor_i64, 8"));
  ()

(* Family 8: stack-arg promotion emission.                             *)

(* A promoted callee (two proven slots) and a caller with one resolved
   indirect site and the outgoing stores the slots feed. *)
(* Family 9: the promotion as a BIR rewrite — the sub's structure *)
(* is the emitter's only input.                                         *)

(* Family 10: the phi edge multiplicity — one incoming per EDGE.       *)

(* Phi lines with exactly two incomings. A block whose cond and
   fallthrough gotos target the SAME successor contributes TWO edges;
   the target's phis take one incoming per edge (2), where a
   node-keyed predecessor list would render one. *)
let count_two_incoming_phis (ir : string) : int =
  String.split_on_char '\n' ir
  |> List.filter (fun l -> contains_substring l " = phi i64 ")
  |> List.filter (fun l ->
      match String.split_on_char '[' l with
      | _ :: rest -> List.length rest = 2
      | [] -> false)
  |> List.length

let run_phi_edge_multiplicity () =
  (* Shared shape: A defines x := RSP + 1 and branches on a flag; T
     reads x. E is the alternate fallthrough. *)
  let build ~(both_to_t : bool) () : string =
    let x = v64 "edge_mult_x" in
    let flag = v64 "edge_mult_flag" in
    (* The second (fallthrough) edge targets T when duplicated, E otherwise. *)
    let second_i = if both_to_t then 1 else 2 in
    let s, _ =
      sub_of "edge_mult"
        [ [ Def.create flag (Bil.Int (Cbat_word.to_word (w64 1)));
            Def.create x
              (Bil.BinOp (Bil.PLUS, Bil.Var (v64 "RSP"), Bil.Int (Cbat_word.to_word (w64 1)))) ],
          [ (1,
             fun t ->
               mk_jmp_to t (Bil.BinOp (Bil.EQ, Bil.Var flag, Bil.Int (Cbat_word.to_word (w64 0)))));
            (second_i, mk_goto) ];
          [ Def.create (v64 "edge_mult_use") (Bil.Var x) ], [];
          [], [] ]
    in
    emit_ir [ s ]
  in
  let duplicated = count_two_incoming_phis (build ~both_to_t:true ()) in
  let distinct = count_two_incoming_phis (build ~both_to_t:false ()) in
  check
    "PHI-EDGES: a duplicated edge yields one phi incoming per EDGE (two-incoming phis exist)"
    (duplicated >= 1);
  check
    "PHI-EDGES: the single-edge control has no two-incoming phis"
    (distinct = 0)

(* Family 11: the width-family read fallback (the read stays total     *)
(* across binding widths).                                             *)

let run_width_family_read () =
  (* A var bound at i64 read back under a same-name i32 var: the read
     truncates to the asked width (never a crash, never undef).  The
     binding is non-constant (an arg-lane add) so the coercion stays
     in the printed IR; the same-width control emits no i64 narrowing
     (the i256 param-lane coercions are not read coercions). *)
  let wfam = v64 "wfam_val" in
  let wfam32 = Var.create ~is_virtual:false ~fresh:false "wfam_val" (Type.Imm 32) in
  let out32 = Var.create ~is_virtual:false ~fresh:false "wfam_out" (Type.Imm 32) in
  let binding () : def term =
    Def.create wfam
      (Bil.BinOp (Bil.PLUS, Bil.Var (v64 "RDI"), Bil.Int (Cbat_word.to_word (w64 1))))
  in
  let build_mismatched () : string =
    let s, _ =
      sub_of "wfam_mismatch"
        [ [ binding (); Def.create out32 (Bil.Var wfam32) ], [ (0, mk_ret) ] ]
    in
    emit_ir [ s ]
  in
  let build_control () : string =
    let out64 = v64 "wfam_out" in
    let s, _ =
      sub_of "wfam_control"
        [ [ binding (); Def.create out64 (Bil.Var wfam) ], [ (0, mk_ret) ] ]
    in
    emit_ir [ s ]
  in
  let mismatched = build_mismatched () in
  let control = build_control () in
  check
    "WFAM: the i64 binding read at i32 truncates (the width-family fallback)"
    (contains_substring mismatched "trunc i64 ");
  check
    "WFAM: the same-width read control emits no i64 read coercion"
    (not (contains_substring control "trunc i64 "))

(* Family 6b: the anchor residue invariant, frame shape — the layout   *)
(* tag is set DIRECTLY so the pin exercises the emitter's anchor        *)
(* construction for arbitrary frame geometry, not just the producer's   *)
(* 16-aligned sizes.                                                    *)

let run_anchor_residue () =
  let rsp = v64 "RSP" in
  let m = memv "res_m" in
  let addr = Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 16))) in
  let d_st =
    Def.create m
      (Bil.Store
         ( Bil.Var m, addr, Bil.Int (Cbat_word.to_word (w64 1)), LittleEndian,
           `r64 ))
  in
  let sub0, _ =
    sub_of "residue_sub"
      [ [ d_st ], [ (1, mk_goto) ];
        [], [ (0, mk_ret) ] ]
  in
  let sub = stamp [ (Term.tid d_st, Sm.Tag.Stack (pos (-16L), pos (-16L))) ] sub0 in
  (* The anchor is the fold's (region id, index): the residue alloca
     is 33 bytes (the array count is exact, no pad) and the anchor GEP
     sits at the SysV residue — 33 rounded to the entry-SP residue
     8192 ≡ 8 (mod 16) would exceed, so the fold places 8192 only when
     the extent allows; this layout names 24 (≡ 8 mod 16). *)
  let sub =
    Cu.set_layout
      Cu.{ regions = [ (0, (pos (-24L), pos (-16L)), 33L) ];
           Cu.anchor = Some (0, 24L); Cu.window_param = false }
      sub
  in
  let ir = emit_ir [ sub ] in
  check_ir "ANCHOR-RESIDUE: the residue alloca keeps the fold's exact byte count"
    "%stack_r0 = alloca [33 x i8]" ir;
  check_ir "ANCHOR-RESIDUE: the anchor word is the GEP at the fold's index"
    "getelementptr i8, ptr %stack_r0, i64 24" ir;
  (* A second layout: the anchor index rides whatever the fold named —
     8192 (≡ 8 mod 16) for a full-depth residue. *)
  let sub =
    Cu.set_layout
      Cu.{ regions = [ (0, (pos (-24L), pos (-16L)), 8208L) ];
           Cu.anchor = Some (0, 8192L); Cu.window_param = false }
      sub
  in
  let ir = emit_ir [ sub ] in
  check_ir "ANCHOR-RESIDUE: the anchor follows the fold's index, any residue value"
    "getelementptr i8, ptr %stack_r0, i64 8192" ir

(* Family 12: the resolved-dispatch rows' emitter views — the phi
   incomings (per-target grouping) and the phi arity (per-edge
   multiplicity), folded from the producer's rows (the J2 shape: a
   stamped dispatch over real BIR). *)
let run_tls_anchor () =
  (* The TLS-relative access (the stack-protector canary shape): the
     address bases on the ABI's thread-pointer register and renders as
     the thread-local anchor's per-thread address — the thread_local
     global, the accessor intrinsic, the load; the binary's offset
     drops with the base.  The pin asserts the generic contract; the
     target's lowering is llc's own. *)
  let tp = Hike.Abi.x86_64_sysv.thread_pointer in
  let m = memv "tls_m" in
  let out = v64 "tls_out" in
  let addr =
    Bil.BinOp (Bil.PLUS, Bil.Var tp, Bil.Int (Cbat_word.to_word (w64 0x28)))
  in
  let ld = Def.create out (Bil.Load (Bil.Var m, addr, LittleEndian, `r64)) in
  (* The read feeds a guard so the rendered anchor chain is live. *)
  let sub, _ =
    sub_of "tls_anchor_sub"
      [ [ ld ],
        [ (1,
           fun t ->
             mk_jmp_to t
               (Bil.BinOp (Bil.EQ, Bil.Var out, Bil.Int (Cbat_word.to_word (w64 0))))) ];
        [], [ (0, mk_ret) ] ]
  in
  let ir = emit_ir [ sub ] in
  check "TLS: the anchor global is thread_local"
    (contains_substring ir "@hike_tls_anchor = thread_local global i64 0");
  check "TLS: the accessor intrinsic is declared"
    (contains_substring ir "ptr @llvm.threadlocal.address(ptr");
  check "TLS: the access reads the anchor's per-thread address"
    (contains_substring ir "call ptr @llvm.threadlocal.address(ptr @hike_tls_anchor)"
     && contains_substring ir "load i64, ptr %tls_anchor");
  check "TLS: the binary's offset drops with the base"
    (not (contains_substring ir "getelementptr")
    && not (contains_substring ir "add i64 40"))

let run_rows_views () =
  let module Bl = Hike.Bil2llvm in
  (* The completed dispatch's BIR: the guarded-goto series in the
     dispatching blocks — one conditional goto per distinct target
     (the rewrite's rule) — plus the plain term edge. *)
  let sub, tids =
    sub_of "rows_views"
      [ [],
        [ (2, fun t -> mk_jmp_to t (Bil.Var (v64 "rows_g1")));
          (3, fun t -> mk_jmp_to t (Bil.Var (v64 "rows_g2")));
          (4, mk_goto) ];
        [],
        [ (3, fun t -> mk_jmp_to t (Bil.Var (v64 "rows_g3"))) ];
        [], [ (0, mk_ret) ];
        [], [ (0, mk_ret); (5, mk_goto) ];
        [], [ (0, mk_ret) ];
        [], [] ]
  in
  let blk_a = tids.(0) and blk_b = tids.(1) in
  let t_fresh = tids.(2) and t_two = tids.(3) and t_dup = tids.(4) in
  let exit_tid = tids.(5) in
  let edge_count = Bl.edge_counts_of_sub sub in
  let count ptid t =
    match Core.Hashtbl.find edge_count ptid with
    | None -> 0
    | Some h -> ( match Core.Hashtbl.find h t with Some n -> n | None -> 0)
  in
  check "ROWS-COUNT: each guarded goto of the series counts one incoming"
    (count blk_a t_fresh = 1 && count blk_a t_two = 1
     && count blk_a t_dup = 1);
  check "ROWS-COUNT: distinct dispatch blocks count separately per block"
    (count blk_b t_two = 1);
  check "ROWS-COUNT: the term edge keeps its one incoming"
    (count t_two exit_tid = 1);
  check "ROWS-COUNT: an untraveled (block, target) pair carries no edge"
    (count blk_a exit_tid = 0)


(* The section-tiling algebra (Bil2llvm.build_sections): the pins read
   owner ids, spans, typed decisions, and the globals' names — the LLVM
   values are not asserted. *)
let tile_comp sid slo shi lo_w hi_w tw =
  { Sm.comp_id = sid; Sm.sec_lo = slo; Sm.sec_hi = shi;
    Sm.lo_w = lo_w; Sm.hi_w = hi_w; Sm.typed_w = tw }

let tile_bytes ty lo hi ~words ~const img =
  Hike.Bil2llvm.Sec_bytes
    { si_type = ty; si_lo = lo; si_hi = hi;
      si_words = words; si_const = const; si_image = img }

let tile_bss lo hi ~words relocs =
  Hike.Bil2llvm.Sec_bss
    { si_lo = lo; si_hi = hi; si_words = words; si_copy_relocs = relocs }

let tile_build specs comps =
  let ctx = Llvm.create_context () in
  let md = Llvm.create_module ctx "Tiling" in
  let built =
    Hike.Bil2llvm.build_sections ctx md
      { Hike.Bil2llvm.spec_comps = comps; Hike.Bil2llvm.spec_whole = [];
        Hike.Bil2llvm.spec_word = 8;
        Hike.Bil2llvm.spec_sections = specs }
  in
  (ctx, md, built)

let tile_dispose (ctx, md, _) =
  Llvm.dispose_module md;
  Llvm.dispose_context ctx

(* The owner's (id, lo, hi) triple. *)
let tile_own (id : int option) (lo : int64) (hi : int64)
    (o : Hike.Bil2llvm.sec_owner) =
  o.Hike.Bil2llvm.own_id = id && Int64.equal o.Hike.Bil2llvm.own_lo lo
  && Int64.equal o.Hike.Bil2llvm.own_hi hi

let tile_name (o : Hike.Bil2llvm.sec_owner) = Llvm.value_name o.Hike.Bil2llvm.base

let run_tiling () =
  (* The two-component span: comps at words [1..2] and [5..6] of 8 —
     the gaps around them are runs. *)
  let span_lo = 0x4000L and span_hi = 0x403FL in
  let comps =
    [ tile_comp 7 span_lo span_hi 1 2 8;
      tile_comp 3 span_lo span_hi 5 6 4 ]
  in
  let img = Array.init 64 (fun i -> i mod 251) in
  let ctx, md, built =
    tile_build [ Some (tile_bytes Hike.Bil2llvm.DATA span_lo span_hi ~words:8 ~const:false img) ] comps
  in
  check "TILE-OWNER: the components are owners in ascending word order, ids carried"
    (match built with
     | [ s ] ->
       (match s.Hike.Bil2llvm.owners with
        | [ o1; o2; o3; o4; o5 ] ->
          tile_own None 0x4000L 0x4007L o1
          && tile_own (Some 7) 0x4008L 0x4017L o2
          && tile_own None 0x4018L 0x4027L o3
          && tile_own (Some 3) 0x4028L 0x4037L o4
          && tile_own None 0x4038L 0x403FL o5
        | _ -> false)
     | _ -> false);
  (* T6: text is a section row — a TEXT spec entry builds beside the
     data sections (const, image-backed), the same tiling machinery. *)
  let tctx, tmd, tbuilt =
    tile_build
      [ Some (tile_bytes Hike.Bil2llvm.DATA 0x4000L 0x403FL ~words:8 ~const:false
                (Array.init 64 (fun i -> i mod 251)));
        Some (tile_bytes Hike.Bil2llvm.TEXT 0x1000L 0x100FL ~words:2 ~const:true
                (Array.init 16 (fun i -> i + 1))) ]
      []
  in
  check "T6-TEXT: the text row builds as a constant image-backed section"
    (match tbuilt with
     | [ _data; text ] ->
       Int64.equal (Word.to_int64_exn text.Hike.Bil2llvm.min_addr) 0x1000L
       && Int64.equal (Word.to_int64_exn text.Hike.Bil2llvm.max_addr) 0x100FL
       && text.Hike.Bil2llvm.owners = []
       && (match text.Hike.Bil2llvm.bytes with Some b -> Array.length b = 16 | None -> false)
     | _ -> false);
  tile_dispose (tctx, tmd, tbuilt);
  check "TILE-SPAN: the run spans are the byte-exact gap words"
    (match built with
     | [ s ] ->
       (match s.Hike.Bil2llvm.owners with
        | [ o1; _; o3; _; o5 ] ->
          Int64.equal o1.Hike.Bil2llvm.own_lo (Int64.add span_lo 0L)
          && Int64.equal o1.Hike.Bil2llvm.own_hi (Int64.add span_lo 7L)
          && Int64.equal o3.Hike.Bil2llvm.own_lo (Int64.add span_lo 24L)
          && Int64.equal o3.Hike.Bil2llvm.own_hi (Int64.add span_lo 39L)
          && Int64.equal o5.Hike.Bil2llvm.own_lo (Int64.add span_lo 56L)
          && Int64.equal o5.Hike.Bil2llvm.own_hi span_hi
        | _ -> false)
     | _ -> false);
  check "TILE-COVER: the owners cover every byte of the span exactly once"
    (match built with
     | [ s ] ->
       (match s.Hike.Bil2llvm.owners with
        | o :: rest ->
          let rec adj prev = function
            | [] -> Int64.equal prev span_hi
            | n :: tl ->
              Int64.equal n.Hike.Bil2llvm.own_lo (Int64.add prev 1L)
              && adj n.Hike.Bil2llvm.own_hi tl
          in
          Int64.equal o.Hike.Bil2llvm.own_lo span_lo && adj o.Hike.Bil2llvm.own_hi rest
        | [] -> false)
     | _ -> false);
  check "TILE-TYPE: a run carries the word type, a component its plan decision"
    (match built with
     | [ s ] ->
       (match s.Hike.Bil2llvm.owners with
        | [ o1; o2; o3; o4; o5 ] ->
          (Int.equal o1.Hike.Bil2llvm.typed_w 8)
          && (Int.equal o2.Hike.Bil2llvm.typed_w 8)
          && (Int.equal o3.Hike.Bil2llvm.typed_w 8)
          && (Int.equal o4.Hike.Bil2llvm.typed_w 4)
          && (Int.equal o5.Hike.Bil2llvm.typed_w 8)
        | _ -> false)
     | _ -> false);
  tile_dispose (ctx, md, built);
  (* The residue counter is module-wide AND consumes in the fixed
     tiling order (data before rodata): each section's comps leave one
     tail word, and the runs' names continue across the sections. *)
  let d_lo = 0x6000L and d_hi = 0x600FL and r_lo = 0x7000L and r_hi = 0x700FL in
  let comps_two =
    [ tile_comp 0 d_lo d_hi 0 0 8;
      tile_comp 1 r_lo r_hi 0 0 8 ]
  in
  let ctx, md, built_two =
    tile_build
      [ Some (tile_bytes Hike.Bil2llvm.DATA d_lo d_hi ~words:2 ~const:false (Array.init 16 (fun _ -> 0)));
        Some (tile_bytes Hike.Bil2llvm.RODATA r_lo r_hi ~words:2 ~const:true (Array.init 16 (fun _ -> 0))) ]
      comps_two
  in
  check "TILE-RESIDUE: the run counter is module-wide and consumes in the fixed tiling order"
    (match built_two with
     | [ d; r ] ->
       (match d.Hike.Bil2llvm.owners, r.Hike.Bil2llvm.owners with
        | [ do_; dr ], [ ro; rr ] ->
          tile_own (Some 0) d_lo (Int64.add d_lo 7L) do_
          && tile_own (Some 1) r_lo (Int64.add r_lo 7L) ro
          && (contains_substring (tile_name dr) "sec_res_2")
          && (contains_substring (tile_name rr) "sec_res_3")
          && (contains_substring (tile_name do_) "sec_comp_0")
          && (contains_substring (tile_name ro) "sec_comp_1")
        | _ -> false)
     | _ -> false);
  tile_dispose (ctx, md, built_two);
  (* The identity shapes: no components — the whole-section array
     (bytes kept) and the bss span (no image). *)
  let ctx, md, built_id =
    tile_build
      [ Some (tile_bytes Hike.Bil2llvm.DATA 0x8000L 0x801FL ~words:2 ~const:false (Array.init 16 (fun _ -> 1)));
        Some (tile_bss 0x9000L 0x901FL ~words:2 []) ]
      []
  in
  check "TILE-IDENTITY: a span with no components keeps owners = [] and its image"
    (match built_id with
     | [ s; _ ] -> s.Hike.Bil2llvm.owners = [] && s.Hike.Bil2llvm.bytes = Some (Array.init 16 (fun _ -> 1))
     | _ -> false);
  check "TILE-BSS: the bss identity keeps bytes = None and owners = []"
    (match built_id with
     | [ _; b ] -> b.Hike.Bil2llvm.owners = [] && b.Hike.Bil2llvm.bytes = None
     | _ -> false);
  tile_dispose (ctx, md, built_id);
  (* The output list follows the spec's section-list order; an absent
     section is skipped. *)
  let ctx, md, built_ord =
    tile_build
      [ Some (tile_bytes Hike.Bil2llvm.DATA 0x8000L 0x801FL ~words:2 ~const:false (Array.init 16 (fun _ -> 0)));
        None;
        Some (tile_bss 0x9000L 0x901FL ~words:2 []) ]
      []
  in
  check "TILE-ORDER: the output follows the spec's order, absent sections skipped"
    (match built_ord with
     | [ s; b ] ->
       Int64.equal (Word.to_int64_exn s.Hike.Bil2llvm.min_addr) 0x8000L
       && Int64.equal (Word.to_int64_exn b.Hike.Bil2llvm.min_addr) 0x9000L
       && Option.is_some s.Hike.Bil2llvm.bytes
       && Option.is_none b.Hike.Bil2llvm.bytes
     | _ -> false);
  tile_dispose (ctx, md, built_ord)


(* Family: the typed slot channel.  The callee's k-th slot parameter
   binds the caller's [call_arg k] def BY MINTED-VAR IDENTITY — the
   block's def order (the stores' order) never crosses the values. *)
let run_slot_channel () =
  let slot_arg i = Arg.create ~intent:In (Sm.arg_slot ~word:8 i) (Bil.Var (Sm.arg_slot ~word:8 i)) in
  let callee =
    fst
      (sub_of "@slotcallee"
         [ [ Def.create (v64 "slot_sum")
               (Bil.BinOp
                  (Bil.PLUS, Bil.Var (Sm.arg_slot ~word:8 0),
                   Bil.Var (Sm.arg_slot ~word:8 1))) ],
           [ (0, mk_ret) ] ])
  in
  (* The args ride the sub term in slot order, the promotion's own
     convention. *)
  let callee = Term.append arg_t callee (slot_arg 0) in
  let callee = Term.append arg_t callee (slot_arg 1) in
  (* The site's defs in REVERSE slot order: hike_arg1 lands before
     hike_arg0 (the stores fired 1-then-0). *)
  let arg_def i v =
    Def.create (Sm.call_arg ~word:8 i) (Bil.Int (Cbat_word.to_word (w64 v)))
  in
  let caller, _ =
    sub_of "slot_caller"
      [ [ arg_def 1 6; arg_def 0 5 ],
        [ (1, fun t ->
              Jmp.create
                (Call
                   (Call.create ~return:(Direct t)
                      ~target:(Direct (Term.tid callee))
                      ()))) ];
        [], [ (0, mk_ret) ] ]
  in
  let ir = emit_ir [ callee; caller ] in
  check "SLOT-CHANNEL: the call binds slot args by minted var, not def order"
    (contains_substring ir "(i64 5, i64 6)"
    && not (contains_substring ir "(i64 6, i64 5)"))

let run () =
  run_poison ();
  run_frozen_undef ();
  run_slot_channel ();
  run_sp_restore ();
  run_casts ();
  run_golden ();
  run_anchor_residue ();
  run_fp_gpr ();
  run_phi_edge_multiplicity ();
  run_width_family_read ();
  run_tls_anchor ();
  run_rows_views ();
  run_tiling ()
