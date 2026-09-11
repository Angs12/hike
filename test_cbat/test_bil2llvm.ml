(* Emitter tests: the first seam over bil2llvm (emit_program).
   Each fixture builds a BIR sub, emits it via emit_program with
   Theory.Target.unknown + ptrsize:64, and asserts on the textual IR
   (Llvm.print_module) — the same idiom check_allocas.sh uses. *)

open Printf
open Test_common
open Test_fixtures
open Bap.Std
open Bap_core_theory

module B2l = Hike.Bil2llvm
module Cu = Hike.Stack_model

(* T10: the emitter consumes NO record — the fixture stamps the
   producer's facts onto the terms (what the pipeline's vsa pass does:
   per-def kinds, the layout tag, and the promotion's BIR structure).
   [Kb.provide] stays a pipeline-pass concern and is not used here. *)
let stamp (info : Cu.vsa_info) (sub : sub term) : sub term =
  let sub = Cu.stamp_def_kinds info sub in
  let sub =
    Cu.set_layout
      (Cu.layout_of_sub sub ~abi:Hike.Abi.x86_64_sysv info)
      sub
  in
  Hike.Vsa.promote_sub info sub

(* The native op each table row must emit. *)
let fp_rows : (string * B2l.native_fp) list =
  [
    ("intrinsic:fmul_rne_ieee754_binary_64", FMUL);
    ("intrinsic:fmul_rne_ieee754_binary_32", FMUL);
    ("intrinsic:fadd_rne_ieee754_binary_64", FADD);
    ("intrinsic:fadd_rne_ieee754_binary_32", FADD);
    ("intrinsic:fsub_rne_ieee754_binary_64", FSUB);
    ("intrinsic:fsub_rne_ieee754_binary_32", FSUB);
    ("intrinsic:fdiv_rne_ieee754_binary_64", FDIV);
    ("intrinsic:fdiv_rne_ieee754_binary_32", FDIV);
    ("intrinsic:frem_rne_ieee754_binary_64", FREM);
    ("intrinsic:frem_rne_ieee754_binary_32", FREM);
    ("intrinsic:forder_rne_ieee754_binary_64", FORDER);
    ("intrinsic:forder_rne_ieee754_binary_32", FORDER);
    ("intrinsic:is_nan_rne_ieee754_binary_64", ISNAN);
    ("intrinsic:is_nan_rne_ieee754_binary_32", ISNAN);
    ("intrinsic:is_nan_ieee754_binary", ISNAN);
    ("intrinsic:is_nan_rne_ieee754_binary", ISNAN);
    ("intrinsic:forder_ieee754_binary", FORDER);
    ("intrinsic:forder_rne_ieee754_binary", FORDER);
    ("intrinsic:cast_sfloat_rne_ieee754_binary_64", SFLOAT);
    ("intrinsic:cast_sint_rne_ieee754_binary_64", SINT);
    ("intrinsic:fmul_rne_ieee754_binary", FMUL);
    ("intrinsic:fadd_rne_ieee754_binary", FADD);
    ("intrinsic:fsub_rne_ieee754_binary", FSUB);
    ("intrinsic:fdiv_rne_ieee754_binary", FDIV);
    ("intrinsic:frem_rne_ieee754_binary", FREM);
    ("intrinsic:hlt", FHLT);
  ]

(* The IR opcode each native_fp constructor emits. *)
let op_ir_string = function
  | B2l.FMUL -> "fmul"
  | B2l.FADD -> "fadd"
  | B2l.FSUB -> "fsub"
  | B2l.FDIV -> "fdiv"
  | B2l.FREM -> "frem"
  | B2l.SFLOAT -> "sitofp"
  | B2l.SINT -> "fptosi"
  | B2l.FORDER -> "fcmp olt"
  | B2l.FHLT -> "unreachable"
  | B2l.ISNAN -> "fcmp uno"

let string_of_natfp = function
  | B2l.FMUL -> "FMUL"
  | B2l.FADD -> "FADD"
  | B2l.FSUB -> "FSUB"
  | B2l.FDIV -> "FDIV"
  | B2l.FREM -> "FREM"
  | B2l.SFLOAT -> "SFLOAT"
  | B2l.SINT -> "SINT"
  | B2l.FORDER -> "FORDER"
  | B2l.FHLT -> "FHLT"
  | B2l.ISNAN -> "ISNAN"

let run_fp_table () =
  (* Every row maps to its constructor. *)
  List.iter
    (fun (name, op) ->
      check ("FP-TABLE " ^ name ^ ": native_fp_op gives " ^ string_of_natfp op)
        (match B2l.native_fp_op ("@" ^ name) with
         | Some op' -> op' = op
         | None -> false))
    fp_rows;
  (* Every row EMITS its native op — a dropped row degrades to a soft-float
     call without any warning difference, so emission is checked per row,
     not sampled. Unary rows take one x-def, binary rows two. *)
  let d0 = ivar64 "intrinsic:x0" in
  let d1 = ivar64 "intrinsic:x1" in
  (* Non-constant operand temps: a constant folds away in LLVM, and the
     emission check must see the REAL instruction. *)
  let x0_def = Def.create d0 (Bil.Var (v64 "fp_arg0")) in
  let x1_def = Def.create d1 (Bil.Var (v64 "fp_arg1")) in
  let unary (op : B2l.native_fp) : bool =
    match op with
    | B2l.SFLOAT | B2l.SINT | B2l.ISNAN | B2l.FHLT -> true
    | _ -> false
  in
  List.iter
    (fun (name, op) ->
      let arg_defs = if unary op then [ x0_def ] else [ x0_def; x1_def ] in
      let ir = emit_ir (mk_fp_program name arg_defs) in
      check ("FP-TABLE " ^ name ^ ": the native op is emitted")
        (contains_substring ir (op_ir_string op)))
    fp_rows;
  (* Rows NOT in the table must not map. *)
  check "FP-TABLE: unmapped name returns None"
    (match B2l.native_fp_op "@intrinsic:not_a_real_intrinsic" with
     | None -> true
     | Some _ -> false);
  (* fadd_64 also pins the no-soft-float-call half of the contract. *)
  let ir_fadd =
    emit_ir
      (mk_fp_program "intrinsic:fadd_rne_ieee754_binary_64" [ x0_def; x1_def ])
  in
  check "FP-TABLE fadd_64: no soft-float call survives"
    (not (contains_substring ir_fadd "call") || not (contains_substring ir_fadd "@intrinsic:fadd"));
  (* A dropped table row degrades loudly: a caller of an
     unmapped name gets the guarded warning. *)
  let x0b = ivar64 "intrinsic:x0" in
  let db = Def.create x0b (Bil.Int (Cbat_word.to_word (w64 7))) in
  let ir_un =
    capture_stderr (fun () ->
        ignore (emit_ir (mk_fp_program "intrinsic:not_a_real_intrinsic" [ db ])))
  in
  check "FP-TABLE: an unmapped name emits the guarded warning on stderr"
    (contains_substring ir_un "hike: guarded:")


let run_poison () =
  (* The warned-poison class, pinned: an Unbounded-tagged stack access warns
     through Hike_diag and still emits (create_exp); a Dead-tagged access
     emits a poison value. *)
  let rsp = v64 "RSP" in
  let m = memv "poison_m" in
  let t = v64 "poison_t" in
  let addr = Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 16))) in
  let ld = Def.create t (Bil.Load (Bil.Var m, addr, LittleEndian, `r64)) in
  (* The store consumes the LOAD result: the poison is textually live. *)
  let st =
    Def.create m (Bil.Store (Bil.Var m, addr, Bil.Var t, LittleEndian, `r64))
  in
  (* Unbounded on the load/store; Dead on the second pair. *)
  let unb_info : Cu.vsa_info =
    Cu.mk_vsa_info
      ~offsets:
        [ (Term.tid ld, Cu.Unbounded); (Term.tid st, Cu.Unbounded) ] ~regions:[] ~stack_plan:[] ~degraded:false ~vla_alloc_tids:Tid.Set.empty ()
  in
  let dead_info : Cu.vsa_info =
    Cu.mk_vsa_info
      ~offsets:[ (Term.tid ld, Cu.Dead) ] ~regions:[] ~stack_plan:[] ~degraded:false ~vla_alloc_tids:Tid.Set.empty ()
  in
  let unb_sub = mk_lds_sub "poison_unb" [ ld; st ] in
  let dead_sub = mk_lds_sub "poison_dead" [ ld; st ] in
  let unb_sub = stamp unb_info unb_sub in
  let dead_sub = stamp dead_info dead_sub in
  let ir_holder = ref "" in
  let err_unb =
    capture_stderr (fun () -> ir_holder := emit_ir [ unb_sub ])
  in
  check "POISON: the Unbounded access warns through the Hike_diag channel"
    (contains_substring err_unb "hike: guarded: sub");
  check "POISON: the Unbounded access still emits (create_exp, no crash)"
    (contains_substring !ir_holder "load");
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
  let bb = Blk.Builder.create () in
  let exit_blk = mk_exit_blk () in
  Blk.Builder.add_jmp bb
    (Jmp.create ~cond:(Bil.BinOp (Bil.EQ, Bil.Var rax, Bil.Int (Cbat_word.to_word (w64 0))))
       (Goto (Direct (Term.tid exit_blk))));
  Blk.Builder.add_jmp bb (Jmp.create (Goto (Direct (Term.tid exit_blk))));
  let sb = Sub.Builder.create ~name:"undef_read_sub" () in
  Sub.Builder.add_blk sb (Blk.Builder.result bb);
  Sub.Builder.add_blk sb exit_blk;
  let sub = Sub.Builder.result sb in
  let ir_holder3 = ref "" in
  let err_und =
    capture_stderr (fun () -> ir_holder3 := emit_ir [ sub ])
  in
  check "UNDEF: a never-defined register read warns through Hike_diag"
    (contains_substring err_und "hike: undef-read:");
  check "UNDEF: the never-defined read becomes undef"
    (contains_substring !ir_holder3 "undef")

(* Family 3: restore_sp_after_call idempotence (the L-E1e class).     *)
(* ------------------------------------------------------------------ *)

let run_sp_restore () =
  (* A direct call: after it, the sp local rebinds to post-push + 8. *)
  let rsp = v64 "RSP" in
  let m = memv "sp_m" in
  let callee_tid = Tid.for_name "sp_callee" in
  let caller = Blk.Builder.create () in
  let cont_blk = mk_exit_blk () in
  let cont_tid = Term.tid cont_blk in
  (* The push: RSP := RSP - 8; mem[RSP] := retaddr — the lifted call shape. *)
  Blk.Builder.add_def caller (Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 8)))));
  Blk.Builder.add_def caller
    (Def.create m (Bil.Store (Bil.Var m, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 1234)), LittleEndian, `r64)));
  Blk.Builder.add_jmp caller
    (Jmp.create
       (Call (Call.create ~return:(Direct cont_tid) ~target:(Direct callee_tid) ())));
  let sb = Sub.Builder.create ~name:"sp_caller" () in
  Sub.Builder.add_blk sb (Blk.Builder.result caller);
  Sub.Builder.add_blk sb cont_blk;
  let caller = Sub.Builder.result sb in
  let callee =
    let bb2 = Blk.Builder.create () in
    Blk.Builder.add_jmp bb2 (Jmp.create (Ret (Direct (Tid.create ()))));
    let sb2 = Sub.Builder.create ~name:"sp_callee" () in
    Sub.Builder.add_blk sb2 (Blk.Builder.result bb2);
    Sub.Builder.result sb2
  in
  let ir = emit_ir [ caller; callee ] in
  (* The restore rebinds sp to post-push + 8, by name. *)
  check "SP-RESTORE: the named sp_restored = add <pushed>, 8 is emitted"
    (contains_substring ir "%sp_restored = add i64 ");
  check "SP-RESTORE: the continuation's sp phi reads the restore (no net drift)"
    (contains_substring ir "[ %sp_restored,")

(* ------------------------------------------------------------------ *)
(* Family 4: cast preservation at BIL type boundaries.                 *)
(* ------------------------------------------------------------------ *)

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
  let bb = Blk.Builder.create () in
  Blk.Builder.add_def bb d_src;
  Blk.Builder.add_def bb d_st;
  let exit_blk = mk_exit_blk () in
  Blk.Builder.add_jmp bb
    (Jmp.create ~cond:(Bil.BinOp (Bil.EQ, Bil.Var src, Bil.Int (Cbat_word.to_word (w64 0x7B))))
       (Goto (Direct (Term.tid exit_blk))));
  let sb = Sub.Builder.create ~name:"cast_sub" () in
  Sub.Builder.add_blk sb (Blk.Builder.result bb);
  Sub.Builder.add_blk sb exit_blk;
  let sub = Sub.Builder.result sb in
  (* Singleton Range tag on the store: the converted-cell shape. *)
  let info : Cu.vsa_info =
    Cu.mk_vsa_info
      ~offsets:[ (Term.tid d_st, Cu.Range (-16L, -16L)) ] ~regions:[] ~stack_plan:[] ~degraded:false ~vla_alloc_tids:Tid.Set.empty ()
  in
  let sub = stamp info sub in
  let ir = emit_ir [ sub ] in
  check "CAST: the tagged store reaches memory with its narrowing cast intact"
    (contains_substring ir "store" && contains_substring ir "trunc")

(* ------------------------------------------------------------------ *)
(* Family 5: the substring-complete golden (singleton slot + one      *)
(* fission region).                                                   *)
(* ------------------------------------------------------------------ *)

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
  let exit_blk = mk_exit_blk () in
  let exit_tid = Term.tid exit_blk in
  let bb = Blk.Builder.create () in
  Blk.Builder.add_def bb d_ld;
  Blk.Builder.add_def bb d_st;
  Blk.Builder.add_def bb d_val;
  Blk.Builder.add_jmp bb
    (Jmp.create ~cond:(Bil.BinOp (Bil.EQ, Bil.Var st_val, Bil.Int (Cbat_word.to_word (w64 0))))
       (Goto (Direct exit_tid)));
  Blk.Builder.add_jmp bb (Jmp.create (Goto (Direct exit_tid)));
  let sb = Sub.Builder.create ~name:"golden_sub" () in
  Sub.Builder.add_blk sb (Blk.Builder.result bb);
  Sub.Builder.add_blk sb exit_blk;
  let sub = Sub.Builder.result sb in
  (* The vsa_info: singleton Range tags on both accesses + one
     convertible region, the write-closed fission shape. *)
  let info : Cu.vsa_info =
    let offsets =
      [
        (Term.tid d_ld, Cu.Range (-16L, -16L));
        (Term.tid d_st, Cu.Range (-24L, -24L));
      ]
    in
    let region =
      Cu.
        {
          id = 0;
          span = (-24L, -16L);
          members = [];
          convertible = true;
          max_width = 64;
        }
    in
    Cu.mk_vsa_info ~offsets
      ~regions:[ region ] ~stack_plan:[ region ]
      ~degraded:false ~vla_alloc_tids:Tid.Set.empty ()
  in
  let sub = stamp info sub in
  let ir = emit_ir [ sub ] in
  check_ir "GOLDEN: the golden sub emits a function define" "define" ir;
  check_ir "GOLDEN: the fission region alloca is built by name" "stack_r0" ir;
  check_ir "GOLDEN: the region base GEP lane is present" "getelementptr" ir;
  check_ir "GOLDEN: a load reaches the frame" "load" ir;
  check_ir "GOLDEN: a store reaches the frame" "store" ir;
  check_ir "GOLDEN: the jmp cond comparison emitted" "icmp" ir;
  check_ir "GOLDEN: a branch on the cond" "br " ir;
  check_ir "GOLDEN: a return is emitted" "ret" ir;
  check_ir "GOLDEN: i64 lanes (ptrsize 64)" "i64" ir

(* ------------------------------------------------------------------ *)
(* Family 6: the fp-GPR lane (ADR 0008) — the emitter never invents a   *)
(* register value.                                                      *)
(* ------------------------------------------------------------------ *)

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
  let cont_blk = mk_exit_blk () in
  let cont_tid = Term.tid cont_blk in
  let caller = Blk.Builder.create () in
  List.iter (Blk.Builder.add_def caller) [ d_st; d_v; d_arg ];
  Blk.Builder.add_jmp caller
    (Jmp.create (Call (Call.create ~return:(Direct cont_tid) ~target:(Direct callee_tid) ())));
  let sb = Sub.Builder.create ~name:"fpg_read_rbp" () in
  Sub.Builder.add_blk sb (Blk.Builder.result caller);
  Sub.Builder.add_blk sb cont_blk;
  let caller_sub = Sub.Builder.result sb in
  let callee =
    let bb2 = Blk.Builder.create () in
    Blk.Builder.add_jmp bb2 (Jmp.create (Ret (Direct (Tid.create ()))));
    let sb2 = Sub.Builder.create ~name:"fpg_callee" () in
    Sub.Builder.add_blk sb2 (Blk.Builder.result bb2);
    Sub.Builder.result sb2
  in
  let info : Cu.vsa_info =
    Cu.mk_vsa_info
      ~offsets:[ (Term.tid d_st, Cu.Range (-16L, -16L)) ] ~regions:[] ~stack_plan:[] ~degraded:false       ~vla_alloc_tids:Tid.Set.empty ()
  in
  let caller_sub = stamp info caller_sub in
  let ir_holder = ref "" in
  let err = capture_stderr (fun () -> ir_holder := emit_ir [ caller_sub; callee ]) in
  let ir = !ir_holder in
  check
    "FP-GPR (RED until T5): a never-defined RBP read warns through the undef-read lane \
     (the RBX treatment)"
    (contains_substring err "hike: undef-read:");
  (* The invented value is [fp := anchor - 8]: a [sub] off the frame anchor
     reaching a use of RBP. Its absence is the positive half. *)
  (* The invention is literal: [fp := anchor - 8] binds RBP at entry, so the
     never-defined read resolves to a frame-relative constant instead of the
     caller's RBP. [sub i64 %anchor_i64, 8] is that binding (SP takes
     [anchor_i64] itself and the call-restore is an [add]). *)
  check
    "FP-GPR (RED until T5): no invented [fp := anchor - 8] binding is emitted for RBP \
     (the emitter does not invent a register value)"
    (not (contains_substring ir "sub i64 %anchor_i64, 8"));
  ()

(* ------------------------------------------------------------------ *)
(* Family 7: the fp-GPR cast width (ADR 0008) — the sitofp's source      *)
(* width is the operand value's own type, never a register-name fact.    *)
(* ------------------------------------------------------------------ *)

let run_fp_gpr_cast () =
  (* A 32-bit store at [RBP + w] where RBP holds a NON-STACK value (no
     prologue), then a sitofp whose x0 loads from that slot. The spill-slot
     apparatus that once truncated such casts to i32 is DELETED (ADR 0008);
     the cast width now comes from the operand value's own LLVM type, so
     every base behaves identically. *)
  let off = 0x40 in
  let cast_ir (base_name : string) : string =
    let base = v64 base_name in
    let m = memv ("fgc_m_" ^ base_name) in
    let d_base = Def.create base (Bil.Int (Cbat_word.to_word (w64 0x400000))) in
    let addr = Bil.BinOp (Bil.PLUS, Bil.Var base, Bil.Int (Cbat_word.to_word (w64 off))) in
    let d_st = Def.create m (Bil.Store (Bil.Var m, addr, Bil.Int (Cbat_word.to_word (w64 7)), LittleEndian, `r32)) in
    (* x0 loads the slot; the cast source width is the load's own type. *)
    let d_x0 = Def.create (ivar64 "intrinsic:x0") (Bil.Load (Bil.Var m, addr, LittleEndian, `r64)) in
    let intr = "intrinsic:cast_sfloat_rne_ieee754_binary_64" in
    let prog = mk_fp_program intr [ d_base; d_st; d_x0 ] in
    (* No vsa_info: the store is untagged, and no tag is consulted anyway. *)
    emit_ir prog
  in
  let ir_rbp = cast_ir "RBP" in
  let ir_rbx = cast_ir "RBX" in
  (* Spill-slot detection is DELETED (ADR 0008, no gates): the cast's
     source width is the operand value's own LLVM type — the lifter's
     extract chain builds i32, a plain [:u64] load builds i64.  No
     register name, no tag test: every base behaves identically. *)
  check
    "FP-GPR: a [:u64] load feeds sitofp i64 regardless of the address base \
     (no spill-slot rule, no name test)"
    (contains_substring ir_rbp "sitofp i64"
    && contains_substring ir_rbx "sitofp i64"
    && not (contains_substring ir_rbp "sitofp i32")
    && not (contains_substring ir_rbx "sitofp i32"));
  (* The by-construction i32 case: the lifter's own extract chain. *)
  let ir_ext =
    let base = v64 "RAX" in
    let d_x0 =
      Def.create (ivar64 "intrinsic:x0")
        (Bil.Extract (31, 0, Bil.Var base))
    in
    let intr = "intrinsic:cast_sfloat_rne_ieee754_binary_64" in
    emit_ir (mk_fp_program intr [ d_x0 ])
  in
  check
    "FP-GPR: the lifter's own [31:0] extract feeds sitofp i32 (the width \
     is the value's type, by construction)"
    (contains_substring ir_ext "sitofp i32");
  ()

(* ------------------------------------------------------------------ *)


(* ------------------------------------------------------------------ *)
(* Family 8: stack-arg promotion emission (T4).                        *)
(* ------------------------------------------------------------------ *)

(* A promoted callee (two proven slots) and a caller with one resolved
   indirect site and the outgoing stores the slots feed. *)
let run_promotion () =
  let m = memv "prom_m" in
  let rsp = v64 "RSP" in
  let slot0 = ivar64 "hike_slot0" in
  let slot1 = ivar64 "hike_slot1" in
  (* The callee: reads its two promoted slots (the production Caller
     reads) and returns through the model ret lane. *)
  let callee_bb = Blk.Builder.create () in
  let exit_blk = mk_exit_blk () in
  let acc = v64 "prom_acc" in
  (* The callee also reads RDI/RSI (never defines them): the register
     lanes of the signature, the realistic promoted shape. *)
  let rdi = v64 "RDI" in
  let rsi = v64 "RSI" in
  let ld0 =
    Def.create (v64 "prom_ld0")
      (Bil.Load (Bil.Var m, Bil.Var slot0, LittleEndian, `r64))
  in
  Blk.Builder.add_def callee_bb ld0;
  Blk.Builder.add_def callee_bb
    (Def.create acc
       (Bil.BinOp (Bil.PLUS, Bil.Var rdi,
                   Bil.BinOp (Bil.PLUS, Bil.Var rsi,
                              Bil.BinOp (Bil.PLUS, Bil.Var slot0, Bil.Var slot1)))));
  Blk.Builder.add_jmp callee_bb (Goto (Direct (Term.tid exit_blk)) |> Jmp.create);
  let callee_b = Sub.Builder.create ~name:"prom_callee" () in
  Sub.Builder.add_blk callee_b (Blk.Builder.result callee_bb);
  Sub.Builder.add_blk callee_b exit_blk;
  let callee = Sub.Builder.result callee_b in
  (* The caller: pushes two outgoing stores, then an indirect call the
     VSA resolves (the volatile-singleton class). *)
  let caller_bb = Blk.Builder.create () in
  let cont_blk = mk_exit_blk () in
  let cont_tid = Term.tid cont_blk in
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
  let j =
    Jmp.create
      (Call
         (Call.create ~return:(Direct cont_tid)
            ~target:(Indirect (Bil.Var (v64 "prom_tptr"))) ()))
  in
  Blk.Builder.add_def caller_bb store1;
  Blk.Builder.add_def caller_bb store2;
  Blk.Builder.add_jmp caller_bb j;
  let caller_b = Sub.Builder.create ~name:"prom_caller" () in
  Sub.Builder.add_blk caller_b (Blk.Builder.result caller_bb);
  Sub.Builder.add_blk caller_b cont_blk;
  let caller = Sub.Builder.result caller_b in
  let callee_info : Cu.vsa_info =
    Cu.mk_vsa_info
      ~prom_slots:Tid.Map.empty ~prom_arity:2 ~prom_window:false
      ~offsets:[] ~regions:[] ~stack_plan:[] ~degraded:false
      ~vla_alloc_tids:Tid.Set.empty ()
  in
  let caller_info : Cu.vsa_info =
    Cu.mk_vsa_info
      ~prom_resolved:(Tid.Map.singleton (Term.tid j) (Some (Term.tid callee)))
      ~offsets:[] ~regions:[] ~stack_plan:[] ~degraded:false
      ~vla_alloc_tids:Tid.Set.empty ()
  in
  let callee = stamp callee_info callee in
  let caller = stamp caller_info caller in
  let ir = emit_ir [ caller; callee ] in
  (try
     let oc = open_out "/tmp/t10_prom_ir.txt" in
     output_string oc ir; close_out oc
   with _ -> ());
  (* The callee's promoted signature carries the register lanes then
     the positional slots. *)
  check_ir "T4-PROM: the promoted signature carries the positional slots"
    "(i64 %RDI, i64 %RSI, i64 %hike_slot0, i64 %hike_slot1)" ir;
  (* T10: the resolved site is a DIRECT call through the promoted
     signature (the producer rewrote the target); the unpassed slots
     stay undef.  The register lanes carry the caller's own signature
     values (the direct call freed the caller of its indirect-target
     var, so the PLT shape rule no longer fires - the lanes are real
     parameters, not undefs). *)
  check
    "T4-PROM: the resolved site calls the promoted body directly"
    (contains_substring ir
       (sprintf "call void @\"%s\"("
          (Hike.Bil2llvm.sanitize_name (Tid.name (Term.tid callee))))
     && contains_substring ir ", i64 undef, i64 undef)");
  (* The Thunk: internal linkage, the legacy memory-path signature. *)
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
  let j2 =
    Jmp.create
      (Call
         (Call.create ~return:(Direct cont_tid)
            ~target:(Indirect (Bil.Var (v64 "prom_tptr2"))) ()))
  in
  let caller2_bb = Blk.Builder.create () in
  Blk.Builder.add_jmp caller2_bb j2;
  let caller2_b = Sub.Builder.create ~name:"prom_caller2" () in
  Sub.Builder.add_blk caller2_b (Blk.Builder.result caller2_bb);
  Sub.Builder.add_blk caller2_b cont_blk;
  let caller2 = Sub.Builder.result caller2_b in
  let caller2_info : Cu.vsa_info =
    Cu.mk_vsa_info
      ~prom_resolved:(Tid.Map.singleton (Term.tid j2) None)
      ~offsets:[] ~regions:[] ~stack_plan:[] ~degraded:false
      ~vla_alloc_tids:Tid.Set.empty ()
  in
  let caller2 = stamp caller2_info caller2 in
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

(* ------------------------------------------------------------------ *)
(* Family 9: the promotion as a BIR rewrite (T10) — the sub's structure *)
(* carries what the record used to.                                     *)
(* ------------------------------------------------------------------ *)

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
  let exit_blk = mk_exit_blk () in
  let bb = Blk.Builder.create () in
  Blk.Builder.add_def bb d_ld;
  Blk.Builder.add_jmp bb (Jmp.create (Goto (Direct (Term.tid exit_blk))));
  let sb = Sub.Builder.create ~name:"t10_callee" () in
  Sub.Builder.add_blk sb (Blk.Builder.result bb);
  Sub.Builder.add_blk sb exit_blk;
  let sub = Sub.Builder.result sb in
  let info =
    Cu.mk_vsa_info
      ~prom_slots:(Tid.Map.singleton (Term.tid d_ld) 0)
      ~prom_arity:1
      ~offsets:[ (Term.tid d_ld, Cu.Caller (8L, 8L)) ]
      ~regions:[] ~stack_plan:[] ~degraded:false
      ~vla_alloc_tids:Tid.Set.empty ()
  in
  let sub' = Hike.Vsa.promote_sub info sub in
  check "T10-PROMOTE: the sub gains its promoted parameter as a real BIR arg"
    (Base.List.exists
       (Term.enum arg_t sub' |> Seq.to_list)
       ~f:(fun a -> Var.equal (Arg.lhs a) (Cu.arg_slot 0)));
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
  let d_ld' = Base.Option.value_exn (find_def sub' (Term.tid d_ld)) in
  check "T10-PROMOTE: the proven slot load reads its parameter"
    (match Def.rhs d_ld' with
     | Bil.Var v -> Var.equal v (Cu.arg_slot 0)
     | _ -> false);
  (* The stamped kind survives the rhs rewrite (the load-bearing stamp
     fact: Def.with_rhs keeps the def's value). *)
  let sub'' = Cu.stamp_def_kinds info sub' in
  let d_stamped = Base.Option.value_exn (find_def sub'' (Term.tid d_ld)) in
  check "T10-PROMOTE: the stamped kind survives the rhs rewrite"
    (match Cu.def_kind d_stamped with
     | Some (Cu.Caller (8L, 8L)) -> true
     | _ -> false);
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
  let cont_blk = mk_exit_blk () in
  let j =
    Jmp.create
      (Call
         (Call.create ~return:(Direct (Term.tid cont_blk))
            ~target:(Indirect (Bil.Var (ivar64 "t10_tptr")))
            ()))
  in
  let cbb = Blk.Builder.create () in
  Blk.Builder.add_def cbb store;
  Blk.Builder.add_jmp cbb j;
  let csb = Sub.Builder.create ~name:"t10_caller" () in
  Sub.Builder.add_blk csb (Blk.Builder.result cbb);
  Sub.Builder.add_blk csb cont_blk;
  let caller = Sub.Builder.result csb in
  let call_blk_tid = Term.tid (Base.List.hd_exn (Term.enum blk_t caller |> Seq.to_list)) in
  let caller_info =
    Cu.mk_vsa_info
      ~prom_sites:
        (Tid.Map.singleton call_blk_tid
           { Cu.site_slots = [ (0, Term.tid store) ] })
      ~prom_resolved:(Tid.Map.singleton (Term.tid j) (Some (Term.tid sub')))
      ~offsets:[] ~regions:[] ~stack_plan:[] ~degraded:false
      ~vla_alloc_tids:Tid.Set.empty ()
  in
  let caller' = Hike.Vsa.promote_sub caller_info caller in
  let cblk = Base.List.hd_exn (Term.enum blk_t caller' |> Seq.to_list) in
  let cdefs = Term.enum def_t cblk |> Seq.to_list in
  let pos dtid =
    Base.List.findi cdefs ~f:(fun _ d -> Tid.equal (Term.tid d) dtid)
  in
  (match (pos (Term.tid store), Base.List.findi cdefs ~f:(fun _ d -> Var.equal (Def.lhs d) (Cu.call_arg 0))) with
   | Some (i_store, _), Some (i_arg, arg_def) ->
       check "T10-SITE: the call-arg def is bound right after the storing def"
         (Int.equal i_arg (i_store + 1));
       check "T10-SITE: the call-arg def reads the storing def's own value"
         (match Def.rhs arg_def with
          | Bil.Var v -> Var.equal v (Def.lhs store)
          | _ -> false)
   | _ ->
       check "T10-SITE: the call-arg def is bound right after the storing def" false);
  (match Term.enum jmp_t cblk |> Seq.to_list with
   | [ j' ] -> (
       match Jmp.kind j' with
       | Call c -> (
           match Call.target c with
           | Direct t ->
               check "T10-SITE: the resolved indirect target became a direct call"
                 (Tid.equal t (Term.tid sub'))
           | Indirect _ ->
               check "T10-SITE: the resolved indirect target became a direct call" false)
       | _ ->
           check "T10-SITE: the resolved indirect target became a direct call" false)
   | _ ->
       check "T10-SITE: the resolved indirect target became a direct call" false)

let run () =
  run_fp_table ();
  run_poison ();
  run_sp_restore ();
  run_casts ();
  run_golden ();
  run_fp_gpr ();
  run_fp_gpr_cast ();
  run_promotion ();
  run_t10_rewrite ()
