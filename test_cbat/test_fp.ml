(* FP-lane tests (bil2llvm_fp): the native-FP table's mapping and
   emission, and the render arms' operand-width rules. *)

open Printf
open Test_common
open Test_fixtures
open Bap.Std
open Bap_core_theory

module B2l = Hike.Bil2llvm

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
    ("intrinsic:cast_sint_rne_ieee754_binary_32", SINT);
    ("intrinsic:fconvert_rne_ieee754_binary_64", FCONVERT 64);
    ("intrinsic:fconvert_rne_ieee754_binary_32", FCONVERT 32);
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
  | B2l.FCONVERT 64 -> "fpext"
  | B2l.FCONVERT _ -> "fptrunc"
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
  | B2l.FCONVERT 64 -> "FCONVERT 64"
  | B2l.FCONVERT _ -> "FCONVERT 32"
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
    | B2l.SFLOAT | B2l.SINT | B2l.FCONVERT _ | B2l.ISNAN | B2l.FHLT -> true
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


(* Family 7: the fp-GPR cast width (ADR 0008) — the sitofp's source      *)
(* width is the operand value's own type, never a register-name fact.    *)

let run_fp_gpr_cast () =
  (* A 32-bit store at [RBP + w] where RBP holds a NON-STACK value (no
     prologue), then a sitofp whose x0 loads from that slot. The cast
     width comes from the operand value's own LLVM type, so every base
     behaves identically. *)
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
  (* The cast's source width is the operand value's own LLVM type —
     the lifter's extract chain builds i32, a plain [:u64] load builds
     i64.  No register name, no tag test: every base behaves
     identically. *)
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


(* Family 8 (V-F): the native-op operand routes through the ONE memory
   dispatch — a converted operand temp (its load re-pointed at a region
   mem var) materializes against the region's alloca, never the raw
   model lane. *)
let run_fp_operand_routing () =
  let minus_addr sp (off : int64) : exp =
    Bil.BinOp
      ( Bil.MINUS, Bil.Var sp,
        Bil.Int (Cbat_word.to_word (w64 (Int64.to_int off))) )
  in
  let x0d = Def.create (ivar64 "intrinsic:x0") (Bil.Int (Cbat_word.to_word (w64 0))) in
  let x1d =
    Def.create (ivar64 "intrinsic:x1")
      (Bil.Load (Bil.Var (Sm.region_mem 1), minus_addr sp 16L, LittleEndian, `r64))
  in
  let layout : Sm.sub_layout =
    { regions =
        [ (0, (pos (-8200L), pos (-17L)), 8192L); (1, (pos (-16L), pos (-9L)), 16L) ];
      anchor = Some (0, 8L); window_param = false }
  in
  let stamp sub =
    Sm.stamp_dyn_allocs ~dynamic_alloc_tids:Tid.Set.empty sub
    |> Sm.set_layout layout
  in
  let ir =
    emit_ir
      (Base.List.map ~f:stamp
         (mk_fp_program "intrinsic:fadd_rne_ieee754_binary_64" [ x0d; x1d ]))
  in
  check "FP-OPERAND: a region-mem operand load GEPs its region's alloca (no raw model lane)"
    (contains_substring ir "getelementptr i8, ptr %stack_r1"
    && not (contains_substring ir "inttoptr"));
  ()


let run () =
  run_fp_table ();
  run_fp_gpr_cast ();
  run_fp_operand_routing ()
