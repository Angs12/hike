(* FP-lane pins (bil2llvm_fp): the native-FP table's mapping and emission,
   the fp-GPR cast width, and the FP-operand region routing.  One Alcotest
   group per pin; each pin builds its own fixture, so no state crosses pins. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

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

(* Unary rows take one x-def, binary rows two. *)
let fp_unary = function
  | B2l.SFLOAT | B2l.SINT | B2l.FCONVERT _ | B2l.ISNAN | B2l.FHLT -> true
  | _ -> false

(* One table row: the intrinsic maps to its constructor AND its native op is
   emitted (a dropped row degrades to a soft-float call with no warning
   difference, so emission is checked per row, not sampled). *)
let fp_assert (name : string) (op : B2l.native_fp) : unit =
  check_bound
    ("FP-TABLE " ^ name ^ ": native_fp_op gives " ^ string_of_natfp op)
    (B2l.native_fp_op ("@" ^ name))
    (fun op' -> op' = op);
  (* Non-constant operand temps: a constant folds away in LLVM, and the
     emission check must see the REAL instruction. *)
  let x0_def = Def.create (ivar64 "intrinsic:x0") (Bil.Var (v64 "fp_arg0")) in
  let x1_def = Def.create (ivar64 "intrinsic:x1") (Bil.Var (v64 "fp_arg1")) in
  let arg_defs = if fp_unary op then [ x0_def ] else [ x0_def; x1_def ] in
  let ir = emit_ir (mk_fp_program name arg_defs) in
  check
    ("FP-TABLE " ^ name ^ ": the native op is emitted")
    (contains_substring ir (op_ir_string op))

let tests : unit Alcotest.test list =
  [
    (* FP-01..FP-29: one pin per native-FP table row, in table order. *)
    pin "FP-01" "fmul_64 maps to FMUL and emits fmul"
      (fun () -> fp_assert "intrinsic:fmul_rne_ieee754_binary_64" B2l.FMUL);
    pin "FP-02" "fmul_32 maps to FMUL and emits fmul"
      (fun () -> fp_assert "intrinsic:fmul_rne_ieee754_binary_32" B2l.FMUL);
    pin "FP-03" "fadd_64 maps to FADD and emits fadd"
      (fun () -> fp_assert "intrinsic:fadd_rne_ieee754_binary_64" B2l.FADD);
    pin "FP-04" "fadd_32 maps to FADD and emits fadd"
      (fun () -> fp_assert "intrinsic:fadd_rne_ieee754_binary_32" B2l.FADD);
    pin "FP-05" "fsub_64 maps to FSUB and emits fsub"
      (fun () -> fp_assert "intrinsic:fsub_rne_ieee754_binary_64" B2l.FSUB);
    pin "FP-06" "fsub_32 maps to FSUB and emits fsub"
      (fun () -> fp_assert "intrinsic:fsub_rne_ieee754_binary_32" B2l.FSUB);
    pin "FP-07" "fdiv_64 maps to FDIV and emits fdiv"
      (fun () -> fp_assert "intrinsic:fdiv_rne_ieee754_binary_64" B2l.FDIV);
    pin "FP-08" "fdiv_32 maps to FDIV and emits fdiv"
      (fun () -> fp_assert "intrinsic:fdiv_rne_ieee754_binary_32" B2l.FDIV);
    pin "FP-09" "frem_64 maps to FREM and emits frem"
      (fun () -> fp_assert "intrinsic:frem_rne_ieee754_binary_64" B2l.FREM);
    pin "FP-10" "frem_32 maps to FREM and emits frem"
      (fun () -> fp_assert "intrinsic:frem_rne_ieee754_binary_32" B2l.FREM);
    pin "FP-11" "forder_64 maps to FORDER and emits fcmp olt"
      (fun () -> fp_assert "intrinsic:forder_rne_ieee754_binary_64" B2l.FORDER);
    pin "FP-12" "forder_32 maps to FORDER and emits fcmp olt"
      (fun () -> fp_assert "intrinsic:forder_rne_ieee754_binary_32" B2l.FORDER);
    pin "FP-13" "is_nan_64 maps to ISNAN and emits fcmp uno"
      (fun () -> fp_assert "intrinsic:is_nan_rne_ieee754_binary_64" B2l.ISNAN);
    pin "FP-14" "is_nan_32 maps to ISNAN and emits fcmp uno"
      (fun () -> fp_assert "intrinsic:is_nan_rne_ieee754_binary_32" B2l.ISNAN);
    pin "FP-15" "is_nan (unwidth'd) maps to ISNAN and emits fcmp uno"
      (fun () -> fp_assert "intrinsic:is_nan_ieee754_binary" B2l.ISNAN);
    pin "FP-16" "is_nan_rne (unwidth'd) maps to ISNAN and emits fcmp uno"
      (fun () -> fp_assert "intrinsic:is_nan_rne_ieee754_binary" B2l.ISNAN);
    pin "FP-17" "forder (unwidth'd) maps to FORDER and emits fcmp olt"
      (fun () -> fp_assert "intrinsic:forder_ieee754_binary" B2l.FORDER);
    pin "FP-18" "forder_rne (unwidth'd) maps to FORDER and emits fcmp olt"
      (fun () -> fp_assert "intrinsic:forder_rne_ieee754_binary" B2l.FORDER);
    pin "FP-19" "cast_sfloat_64 maps to SFLOAT and emits sitofp"
      (fun () -> fp_assert "intrinsic:cast_sfloat_rne_ieee754_binary_64" B2l.SFLOAT);
    pin "FP-20" "cast_sint_64 maps to SINT and emits fptosi"
      (fun () -> fp_assert "intrinsic:cast_sint_rne_ieee754_binary_64" B2l.SINT);
    pin "FP-21" "cast_sint_32 maps to SINT and emits fptosi"
      (fun () -> fp_assert "intrinsic:cast_sint_rne_ieee754_binary_32" B2l.SINT);
    pin "FP-22" "fconvert_64 maps to FCONVERT 64 and emits fpext"
      (fun () -> fp_assert "intrinsic:fconvert_rne_ieee754_binary_64" (B2l.FCONVERT 64));
    pin "FP-23" "fconvert_32 maps to FCONVERT 32 and emits fptrunc"
      (fun () -> fp_assert "intrinsic:fconvert_rne_ieee754_binary_32" (B2l.FCONVERT 32));
    pin "FP-24" "fmul (unwidth'd) maps to FMUL and emits fmul"
      (fun () -> fp_assert "intrinsic:fmul_rne_ieee754_binary" B2l.FMUL);
    pin "FP-25" "fadd (unwidth'd) maps to FADD and emits fadd"
      (fun () -> fp_assert "intrinsic:fadd_rne_ieee754_binary" B2l.FADD);
    pin "FP-26" "fsub (unwidth'd) maps to FSUB and emits fsub"
      (fun () -> fp_assert "intrinsic:fsub_rne_ieee754_binary" B2l.FSUB);
    pin "FP-27" "fdiv (unwidth'd) maps to FDIV and emits fdiv"
      (fun () -> fp_assert "intrinsic:fdiv_rne_ieee754_binary" B2l.FDIV);
    pin "FP-28" "frem (unwidth'd) maps to FREM and emits frem"
      (fun () -> fp_assert "intrinsic:frem_rne_ieee754_binary" B2l.FREM);
    pin "FP-29" "hlt maps to FHLT and emits unreachable"
      (fun () -> fp_assert "intrinsic:hlt" B2l.FHLT);

    (* FP-30: rows NOT in the table must not map. *)
    pin "FP-30" "an unknown intrinsic name returns None"
      (fun () ->
        check "FP-TABLE: unmapped name returns None"
          (match B2l.native_fp_op "@intrinsic:not_a_real_intrinsic" with
           | None -> true
           | Some _ -> false));

    (* FP-31: fadd_64 also pins the no-soft-float-call half of the contract. *)
    pin "FP-31" "fadd_64's emission carries no soft-float call"
      (fun () ->
        let x0_def = Def.create (ivar64 "intrinsic:x0") (Bil.Var (v64 "fp_arg0")) in
        let x1_def = Def.create (ivar64 "intrinsic:x1") (Bil.Var (v64 "fp_arg1")) in
        let ir_fadd =
          emit_ir
            (mk_fp_program "intrinsic:fadd_rne_ieee754_binary_64" [ x0_def; x1_def ])
        in
        check "FP-TABLE fadd_64: no soft-float call survives"
          (not (contains_substring ir_fadd "call")
          || not (contains_substring ir_fadd "@intrinsic:fadd")));

    (* FP-32: a caller of an unmapped name gets the guarded warning. *)
    pin "FP-32" "an unmapped intrinsic name emits the guarded warning on stderr"
      (fun () ->
        let x0b = ivar64 "intrinsic:x0" in
        let db = Def.create x0b (Bil.Int (Cbat_word.to_word (w64 7))) in
        let ir_un =
          capture_stderr (fun () ->
              ignore (emit_ir (mk_fp_program "intrinsic:not_a_real_intrinsic" [ db ])))
        in
        check "FP-TABLE: an unmapped name emits the guarded warning on stderr"
          (contains_substring ir_un "hike: guarded:"));

    (* FP-33: the fp-GPR cast width is the operand value's own type, never a
       register-name fact. *)
    pin "FP-33" "a [:u64] load feeds sitofp i64 regardless of the address base"
      (fun () ->
        let off = 0x40 in
        let cast_ir (base_name : string) : string =
          let base = v64 base_name in
          let m = memv ("fgc_m_" ^ base_name) in
          let d_base = Def.create base (Bil.Int (Cbat_word.to_word (w64 0x400000))) in
          let addr =
            Bil.BinOp (Bil.PLUS, Bil.Var base, Bil.Int (Cbat_word.to_word (w64 off)))
          in
          let d_st =
            Def.create m
              (Bil.Store
                 ( Bil.Var m, addr, Bil.Int (Cbat_word.to_word (w64 7)),
                   LittleEndian, `r32 ))
          in
          let d_x0 =
            Def.create (ivar64 "intrinsic:x0")
              (Bil.Load (Bil.Var m, addr, LittleEndian, `r64))
          in
          let intr = "intrinsic:cast_sfloat_rne_ieee754_binary_64" in
          emit_ir (mk_fp_program intr [ d_base; d_st; d_x0 ])
        in
        let ir_rbp = cast_ir "RBP" in
        let ir_rbx = cast_ir "RBX" in
        check
          "FP-GPR: a [:u64] load feeds sitofp i64 regardless of the address base \
           (no spill-slot rule, no name test)"
          (contains_substring ir_rbp "sitofp i64"
          && contains_substring ir_rbx "sitofp i64"
          && not (contains_substring ir_rbp "sitofp i32")
          && not (contains_substring ir_rbx "sitofp i32")));

    (* FP-34: the by-construction i32 case — the lifter's own extract chain. *)
    pin "FP-34" "the lifter's own [31:0] extract feeds sitofp i32"
      (fun () ->
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
          (contains_substring ir_ext "sitofp i32"));

    (* FP-35: a converted operand temp (its load re-pointed at a region mem
       var) materializes against the region's alloca, never the raw model
       lane. *)
    pin "FP-35" "a region-mem operand load GEPs its region's alloca (no raw model lane)"
      (fun () ->
        let minus_addr sp (off : int64) : exp =
          Bil.BinOp
            ( Bil.MINUS, Bil.Var sp,
              Bil.Int (Cbat_word.to_word (w64 (Int64.to_int off))) )
        in
        let x0d =
          Def.create (ivar64 "intrinsic:x0")
            (Bil.Int (Cbat_word.to_word (w64 0)))
        in
        let x1d =
          Def.create (ivar64 "intrinsic:x1")
            (Bil.Load (Bil.Var (Sm.region_mem 1), minus_addr sp 16L, LittleEndian, `r64))
        in
        let layout : Sm.sub_layout =
          {
            regions =
              [ (0, (pos (-8200L), pos (-17L)), 8192L);
                (1, (pos (-16L), pos (-9L)), 16L) ];
            anchor = Some (0, 8L);
            window_param = false;
          }
        in
        let stamp sub =
          Ds.stamp_dyn_allocs ~dynamic_alloc_tids:Tid.Set.empty sub
          |> Sm.set_layout layout
        in
        let ir =
          emit_ir
            (Base.List.map ~f:stamp
               (mk_fp_program "intrinsic:fadd_rne_ieee754_binary_64" [ x0d; x1d ]))
        in
        check
          "FP-OPERAND: a region-mem operand load GEPs its region's alloca (no raw model lane)"
          (contains_substring ir "getelementptr i8, ptr %stack_r1"
          && not (contains_substring ir "inttoptr")));
  ]

let () = run "emit_fp" tests
