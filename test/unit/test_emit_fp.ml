(* FP-lane pins (bil2llvm_fp): the native-FP table's mapping and emission,
   the fp-GPR cast width, and the FP-operand region routing.  One Alcotest
   group per pin; each pin builds its own fixture, so no state crosses pins. *)

open Bap.Std
open Bap_core_theory
open Bap.Std
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures
module Bil2llvm_fp = Hike.Bil2llvm.Fp

(* The IR opcode each native_fp constructor emits. *)
let op_ir_string = function
  | Bil2llvm_fp.FMUL -> "fmul"
  | Bil2llvm_fp.FADD -> "fadd"
  | Bil2llvm_fp.FSUB -> "fsub"
  | Bil2llvm_fp.FDIV -> "fdiv"
  | Bil2llvm_fp.FREM -> "frem"
  | Bil2llvm_fp.SFLOAT _ -> "sitofp"
  | Bil2llvm_fp.SINT _ -> "fptosi"
  | Bil2llvm_fp.FCONVERT 64 -> "fpext"
  | Bil2llvm_fp.FCONVERT _ -> "fptrunc"
  | Bil2llvm_fp.FORDER -> "fcmp olt"
  | Bil2llvm_fp.FHLT -> "unreachable"
  | Bil2llvm_fp.ISNAN -> "fcmp uno"
  | Bil2llvm_fp.FSQRT -> "llvm.sqrt"

let string_of_natfp = function
  | Bil2llvm_fp.FMUL -> "FMUL"
  | Bil2llvm_fp.FADD -> "FADD"
  | Bil2llvm_fp.FSUB -> "FSUB"
  | Bil2llvm_fp.FDIV -> "FDIV"
  | Bil2llvm_fp.FREM -> "FREM"
  | Bil2llvm_fp.SFLOAT w -> "SFLOAT " ^ string_of_int w
  | Bil2llvm_fp.SINT (Bil2llvm_fp.Rne, w) -> "SINT rne " ^ string_of_int w
  | Bil2llvm_fp.SINT (Bil2llvm_fp.Rtz, w) -> "SINT rtz " ^ string_of_int w
  | Bil2llvm_fp.FCONVERT 64 -> "FCONVERT 64"
  | Bil2llvm_fp.FCONVERT _ -> "FCONVERT 32"
  | Bil2llvm_fp.FORDER -> "FORDER"
  | Bil2llvm_fp.FHLT -> "FHLT"
  | Bil2llvm_fp.ISNAN -> "ISNAN"
  | Bil2llvm_fp.FSQRT -> "FSQRT"

(* Unary rows take one x-def, binary rows two. *)
let fp_unary = function
  | Bil2llvm_fp.SFLOAT _ | Bil2llvm_fp.SINT _ | Bil2llvm_fp.FCONVERT _ | Bil2llvm_fp.ISNAN | Bil2llvm_fp.FSQRT | Bil2llvm_fp.FHLT -> true
  | _ -> false

(* One table row: the intrinsic maps to its constructor AND its native op is
   emitted (a dropped row degrades to a soft-float call with no warning
   difference, so emission is checked per row, not sampled). *)
let fp_assert (name : string) (op : Bil2llvm_fp.native_fp) : unit =
  check_bound
    ("FP-TABLE " ^ name ^ ": native_fp_op gives " ^ string_of_natfp op)
    (Bil2llvm_fp.native_fp_op ("@" ^ name))
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
    (* FP-01: every native-FP table row.  The names are the lifter's
       families spelled out (not read back from the table), so a dropped
       row is a red — it would otherwise degrade to a correct soft-float
       call the semantic gate cannot see. *)
    pin "FP-01"
      "every native-FP intrinsic maps to its constructor and emits its native op"
      (fun () ->
        let widths = [ "_64"; "_32"; "" ] in
        let named stem rne w = "intrinsic:" ^ stem ^ rne ^ "_ieee754_binary" ^ w in
        let arith =
          Base.List.concat_map
            [ "fmul", Bil2llvm_fp.FMUL; "fadd", Bil2llvm_fp.FADD;
              "fsub", Bil2llvm_fp.FSUB; "fdiv", Bil2llvm_fp.FDIV;
              "frem", Bil2llvm_fp.FREM ]
            ~f:(fun (stem, op) ->
                Base.List.map widths ~f:(fun w -> named stem "_rne" w, op)) in
        let compare_ =
          Base.List.concat_map
            [ "forder", Bil2llvm_fp.FORDER; "is_nan", Bil2llvm_fp.ISNAN ]
            ~f:(fun (stem, op) ->
                Base.List.concat_map [ ""; "_rne" ] ~f:(fun rne ->
                    Base.List.map widths ~f:(fun w -> named stem rne w, op))) in
        let casts =
          Base.List.concat_map [ 64; 32 ] ~f:(fun w ->
              let sw = "_" ^ string_of_int w in
              [ named "cast_sfloat" "_rne" sw, Bil2llvm_fp.SFLOAT w;
                named "cast_sint" "_rne" sw, Bil2llvm_fp.SINT (Bil2llvm_fp.Rne, w);
                named "fconvert" "_rne" sw, Bil2llvm_fp.FCONVERT w ]) in
        Base.List.iter (arith @ compare_ @ casts @ [ "intrinsic:hlt", Bil2llvm_fp.FHLT ])
          ~f:(fun (name, op) -> fp_assert name op));

    (* FP-32: a caller of an unmapped name is a loud failure — the
       external-emission fallback is gone (the atomic lane's deletion),
       so no module ever carries a silent external intrinsic call. *)
    pin "FP-32" "an unmapped intrinsic name is a loud failure at emission"
      (fun () ->
        let x0b = ivar64 "intrinsic:x0" in
        let db = Def.create x0b (Bil.Int (Cbat_word.to_word (w64 7))) in
        let loud =
          try
            ignore (emit_ir (mk_fp_program "intrinsic:not_a_real_intrinsic" [ db ]));
            false
          with Failure msg ->
            contains_substring msg "unmapped intrinsic call"
        in
        check "FP-32: an unmapped name fails loudly"
          loud);

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
        let ir_rbp = cast_ir (Var.name frame_ptr) in
        let ir_rbx = cast_ir (Var.name (callee_saved 0)) in
        check
          "FP-GPR: a [:u64] load feeds sitofp i64 regardless of the address base \
           (no spill-slot rule, no name test)"
          (contains_substring ir_rbp "sitofp i64"
          && contains_substring ir_rbx "sitofp i64"
          && not (contains_substring ir_rbp "sitofp i32")
          && not (contains_substring ir_rbx "sitofp i32")));

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
            (Bil.Load (Bil.Var (Sm.region_mem ~addr_bits:64 1), minus_addr sp 16L, LittleEndian, `r64))
        in
        let residue_lo = -8200L
        and residue_hi = -17L
        and residue_bytes = 8192L
        and arg_lo = -16L
        and arg_hi = -9L
        and arg_bytes = 16L in
        let layout : Sm.sub_layout =
          {
            regions =
              [ { Sm.r_id = 0;
                  r_lo = pos residue_lo;
                  r_hi = pos residue_hi;
                  r_bytes = residue_bytes };
                { Sm.r_id = 1;
                  r_lo = pos arg_lo;
                  r_hi = pos arg_hi;
                  r_bytes = arg_bytes } ];
            window_param = false;
            runtime_residue = false;
          }
        in
        let stamp sub = Sm.set_layout layout sub in
        let ir =
          emit_ir
            (Base.List.map ~f:stamp
               (mk_fp_program "intrinsic:fadd_rne_ieee754_binary_64" [ x0d; x1d ]))
        in
        check
          "FP-OPERAND: a region-mem operand load uses a real pointer address (no raw model lane)"
          (contains_substring ir "getelementptr i8, ptr %stack_r0"
          && contains_substring ir "load i64"
          && not (contains_substring ir "inttoptr")));
  ]

let () = run "emit_fp" tests
