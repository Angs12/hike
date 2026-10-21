(* FP-lane pins (bil2llvm_fp): the native-FP table's mapping and emission,
   the fp-GPR cast width, and the FP-operand region routing. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures
module Bil2llvm_fp = Hike.Bil2llvm.Fp

let emits op instruction =
  let opcode = Llvm.instr_opcode instruction in
  let open Llvm.Opcode in
  match op with
  | Bil2llvm_fp.FMUL -> opcode = FMul
  | Bil2llvm_fp.FADD -> opcode = FAdd
  | Bil2llvm_fp.FSUB -> opcode = FSub
  | Bil2llvm_fp.FDIV -> opcode = FDiv
  | Bil2llvm_fp.FREM -> opcode = FRem
  | Bil2llvm_fp.SFLOAT _ -> opcode = SIToFP
  | Bil2llvm_fp.SINT _ -> opcode = FPToSI
  | Bil2llvm_fp.FCONVERT 64 -> opcode = FPExt
  | Bil2llvm_fp.FCONVERT _ -> opcode = FPTrunc
  | Bil2llvm_fp.FORDER -> opcode = FCmp && Llvm.fcmp_predicate instruction = Some Llvm.Fcmp.Olt
  | Bil2llvm_fp.ISNAN -> opcode = FCmp && Llvm.fcmp_predicate instruction = Some Llvm.Fcmp.Uno
  | Bil2llvm_fp.FHLT -> opcode = Unreachable
  | Bil2llvm_fp.FSQRT ->
      opcode = Call
      && Base.String.is_prefix
           (Llvm.value_name
              (Llvm.operand instruction (Llvm.num_operands instruction - 1)))
           ~prefix:"llvm.sqrt."

(* Each row uses real ABI inputs and reads the correctly sized result. *)
let fp_assert name op width =
  check_bound (name ^ " maps to its native operation")
    (Bil2llvm_fp.native_fp_op ("@" ^ name)) (fun actual -> actual = op);
  let lane w name = Var.create ~is_virtual:false ~fresh:false name (Type.Imm w) in
  let input i =
    let source = Bil.Var (int_param i) in
    Def.create (lane width ("intrinsic:x" ^ string_of_int i))
      (if width = 64 then source else Bil.Cast (Bil.LOW, width, source)) in
  let inputs = match op with
    | Bil2llvm_fp.FHLT -> []
    | Bil2llvm_fp.FMUL | Bil2llvm_fp.FADD | Bil2llvm_fp.FSUB
    | Bil2llvm_fp.FDIV | Bil2llvm_fp.FREM | Bil2llvm_fp.FORDER -> [ input 0; input 1 ]
    | _ -> [ input 0 ] in
  let result_width = match op with
    | Bil2llvm_fp.SFLOAT w | Bil2llvm_fp.SINT (_, w) | Bil2llvm_fp.FCONVERT w -> w
    | Bil2llvm_fp.ISNAN | Bil2llvm_fp.FORDER -> 1
    | _ -> width in
  let result = Bil.Var (lane result_width "intrinsic:y0") in
  let output = if op = Bil2llvm_fp.FHLT then [] else
      [ Def.create (int_ret 0)
          (if result_width = 64 then result else Bil.Cast (Bil.UNSIGNED, 64, result)) ] in
  let target = Tid.for_name name in
  let caller, _ = raw_sub_of "fp_row"
      [ inputs, [ (1, fun t -> Jmp.create (Call (Call.create
            ~return:(Direct t) ~target:(Direct target) ()))) ];
        output, [ (0, mk_ret) ] ] in
  with_emitted_module ~synth:Hike.Synth.empty empty_spec [ caller; mk_fp_stub name ]
    (fun llvm_module ->
      check (name ^ " emits its native operation")
        (List.exists (emits op) (llvm_instructions llvm_module)))

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
              "frem", Bil2llvm_fp.FREM; "fsqrt", Bil2llvm_fp.FSQRT ]
            ~f:(fun (stem, op) ->
                Base.List.map widths ~f:(fun w -> named stem "_rne" w, op, if w = "_32" then 32 else 64)) in
        let compare_ =
          Base.List.concat_map
            [ "forder", Bil2llvm_fp.FORDER; "is_nan", Bil2llvm_fp.ISNAN ]
            ~f:(fun (stem, op) ->
                Base.List.concat_map [ ""; "_rne" ] ~f:(fun rne ->
                    Base.List.map widths ~f:(fun w -> named stem rne w, op, if w = "_32" then 32 else 64))) in
        let casts =
          Base.List.concat_map [ 64; 32 ] ~f:(fun w ->
              let sw = "_" ^ string_of_int w in
              let conversions =
                [ named "cast_sfloat" "_rne" sw, Bil2llvm_fp.SFLOAT w;
                  named "cast_sint" "_rne" sw, Bil2llvm_fp.SINT (Bil2llvm_fp.Rne, w);
                  named "cast_sint" "_rtz" sw, Bil2llvm_fp.SINT (Bil2llvm_fp.Rtz, w) ] in
              (named "fconvert" "_rne" sw, Bil2llvm_fp.FCONVERT w, if w = 64 then 32 else 64)
              :: Base.List.concat_map conversions ~f:(fun (name, op) ->
                  [ name, op, 64; name ^ "_32", op, 32; name ^ "_64", op, 64 ])) in
        Base.List.iter (arith @ compare_ @ casts @ [ "intrinsic:hlt", Bil2llvm_fp.FHLT, 64 ])
          ~f:(fun (name, op, width) -> fp_assert name op width));

    (* FP-32: a caller of an unmapped name is a loud failure — the
       external-emission fallback is gone (the atomic lane's deletion),
       so no module ever carries a silent external intrinsic call. *)
    pin "FP-32" "an unmapped intrinsic name is a loud failure at emission"
      (fun () ->
        let x0b = ivar64 "intrinsic:x0" in
        let db = Def.create x0b (Bil.Int (Cbat_word.to_word (w64 7))) in
        let loud =
          try
            ignore (emit_ir ~synth:Hike.Synth.empty (mk_fp_program "intrinsic:not_a_real_intrinsic" [ db ]));
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
        let check_cast (base_name : string) =
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
          with_emitted_module ~synth:Hike.Synth.empty empty_spec
            (mk_fp_program intr [ d_base; d_st; d_x0 ]) (fun llvm_module ->
              match List.filter (fun i -> Llvm.instr_opcode i = Llvm.Opcode.SIToFP)
                      (llvm_instructions llvm_module) with
              | [ conversion ] ->
                Alcotest.(check string) "conversion operand type" "i64"
                  (Llvm.string_of_lltype (Llvm.type_of (Llvm.operand conversion 0)))
              | _ -> Alcotest.fail "expected one signed integer-to-float conversion")
        in
        List.iter check_cast [ Var.name frame_ptr; Var.name (callee_saved 0) ]);

    ( "region operand",
      [
        case "a native FP operand loads from its declared storage" (fun () ->
            let synth, base =
              Hike.Synth.mint_base ~addr_bits:64 (Hike.Synth.Stack 1)
                Hike.Synth.empty
            in
            let x0 =
              Def.create (ivar64 "intrinsic:x0")
                (Bil.Int (Cbat_word.to_word (w64 0)))
            in
            let x1 =
              Def.create (ivar64 "intrinsic:x1")
                (Bil.Load
                   ( Bil.Var (Sm.region_mem ~addr_bits:64 1),
                     Bil.(var base + int (Cbat_word.to_word (w64 4))),
                     LittleEndian,
                     `r64 ))
            in
            let layout : Sm.sub_layout =
              {
                regions =
                  [
                    {
                      Sm.r_id = 0;
                      r_lo = pos (-8200L);
                      r_hi = pos (-17L);
                      r_bytes = 8192L;
                    };
                    {
                      Sm.r_id = 1;
                      r_lo = pos (-16L);
                      r_hi = pos (-9L);
                      r_bytes = 16L;
                    };
                  ];
                window_param = false;
                runtime_residue = false;
              }
            in
            let program =
              mk_fp_program "intrinsic:fadd_rne_ieee754_binary_64" [ x0; x1 ]
              |> List.map (Sm.set_layout layout)
            in
            with_emitted_module ~synth empty_spec program (fun llvm_module ->
                let instructions = llvm_instructions llvm_module in
                check "no raw integer address cast"
                  (not
                     (List.exists
                        (fun i -> Llvm.instr_opcode i = Llvm.Opcode.IntToPtr)
                        instructions));
                let addition =
                  List.find
                    (fun i -> Llvm.instr_opcode i = Llvm.Opcode.FAdd)
                    instructions
                in
                let operand = Llvm.operand addition 1 in
                check "FP operand interprets the loaded bits"
                  (Llvm.classify_value operand
                  = Llvm.ValueKind.Instruction Llvm.Opcode.BitCast);
                let load = Llvm.operand operand 0 in
                check "FP operand comes from a load"
                  (Llvm.classify_value load
                 = Llvm.ValueKind.Instruction Llvm.Opcode.Load);
                Alcotest.(check string)
                  "operand load type" "i64"
                  (Llvm.string_of_lltype (Llvm.type_of load));
                let pointer = Llvm.operand load 0 in
                check "load addresses its region storage"
                  (match Llvm.classify_value pointer with
                  | Llvm.ValueKind.Instruction Llvm.Opcode.GetElementPtr ->
                      let storage = Llvm.operand pointer 0 in
                      Llvm.classify_value storage
                      = Llvm.ValueKind.Instruction Llvm.Opcode.Alloca
                      && Llvm.int64_of_const (Llvm.operand pointer 1) = Some 4L
                      && contains_substring
                           (Llvm.string_of_llvalue storage)
                           "alloca [16 x i8]"
                  | _ -> false)));
      ] );

  ]

let () = run "emit_fp" tests
