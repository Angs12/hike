(* Emitter FP lane: the native render arms.  The op vocabulary, its
   sized spellings and the lane signatures live in [Hike_native_fp]
   (the lower core library); this module only lowers them to LLVM. *)

open Bap.Std
module Abi = Hike_abi
open Bil2llvm_env
open Bil2llvm_exp
open Bil2llvm_access

include Hike_native_fp

let fp_ty_of (llvm_ctx : Llvm.llcontext) (w : int) :
    Llvm.lltype * Llvm.lltype =
  ( (if w <= 32 then Llvm.float_type llvm_ctx
     else Llvm.double_type llvm_ctx),
    (if w <= 32 then Llvm.i32_type llvm_ctx else Llvm.i64_type llvm_ctx) )

(* An FP operand is an integer lane holding the value's bits. *)
let bitcast_to_fp llvm_builder v fp_ty =
  Llvm.build_bitcast v fp_ty "" llvm_builder



(* x86's float-to-integer conversion: [rne] rounds to nearest-even
   first, [rtz] truncates; an unordered or out-of-range source answers
   the integer indefinite (the most negative value), where LLVM's
   [fptosi] would be poison. *)
let build_fp_to_int ctx llvm_builder (rnd : rounding) (xf : Llvm.llvalue)
    ~(src_w : int) ~(res_w : int) : Llvm.llvalue =
  let llvm_ctx = ctx.llvm_ctx in
  let fp_ty, _ = fp_ty_of llvm_ctx src_w in
  let xf =
    match rnd with
    | Rtz -> xf
    | Rne ->
      let fty = Llvm.function_type fp_ty [| fp_ty |] in
      let name = if src_w <= 32 then "llvm.roundeven.f32" else "llvm.roundeven.f64" in
      let f = Llvm.declare_function name fty ctx.llvm_module in
      Llvm.build_call fty f [| xf |] "" llvm_builder
  in
  let int_ty = Llvm.integer_type llvm_ctx res_w in
  let bound = Float.ldexp 1.0 (res_w - 1) in
  let lo = Llvm.const_float fp_ty (-. bound) in
  let hi = Llvm.const_float fp_ty bound in
  let in_range =
    Llvm.build_and
      (Llvm.build_fcmp Llvm.Fcmp.Oge xf lo "" llvm_builder)
      (Llvm.build_fcmp Llvm.Fcmp.Olt xf hi "" llvm_builder)
      "" llvm_builder
  in
  let i = Llvm.build_fptosi xf int_ty "" llvm_builder in
  let indefinite =
    Llvm.const_of_int64 int_ty (Int64.shift_left 1L (res_w - 1)) true in
  Llvm.build_select in_range i indefinite "" llvm_builder

let build_fp_binop ctx llvm_builder op a b ~(w : int) =
  let fp_ty, ret_ty = fp_ty_of ctx.llvm_ctx w in
  let da = bitcast_to_fp llvm_builder a fp_ty in
  let db = bitcast_to_fp llvm_builder b fp_ty in
  let d =
    match op with
    | FMUL -> Llvm.build_fmul da db "" llvm_builder
    | FADD -> Llvm.build_fadd da db "" llvm_builder
    | FSUB -> Llvm.build_fsub da db "" llvm_builder
    | FDIV -> Llvm.build_fdiv da db "" llvm_builder
    | FREM -> Llvm.build_frem da db "" llvm_builder
    | _ -> assert false
  in
  Llvm.build_bitcast d ret_ty "" llvm_builder

(* Operand defs of a block indexed by base var, last def wins. *)
let temp_defs_of_blk (blk : blk term) : def term Var.Map.t =
  Term.enum def_t blk
  |> Seq.fold ~init:Var.Map.empty ~f:(fun m d ->
         Core.Map.set m ~key:(Var.base (Def.lhs d)) ~data:d)

let create_native_fp_call ctx scope llvm_builder blk_tid blk call op =
  match op with
  | FHLT ->
      (* Halt traps without binding results or emitting fallthrough. *)
      create_interrupt ctx llvm_builder
  | FMUL | FADD | FSUB | FDIV | FREM | SFLOAT _ | SINT _ | FCONVERT _ | FORDER
   | ISNAN | FSQRT ->
  let llvm_ctx = ctx.llvm_ctx in
  let fallthrough = Option.map label_tid (Call.return call) in
  let target = Call.target call |> label_tid in
  let word_bits = Hike_abi.word_bits ctx.abi in
  let temp_defs = temp_defs_of_blk blk in
  let sig_ =
    fp_sig_of op
      ~w:(lane_width_of_name ~word_bits (Tid.name target))
  in
  let arg_value (i : int) : Llvm.llvalue =
    (* The [intrinsic:xN] temp the block defined IS the operand; it
       routes through the memory dispatch, so a converted operand
       materializes in its own world. *)
    let av = Base.List.nth_exn sig_.fp_args i in
    as_int ctx llvm_builder
      (match Core.Map.find temp_defs av with
       | Some d ->
           mem_access ctx scope llvm_builder blk_tid (find_def_tag d) d
             (Def.rhs d)
       | None -> create_exp ctx scope llvm_builder blk_tid (Bil.Var av))
  in
  let w_of = Bil2llvm_int.width in
  let result =
    match op with
    | FMUL | FADD | FSUB | FDIV | FREM ->
        let a = arg_value 0 in
        let b = arg_value 1 in
        let w = min (w_of a) (w_of b) in
        build_fp_binop ctx llvm_builder op a b ~w
    | SFLOAT res_w ->
        (* [sitofp] converts at the operand's own LLVM type (the
           lifter's extract/cast chain built it). *)
        let x = arg_value 0 in
        let tgt_fp_ty, tgt_lane_ty = fp_ty_of llvm_ctx res_w in
        let d = Llvm.build_sitofp x tgt_fp_ty "" llvm_builder in
        Llvm.build_bitcast d tgt_lane_ty "" llvm_builder
    | SINT (rnd, res_w) ->
        let x = arg_value 0 in
        let src_w = Bil2llvm_int.width x in
        let src_fp_ty, _ = fp_ty_of llvm_ctx src_w in
        let d = Llvm.build_bitcast x src_fp_ty "" llvm_builder in
        build_fp_to_int ctx llvm_builder rnd d ~src_w ~res_w
    | FCONVERT res_w ->
        let x = arg_value 0 in
        let in_w = conv_in_w op in
        let x =
          coerce_int_width llvm_ctx llvm_builder
            ~bits:(Bil2llvm_int.width x) x in_w
        in
        let src_fp_ty, _ = fp_ty_of llvm_ctx in_w in
        let tgt_fp_ty, tgt_lane_ty = fp_ty_of llvm_ctx res_w in
        let xf = bitcast_to_fp llvm_builder x src_fp_ty in
        let d =
          if res_w > in_w
          then Llvm.build_fpext xf tgt_fp_ty "" llvm_builder
          else Llvm.build_fptrunc xf tgt_fp_ty "" llvm_builder
        in
        Llvm.build_bitcast d tgt_lane_ty "" llvm_builder
    | FORDER ->
        let a = arg_value 0 in
        let b = arg_value 1 in
        let w = min (w_of a) (w_of b) in
        let src_fp_ty, _ = fp_ty_of llvm_ctx w in
        Llvm.build_fcmp Llvm.Fcmp.Olt
          (bitcast_to_fp llvm_builder a src_fp_ty)
          (bitcast_to_fp llvm_builder b src_fp_ty)
          "" llvm_builder
    | ISNAN ->
        let x = arg_value 0 in
        let w = Bil2llvm_int.width x in
        let src_fp_ty, _ = fp_ty_of llvm_ctx w in
        let xf = bitcast_to_fp llvm_builder x src_fp_ty in
        Llvm.build_fcmp Llvm.Fcmp.Uno xf xf "" llvm_builder
    | FSQRT ->
        let x = arg_value 0 in
        let w = Bil2llvm_int.width x in
        let fp_ty, lane_ty = fp_ty_of llvm_ctx w in
        let fty = Llvm.function_type fp_ty [| fp_ty |] in
        let name = if w <= 32 then "llvm.sqrt.f32" else "llvm.sqrt.f64" in
        let f = Llvm.declare_function name fty ctx.llvm_module in
        let d =
          Llvm.build_call fty f [| bitcast_to_fp llvm_builder x fp_ty |] ""
            llvm_builder
        in
        Llvm.build_bitcast d lane_ty "" llvm_builder
    | FHLT -> assert false
  in
  (* Ret temps bind their stamped version at the call block: the SSA
     pass minted one per call, so every read downstream resolves. *)
  Base.List.iter sig_.fp_rets ~f:(fun ret ->
      let rw = match Var.typ ret with Type.Imm w -> w | _ -> word_bits in
      let r_lane =
        coerce_int_width llvm_ctx llvm_builder
          ~bits:(Bil2llvm_int.width result) result rw in
      let arg = Arg.create ret (Bil.Var ret) in
      bind_call_ret ctx scope blk_tid arg (Bil2llvm_value.Int r_lane));
  finish_call scope llvm_builder fallthrough
