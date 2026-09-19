(* Emitter FP lane: the native-FP intrinsic table, the fp_sig interface
   records, and the native render arms. *)

open Bap.Std
module Abi = Hike_abi
module KB = Bap_knowledge.Knowledge
open Bil2llvm_env
open Bil2llvm_exp
open Bil2llvm_mem

(* Maps soft-float calls to native FP ops. *)
type native_fp = FMUL | FADD | FSUB | FDIV | FREM | SFLOAT | SINT
               | FCONVERT of int | FORDER | FHLT | ISNAN

let fp_intrinsic_name = strip_at

(* The mapped intrinsic names and their ops, one row per name (the
   width-suffixed forms, then the unsuffixed ones). *)
let native_fp_table : (string * native_fp) list =
  [ ("intrinsic:fmul_rne_ieee754_binary_64", FMUL);
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
    (* NaN predicate via fcmp uno. *)
    ("intrinsic:is_nan_rne_ieee754_binary_64", ISNAN);
    ("intrinsic:is_nan_rne_ieee754_binary_32", ISNAN);
    ("intrinsic:is_nan_ieee754_binary", ISNAN);
    ("intrinsic:is_nan_rne_ieee754_binary", ISNAN);
    (* Unsuffixed compare names. *)
    ("intrinsic:forder_ieee754_binary", FORDER);
    ("intrinsic:forder_rne_ieee754_binary", FORDER);
    ("intrinsic:cast_sfloat_rne_ieee754_binary_64", SFLOAT);
    ("intrinsic:cast_sint_rne_ieee754_binary_64", SINT);
    ("intrinsic:cast_sint_rne_ieee754_binary_32", SINT);
    (* Exact width conversions: the suffix is the result width. *)
    ("intrinsic:fconvert_rne_ieee754_binary_64", FCONVERT 64);
    ("intrinsic:fconvert_rne_ieee754_binary_32", FCONVERT 32);
    (* Unsuffixed arithmetic names. *)
    ("intrinsic:fmul_rne_ieee754_binary", FMUL);
    ("intrinsic:fadd_rne_ieee754_binary", FADD);
    ("intrinsic:fsub_rne_ieee754_binary", FSUB);
    ("intrinsic:fdiv_rne_ieee754_binary", FDIV);
    ("intrinsic:frem_rne_ieee754_binary", FREM);
    (* Halt uses the trap model. *)
    ("intrinsic:hlt", FHLT) ]

let native_fp_op (name : string) : native_fp option =
  Base.List.Assoc.find native_fp_table (fp_intrinsic_name name)
    ~equal:String.equal

(* The STATIC model interface of each mapped op: the input temps the call
   block must define, in order.  The name IS the interface fact — operand
   resolution reads these temps directly, never a signature-table fallback
   and never a register lane. *)
(* The mapped intrinsic's interface, declared: the convention temps
   the block defines (args) and the result temps the consumer reads
   (rets).  Widths derive from the op — FCONVERT w reads x0 at the
   complementary width and yields y0 at w. *)
type fp_sig = { fp_args : Var.t list; fp_rets : Var.t list }

let fp_sig_of (op : native_fp) : fp_sig =
  let v n w = Var.create ~is_virtual:false ~fresh:false n (Type.Imm w) in
  let x0 w = v "intrinsic:x0" w in
  let y0 w = v "intrinsic:y0" w in
  match op with
  | FMUL | FADD | FSUB | FDIV | FREM | FORDER ->
    { fp_args = [ x0 64; v "intrinsic:x1" 64 ]; fp_rets = [ y0 64 ] }
  | SFLOAT | SINT | ISNAN ->
    { fp_args = [ x0 64 ]; fp_rets = [ y0 64 ] }
  | FCONVERT res_w ->
    { fp_args = [ x0 (if res_w = 64 then 32 else 64) ];
      fp_rets = [ y0 res_w ] }
  | FHLT -> { fp_args = []; fp_rets = [] }

(* Returns width-derived FP/int types. *)
let fp_ty_of (llvm_ctx : Llvm.llcontext) (w : int) :
    Llvm.lltype * Llvm.lltype =
  ( (if w <= 32 then Llvm.float_type llvm_ctx
     else Llvm.double_type llvm_ctx),
    (if w <= 32 then Llvm.i32_type llvm_ctx else Llvm.i64_type llvm_ctx) )

(* Integer width of a value, defaulting to a declared width. *)
let int_width_or default_w v =
  match Llvm.classify_type (Llvm.type_of v) with
  | Llvm.TypeKind.Integer -> Llvm.integer_bitwidth (Llvm.type_of v)
  | _ -> default_w

(* Bitcasts integer lanes to an FP type; other lanes pass through. *)
let bitcast_to_fp llvm_builder v fp_ty =
  if Llvm.classify_type (Llvm.type_of v) = Llvm.TypeKind.Integer then
    Llvm.build_bitcast v fp_ty "" llvm_builder
  else v

(* Builds a width-aware FP binop. *)
let build_fp_binop llvm_builder op a b ~(w : int) =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let fp_ty, ret_ty = fp_ty_of llvm_ctx w in
  let da = bitcast_to_fp llvm_builder a fp_ty in
  let db = bitcast_to_fp llvm_builder b fp_ty in
  let d =
    match op with
    | FMUL -> Llvm.build_fmul da db "" llvm_builder
    | FADD -> Llvm.build_fadd da db "" llvm_builder
    | FSUB -> Llvm.build_fsub da db "" llvm_builder
    | FDIV -> Llvm.build_fdiv da db "" llvm_builder
    | FREM -> Llvm.build_frem da db "" llvm_builder
    | SFLOAT | SINT | FCONVERT _ | FORDER | FHLT | ISNAN -> assert false
  in
  return
  @@ Llvm.build_bitcast d ret_ty "" llvm_builder

(* Operand defs of a block indexed by base var, last def wins. *)
let temp_defs_of_blk (blk : blk term) : def term Var.Map.t =
  Term.enum def_t blk
  |> Seq.fold ~init:Var.Map.empty ~f:(fun m d ->
         Core.Map.set m ~key:(Var.base (Def.lhs d)) ~data:d)

(* Derives intrinsic widths from types. *)
let fp_intrinsic_sizes ~(word_bits : int) (args : Arg.t list)
    (rets : Arg.t list) : int * int =
  let arg_w (i : int) : int =
    match Base.List.nth args i with
    | Some a -> (
        match Var.typ (Arg.lhs a) with Type.Imm w -> w | _ -> word_bits)
    | None -> word_bits
  in
  let res_w =
    match rets with
    | r :: _ -> (
        match Var.typ (Arg.lhs r) with Type.Imm w -> w | _ -> word_bits)
    | [] -> word_bits
  in
  (arg_w 0, res_w)

(* Emits native FP ops inline. *)
let create_native_fp_call llvm_builder blk_tid sub_tid fr blk call op =
  let open KB in
  match op with
  | FHLT ->
      (* Halt traps without binding results or emitting fallthrough. *)
      create_interrupt llvm_builder
  | FMUL | FADD | FSUB | FDIV | FREM | SFLOAT | SINT | FCONVERT _ | FORDER
   | ISNAN ->
      let* llvm_ctx = Context.get llvm_ctx_var in
      let* ctx = Context.get emit_ctx_var in
  let fallthrough = Option.map label_tid (Call.return call) in
  let target = Call.target call |> label_tid in
  let args = get_args ctx target in
  (* Widths come from declared types. *)
  let rets = get_rets ctx target in
  let word_bits = 8 * ctx.abi.Abi.word in
  let in_w, res_w = fp_intrinsic_sizes ~word_bits args rets in
  (* Operand defs indexed once per call. *)
  let temp_defs = temp_defs_of_blk blk in
  let sig_ = fp_sig_of op in
  let arg_value (i : int) : Llvm.llvalue KB.t =
    (* Resolves operands from the declared input temps: the [intrinsic:xN]
       temp the block defined IS the operand — a signature-table miss can
       never substitute a register lane for it.  The temp routes through
       the ONE memory dispatch, so a converted operand (its def's load
       re-pointed at a region/window mem var) materializes in its own
       world, never the raw model lane. *)
    let av = Base.List.nth_exn sig_.fp_args i in
    match Core.Map.find temp_defs av with
    | Some d ->
        mem_access llvm_builder blk_tid sub_tid fr (find_def_tag d) d
          (Def.rhs d)
    | None -> create_exp llvm_builder blk_tid (Bil.Var av)
  in
  (* Integer width of a value, defaulting to the declared input width. *)
  let w_of = int_width_or in_w in
  let result =
    match op with
    | FMUL | FADD | FSUB | FDIV | FREM ->
        (* Operand width comes from values. *)
        let* a = arg_value 0 in
        let* b = arg_value 1 in
        let w = min (w_of a) (w_of b) in
        build_fp_binop llvm_builder op a b ~w
    | SFLOAT ->
        (* Int-to-FP casts: [sitofp] converts at the operand's own LLVM
           type — the lifter's extract/cast chain built it (an
           [x0 := 31:0[RAX]] read is i32; a [:u64] load is i64). *)
        let* x = arg_value 0 in
        (* Converts use result width. *)
        let tgt_fp_ty, tgt_lane_ty = fp_ty_of llvm_ctx res_w in
        let* d =
          KB.return
          @@ Llvm.build_sitofp x tgt_fp_ty "" llvm_builder
        in
        return
        @@ Llvm.build_bitcast d tgt_lane_ty "" llvm_builder
    | SINT ->
        (* FP-to-int casts use operand width. *)
        let* x = arg_value 0 in
        let src_w = int_width_or in_w x in
        let src_fp_ty, _ = fp_ty_of llvm_ctx src_w in
        let _, res_lane_ty = fp_ty_of llvm_ctx res_w in
        let* d =
          KB.return
          @@ Llvm.build_bitcast x src_fp_ty "" llvm_builder
        in
        let* r =
          KB.return
          @@ Llvm.build_fptosi d res_lane_ty "" llvm_builder
        in
        return r
    | FCONVERT res_w ->
        (* Exact width conversions: the name's suffix is the result
           width and the input is the complementary FP width — fpext
           widens, fptrunc narrows with round-to-nearest. *)
        let* x = arg_value 0 in
        let in_w = if res_w = 64 then 32 else 64 in
        let x =
          coerce_int_width llvm_ctx llvm_builder
            ~bits:(int_width_or in_w x) x in_w
        in
        let src_fp_ty, _ = fp_ty_of llvm_ctx in_w in
        let tgt_fp_ty, tgt_lane_ty = fp_ty_of llvm_ctx res_w in
        let* xf =
          KB.return @@ bitcast_to_fp llvm_builder x src_fp_ty
        in
        let* d =
          if res_w > in_w
          then KB.return @@ Llvm.build_fpext xf tgt_fp_ty "" llvm_builder
          else KB.return @@ Llvm.build_fptrunc xf tgt_fp_ty "" llvm_builder
        in
        return
        @@ Llvm.build_bitcast d tgt_lane_ty "" llvm_builder
    | FORDER ->
        (* Ordered less-than via fcmp olt. *)
        let* a = arg_value 0 in
        let* b = arg_value 1 in
        let w = min (w_of a) (w_of b) in
        let src_fp_ty, _ = fp_ty_of llvm_ctx w in
        let* p =
          KB.return
          @@ Llvm.build_fcmp Llvm.Fcmp.Olt
               (bitcast_to_fp llvm_builder a src_fp_ty)
               (bitcast_to_fp llvm_builder b src_fp_ty)
               "" llvm_builder
        in
        return @@ Llvm.build_zext p (Llvm.i64_type llvm_ctx) "" llvm_builder
    | ISNAN ->
        (* NaN test via fcmp uno. *)
        let* x = arg_value 0 in
        let w = int_width_or in_w x in
        let src_fp_ty, _ = fp_ty_of llvm_ctx w in
        let xf = bitcast_to_fp llvm_builder x src_fp_ty in
        let* p =
          KB.return
          @@ Llvm.build_fcmp Llvm.Fcmp.Uno xf xf "" llvm_builder
        in
        return @@ Llvm.build_zext p (Llvm.i64_type llvm_ctx) "" llvm_builder
    | FHLT -> assert false
  in
  let* r = result in
  (* The declared ret temps bind in BOTH scopes: the call block's exit
     (the phi-threaded consumers) and the fallthrough block's entry
     (the direct reads — the YMM assembly defs the BIR places in the
     return block).  Each ret takes the result at its own declared
     width. *)
  Base.List.iter sig_.fp_rets ~f:(fun ret ->
      let rw = match Var.typ ret with Type.Imm w -> w | _ -> word_bits in
      let r_lane =
        coerce_int_width llvm_ctx llvm_builder
          ~bits:(int_width_or word_bits r) r rw in
      insert_local ctx blk_tid ret r_lane;
      Option.iter (fun t -> insert_local ctx t ret r_lane) fallthrough);
  finish_call llvm_builder ctx fallthrough
