(* Emitter FP lane: the native-FP intrinsic table, the fp_sig interface
   records, and the native render arms. *)

open Bap.Std
module Abi = Hike_abi
open Bil2llvm_env
open Bil2llvm_exp
open Bil2llvm_mem

type native_fp = FMUL | FADD | FSUB | FDIV | FREM | SFLOAT | SINT
               | FCONVERT of int | FORDER | FHLT | ISNAN

let fp_intrinsic_name = strip_at

(* The FP temps' identity carries their width: the lifter uses one name
   ([intrinsic:x0]) for a single- AND a double-precision operand, and
   BAP's var identity is type-blind, so the width must be in the name.
   [hike-fp] qualifies every occurrence. *)
let temp_name (n : string) (w : int) : string = Printf.sprintf "%s:%d" n w

(* One row per mapped intrinsic name, with the operand width it names.
   The unsized spellings ([_binary]) carry none: the lifter picks the
   width per instruction, and [hike-fp] rewrites the target to the sized
   spelling before any consumer reads it. *)
let native_fp_table : (string * native_fp * int option) list =
  [ ("intrinsic:fmul_rne_ieee754_binary_64", FMUL, Some 64);
    ("intrinsic:fmul_rne_ieee754_binary_32", FMUL, Some 32);
    ("intrinsic:fadd_rne_ieee754_binary_64", FADD, Some 64);
    ("intrinsic:fadd_rne_ieee754_binary_32", FADD, Some 32);
    ("intrinsic:fsub_rne_ieee754_binary_64", FSUB, Some 64);
    ("intrinsic:fsub_rne_ieee754_binary_32", FSUB, Some 32);
    ("intrinsic:fdiv_rne_ieee754_binary_64", FDIV, Some 64);
    ("intrinsic:fdiv_rne_ieee754_binary_32", FDIV, Some 32);
    ("intrinsic:frem_rne_ieee754_binary_64", FREM, Some 64);
    ("intrinsic:frem_rne_ieee754_binary_32", FREM, Some 32);
    ("intrinsic:forder_rne_ieee754_binary_64", FORDER, Some 64);
    ("intrinsic:forder_rne_ieee754_binary_32", FORDER, Some 32);
    ("intrinsic:forder_ieee754_binary_64", FORDER, Some 64);
    ("intrinsic:forder_ieee754_binary_32", FORDER, Some 32);
    ("intrinsic:is_nan_rne_ieee754_binary_64", ISNAN, Some 64);
    ("intrinsic:is_nan_rne_ieee754_binary_32", ISNAN, Some 32);
    ("intrinsic:is_nan_ieee754_binary_64", ISNAN, Some 64);
    ("intrinsic:is_nan_ieee754_binary_32", ISNAN, Some 32);
    ("intrinsic:cast_sfloat_rne_ieee754_binary_64", SFLOAT, Some 64);
    ("intrinsic:cast_sfloat_rne_ieee754_binary_32", SFLOAT, Some 32);
    ("intrinsic:cast_sint_rne_ieee754_binary_64", SINT, Some 64);
    ("intrinsic:cast_sint_rne_ieee754_binary_32", SINT, Some 32);
    (* Exact width conversions: the suffix is the result width. *)
    ("intrinsic:fconvert_rne_ieee754_binary_64", FCONVERT 64, Some 64);
    ("intrinsic:fconvert_rne_ieee754_binary_32", FCONVERT 32, Some 32);
    (* The untagged spellings the lifter emits: [hike-fp] rewrites them
       to one of the sized rows above. *)
    ("intrinsic:fmul_rne_ieee754_binary", FMUL, None);
    ("intrinsic:fadd_rne_ieee754_binary", FADD, None);
    ("intrinsic:fsub_rne_ieee754_binary", FSUB, None);
    ("intrinsic:fdiv_rne_ieee754_binary", FDIV, None);
    ("intrinsic:frem_rne_ieee754_binary", FREM, None);
    ("intrinsic:forder_rne_ieee754_binary", FORDER, None);
    ("intrinsic:is_nan_rne_ieee754_binary", ISNAN, None);
    ("intrinsic:is_nan_ieee754_binary", ISNAN, None);
    ("intrinsic:forder_ieee754_binary", FORDER, None);
    ("intrinsic:hlt", FHLT, None) ]

(* The table as a hash map, built once: call dispatch consults it
   per call site per sub. *)
let native_fp_map =
  let t = Core.String.Table.create () in
  Base.List.iter native_fp_table ~f:(fun (k, v, w) ->
      Core.Hashtbl.set t ~key:k ~data:(v, w));
  t

let row_of_name (name : string) : (native_fp * int option) option =
  Core.Hashtbl.find native_fp_map (fp_intrinsic_name name)

let native_fp_op (name : string) : native_fp option =
  Core.Option.map (row_of_name name) ~f:fst

(* The operand width the target names; [None] for an untagged spelling. *)
let fp_width_of_name (name : string) : int option =
  Core.Option.bind (row_of_name name) ~f:snd

(* The bare sized spelling of an untagged FP target, when the table
   knows it: the name [hike-fp] rewrites the target to. *)
let sized_name (name : string) (w : int) : string option =
  let sized = Printf.sprintf "%s_%d" (fp_intrinsic_name name) w in
  if Core.Hashtbl.mem native_fp_map sized then Some sized else None

(* The static model interface of each mapped op: the input temps the
   call block defines (fp_args) and the result temps consumers read
   (fp_rets); FCONVERT w reads x0 at the complementary width. *)
type fp_sig = { fp_args : Var.t list; fp_rets : Var.t list }

(* The complementary FP input width of a conversion (fpext widens,
   fptrunc narrows); the identity for the non-conversion ops. *)
let conv_in_w = function
  | FCONVERT res_w -> if res_w = 64 then 32 else 64
  | _ -> 64

let fp_sig_of (op : native_fp) ~(w : int) : fp_sig =
  let v n k =
    Var.create ~is_virtual:false ~fresh:false (temp_name n k) (Type.Imm k)
  in
  let x0 k = v "intrinsic:x0" k in
  let y0 k = v "intrinsic:y0" k in
  match op with
  | FMUL | FADD | FSUB | FDIV | FREM | FORDER ->
    { fp_args = [ x0 w; v "intrinsic:x1" w ]; fp_rets = [ y0 w ] }
  | SFLOAT | SINT | ISNAN ->
    { fp_args = [ x0 w ]; fp_rets = [ y0 w ] }
  | FCONVERT res_w ->
    { fp_args = [ x0 (conv_in_w op) ];
      fp_rets = [ y0 res_w ] }
  | FHLT -> { fp_args = []; fp_rets = [] }

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

let fp_intrinsic_sizes ~(word_bits : int) (args : Arg.t list)
    (rets : Arg.t list) : int * int =
  let arg_w (i : int) : int =
    Base.Option.value_map (Base.List.nth args i) ~default:word_bits
      ~f:(fun a ->
          match Var.typ (Arg.lhs a) with Type.Imm w -> w | _ -> word_bits)
  in
  let res_w =
    match rets with
    | r :: _ -> (
        match Var.typ (Arg.lhs r) with Type.Imm w -> w | _ -> word_bits)
    | [] -> word_bits
  in
  (arg_w 0, res_w)

let create_native_fp_call ctx scope llvm_builder blk_tid sub_tid _fr blk call op =
  match op with
  | FHLT ->
      (* Halt traps without binding results or emitting fallthrough. *)
      create_interrupt ctx llvm_builder
  | FMUL | FADD | FSUB | FDIV | FREM | SFLOAT | SINT | FCONVERT _ | FORDER
   | ISNAN ->
  let llvm_ctx = ctx.llvm_ctx in
  let fallthrough = Option.map label_tid (Call.return call) in
  let target = Call.target call |> label_tid in
  let args = get_args ctx target in
  let rets = get_rets ctx target in
  let word_bits = Hike_abi.word_bits ctx.abi in
  let in_w, res_w = fp_intrinsic_sizes ~word_bits args rets in
  let temp_defs = temp_defs_of_blk blk in
  let sig_ =
    fp_sig_of op
      ~w:
        (Base.Option.value (fp_width_of_name (Tid.name target))
           ~default:word_bits)
  in
  let arg_value (i : int) : Llvm.llvalue =
    (* The [intrinsic:xN] temp the block defined IS the operand; it
       routes through the memory dispatch, so a converted operand
       materializes in its own world. *)
    let av = Base.List.nth_exn sig_.fp_args i in
    match Core.Map.find temp_defs av with
    | Some d ->
        mem_access ctx scope llvm_builder blk_tid sub_tid (find_def_tag d) d
          (Def.rhs d)
    | None -> create_exp ctx scope llvm_builder blk_tid (Bil.Var av)
  in
  let w_of = int_width_or in_w in
  let result =
    match op with
    | FMUL | FADD | FSUB | FDIV | FREM ->
        let a = arg_value 0 in
        let b = arg_value 1 in
        let w = min (w_of a) (w_of b) in
        build_fp_binop ctx llvm_builder op a b ~w
    | SFLOAT ->
        (* [sitofp] converts at the operand's own LLVM type (the
           lifter's extract/cast chain built it). *)
        let x = arg_value 0 in
        let tgt_fp_ty, tgt_lane_ty = fp_ty_of llvm_ctx res_w in
        let d = Llvm.build_sitofp x tgt_fp_ty "" llvm_builder in
        Llvm.build_bitcast d tgt_lane_ty "" llvm_builder
    | SINT ->
        let x = arg_value 0 in
        let src_w = int_width_or in_w x in
        let src_fp_ty, _ = fp_ty_of llvm_ctx src_w in
        let _, res_lane_ty = fp_ty_of llvm_ctx res_w in
        let d = Llvm.build_bitcast x src_fp_ty "" llvm_builder in
        Llvm.build_fptosi d res_lane_ty "" llvm_builder
    | FCONVERT res_w ->
        let x = arg_value 0 in
        let in_w = conv_in_w op in
        let x =
          coerce_int_width llvm_ctx llvm_builder
            ~bits:(int_width_or in_w x) x in_w
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
        let p =
          Llvm.build_fcmp Llvm.Fcmp.Olt
            (bitcast_to_fp llvm_builder a src_fp_ty)
            (bitcast_to_fp llvm_builder b src_fp_ty)
            "" llvm_builder
        in
        Llvm.build_zext p (Llvm.i64_type llvm_ctx) "" llvm_builder
    | ISNAN ->
        let x = arg_value 0 in
        let w = int_width_or in_w x in
        let src_fp_ty, _ = fp_ty_of llvm_ctx w in
        let xf = bitcast_to_fp llvm_builder x src_fp_ty in
        let p =
          Llvm.build_fcmp Llvm.Fcmp.Uno xf xf "" llvm_builder
        in
        Llvm.build_zext p (Llvm.i64_type llvm_ctx) "" llvm_builder
    | FHLT -> assert false
  in
  (* Ret temps bind their stamped version at the call block: the SSA
     pass minted one per call, so every read downstream resolves. *)
  Base.List.iter sig_.fp_rets ~f:(fun ret ->
      let rw = match Var.typ ret with Type.Imm w -> w | _ -> word_bits in
      let r_lane =
        coerce_int_width llvm_ctx llvm_builder
          ~bits:(int_width_or word_bits result) result rw in
      let arg = Arg.create ret (Bil.Var ret) in
      bind_call_ret ctx scope blk_tid arg r_lane);
  finish_call scope llvm_builder fallthrough
