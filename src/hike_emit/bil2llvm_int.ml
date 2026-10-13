(* The integer operators: LLVM integers at their BIR widths.  The value
   lane ([Bil2llvm_value]) dispatches here for every Int operand. *)

open Bap.Std
open Bap.Std.Bil.Types

let int_ty v n = Llvm.integer_type (Llvm.type_context (Llvm.type_of v)) n
let width v = Llvm.integer_bitwidth (Llvm.type_of v)

(* Zero-extends or truncates to [bits]. *)
let to_width b ~bits v =
  let w = width v in
  if w = bits then v
  else if w > bits then Llvm.build_trunc v (int_ty v bits) "" b
  else Llvm.build_zext v (int_ty v bits) "" b

(* A shift's amount reads at the shifted value's width: LLVM requires
   the two operands to share the type, while the BIL's shift amount
   carries its own (the ISA's i8 encoding idiom). *)
let shift_amount b v1 v2 = to_width b ~bits:(width v1) v2

let binop b op v1 v2 =
  match op with
  | PLUS -> Llvm.build_add v1 v2 "" b
  | MINUS -> Llvm.build_sub v1 v2 "" b
  | TIMES -> Llvm.build_mul v1 v2 "" b
  | DIVIDE -> Llvm.build_udiv v1 v2 "" b
  | SDIVIDE -> Llvm.build_sdiv v1 v2 "" b
  | MOD -> Llvm.build_urem v1 v2 "" b
  | SMOD -> Llvm.build_srem v1 v2 "" b
  | AND -> Llvm.build_and v1 v2 "" b
  | OR -> Llvm.build_or v1 v2 "" b
  | XOR -> Llvm.build_xor v1 v2 "" b
  | LSHIFT -> Llvm.build_shl v1 (shift_amount b v1 v2) "" b
  | RSHIFT -> Llvm.build_lshr v1 (shift_amount b v1 v2) "" b
  | ARSHIFT -> Llvm.build_ashr v1 (shift_amount b v1 v2) "" b
  | EQ -> Llvm.build_icmp Llvm.Icmp.Eq v1 v2 "" b
  | NEQ -> Llvm.build_icmp Llvm.Icmp.Ne v1 v2 "" b
  | LT -> Llvm.build_icmp Llvm.Icmp.Ult v1 v2 "" b
  | SLT -> Llvm.build_icmp Llvm.Icmp.Slt v1 v2 "" b
  | LE -> Llvm.build_icmp Llvm.Icmp.Ule v1 v2 "" b
  | SLE -> Llvm.build_icmp Llvm.Icmp.Sle v1 v2 "" b

let unop b op v =
  match op with
  | NEG -> Llvm.build_neg v "" b
  | NOT -> Llvm.build_not v "" b

let cast b (cast, i) v =
  let w = width v in
  if i <= 0 then
    (* A zero-width cast names no bits; the value is zero. *)
    Llvm.const_int (int_ty v 1) 0
  else
    let target = int_ty v i in
    let coerce signed v =
      if i > w then
        (if signed then Llvm.build_sext else Llvm.build_zext) v target "" b
      else if i < w then Llvm.build_trunc v target "" b
      else v
    in
    match cast with
    | UNSIGNED | LOW -> coerce false v
    | SIGNED -> coerce true v
    | HIGH ->
        let shift = max 0 (w - i) in
        let shifted =
          if shift > 0 then
            Llvm.build_lshr v (Llvm.const_int (Llvm.type_of v) shift) "" b
          else v
        in
        coerce false shifted

let extract b (hi, lo) v =
  let w = width v in
  let size = hi - lo + 1 in
  if size <= 0 then
    (* An empty extract names no bits; the value is zero. *)
    Llvm.const_int (int_ty v 1) 0
  else if lo >= w then
    (* Out-of-range extracts yield zero. *)
    Llvm.const_int (int_ty v size) 0
  else
    let shifted =
      Llvm.build_lshr v (Llvm.const_int (Llvm.type_of v) lo) "" b
    in
    (* Wide extracts zero-extend. *)
    if size >= w then Llvm.build_zext shifted (int_ty v size) "" b
    else Llvm.build_trunc shifted (int_ty v size) "" b

let concat b v1 v2 =
  let w2 = width v2 in
  let ty = int_ty v1 (width v1 + w2) in
  let hi = Llvm.build_shl (Llvm.build_zext v1 ty "" b)
      (Llvm.const_int ty w2) "" b in
  Llvm.build_or hi (Llvm.build_zext v2 ty "" b) "" b

let select b cond x y = Llvm.build_select cond x y "" b

(* Immediates keep their native bits; only the section initializers
   remap words that name lifted addresses.  Widths to 64 bits take the
   direct integer path; wider words go through the text form. *)
let immediate llvm_ctx word =
  let w = Word.bitwidth word in
  let ty = Llvm.integer_type llvm_ctx w in
  if w <= 64 then Llvm.const_of_int64 ty (Word.to_int64_exn word) false
  else Llvm.const_int_of_string ty (Word.string_of_value word) 16

(* The integer's pointer: the one Int-to-Ptr conversion. *)
let to_ptr b v =
  Llvm.build_inttoptr v
    (Llvm.pointer_type (Llvm.type_context (Llvm.type_of v))) "" b
