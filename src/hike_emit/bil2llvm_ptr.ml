(* The pointer operators: LLVM pointers into the module's storage.  The
   value lane ([Bil2llvm_value]) dispatches here for every Ptr operand. *)

open Bap.Std.Bil.Types

(* The byte GEP: [idx] is a byte offset at the address width.  Not
   inbounds — a model address may leave its storage. *)
let offset ~addr_bits b p idx =
  let ctx = Llvm.type_context (Llvm.type_of p) in
  Llvm.build_gep (Llvm.i8_type ctx) p
    [| Bil2llvm_int.to_width b ~bits:addr_bits idx |] "" b

(* The comparisons a pointer pair keeps; any other op materialises. *)
let cmp b op p q =
  match op with
  | EQ -> Some (Llvm.build_icmp Llvm.Icmp.Eq p q "" b)
  | NEQ -> Some (Llvm.build_icmp Llvm.Icmp.Ne p q "" b)
  | LT -> Some (Llvm.build_icmp Llvm.Icmp.Ult p q "" b)
  | LE -> Some (Llvm.build_icmp Llvm.Icmp.Ule p q "" b)
  | _ -> None

let null p = Llvm.const_null (Llvm.type_of p)

let select b cond p q = Llvm.build_select cond p q "" b

(* The pointer's address bits: the one Ptr-to-Int conversion. *)
let to_int ~addr_bits b p =
  let ctx = Llvm.type_context (Llvm.type_of p) in
  Llvm.build_ptrtoint p (Llvm.integer_type ctx addr_bits) "" b
