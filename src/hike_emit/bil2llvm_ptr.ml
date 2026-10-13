(* The pointer operators: LLVM pointers into the module's storage.  The
   value lane ([Bil2llvm_value]) dispatches here for every Ptr operand. *)

open Bap.Std.Bil.Types

(* The byte GEP: [idx] is a byte offset at the address width.  Not
   inbounds — a model address may leave its storage. *)
let offset ~addr_bits b p idx =
  let ctx = Llvm.type_context (Llvm.type_of p) in
  Llvm.build_gep (Llvm.i8_type ctx) p
    [| Bil2llvm_int.to_width b ~bits:addr_bits idx |] "" b

(* A pointer comparison: [op] is one of the BIL comparisons. *)
let cmp b op p q =
  let pred =
    match op with
    | EQ -> Llvm.Icmp.Eq
    | NEQ -> Llvm.Icmp.Ne
    | LT -> Llvm.Icmp.Ult
    | LE -> Llvm.Icmp.Ule
    | SLT -> Llvm.Icmp.Slt
    | SLE -> Llvm.Icmp.Sle
    | _ -> invalid_arg "Bil2llvm_ptr.cmp: not a comparison"
  in
  Llvm.build_icmp pred p q "" b

(* The pointer with its address masked (an alignment): [llvm.ptrmask]
   keeps the pointer's provenance. *)
let mask ~addr_bits b p m =
  let ctx = Llvm.type_context (Llvm.type_of p) in
  let ity = Llvm.integer_type ctx addr_bits in
  let md = Llvm.global_parent (Llvm.block_parent (Llvm.insertion_block b)) in
  let name = Printf.sprintf "llvm.ptrmask.p0.i%d" addr_bits in
  let fty = Llvm.function_type (Llvm.type_of p) [| Llvm.type_of p; ity |] in
  let f = Llvm.declare_function name fty md in
  Llvm.build_call fty f [| p; Bil2llvm_int.to_width b ~bits:addr_bits m |] "" b

(* The distance between two pointers, in bytes. *)
let diff ~addr_bits b p q =
  let ctx = Llvm.type_context (Llvm.type_of p) in
  let ity = Llvm.integer_type ctx addr_bits in
  Llvm.build_sub (Llvm.build_ptrtoint p ity "" b) (Llvm.build_ptrtoint q ity "" b)
    "" b

let select b cond p q = Llvm.build_select cond p q "" b

(* The pointer's address bits: the one Ptr-to-Int conversion. *)
let to_int ~addr_bits b p =
  let ctx = Llvm.type_context (Llvm.type_of p) in
  Llvm.build_ptrtoint p (Llvm.integer_type ctx addr_bits) "" b
