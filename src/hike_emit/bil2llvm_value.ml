(* An emitted value with the type the type pass gave it: an integer at
   its BIR width, or a pointer.  Every operator lifts over the
   constructors and dispatches to [Bil2llvm_int] or [Bil2llvm_ptr].
   The only conversions are [as_int] and [as_ptr]. *)

open Bap.Std.Bil.Types

type t = Int of Llvm.llvalue | Ptr of Llvm.llvalue

let ll = function Int v | Ptr v -> v

let as_int ~addr_bits b = function
  | Int v -> v
  | Ptr p -> Bil2llvm_ptr.to_int ~addr_bits b p

let as_ptr b = function
  | Ptr p -> p
  | Int v -> Bil2llvm_int.to_ptr b v

(* The value at a typed home: a def, phi, lane, or cell of that type. *)
let coerce ~addr_bits b ~ptr v =
  if ptr then Ptr (as_ptr b v) else Int (as_int ~addr_bits b v)

let lift1 ~addr_bits b op v = Int (Bil2llvm_int.unop b op (as_int ~addr_bits b v))

(* An operation with a pointer operand: an offset or a mask keeps the
   pointer, a comparison compares addresses, a pointer difference is an
   integer.  The arithmetic and bit operations with no address meaning
   compute on the address bits. *)
let lift2 ~addr_bits b op a c =
  let on_bits () =
    let bits v =
      Bil2llvm_int.to_width b ~bits:addr_bits (as_int ~addr_bits b v)
    in
    Int (Bil2llvm_int.binop b op (bits a) (bits c))
  in
  match op, a, c with
  | _, Int x, Int y -> Int (Bil2llvm_int.binop b op x y)
  | PLUS, Ptr p, Int i | PLUS, Int i, Ptr p ->
      Ptr (Bil2llvm_ptr.offset ~addr_bits b p i)
  | MINUS, Ptr p, Int i ->
      Ptr (Bil2llvm_ptr.offset ~addr_bits b p (Bil2llvm_int.unop b NEG i))
  | MINUS, Ptr p, Ptr q -> Int (Bil2llvm_ptr.diff ~addr_bits b p q)
  | AND, Ptr p, Int m | AND, Int m, Ptr p ->
      Ptr (Bil2llvm_ptr.mask ~addr_bits b p m)
  | (EQ | NEQ | LT | LE | SLT | SLE), _, _ ->
      Int (Bil2llvm_ptr.cmp b op (as_ptr b a) (as_ptr b c))
  | (PLUS | MINUS | AND | OR | XOR | TIMES | DIVIDE | SDIVIDE | MOD | SMOD
    | LSHIFT | RSHIFT | ARSHIFT), _, _ ->
      on_bits ()

let cast ~addr_bits b c i v =
  Int (Bil2llvm_int.cast b (c, i) (as_int ~addr_bits b v))

let extract ~addr_bits b hi lo v =
  Int (Bil2llvm_int.extract b (hi, lo) (as_int ~addr_bits b v))

let concat ~addr_bits b v1 v2 =
  Int (Bil2llvm_int.concat b (as_int ~addr_bits b v1) (as_int ~addr_bits b v2))

(* A select keeps its arms' type; a pointer/integer mix is a pointer
   (the join is int ⊑ ptr). *)
let select ~addr_bits b cond a c =
  let cond = as_int ~addr_bits b cond in
  match a, c with
  | Int x, Int y -> Int (Bil2llvm_int.select b cond x y)
  | _ -> Ptr (Bil2llvm_ptr.select b cond (as_ptr b a) (as_ptr b c))
