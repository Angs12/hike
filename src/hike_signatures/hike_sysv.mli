(* The System V x86-64 calling convention for argument and return values
   (psABI, section 3.2.3): the type model, the classification of a value
   into eightbyte classes, and the placement of a call's arguments and
   return value.  It is target-independent data: registers are indices
   into the integer argument registers (%rdi, %rsi, %rdx, %rcx, %r8, %r9)
   and the vector argument registers (%xmm0..%xmm7); the caller maps them
   to the target's variables. *)

(* ---- types ---- *)

type real = Float16 | Float | Double | Long_double

type scalar =
  | Bool | Char | Short | Int | Long | Long_long | Pointer
  | Real of real
  | Float128
  | Decimal32 | Decimal64 | Decimal128
  | Int128
  | M64 | M128 | M256 | M512

type ctype =
  | Scalar of scalar
  | Complex of real
  | Aggregate of aggregate  (* a struct, union or array *)

(* [fields] are the members with their byte offsets from the aggregate's
   start (every member of a union sits at offset 0).  [trivial] is false
   for a C++ object that is non-trivial for the purpose of calls: it is
   passed and returned by invisible reference. *)
and aggregate = {
  size : int;
  align : int;
  fields : field list;
  trivial : bool;
}

and field = { offset : int; ty : ctype }

(* The written form of a type: a scalar is its constructor name (Bool,
   Char, Short, Int, Long, Long_long, Pointer, Float16, Float, Double,
   Long_double, Float128, Decimal32, Decimal64, Decimal128, Int128, M64,
   M128, M256, M512); a complex type is (Complex Float); an aggregate is
   (Aggregate ((size N) (align N) (fields (((offset N) (ty TYPE)) ...))
   (trivial false)?)).  [trivial] defaults to true. *)
val ctype_of_sexp : Sexplib0.Sexp.t -> ctype
val sexp_of_ctype : ctype -> Sexplib0.Sexp.t

(* An array of [count] elements as an aggregate. *)
val array : ctype -> count:int -> ctype

val size_of : ctype -> int
val align_of : ctype -> int

(* ---- classification ---- *)

type eightbyte = Integer | Sse | Sse_up | X87 | X87_up | No_class

type classification =
  | Memory
  | Invisible_reference  (* passed as a pointer to a caller-made copy *)
  | Complex_x87
  | Eightbytes of eightbyte list

val classify : ctype -> classification

(* ---- placement ---- *)

(* One register an argument eightbyte travels in: an integer register
   by index, or a vector register by index with the number of eightbytes
   it carries (an SSE eightbyte and the SSEUP eightbytes after it). *)
type register_part =
  | Integer_register of int
  | Vector_register of { index : int; eightbytes : int }

type location =
  | Registers of register_part list
  | Stack of { offset : int; size : int }
      (* bytes from the first stack argument; [size] is rounded up to
         whole eightbytes *)
  | Nowhere  (* no eightbytes (an empty aggregate) *)

type argument = {
  location : location;
  indirect : bool;  (* the location carries a pointer to the value *)
}

type return_part =
  | Integer_return of int  (* 0 = %rax, 1 = %rdx *)
  | Vector_return of { index : int; eightbytes : int }
  | X87_return  (* %st0 *)
  | X87_complex_return  (* %st0 real, %st1 imaginary *)

type return_location =
  | Void
  | Returned_in of return_part list
  | Returned_in_memory
      (* the caller passes the storage's address as a hidden first
         argument in the first integer register; it comes back in %rax *)

type call = {
  return : return_location;
  arguments : argument list;
  vector_registers_used : int;
      (* the upper bound a variadic call passes in %al, 0..8 *)
  integer_registers_used : int;  (* the hidden return pointer included *)
  stack_size : int;  (* bytes of stack arguments *)
}

val place_return : ctype option -> return_location

(* The arguments in declaration order, after the return value's hidden
   pointer. *)
val place_call : return:ctype option -> ctype list -> call
