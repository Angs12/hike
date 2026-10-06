(** The synthetic-variable vocabulary: the one module that knows what a
    synthetic variable is.  The private kind never escapes; producers
    construct through the general storage/lane entries, and every
    consumer asks the general var operations here. *)

open Bap.Std

type temporary = Comparison | Load | Refinement
type kind
type table

(** The storage a synthetic variable is based at, or names the bytes
    of.  One general descriptor covers every family: a stack region, the
    caller window, a section component, an argument slot, a call-argument
    pointer, and a dynamic allocation. *)
type storage =
  | Stack of int
  | Window
  | Global of int
  | Slot of int
  | Argument of int
  | Allocation of int

type lane = Input | Output

(** The general classification of a synthetic variable: a module
    address, a storage base or its bytes, an environment register, an FP
    lane, or a transient value.  One function answers every consumer. *)
type classification =
  | Module_addr of int64
  | Storage of storage
  | Bytes of storage
  | Env_register of var
  | Fp_lane of lane * int
  | Transient

val classify : table -> var -> classification option

val empty : table
val table_of_program : program term -> table
val mem : table -> var -> bool

(** Every var the table knows, with its classification. *)
val bindings : table -> (var * classification) list

(* — Construction: the general producer entries. — *)
val base : addr_bits:int -> storage -> var
val bytes : addr_bits:int -> storage -> var
val module_addr : addr_bits:int -> int64 -> var
val fp_lane : addr_bits:int -> lane -> int -> var
val environment : var -> var
val accumulator : addr_bits:int -> var
val let_var : addr_bits:int -> int -> typ -> var
val fresh : bits:int -> temporary -> var

(* — General operations: every question about a synthetic variable. — *)
(* Transient synthetic values and the lifter's virtual temporaries. *)
val is_temporary : Var.t -> bool
(* A base operand: a module address or a storage base, never a cell. *)
val is_base_var : table -> var -> bool
val is_storage_var : table -> var -> bool
val is_memory_var : table -> var -> bool
val is_module_addr_var : table -> var -> bool
val module_addr_of : table -> var -> int64 option
val env_of : table -> var -> var option
val storage_of : table -> var -> storage option
val index_of : table -> var -> int option
(* The canonical base and memory vars of a synthetic storage var. *)
val base_var : addr_bits:int -> var -> var option
val memory_var : addr_bits:int -> var -> var option

(* — Address interpretation. — *)
type region = { id : int; lo : int64; hi : int64 }
val contains : region -> int64 -> bool

(** The owning memory variable and its byte index. *)
val of_address :
  addr_bits:int -> regions:region list -> int64 -> (var * exp) option

(** Constant address arithmetic and its synthetic address basis. *)
val address_of_exp : table -> exp -> int64 option
val address_basis : table -> exp -> int64 option

(** The module address of a storage access: the storage's byte origin
    plus its constant index.  [origin] supplies a base var's byte origin
    (the emitter's component map, the layout's regions); an access with
    no synthetic storage keeps its index as the address. *)
val access_address :
  ?origin:(var -> int64 option) -> table -> var -> exp -> int64 option

(** The general access rewriting: every Load/Store takes its storage's
    memory var and the storage-relative index.  [named_only] rewrites
    only accesses whose memory var already names a synthetic storage; a
    copy-relocated [slots] access reads the pointer the loader stores in
    the slot, so the emitter needs no relocation path. *)
val rewrite_exp :
  ?slots:int64 list -> addr_bits:int -> table -> regions:region list ->
  named_only:bool -> exp -> exp

val rewrite_def :
  ?slots:int64 list -> addr_bits:int -> table -> regions:region list ->
  named_only:bool -> def term -> def term
