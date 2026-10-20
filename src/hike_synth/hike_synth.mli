(** The synthetic-variable vocabulary: the one module that knows what a
    synthetic variable is.  A producer records each var it creates in the
    table of its context ([mint], [add]); a var absent from the table is
    not synthetic.  Consumers ask the general var operations here and
    never inspect a kind. *)

open Bap.Std

type temporary = Comparison | Load | Refinement | Binding
type kind =
  | K_addr of int64
  | K_thread_addr of int64
  | K_slot of int
  | K_argument of int
  | K_window
  | K_window_memory
  | K_region of int
  | K_region_memory of int
  | K_global of int
  | K_global_memory of int
  | K_environment of var
  | K_fp_input of int
  | K_fp_output of int
  | K_accumulator
  | K_let of int * typ
  | K_temporary of temporary * int

type table

(** The storage a synthetic variable is based at, or names the bytes
    of.  One general descriptor covers every family: a stack region, the
    caller window, a section component, an argument slot, a call-argument
    pointer. *)
type storage =
  | Stack of int
  | Window
  | Global of int
  | Slot of int
  | Argument of int

type lane = Input | Output

(** The general classification of a synthetic variable: a module
    address, a storage base or its bytes, an environment register, an FP
    lane, or a transient value.  One function answers every consumer. *)
type classification =
  | Module_addr of int64
  | Thread_addr of int64
  | Storage of storage
  | Bytes of storage
  | Env_register of var
  | Fp_lane of lane * int
  | Transient

val classify : table -> var -> classification option

val empty : table
val mem : table -> var -> bool

val union : table -> table -> table

(** The table narrowed to the vars the program names (target registers
    stay). *)
val restrict_to_program : table -> program term -> table

(** Records [v] under its base var. *)
val add : table -> var -> kind -> table

(** Every var the table knows, with its classification. *)
val bindings : table -> (var * classification) list

(* — Construction: the general producer entries. — *)
val base : addr_bits:int -> storage -> var
val bytes : addr_bits:int -> storage -> var
val module_addr : addr_bits:int -> int64 -> var
val thread_addr : addr_bits:int -> int64 -> var
val fp_lane : addr_bits:int -> lane -> int -> var

(* — Creation with registration: the pass that mints a var records it. — *)
val mint : addr_bits:int -> kind -> table -> table * var
val mint_base : addr_bits:int -> storage -> table -> table * var
val mint_bytes : addr_bits:int -> storage -> table -> table * var
val mint_module_addr : addr_bits:int -> int64 -> table -> table * var
val mint_thread_addr : addr_bits:int -> int64 -> table -> table * var
val mint_fp_lane : addr_bits:int -> lane -> int -> table -> table * var
val mint_fresh : bits:int -> temporary -> table -> table * var

(** Runs one mint against a traversal's table cell and keeps the grown
    table there. *)
val record : table ref -> (table -> table * 'a) -> 'a

(** Records the target's caller-window base. *)
val add_window : table -> addr_bits:int -> table

(** Records a target register under the environment kind. *)
val add_environment : table -> var -> table

(* — General operations: every question about a synthetic variable. — *)
(* Transient synthetic values and the lifter's virtual temporaries. *)
val is_temporary : table:table -> Var.t -> bool
val is_memory_var : table -> var -> bool
val is_address_var : table -> var -> bool
val module_addr_of : table -> var -> int64 option
val thread_addr_of : table -> var -> int64 option
val env_of : table -> var -> var option
val storage_of : table -> var -> storage option
val index_of : table -> var -> int option

(** A storage's allocated span and canonical base var: the one layout
    fact every consumer reads.  Endpoints are model addresses. *)
type storage_span = {
  ss_storage : storage;
  ss_base : var;
  ss_lo : int64;
  ss_hi : int64;
}

val storage_span :
  addr_bits:int -> storage -> lo:int64 -> hi:int64 -> table ->
  table * storage_span
val span_of_storage : storage_span list -> storage -> storage_span option
(* The canonical memory var of a synthetic storage var. *)
val memory_var : table -> addr_bits:int -> var -> var option
