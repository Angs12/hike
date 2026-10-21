(* The synthetic-variable vocabulary: one module owns the kinds and the
   storage/base/index machinery; the address interpretation and access
   rewriting live above, in Hike_synth_addr.  Consumers use the general
   operations and never inspect a kind. *)

open Bap.Std

type temporary = Comparison | Load | Store | Refinement | Binding

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

type storage =
  | Stack of int
  | Window
  | Global of int
  | Slot of int
  | Argument of int

type lane = Input | Output

let mem_type addr_bits =
  if addr_bits <= 0 then
    failwith "hike_synth: memory type has no address width";
  Hike_abi.mem_type ~addr_bits

let var ~addr_bits kind =
  let name, typ = match kind with
    | K_addr a -> Printf.sprintf "hike_synth_%Lx" a, Type.Imm addr_bits
    | K_thread_addr a -> Printf.sprintf "hike_thread_%Lx" a, Type.Imm addr_bits
    | K_slot i -> Printf.sprintf "hike_slot%d" i, mem_type addr_bits
    | K_argument i -> Printf.sprintf "hike_arg%d" i, mem_type addr_bits
    | K_window -> "hike_window", Type.Imm addr_bits
    | K_window_memory -> "hike_window_mem", mem_type addr_bits
    | K_region i -> Printf.sprintf "stack_r%d_ptr" i, mem_type addr_bits
    | K_region_memory i -> Printf.sprintf "stack_r%d_mem" i, mem_type addr_bits
    | K_global i -> Printf.sprintf "sec_comp_%d_ptr" i, mem_type addr_bits
    | K_global_memory i -> Printf.sprintf "sec_comp_%d_mem" i, mem_type addr_bits
    | K_environment v -> Var.name v, Var.typ v
    | K_fp_input i -> Printf.sprintf "intrinsic:x%d:%d" i addr_bits, Type.Imm addr_bits
    | K_fp_output i -> Printf.sprintf "intrinsic:y%d:%d" i addr_bits, Type.Imm addr_bits
    | K_accumulator -> "hike_acc", Type.Imm addr_bits
    | K_let (i, typ) -> Printf.sprintf "hike_let%d" i, typ
    | K_temporary (temporary, i) ->
      let prefix, typ = match temporary with
        | Comparison -> "hike_cmp", Type.Imm addr_bits
        | Load -> "hike_ld", Type.Imm addr_bits
        | Store -> "hike_st", mem_type addr_bits
        | Refinement -> "hike_rd", Type.Imm addr_bits
        | Binding -> "hike_bd", Type.Imm addr_bits in
      Printf.sprintf "%s%d" prefix i, typ
  in
  Var.create ~is_virtual:false ~fresh:false name typ

(* — Construction: the general producer entries. — *)

let base_kind_of_storage = function
  | Stack id -> K_region id
  | Window -> K_window
  | Global id -> K_global id
  | Slot i -> K_slot i
  | Argument i -> K_argument i

let bytes_kind_of_storage = function
  | Stack id -> K_region_memory id
  | Window -> K_window_memory
  | Global id -> K_global_memory id
  | Slot i -> K_slot i
  | Argument i -> K_argument i

let base ~addr_bits storage = var ~addr_bits (base_kind_of_storage storage)
let bytes ~addr_bits storage = var ~addr_bits (bytes_kind_of_storage storage)
let module_addr ~addr_bits a = var ~addr_bits (K_addr a)
let thread_addr ~addr_bits a = var ~addr_bits (K_thread_addr a)

let fp_lane ~addr_bits lane i =
  match lane with
  | Input -> var ~addr_bits (K_fp_input i)
  | Output -> var ~addr_bits (K_fp_output i)

let next_temporary = ref 0

type table = kind Var.Map.t

let empty : table = Var.Map.empty

(* The creating pass records each synthetic var with its kind, keyed by
   the base var (an SSA version resolves to its base). *)
let add (tbl : table) (v : Var.t) (k : kind) : table =
  let key = Var.base v in
  match Core.Map.find tbl key with
  | Some old when old = k -> tbl
  | Some _ ->
    failwith
      (Printf.sprintf "hike_synth: conflicting classification for %s"
         (Var.name key))
  | None -> Core.Map.set tbl ~key ~data:k

let resolve (tbl : table) (v : Var.t) : kind option =
  Core.Map.find tbl (Var.base v)

(* Mints a var of [kind] and records it. *)
let mint ~addr_bits kind tbl =
  let v = var ~addr_bits kind in
  (add tbl v kind, v)

let mint_base ~addr_bits storage = mint ~addr_bits (base_kind_of_storage storage)
let mint_bytes ~addr_bits storage = mint ~addr_bits (bytes_kind_of_storage storage)
let mint_module_addr ~addr_bits a = mint ~addr_bits (K_addr a)
let mint_thread_addr ~addr_bits a = mint ~addr_bits (K_thread_addr a)

let mint_fp_lane ~addr_bits lane i =
  mint ~addr_bits (match lane with Input -> K_fp_input i | Output -> K_fp_output i)

let mint_fresh ~bits temporary tbl =
  incr next_temporary;
  mint ~addr_bits:bits (K_temporary (temporary, !next_temporary)) tbl

let mint_fresh_mem ~addr_bits temporary tbl =
  incr next_temporary;
  mint ~addr_bits (K_temporary (temporary, !next_temporary)) tbl

(* The accumulating form for a traversal that keeps its table in a cell. *)
let record (cell : table ref) f =
  let tbl, v = f !cell in
  cell := tbl;
  v

(* The caller-window base is one var per target, known with the facts. *)
let add_window tbl ~addr_bits = fst (mint ~addr_bits K_window tbl)

(* An environment register is the target's own var: recorded as given. *)
let add_environment tbl v = add tbl v (K_environment v)

let mem tbl v = Core.Map.mem tbl (Var.base v)

let union (a : table) (b : table) : table =
  Core.Map.merge_skewed a b ~combine:(fun ~key x y ->
      if x = y then x
      else
        failwith
          (Printf.sprintf "hike_synth: conflicting classification for %s"
             (Var.name key)))

(* The vars the program still names, plus the target's registers and
   caller window (finite facts, kept whole). *)
let restrict_to_program (tbl : table) (prog : program term) : table =
  (object
     inherit [table] Term.visitor
     method! visit_var v acc =
       let key = Var.base v in
       match Core.Map.find tbl key with
       | Some k -> Core.Map.set acc ~key ~data:k
       | None -> acc
   end)#run prog
    (Core.Map.filter tbl ~f:(function K_environment _ | K_window -> true | _ -> false))

(* Virtual vars are the lifter's temporaries even when the table does
   not record them; a recorded kind still wins for a real var. *)
let is_temporary ~table v =
  Var.is_virtual v
  ||
  match resolve table v with
  | Some (K_temporary _ | K_accumulator | K_let _) -> true
  | _ -> false

(* — General operations. — *)

let storage_of_kind = function
  | K_region id | K_region_memory id -> Some (Stack id)
  | K_window | K_window_memory -> Some Window
  | K_global id | K_global_memory id -> Some (Global id)
  | K_slot i -> Some (Slot i)
  | K_argument i -> Some (Argument i)
  | _ -> None

let base_kind = function
  | K_region id | K_region_memory id -> Some (K_region id)
  | K_window | K_window_memory -> Some K_window
  | K_global id | K_global_memory id -> Some (K_global id)
  | K_slot i -> Some (K_slot i)
  | K_argument i -> Some (K_argument i)
  | _ -> None

let memory_kind = function
  | K_region_memory id | K_region id -> Some (K_region_memory id)
  | K_window_memory | K_window -> Some K_window_memory
  | K_global_memory id | K_global id -> Some (K_global_memory id)
  | K_slot i -> Some (K_slot i)
  | _ -> None

type classification =
  | Module_addr of int64
  | Thread_addr of int64
  | Storage of storage
  | Bytes of storage
  | Env_register of var
  | Fp_lane of lane * int
  | Transient

let classify tbl v =
  match resolve tbl v with
  | Some k -> (
    match k with
    | K_addr a -> Some (Module_addr a)
    | K_thread_addr a -> Some (Thread_addr a)
    | K_region _ | K_window | K_global _ | K_slot _ | K_argument _ ->
      Base.Option.map (storage_of_kind k) ~f:(fun s -> Storage s)
    | K_region_memory _ | K_window_memory | K_global_memory _ ->
      Base.Option.map (storage_of_kind k) ~f:(fun s -> Bytes s)
    | K_environment v -> Some (Env_register v)
    | K_fp_input i -> Some (Fp_lane (Input, i))
    | K_fp_output i -> Some (Fp_lane (Output, i))
    | K_accumulator | K_let _ | K_temporary _ -> Some Transient)
  | None -> None

(* Every var the table knows, with its classification: the emitter's
   one enumeration of the synthetic vocabulary. *)
let bindings tbl =
  Core.Map.to_alist tbl
  |> Base.List.filter_map ~f:(fun (v, _) ->
      Base.Option.map (classify tbl v) ~f:(fun c -> (v, c)))

let is_memory_var tbl v =
  match classify tbl v with Some (Bytes _) -> true | _ -> false

let is_address_var tbl v =
  match classify tbl v with Some (Module_addr _ | Thread_addr _) -> true | _ -> false

let module_addr_of tbl v =
  match classify tbl v with Some (Module_addr a) -> Some a | _ -> None

let thread_addr_of tbl v =
  match classify tbl v with Some (Thread_addr a) -> Some a | _ -> None

let env_of tbl v =
  match classify tbl v with Some (Env_register v) -> Some v | _ -> None

let storage_of tbl v =
  match classify tbl v with
  | Some (Storage s | Bytes s) -> Some s
  | _ -> None

let index_of tbl v =
  match classify tbl v with
  | Some (Storage s | Bytes s) -> (
    match s with
    | Stack id | Global id | Slot id | Argument id -> Some id
    | Window -> None)
  | Some (Fp_lane (_, i)) -> Some i
  | _ -> None

(* A storage's allocated span and canonical base var: the one layout
   fact every consumer reads.  [ss_lo]/[ss_hi] are model addresses;
   [ss_base] is the canonical base var at the run's address width. *)
type storage_span = {
  ss_storage : storage;
  ss_base : var;
  ss_lo : int64;
  ss_hi : int64;
}

let equal_storage (a : storage) (b : storage) : bool =
  match (a, b) with
  | Stack i, Stack j | Global i, Global j | Slot i, Slot j
  | Argument i, Argument j -> Int.equal i j
  | Window, Window -> true
  | _ -> false

let storage_span ~addr_bits storage ~lo ~hi tbl =
  let tbl, ss_base = mint_base ~addr_bits storage tbl in
  (tbl, { ss_storage = storage; ss_base; ss_lo = lo; ss_hi = hi })

let span_of_storage (spans : storage_span list) storage =
  Base.List.find spans ~f:(fun s -> equal_storage s.ss_storage storage)

let memory_var tbl ~addr_bits v =
  Base.Option.map ~f:(var ~addr_bits)
    (Base.Option.bind (resolve tbl v) ~f:memory_kind)
