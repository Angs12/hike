(* The synthetic-variable vocabulary: one module owns the kinds and the
   storage/base/index machinery; the address interpretation and access
   rewriting live above, in Hike_synth_addr.  Consumers use the general
   operations and never inspect a kind. *)

open Bap.Std

type temporary = Comparison | Load | Refinement

type kind =
  | K_addr of int64
  | K_slot of int
  | K_argument of int
  | K_window
  | K_window_memory
  | K_region of int
  | K_region_memory of int
  | K_allocation of int
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
  | Allocation of int

type lane = Input | Output

let mem_type addr_bits =
  Type.Mem ((if addr_bits <= 32 then `r32 else `r64), `r8)

let var ~addr_bits kind =
  let name, typ = match kind with
    | K_addr a -> Printf.sprintf "hike_synth_%Lx" a, Type.Imm addr_bits
    | K_slot i -> Printf.sprintf "hike_slot%d" i, mem_type addr_bits
    | K_argument i -> Printf.sprintf "hike_arg%d" i, mem_type addr_bits
    | K_window -> "hike_window", Type.Imm addr_bits
    | K_window_memory -> "hike_window_mem", mem_type addr_bits
    | K_region i -> Printf.sprintf "stack_r%d_ptr" i, mem_type addr_bits
    | K_region_memory i -> Printf.sprintf "stack_r%d_mem" i, mem_type addr_bits
    | K_allocation i -> Printf.sprintf "hike_vla_%d_ptr" i, mem_type addr_bits
    | K_global i -> Printf.sprintf "sec_comp_%d_ptr" i, mem_type addr_bits
    | K_global_memory i -> Printf.sprintf "sec_comp_%d_mem" i, mem_type addr_bits
    | K_environment v -> Var.name v, Var.typ v
    | K_fp_input i -> Printf.sprintf "intrinsic:x%d:%d" i addr_bits, Type.Imm addr_bits
    | K_fp_output i -> Printf.sprintf "intrinsic:y%d:%d" i addr_bits, Type.Imm addr_bits
    | K_accumulator -> "hike_acc", Type.Imm addr_bits
    | K_let (i, typ) -> Printf.sprintf "hike_let%d" i, typ
    | K_temporary (temporary, i) ->
      let prefix = match temporary with
        | Comparison -> "hike_cmp" | Load -> "hike_ld" | Refinement -> "hike_rd" in
      Printf.sprintf "%s%d" prefix i, Type.Imm addr_bits
  in
  Var.create ~is_virtual:false ~fresh:false name typ

(* — Construction: the general producer entries. — *)

let base_kind_of_storage = function
  | Stack id -> K_region id
  | Window -> K_window
  | Global id -> K_global id
  | Slot i -> K_slot i
  | Argument i -> K_argument i
  | Allocation i -> K_allocation i

let bytes_kind_of_storage = function
  | Stack id -> K_region_memory id
  | Window -> K_window_memory
  | Global id -> K_global_memory id
  | Slot i -> K_slot i
  | Argument i -> K_argument i
  | Allocation i -> K_allocation i

let base ~addr_bits storage = var ~addr_bits (base_kind_of_storage storage)
let bytes ~addr_bits storage = var ~addr_bits (bytes_kind_of_storage storage)
let module_addr ~addr_bits a = var ~addr_bits (K_addr a)

let fp_lane ~addr_bits lane i =
  match lane with
  | Input -> var ~addr_bits (K_fp_input i)
  | Output -> var ~addr_bits (K_fp_output i)

(* The environment register keeps its own name and type. *)
let environment v =
  Var.create ~is_virtual:false ~fresh:false (Var.name v) (Var.typ v)

let accumulator ~addr_bits = var ~addr_bits K_accumulator
let let_var ~addr_bits i typ = var ~addr_bits (K_let (i, typ))

let next_temporary = ref 0

let fresh ~bits temporary =
  incr next_temporary;
  var ~addr_bits:bits (K_temporary (temporary, !next_temporary))

(* — The private classification. — *)

let family name ~prefix ~suffix f =
  Base.Option.bind (Base.String.chop_prefix name ~prefix) ~f:(fun rest ->
      Base.Option.bind (Base.String.chop_suffix rest ~suffix) ~f:(fun id ->
          Base.Option.map (Stdlib.int_of_string_opt id) ~f))

let fp_kind name ~prefix make =
  Base.Option.bind (Base.String.chop_prefix name ~prefix) ~f:(fun rest ->
      match String.split_on_char ':' rest with
      | [lane] | [lane; _] -> Base.Option.map (Stdlib.int_of_string_opt lane) ~f:make
      | _ -> None)

let kind_of_var v =
  let v = Var.base v in
  let n = Var.name v in
  if Base.String.is_prefix n ~prefix:"hike_synth_" then
    Base.Option.bind (Base.String.chop_prefix n ~prefix:"hike_synth_")
      ~f:(fun h -> try Some (K_addr (Int64.of_string ("0x" ^ h))) with _ -> None)
  else if Base.String.is_prefix n ~prefix:"hike_slot" then
    family n ~prefix:"hike_slot" ~suffix:"" (fun i -> K_slot i)
  else if Base.String.is_prefix n ~prefix:"hike_arg" then
    family n ~prefix:"hike_arg" ~suffix:"" (fun i -> K_argument i)
  else if String.equal n "hike_window" then Some K_window
  else if String.equal n "hike_window_mem" then Some K_window_memory
  else if Base.String.is_prefix n ~prefix:"stack_r" then
    Base.Option.first_some
      (family n ~prefix:"stack_r" ~suffix:"_mem" (fun i -> K_region_memory i))
      (family n ~prefix:"stack_r" ~suffix:"_ptr" (fun i -> K_region i))
  else if Base.String.is_prefix n ~prefix:"sec_comp_" then
    Base.Option.first_some
      (family n ~prefix:"sec_comp_" ~suffix:"_mem" (fun i -> K_global_memory i))
      (family n ~prefix:"sec_comp_" ~suffix:"_ptr" (fun i -> K_global i))
  else if Base.String.is_prefix n ~prefix:"hike_vla_" then
    family n ~prefix:"hike_vla_" ~suffix:"_ptr" (fun i -> K_allocation i)
  else if Base.String.is_prefix n ~prefix:"intrinsic:x" then
    fp_kind n ~prefix:"intrinsic:x" (fun i -> K_fp_input i)
  else if Base.String.is_prefix n ~prefix:"intrinsic:y" then
    fp_kind n ~prefix:"intrinsic:y" (fun i -> K_fp_output i)
  else if String.equal n "hike_acc" then Some K_accumulator
  else if Base.String.is_prefix n ~prefix:"hike_let" then
    family n ~prefix:"hike_let" ~suffix:"" (fun i -> K_let (i, Var.typ v))
  else if Base.String.is_prefix n ~prefix:"hike_cmp" then
    family n ~prefix:"hike_cmp" ~suffix:"" (fun i -> K_temporary (Comparison, i))
  else if Base.String.is_prefix n ~prefix:"hike_ld" then
    family n ~prefix:"hike_ld" ~suffix:"" (fun i -> K_temporary (Load, i))
  else if Base.String.is_prefix n ~prefix:"hike_rd" then
    family n ~prefix:"hike_rd" ~suffix:"" (fun i -> K_temporary (Refinement, i))
  else if Hike_abi.is_env_reg Hike_abi.x86_64_sysv v then Some (K_environment v)
  else None

type table = kind Var.Map.t

let empty : table = Var.Map.empty

let resolve (tbl : table) (v : Var.t) : kind option =
  match Core.Map.find tbl v with Some k -> Some k | None -> kind_of_var v

let mem tbl v = Core.Map.mem tbl v

let table_of_program (prog : program term) : table =
  (object
     inherit [table] Term.visitor
     method! visit_var v acc =
       match kind_of_var v with
       | Some k -> Core.Map.set acc ~key:v ~data:k
       | None -> acc
   end)#run prog empty

let is_temporary v =
  Var.is_virtual v || match resolve empty v with
  | Some (K_temporary _ | K_accumulator | K_let _) -> true
  | _ -> false

(* — General operations. — *)

let storage_of_kind = function
  | K_region id | K_region_memory id -> Some (Stack id)
  | K_window | K_window_memory -> Some Window
  | K_global id | K_global_memory id -> Some (Global id)
  | K_slot i -> Some (Slot i)
  | K_argument i -> Some (Argument i)
  | K_allocation i -> Some (Allocation i)
  | _ -> None

let base_kind = function
  | K_region id | K_region_memory id -> Some (K_region id)
  | K_window | K_window_memory -> Some K_window
  | K_global id | K_global_memory id -> Some (K_global id)
  | K_slot i -> Some (K_slot i)
  | K_argument i -> Some (K_argument i)
  | K_allocation i -> Some (K_allocation i)
  | _ -> None

let memory_kind = function
  | K_region_memory id | K_region id -> Some (K_region_memory id)
  | K_window_memory | K_window -> Some K_window_memory
  | K_global_memory id | K_global id -> Some (K_global_memory id)
  | K_slot i -> Some (K_slot i)
  | _ -> None

type classification =
  | Module_addr of int64
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
    | K_region _ | K_window | K_global _ | K_slot _ | K_argument _
    | K_allocation _ ->
      Base.Option.map (storage_of_kind k) ~f:(fun s -> Storage s)
    | K_region_memory _ | K_window_memory | K_global_memory _ ->
      Base.Option.map (storage_of_kind k) ~f:(fun s -> Bytes s)
    | K_environment v -> Some (Env_register v)
    | K_fp_input i -> Some (Fp_lane (Input, i))
    | K_fp_output i -> Some (Fp_lane (Output, i))
    | K_accumulator | K_let _ | K_temporary _ -> Some Transient)
  | None -> None

let is_base_var tbl v =
  match classify tbl v with
  | Some (Module_addr _ | Storage _) -> true
  | _ -> false

(* Every var the table knows, with its classification: the emitter's
   one enumeration of the synthetic vocabulary. *)
let bindings tbl =
  Core.Map.to_alist tbl
  |> Base.List.filter_map ~f:(fun (v, _) ->
      Base.Option.map (classify tbl v) ~f:(fun c -> (v, c)))

let is_memory_var tbl v =
  match classify tbl v with Some (Bytes _) -> true | _ -> false

let is_module_addr_var tbl v =
  match classify tbl v with Some (Module_addr _) -> true | _ -> false

let module_addr_of tbl v =
  match classify tbl v with Some (Module_addr a) -> Some a | _ -> None

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
    | Stack id | Global id | Slot id | Argument id | Allocation id -> Some id
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
  | Argument i, Argument j | Allocation i, Allocation j -> Int.equal i j
  | Window, Window -> true
  | _ -> false

let storage_span ~addr_bits storage ~lo ~hi =
  { ss_storage = storage; ss_base = base ~addr_bits storage; ss_lo = lo;
    ss_hi = hi }

let span_of_storage (spans : storage_span list) storage =
  Base.List.find spans ~f:(fun s -> equal_storage s.ss_storage storage)

let base_var ~addr_bits v =
  Base.Option.map ~f:(var ~addr_bits)
    (Base.Option.bind (resolve empty v) ~f:base_kind)

let memory_var ~addr_bits v =
  Base.Option.map ~f:(var ~addr_bits)
    (Base.Option.bind (resolve empty v) ~f:memory_kind)
