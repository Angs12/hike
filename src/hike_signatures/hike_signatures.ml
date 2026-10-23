open Core

type access = Read_only | Write_only | May_write [@@deriving sexp]

type param = {
  ty : Hike_sysv.ctype;
  access : access [@default May_write];
  captured : bool [@default true];
} [@@deriving sexp]

type memory = Any | Argmem of access | Reads_any | None_ [@@deriving sexp]

type record = {
  library : string;
  version : string;
  symbol : string;
  return : Hike_sysv.ctype option [@sexp.option];
  returned : int option [@sexp.option];
  params : param list;
  variadic : bool [@default false];
  memory : memory [@default Any];
  noreturn : bool [@default false];
} [@@deriving sexp]

let place ~(abi : Hike_abi.t) r =
  match abi.Hike_abi.convention with
  | Hike_abi.Sysv_x86_64_gnu ->
    Hike_sysv.place_call ~return:r.return (List.map r.params ~f:(fun p -> p.ty))

(* The target's argument registers, by class. *)
let argument_registers ~(abi : Hike_abi.t) =
  match abi.Hike_abi.convention with
  | Hike_abi.Sysv_x86_64_gnu ->
    (abi.Hike_abi.int_param_regs, abi.Hike_abi.vector_param_regs)

let integer_register ~abi index = List.nth (fst (argument_registers ~abi)) index

let vector_register ~abi index = List.nth (snd (argument_registers ~abi)) index

let rec carries_pointer : Hike_sysv.ctype -> bool = function
  | Scalar Pointer -> true
  | Scalar _ | Complex _ -> false
  | Aggregate a -> List.exists a.fields ~f:(fun f -> carries_pointer f.ty)

(* A record is keyed by library, version and symbol. *)
module Key = struct
  module T = struct
    type t = string * string * string [@@deriving compare, sexp]
  end
  include T
  include Comparator.Make (T)
end

type db = record Map.M(Key).t

let empty = Map.empty (module Key)

let cardinal = Map.length

let key r = (r.library, r.version, r.symbol)

let add db r = Map.set db ~key:(key r) ~data:r

let of_records records = List.fold records ~init:empty ~f:add

let of_sexps sexps =
  Or_error.try_with (fun () ->
      List.fold sexps ~init:empty ~f:(fun db s -> add db (record_of_sexp s)))

let of_string text =
  Or_error.bind (Or_error.try_with (fun () -> Sexp.of_string_many text))
    ~f:of_sexps

let load files =
  let of_file file =
    Or_error.tag ~tag:file
      (Or_error.bind (Or_error.try_with (fun () -> Sexp.load_sexps file))
         ~f:of_sexps) in
  List.fold files ~init:(Ok empty) ~f:(fun db file ->
      Or_error.both db (of_file file)
      |> Or_error.map ~f:(fun (db, later) ->
          (* A later file overrides an earlier entry. *)
          Map.merge_skewed db later ~combine:(fun ~key:_ _ later -> later)))

type t = {
  db : db;
  imports : string -> (string * string) option;
}

let create ~target db ~imports =
  if not (Hike_abi.is_primary_target target) then
    failwith
      (sprintf
         "hike: signatures describe the x86-64 System V (GNU) ABI; target %s \
          is not x86_64-gnu-elf"
         (Bap_core_theory.Theory.Target.to_string target));
  { db; imports }

let find t name =
  Option.bind (t.imports name) ~f:(fun (library, version) ->
      Map.find t.db (library, version, name))
