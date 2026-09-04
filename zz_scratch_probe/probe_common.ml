(* Shared shell for the zz_scratch_probe drivers: init, loading, printing. *)

open Bap.Std

module AI = Cbat_vsa.AI
module Mem = Cbat_vsa.Mem
module Vsa = Cbat_vsa
module Ws = Cbat_clp_set_composite

(* BAP init; call before opening a project. *)
let init () =
  match Bap_main.init ~argv:[|Sys.executable_name|] () with
  | Ok () -> ()
  | Error failed ->
    Format.eprintf "probe: BAP initialization failed: %a@\n%!"
      Bap_main.Extension.Error.pp failed;
    exit 1

(* Print a usage line and exit 2. *)
let usage (prog : string) (msg : string) : 'a =
  Printf.eprintf "usage: %s %s\n" prog msg;
  exit 2

(* Open a corpus binary with the llvm loader. *)
let load_project (path : string) : Project.t =
  match Project.create (Project.Input.file ~loader:"llvm" ~filename:path) with
  | Ok proj -> proj
  | Error e ->
    Format.eprintf "probe: load failed: %s: %s\n%!" path
      (Core_kernel.Error.to_string_hum e);
    exit 1

let sp_of (proj : Project.t) : var = Hike.Abi.sp (Project.target proj)

(* Exact name match, else first name containing it. *)
let find_sub (prog : program term) (name : string) : sub term option =
  let exact =
    Term.enum sub_t prog
    |> Seq.find ~f:(fun s -> String.equal (Sub.name s) name)
  in
  match exact with
  | Some _ as x -> x
  | None ->
    Term.enum sub_t prog
    |> Seq.find ~f:(fun s ->
        Base.String.is_substring (Sub.name s) ~substring:name)

let all_subs (prog : program term) : sub term list =
  Term.enum sub_t prog |> Seq.to_list

(* Run the solution-only fixpoint on the raw sub (spec §2.1). *)
let analyze_and_fixpoint (_sp : var) (_prog : program term) (sub : sub term)
    : sub term * Vsa.vsa_sol =
  let prog' = Program.create ~subs:[ sub ] () in
  let sol = Vsa.static_graph_vsa [] prog' sub (Vsa.init_sol sub) in
  (sub, sol)

(* Word-set printers. *)

let word_to_hex (w : word) : string =
  match Word.to_int64 w with
  | Ok n -> Printf.sprintf "0x%Lx" n
  | Error _ -> Word.to_string w

(* TOP / BOT / [lo .. hi] in hex, with the infinite flag. *)
let ws_to_string (ws : Ws.t) : string =
  if Ws.is_top ws then "TOP"
  else if Ws.is_bottom ws then "BOT"
  else
    match Ws.min_elem ws, Ws.max_elem ws with
    | Some lo, Some hi ->
      Printf.sprintf "[%s .. %s]%s" (word_to_hex lo) (word_to_hex hi)
        (if Ws.is_infinite ws then " (infinite)" else "")
    | _ -> "?"

(* True when the u64 span is >= 2^63 (reads negative in int64). *)
let ws_window_big (ws : Ws.t) : bool =
  if Ws.is_top ws || Ws.is_bottom ws then false
  else
    match Ws.min_elem ws, Ws.max_elem ws with
    | Some lo, Some hi ->
      (match Word.to_int64 lo, Word.to_int64 hi with
       | Ok lo, Ok hi -> Int64.compare (Int64.sub hi lo) 0L < 0
       | _ -> false)
    | _ -> false

let target_to_string (l : label) : string =
  match l with
  | Direct tid -> Tid.name tid
  | Indirect e -> "[" ^ Format.asprintf "%a" Exp.pp e ^ "]"

let jmp_to_string (j : jmp term) : string =
  match Jmp.kind j with
  | Goto l -> Printf.sprintf "goto %s" (target_to_string l)
  | Ret l -> Printf.sprintf "ret %s" (target_to_string l)
  | Int _ -> "int"
  | Call c ->
    Printf.sprintf "call %s%s" (target_to_string (Call.target c))
      (match Call.return c with
       | Some r -> " ret " ^ target_to_string r
       | None -> " (noreturn)")

let def_to_string (d : def term) : string =
  Printf.sprintf "%s := %s" (Var.name (Def.lhs d)) (Format.asprintf "%a" Exp.pp (Def.rhs d))

let blk_bil_to_string (b : blk term) : string =
  let defs =
    Term.enum def_t b
    |> Seq.map ~f:(fun d -> "    " ^ def_to_string d)
    |> Seq.to_list
    |> Base.String.concat ~sep:"\n"
  in
  let jmps =
    Term.enum jmp_t b
    |> Seq.map ~f:(fun j -> "    " ^ jmp_to_string j)
    |> Seq.to_list
    |> Base.String.concat ~sep:"\n"
  in
  Printf.sprintf "-- blk %s\n%s\n%s" (Tid.name (Term.tid b)) defs jmps

let vsa_kind_to_string (k : Hike.Convutils.vsa_kind) : string =
  match k with
  | Hike.Convutils.Range (lo, hi) -> Printf.sprintf "Range(%Ld,%Ld)" lo hi
  | Hike.Convutils.Infinite (lo, hi) -> Printf.sprintf "Infinite(%Ld,%Ld)" lo hi
  | Hike.Convutils.Unbounded -> "Unbounded"
  | Hike.Convutils.Dead -> "Dead"
  | Hike.Convutils.VLA tid -> Printf.sprintf "VLA(%s)" (Tid.name tid)

(* Value-set of each named var in the state. *)
let state_summary (vars : var list) (st : AI.t) : string =
  vars
  |> Base.List.map ~f:(fun v ->
      Printf.sprintf "%s=%s" (Var.name v) (ws_to_string (AI.find_word 64 st v)))
  |> Base.String.concat ~sep:" "

(* Def-lhs vars of a sub, de-duplicated. *)
let lhs_vars_of (sub : sub term) : var list =
  Term.enum blk_t sub
  |> Seq.concat_map ~f:(Term.enum def_t)
  |> Seq.fold ~init:[] ~f:(fun acc d ->
      let base = Var.base (Def.lhs d) in
      if Base.List.exists acc ~f:(Var.same base) then acc else base :: acc)