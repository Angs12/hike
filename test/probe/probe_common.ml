(* Shared shell for the test/probe drivers: init, loading, printing. *)

open Bap.Std
open Bap_core_theory

module AI = Cbat_vsa.AI
module Vsa = Cbat_vsa
module Ws = Cbat_clp_set_composite

(* Watcher-shell driver shared by corpus_watch and precision_probe.
   Each probe owns its per-sub report; this seam owns project loading and
   the common load-failure contract. *)

(* Exception description. *)
let describe_exn (e : exn) : string =
  match e with
  | Assert_failure (file, line, col) ->
    Printf.sprintf "Assert_failure (%s:%d:%d)" file line col
  | Failure msg -> Printf.sprintf "Failure(%s)" msg
  | Invalid_argument msg -> Printf.sprintf "Invalid_argument(%s)" msg
  | _ -> Printexc.to_string e

(* No-args usage (exit 0). *)
let ws_usage (argv0 : string) : 'a =
  Printf.printf "usage: %s <binary> [<binary> ...]\n" argv0;
  flush stdout;
  exit 0

(* BAP init with a tool-named failure line. *)
let ws_init (tool : string) : unit =
  match Bap_main.init ~requires:[ "disassembler" ] ~argv:[|Sys.executable_name|] () with
  | Ok () -> ()
  | Error failed ->
    Format.eprintf "%s: BAP initialization failed: %a@\n%!" tool
      Bap_main.Extension.Error.pp failed;
    exit 1

(* BAP init; call before opening a project. *)
let init () = ws_init "probe"

(* Load-failure lines (the LOAD-FAIL contract). *)
let ws_load_fail (path : string) (e : Core.Error.t) : unit =
  Printf.printf "LOAD-FAIL\t%s\t%s\n" path (Core.Error.to_string_hum e);
  flush stdout

let ws_load_exn (path : string) (e : exn) : unit =
  Printf.printf "LOAD-FAIL\t%s\texception: %s\n" path (describe_exn e);
  flush stdout

(* TOTAL + PASS/FAIL lines and the exit code. *)
let ws_finish ~(pass : string) ~(fail : string) (crashes : int) (loadfails : int) : 'a =
  Printf.printf "TOTAL: %d crashes, %d load failures\n" crashes loadfails;
  Printf.printf "%s\n" (if crashes = 0 && loadfails = 0 then pass else fail);
  flush stdout;
  exit (if crashes = 0 && loadfails = 0 then 0 else 1)

(* DCE seam, aliased once here (no flat-name reach-throughs in probes). *)
module Dce = Hike.Dce

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
      (Core.Error.to_string_hum e);
    exit 1

type ws_binary_error =
  | Load_error of Core.Error.t
  | Run_error of exn

(* The production input: the passes hike runs before the VSA, in the
   chain's order (src/hike.ml).  The probes measure the analysis as
   production runs it, never the raw lift. *)
let production_input (proj : Project.t) : program term =
  let target = Project.target proj in
  Project.program proj
  |> Term.map sub_t ~f:(Hike.Jump.compile_sub target)
  |> Hike.Split_mem.normalize
  |> Hike.Coerce.coerce_program
  |> Hike.Fp.run_program

(* Load a binary and apply [run_sub] to each sub in program order. *)
let ws_run_binary (path : string) (run_sub : sub term -> 'a) :
    ('a list, ws_binary_error) result =
  try
    match Project.create (Project.Input.file ~loader:"llvm" ~filename:path) with
    | Error e -> Error (Load_error e)
    | Ok proj ->
      let subs = Term.enum sub_t (production_input proj) |> Seq.to_list in
      Ok (List.map run_sub subs)
  with e -> Error (Run_error e)

let sp_of (proj : Project.t) : var = Hike.Abi.sp (Project.target proj)

(* Run [f]; wall time in seconds. *)
let time (f : unit -> 'a) : 'a * float =
  let t0 = Unix.gettimeofday () in
  let r = f () in
  (r, Unix.gettimeofday () -. t0)

(* Exact name match, else first name containing it. *)
let find_sub (prog : program term) (name : string) : sub term option =
  let exact =
    Term.enum sub_t prog
    |> Seq.find ~f:(fun s -> String.equal (Sub.name s) name)
  in
  Base.Option.first_some exact
    (Term.enum sub_t prog
     |> Seq.find ~f:(fun s ->
         Base.String.is_substring (Sub.name s) ~substring:name))

let all_subs (prog : program term) : sub term list =
  Term.enum sub_t prog |> Seq.to_list

(* The ONE per-sub solve (spec §2.1): the sub over its own program,
   seeded from init_sol.  Every probe's fixpoint flow is this. *)
let run_sub_fixpoint (sub : sub term) : Vsa.vsa_sol =
  let prog' = Program.create ~subs:[ sub ] () in
  Vsa.static_graph_vsa ~abi:Hike_abi.x86_64_sysv prog' sub
    (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv sub)

let analyze_and_fixpoint (sub : sub term) : sub term * Vsa.vsa_sol =
  (sub, run_sub_fixpoint sub)

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
      Printf.sprintf "[%s .. %s]%s" (word_to_hex (Cbat_word.to_word lo)) (word_to_hex (Cbat_word.to_word hi))
        (if Ws.is_infinite ws then " (infinite)" else "")
    | _ -> "?"

(* True when the u64 span is >= 2^63 (reads negative in int64). *)
let ws_window_big (ws : Ws.t) : bool =
  if Ws.is_top ws || Ws.is_bottom ws then false
  else
    match Ws.min_elem ws, Ws.max_elem ws with
    | Some lo, Some hi ->
      (match Cbat_word.to_int64 lo, Cbat_word.to_int64 hi with
       | Ok lo, Ok hi -> Int64.compare (Int64.sub hi lo) 0L < 0
       | _ -> false)
    | _ -> false

let target_to_string (l : label) : string =
  match l with
  | Direct tid ->
    (try Tid.name tid with _ -> "%" ^ Tid.to_string tid)
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

(* The per-def stack kinds through the seam: the address's denotation
   at the def's own before-env, classified in place (the extraction's
   per-def rule; no merge). *)
let seam_kinds_of (sol : Vsa.vsa_sol) (sub : sub term) :
    Vsa.Cbat_extraction.kind Tid.Map.t =
  (* The seam reads the defs' Env Tags: walk the sweep's stamped sub. *)
  let _, sub = Vsa.stamp_envs_of_sol ~sol sub in
  let kind_of blk d =
    let open Base.Option in
    Base.Option.bind
      (Vsa.Cbat_extraction.stack_address_of_rhs (Def.rhs d))
      ~f:(fun addr ->
        Result.to_option
          (Vsa.denote_exp_at
             ~pre:(Graphlib.Std.Solution.get sol (Term.tid blk))
             ~blk ~def:d addr))
    >>= fun ws ->
    if Ws.is_bottom ws || Ws.in_stack_segment ws then
      Some (Vsa.Cbat_extraction.caller_split (Vsa.Cbat_extraction.classify ws))
    else if Ws.is_top ws then Some Vsa.Cbat_extraction.unbounded_span
    else None
  in
  Term.enum blk_t sub
  |> Seq.fold ~init:Tid.Map.empty ~f:(fun m blk ->
      Seq.fold (Term.enum def_t blk) ~init:m ~f:(fun m d ->
          match kind_of blk d with
          | Some k -> Core.Map.set m ~key:(Term.tid d) ~data:k
          | None -> m))

(* Shared cardinality ladder for the census probes. *)
type cardn_bucket =
  [ `Bottom | `Top | `Exact | `B2_3 | `B4_8 | `B9_64 | `B65p ]

let cardn_bucket_of_count (n : int) : cardn_bucket =
  if n = 1 then `Exact
  else if n <= 3 then `B2_3
  else if n <= 8 then `B4_8
  else if n <= 64 then `B9_64
  else `B65p

let cardn_bucket_of_ws (ws : Ws.t) : cardn_bucket option =
  if Ws.is_top ws then Some `Top
  else if Ws.is_bottom ws then Some `Bottom
  else
    match Cbat_word.to_int (Ws.cardinality ws) with
    | Error _ -> Some `B65p
    | Ok n -> Some (cardn_bucket_of_count n)

let cardn_bucket_name : cardn_bucket -> string = function
  | `Bottom -> "bottom"
  | `Top -> "top"
  | `Exact -> "exact"
  | `B2_3 -> "b2_3"
  | `B4_8 -> "b4_8"
  | `B9_64 -> "b9_64"
  | `B65p -> "b65p"

let vsa_kind_to_string (k : Vsa.Cbat_extraction.kind) : string =
  match k with
  | Vsa.Cbat_extraction.Range (lo, hi) -> Printf.sprintf "Range(%Ld,%Ld)" lo hi
  | Vsa.Cbat_extraction.Infinite (lo, hi) -> Printf.sprintf "Infinite(%Ld,%Ld)" lo hi
  | Vsa.Cbat_extraction.Caller (lo, hi) -> Printf.sprintf "Caller(%Ld,%Ld)" lo hi
  | Vsa.Cbat_extraction.Mixed (lo, hi) -> Printf.sprintf "Mixed(%Ld,%Ld)" lo hi
  | Vsa.Cbat_extraction.Dead -> "Dead"

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
(* The probes' direct-jump CFG view: successors, reachability, and the
   cyclic SCCs (a naive replica of Cbat_wto's SCC — the probes want the
   plain listing, not the WTO component structure). *)
let cfg_succs (blk : blk term) : tid list =
  Term.enum jmp_t blk
  |> Seq.filter_map ~f:(fun j ->
      match Jmp.kind j with
      | Goto (Direct t) | Ret (Direct t) -> Some t
      | Call c -> (
          match Call.target c with
          | Direct t -> Some t
          | _ -> None)
      | _ -> None)
  |> Seq.to_list

let cfg_of (sub : sub term) : (tid * tid list) list =
  Term.enum blk_t sub
  |> Seq.map ~f:(fun b -> (Term.tid b, cfg_succs b))
  |> Seq.to_list

let succs_of (cfg : (tid * tid list) list) (t : tid) : tid list =
  match Base.List.Assoc.find cfg t ~equal:Tid.equal with
  | Some ts -> ts
  | None -> []

let reachable (cfg : (tid * tid list) list) (start : tid) (target : tid) :
    bool =
  let rec go seen = function
    | [] -> false
    | t :: rest ->
      if Tid.equal t target then true
      else if Base.List.mem seen t ~equal:Tid.equal then go seen rest
      else go (t :: seen) (succs_of cfg t @ rest)
  in
  go [] [ start ]

let on_cycle (cfg : (tid * tid list) list) (t : tid) : bool =
  Base.List.exists (succs_of cfg t) ~f:(fun s -> reachable cfg s t)

let cyclic_heads (cfg : (tid * tid list) list) : (tid * tid list) list =
  let cyc =
    Base.List.filter_map cfg ~f:(fun (t, _) ->
        if on_cycle cfg t then Some t else None)
  in
  let rec group = function
    | [] -> []
    | t :: rest ->
      let same_cycle x y = reachable cfg x y && reachable cfg y x in
      let comp, rest' =
        Base.List.partition_tf rest ~f:(fun x -> same_cycle t x)
      in
      let members = t :: comp in
      let head =
        Base.List.fold_left members ~init:t ~f:(fun acc x ->
            if String.compare (Tid.name x) (Tid.name acc) < 0 then x else acc)
      in
      (head, members) :: group rest'
  in
  group cyc

type cyclic_head_report = {
  head : tid;
  members : tid list;
  block : blk term;
  vars : var list;
  state : AI.t;
}

let cyclic_head_reports (sub : sub term) (sol : Vsa.vsa_sol) :
    cyclic_head_report list =
  let block_of_tid t =
    Term.enum blk_t sub
    |> Seq.find_exn ~f:(fun b -> Tid.equal (Term.tid b) t)
  in
  cyclic_heads (cfg_of sub)
  |> List.map (fun (head, members) ->
         let block = block_of_tid head in
         let vars =
           members
           |> Base.List.concat_map ~f:(fun t ->
                  Term.enum def_t (block_of_tid t)
                  |> Seq.map ~f:(fun d -> Var.base (Def.lhs d))
                  |> Seq.to_list)
           |> Base.List.dedup_and_sort
                ~compare:(fun a b -> String.compare (Var.name a) (Var.name b))
         in
         { head; members; block; vars; state = Graphlib.Std.Solution.get sol head })

let report_cyclic_heads ~(label : string) ~(sub : sub term)
    ~(sol : Vsa.vsa_sol) ~(print_one : cyclic_head_report -> unit) : unit =
  let reports = cyclic_head_reports sub sol in
  Printf.printf "%s (%d cyclic SCCs)\n" label (List.length reports);
  List.iter print_one reports

(* The probes' bench harness: the warmup + two-loop measure and the
   table printer, shared by the three bench probes. *)
let bench_now = Unix.gettimeofday

type bench_row = {
  keys : int option;
  name : string;
  n : int;
  ns_a : float;
  ns_b : float;
  w_a : float;
  w_b : float;
}

let bench_measure ?keys ~name ~n (f : unit -> unit) : bench_row =
  let warm = 1 + (n / 10) in
  for _ = 1 to warm do f () done;
  let loop () =
    let w0 = Gc.minor_words () in
    let t0 = bench_now () in
    for _ = 1 to n do f () done;
    let t1 = bench_now () in
    let w1 = Gc.minor_words () in
    ((t1 -. t0) *. 1e9 /. float_of_int n, (w1 -. w0) /. float_of_int n)
  in
  let ns_a, w_a = loop () in
  let ns_b, w_b = loop () in
  { keys; name; n; ns_a; ns_b; w_a; w_b }

(* The bench probes share one optional key column and one measurement row. *)
let bench_print_table ?(name_width = 46) (rows : bench_row list) : unit =
  let has_keys = List.exists (fun r -> r.keys <> None) rows in
  if has_keys then
    Printf.printf "%-*s %5s %8s %11s %11s %12s %12s %5s\n" name_width "op"
      "keys" "n" "ns/op A" "ns/op B" "words/op A" "words/op B" "agree"
  else
    Printf.printf "%-*s %8s %11s %11s %12s %12s %5s\n" name_width "op" "n"
      "ns/op A" "ns/op B" "words/op A" "words/op B" "agree";
  List.iter
    (fun r ->
      let agree = if r.w_a = r.w_b then "yes" else "NO" in
      match r.keys with
      | Some keys ->
        Printf.printf "%-*s %5d %8d %11.1f %11.1f %12.1f %12.1f %5s\n"
          name_width r.name keys r.n r.ns_a r.ns_b r.w_a r.w_b agree
      | None ->
        Printf.printf "%-*s %8d %11.1f %11.1f %12.1f %12.1f %5s\n"
          name_width r.name r.n r.ns_a r.ns_b r.w_a r.w_b agree)
    rows
