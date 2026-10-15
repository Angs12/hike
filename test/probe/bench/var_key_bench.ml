(* Micro-benchmark for C5 ("Var-keyed environments"): is a run-scoped
   [Var.t -> int] intern plus int-keyed / dense environments actually
   cheaper than the [Var]-keyed Core maps the analysis uses?  Reporting
   probe: ns/op and the exact minor-word bill per op, two consecutive
   loops per row; prints a table, asserts nothing, never installed.

   Rows mirror the candidate: the real [WordEnv] op, the bare [Var.Map]/
   [Var.Set] baseline, [Var.compare]/[Var.hash] alone, the intern
   Hashtbl lookup, the int-keyed [Int.Map] and dense array target, and
   the composed intern-then-lookup. *)

open Bap.Std
open Probe_common

module Ws = Cbat_clp_set_composite

(* The public production env op, for a direct cross-check. *)
module AI = Cbat_vsa.AI

(* The production env instantiation, reproduced exactly: production's
   [Cbat_ai_representation] applies this functor to the same key module
   and value lattice ([VarKey] over [WordSet]). *)
module VarKey = struct
  include Var
  let equal = same
end

module WordEnv = Cbat_map_lattice.Make_indexed_val (VarKey) (Ws)

(* The shared bench row carries an optional key-count column. *)
type row = Probe_common.bench_row

(* Exact minor words allocated since start; [Gc.minor_words] advances per
   allocation, unlike [Gc.quick_stat]'s counter which advances at minor
   GCs on OCaml 5. *)
let minor_words () : float = Gc.minor_words ()



(* Two consecutive loops, each preceded by a warmup; the bill is the
   minor-word delta divided by the iteration count.  [f] receives the
   1-based iteration index. *)
let measure ~keys ~name ~n (f : int -> unit) : row =
  let warm = 1 + (n / 10) in
  for i = 1 to warm do f i done;
  let loop () =
    let w0 = minor_words () in
    let t0 = Probe_common.bench_now () in
    for i = 1 to n do f i done;
    let t1 = Probe_common.bench_now () in
    let w1 = minor_words () in
    ((t1 -. t0) *. 1e9 /. float_of_int n, (w1 -. w0) /. float_of_int n)
  in
  let ns_a, w_a = loop () in
  let ns_b, w_b = loop () in
  { keys = Some keys; name; n; ns_a; ns_b; w_a; w_b }

let sink = ref 0
let keep (i : int) : unit = sink := !sink lxor i

(* The register spellings a real x86-64 env holds; a larger env is the
   rest virtual temps, as in the lifted BIR. *)
let register_names : string list =
  [ "RAX"; "RBX"; "RCX"; "RDX"; "RSI"; "RDI"; "RBP"; "RSP";
    "R8"; "R9"; "R10"; "R11"; "R12"; "R13"; "R14"; "R15";
    "XMM0"; "XMM1"; "XMM2"; "XMM3"; "XMM4"; "XMM5"; "XMM6"; "XMM7";
    "XMM8"; "XMM9"; "XMM10"; "XMM11"; "XMM12"; "XMM13"; "XMM14"; "XMM15";
    "RIP"; "EFLAGS"; "ZF"; "CF"; "SF"; "OF"; "PF"; "AF";
    "CS"; "DS"; "ES"; "FS"; "GS"; "SS" ]

let make_vars (n : int) : Var.t array =
  let regs = Core.Array.of_list register_names in
  let nregs = Core.Array.length regs in
  Core.Array.init n ~f:(fun i ->
      if i < nregs then Var.create regs.(i) (Imm 64)
      else Var.create ~is_virtual:true (Printf.sprintf "t%d" i) (Imm 64))

(* Intern key: frozen [Var.compare] semantics with the [==] fast path. *)
module Intern_key = struct
  type t = Var.t

  let compare a b = if a == b then 0 else Var.compare a b
  let hash = Var.hash
  let sexp_of_t = Var.sexp_of_t
  let t_of_sexp = Var.t_of_sexp
end

module Intern = Core.Hashtbl.Make (Intern_key)
module IntMap = Core.Map.Make (Core.Int)

type fixture = {
  vars : Var.t array;
  data : Ws.t;
  idx : int;
  word_env : WordEnv.t;
  ai : AI.t;
  var_map : int Var.Map.t;
  var_set : Var.Set.t;
  intern : int Intern.t;
  int_map : int IntMap.t;
  int_arr : int array;
}

let build (n : int) : fixture =
  let vars = make_vars n in
  let data = Ws.singleton (Cbat_word.of_int ~width:64 8) in
  let idx = Ws.get_idx data in
  let word_env =
    Core.Array.fold vars ~init:WordEnv.top ~f:(fun e v -> WordEnv.add e ~key:v ~data)
  in
  let ai =
    Core.Array.fold vars ~init:AI.top ~f:(fun e v -> AI.add_word e ~key:v ~data)
  in
  let var_map =
    Core.Array.foldi vars ~init:Var.Map.empty ~f:(fun i m v ->
        Core.Map.set m ~key:v ~data:i)
  in
  let var_set =
    Core.Array.fold vars ~init:Var.Set.empty ~f:(fun s v -> Core.Set.add s v)
  in
  let intern = Intern.create () in
  Core.Array.iteri vars ~f:(fun i v -> Core.Hashtbl.set intern ~key:v ~data:i);
  let int_map =
    Core.Array.foldi vars ~init:IntMap.empty ~f:(fun i m _ ->
        Core.Map.set m ~key:i ~data:(i * 3))
  in
  let int_arr = Core.Array.init n ~f:(fun i -> i * 3) in
  { vars; data; idx; word_env; ai; var_map; var_set; intern; int_map; int_arr }

let rows_for (n : int) : row list =
  let fx = build n in
  let mask = n - 1 in
  let key i = fx.vars.(i land mask) in
  let ref_word = ref fx.word_env in
  let ref_ai = ref fx.ai in
  let ref_map = ref fx.var_map in
  let ref_set = ref fx.var_set in
  let ref_im = ref fx.int_map in
  let mut_arr = Core.Array.copy fx.int_arr in
  [ measure ~keys:n ~name:"WordEnv.find" ~n:200_000 (fun i ->
        keep (Ws.get_idx (WordEnv.find fx.idx fx.word_env (key i))));
    measure ~keys:n ~name:"WordEnv.add" ~n:200_000 (fun i ->
        ref_word := WordEnv.add !ref_word ~key:(key i) ~data:fx.data);
    measure ~keys:n ~name:"AI.find_word (production)" ~n:200_000 (fun i ->
        keep (Ws.get_idx (AI.find_word fx.idx fx.ai (key i))));
    measure ~keys:n ~name:"AI.add_word (production)" ~n:200_000 (fun i ->
        ref_ai := AI.add_word !ref_ai ~key:(key i) ~data:fx.data);
    measure ~keys:n ~name:"Var.Map.find" ~n:200_000 (fun i ->
        keep (Option.value (Core.Map.find fx.var_map (key i)) ~default:(-1)));
    measure ~keys:n ~name:"Var.Map.set" ~n:200_000 (fun i ->
        ref_map := Core.Map.set !ref_map ~key:(key i) ~data:i);
    measure ~keys:n ~name:"Var.Set.mem" ~n:200_000 (fun i ->
        keep (if Core.Set.mem fx.var_set (key i) then 1 else 0));
    measure ~keys:n ~name:"Var.Set.add" ~n:200_000 (fun i ->
        ref_set := Core.Set.add !ref_set (key i));
    measure ~keys:n ~name:"Var.compare" ~n:1_000_000 (fun i ->
        keep (Var.compare (key i) (key (i + 1))));
    measure ~keys:n ~name:"Var.hash" ~n:1_000_000 (fun i ->
        keep (Var.hash (key i)));
    measure ~keys:n ~name:"intern find (Var.t -> int)" ~n:500_000 (fun i ->
        keep (Option.value (Core.Hashtbl.find fx.intern (key i)) ~default:(-1)));
    measure ~keys:n ~name:"Int.Map.find (int-keyed)" ~n:500_000 (fun i ->
        keep
          (Option.value (Core.Map.find fx.int_map (i land mask)) ~default:(-1)));
    measure ~keys:n ~name:"Int.Map.set (int-keyed)" ~n:500_000 (fun i ->
        ref_im := Core.Map.set !ref_im ~key:(i land mask) ~data:i);
    measure ~keys:n ~name:"int array get (dense)" ~n:1_000_000 (fun i ->
        keep fx.int_arr.(i land mask));
    measure ~keys:n ~name:"int array set (dense)" ~n:1_000_000 (fun i ->
        mut_arr.(i land mask) <- i);
    measure ~keys:n ~name:"composed: intern + Int.Map.find" ~n:300_000 (fun i ->
        match Core.Hashtbl.find fx.intern (key i) with
        | Some id ->
          keep (Option.value (Core.Map.find fx.int_map id) ~default:(-1))
        | None -> keep (-1));
    measure ~keys:n ~name:"composed: intern + Int.Map.set" ~n:300_000 (fun i ->
        match Core.Hashtbl.find fx.intern (key i) with
        | Some id -> ref_im := Core.Map.set !ref_im ~key:id ~data:i
        | None -> ());
    measure ~keys:n ~name:"composed: intern + array get" ~n:300_000 (fun i ->
        match Core.Hashtbl.find fx.intern (key i) with
        | Some id -> keep fx.int_arr.(id)
        | None -> keep (-1)) ]

let print_header () =
  Printf.printf "%-38s %5s %11s %11s %12s %12s %6s\n" "op" "keys" "ns/op A"
    "ns/op B" "words/op A" "words/op B" "agree"

let print_row (r : row) : unit =
  Printf.printf "%-38s %5d %11.1f %11.1f %12.1f %12.1f %6s\n" r.name
    (Option.value r.keys ~default:0)
    r.ns_a r.ns_b r.w_a r.w_b
    (if r.w_a = r.w_b then "yes" else "NO")

let () =
  init ();
  Printf.printf
    "var_key_bench — ns/op + exact minor-words/op, two consecutive loops\n%!";
  print_header ();
  List.iter
    (fun n -> List.iter print_row (rows_for n))
    [ 16; 64; 256 ];
  Printf.printf "\nsink=%d\n%!" !sink
