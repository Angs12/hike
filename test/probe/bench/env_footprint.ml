(* env_footprint: the abstract env's retained heap footprint.

   Runs the production solve ([Hike.Vsa.fixpoint]) and measures the
   reachable heap words of its per-block (pre, post) environments.
   [Obj.reachable_words] counts each reachable word once per call, so
   the persistent maps' shared structure is not double-counted.  The
   [AI.t] record is {memories; words}; the two fields are measured
   separately to split the footprint.

   Reporting probe: prints a table, asserts nothing, never installed.

   Usage: env_footprint.exe <binary> [subname ...]
          (no name = the whole binary, the largest 15 subs + the total;
           "--top N" = the N largest; "--all" = every sub) *)

open Bap.Std
open Probe_common

(* Reachable heap words from [o]; shared sub-graphs counted once. *)
let rw (o : Obj.t) : int = Obj.reachable_words o

(* The [AI.t] declaration is {memories; words}; field order gives the
   split.  A representation change trips the assert loudly. *)
let ai_field (i : int) (ai : Cbat_vsa.AI.t) : Obj.t =
  let o = Obj.repr ai in
  assert (Obj.size o >= 2);
  Obj.field o i

let memories_of = ai_field 0
let words_of = ai_field 1

let kib (w : int) : float = float_of_int w *. 8. /. 1024.

type row = {
  name : string;
  blocks : int;
  total : int;   (* whole (pre,post) map, shared nodes once *)
  w_words : int; (* aggregate of the word maps, shared nodes once *)
  m_words : int; (* aggregate of the memory maps, shared nodes once *)
  max_block : int; (* the largest single state's reachable words *)
}

let measure_sub (target : Bap_core_theory.Theory.Target.t) (sub : sub term) : row =
  let envs, _, _, _ =
    Probe_common.solve ~synth:Hike.Synth.empty
      ~callee:(Probe_common.callee_of ~synth:Hike.Synth.empty (Program.create ~subs:[ sub ] ())) target sub
  in
  let pairs = Core.Map.data envs in
  let pre = Core.List.map pairs ~f:fst in
  let post = Core.List.map pairs ~f:snd in
  let w_list =
    Core.List.map pre ~f:words_of @ Core.List.map post ~f:words_of in
  let m_list =
    Core.List.map pre ~f:memories_of @ Core.List.map post ~f:memories_of in
  let whole = rw (Obj.repr envs) in
  let w_words = rw (Obj.repr w_list) in
  let m_words = rw (Obj.repr m_list) in
  let max_block =
    Core.List.fold pairs ~init:0 ~f:(fun acc (a, b) ->
        Stdlib.max acc (Stdlib.max (rw (Obj.repr a)) (rw (Obj.repr b))))
  in
  { name = Sub.name sub;
    blocks = List.length pairs;
    total = whole;
    w_words;
    m_words;
    max_block }

let pct (part : int) (whole : int) : float =
  if whole = 0 then 0. else 100. *. float_of_int part /. float_of_int whole

let print_row (r : row) : unit =
  Printf.printf
    "%-28s %7d %12d %9.1f %7.1f%% %7.1f%% %10d\n%!"
    r.name r.blocks r.total (kib r.total)
    (pct r.w_words r.total) (pct r.m_words r.total)
    r.max_block

let rows_of (target : Bap_core_theory.Theory.Target.t) (subs : sub term list) :
    row list =
  Core.List.map subs ~f:(measure_sub target)

let print_rows_with_total ~(top : int) (rows : row list) : unit =
  let sorted =
    Core.List.sort rows ~compare:(fun a b -> Int.compare b.total a.total) in
  List.iter print_row (Core.List.take sorted top);
  let sum f = Core.List.fold rows ~init:0 ~f:(fun a r -> a + f r) in
  Printf.printf "%-28s %7d %12d %9.1f\n%!"
    "TOTAL" (sum (fun r -> r.blocks)) (sum (fun r -> r.total))
    (kib (sum (fun r -> r.total)))

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  init ();
  match args with
  | [] -> usage Sys.argv.(0) "<binary> [subname ...]"
  | path :: rest ->
    let proj = load_project path in
    let prog = Project.program proj in
    let target = Project.target proj in
    Printf.printf "=== env_footprint %s ===\n%!" (Filename.basename path);
    Printf.printf "%-28s %7s %12s %9s %8s %8s %10s\n%!"
      "sub" "blocks" "total(w)" "KiB" "words%" "mem%" "max(w)";
    (match rest with
     (* No name: the whole binary, the largest [top] subs + the total. *)
     | [] -> print_rows_with_total ~top:15 (rows_of target (all_subs prog))
     | [ "--all" ] ->
       print_rows_with_total ~top:Stdlib.max_int (rows_of target (all_subs prog))
     | [ "--top"; n ] ->
       print_rows_with_total ~top:(Stdlib.int_of_string n)
         (rows_of target (all_subs prog))
     | names ->
       Core.List.iter names ~f:(fun name ->
           match find_sub prog name with
           | Some sub -> print_row (measure_sub target sub)
           | None ->
             Printf.printf "%-28s  (not found)\n%!" name))
