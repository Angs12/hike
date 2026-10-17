(* Precision measurement driver: per-sub TSV precision buckets + BIN rollup,
   measured over the production solve (Hike.Drive.run's facts).
   Usage: dune exec test/probe/research/precision_probe.exe -- <binary> [<binary> ...]
   Gate-free: every def is denoted.
   Columns: binary, sub, 8 def, 6 ld, 5 ldstk, 5 ldstk_w, 4 ldstk_sh,
   4 defstk_sh (see [row_of]).
   L2a diag mode (HIKE_VSA_DIAG_BOTTOM=1) adds DIAG/DIAG_SUM lines; OFF output is plain. *)

open Bap.Std
open Probe_common

module AI = Cbat_vsa.AI
module Vsa = Cbat_vsa

(* Set-composite domain of AI word values. *)
module Ws = Cbat_clp_set_composite

(* Default OFF; HIKE_VSA_DIAG_BOTTOM=1 enables L2a diag mode. *)
let diag_on () : bool =
  match Sys.getenv_opt "HIKE_VSA_DIAG_BOTTOM" with
  | Some "1" -> true
  | _ -> false

(* Default OFF; HIKE_VSA_DIAG_ACC=1 dumps one DIAG_ACC line per memory
   access: the address's class, its offset extrema under the tag-meet
   and before-state views, and its absolute extrema. *)
let acc_on () : bool =
  match Sys.getenv_opt "HIKE_VSA_DIAG_ACC" with
  | Some "1" -> true
  | _ -> false

(* Default OFF; HIKE_VSA_DIAG_DEFS=1 dumps one DIAG_DEF line per word def:
   its class, cardinality, extrema and rhs.  Two builds' dumps diff into
   the per-def bucket moves a column total cannot attribute. *)
let defs_on () : bool =
  match Sys.getenv_opt "HIKE_VSA_DIAG_DEFS" with
  | Some "1" -> true
  | _ -> false

let () = Printexc.record_backtrace true

module Rows = Precision_probe_rows
module Sub_stats = Rows.Sub_stats

type outcome =
  | Ok of Sub_stats.t
  | Crash of string * string (* exception description * backtrace *)

(* Classification. *)

let classify_def = Rows.classify_def
let classify_ld = Rows.classify_ld
let classify_operand = Rows.classify_operand

(* Bil binop constructor name. *)
let binop_name (op : Bil.binop) : string =
  match op with
  | Bil.PLUS -> "PLUS"
  | Bil.MINUS -> "MINUS"
  | Bil.TIMES -> "TIMES"
  | Bil.DIVIDE -> "DIVIDE"
  | Bil.SDIVIDE -> "SDIVIDE"
  | Bil.MOD -> "MOD"
  | Bil.SMOD -> "SMOD"
  | Bil.LSHIFT -> "LSHIFT"
  | Bil.RSHIFT -> "RSHIFT"
  | Bil.ARSHIFT -> "ARSHIFT"
  | Bil.AND -> "AND"
  | Bil.OR -> "OR"
  | Bil.XOR -> "XOR"
  | Bil.EQ -> "EQ"
  | Bil.NEQ -> "NEQ"
  | Bil.LT -> "LT"
  | Bil.LE -> "LE"
  | Bil.SLT -> "SLT"
  | Bil.SLE -> "SLE"

(* Bil cast constructor name. *)
let cast_name (ct : Bil.cast) : string =
  match ct with
  | Bil.UNSIGNED -> "UNSIGNED"
  | Bil.SIGNED -> "SIGNED"
  | Bil.HIGH -> "HIGH"
  | Bil.LOW -> "LOW"

(* Per-sub measurement. *)

(* Address argument of either BIL Load/Store form. *)
let addr_exp_of_rhs (e : exp) : exp option =
  match e with
  | Bil.Load (_, a, _, _) -> Some a
  | Bil.Store (_, a, _, _, _) -> Some a
  | _ -> None

(* One L2a DIAG line for a bottom word def. *)
let diag_bottom (bname : string) (sub' : sub term) (b : blk term)
    (d : def term) (input_bottom : bool) (st_before : AI.t) : unit =
  let class_of (e : exp) : string =
    match Vsa.Test_seam.denote_imm_exp e st_before with
    | Error _ -> "err"
    | Ok ws -> classify_operand ws in
  let kind, op1, op2 =
    match Def.rhs d with
    | Bil.BinOp (op, x, y) -> binop_name op, class_of x, class_of y
    | Bil.Load (_, a, _, _) -> "load", class_of a, "n/a"
    | Bil.Cast (ct, _, _) -> "cast:" ^ cast_name ct, "n/a", "n/a"
    | _ -> "other", "n/a", "n/a" in
  Printf.printf "DIAG\t%s\t%s\t%s\t%s\t%d\t%s\t%s\t%s\t%s\n"
    bname (Sub.name sub') (Tid.to_string (Term.tid b))
    (Tid.to_string (Term.tid d))
    (if input_bottom then 1 else 0)
    (Var.name (Def.lhs d)) kind op1 op2;
  flush stdout

(* One DIAG_DEF line: the def's value class, cardinality, extrema and
   rhs, so two runs' dumps attribute every bucket move to a def. *)
let diag_def (bname : string) (sub' : sub term) (b : blk term) (d : def term)
    (st_before : AI.t) (ws : Ws.t) : unit =
  let class_of (e : exp) : string =
    match Vsa.Test_seam.denote_imm_exp e st_before with
    | Error _ -> "err"
    | Ok ws -> classify_operand ws in
  let kind, op1, op2 =
    match Def.rhs d with
    | Bil.BinOp (op, x, y) -> binop_name op, class_of x, class_of y
    | Bil.Load (_, a, _, _) -> "load", class_of a, "n/a"
    | Bil.Store (_, a, u, _, _) -> "store", class_of a, class_of u
    | Bil.Cast (ct, _, _) -> "cast:" ^ cast_name ct, "n/a", "n/a"
    | Bil.UnOp (_, x) -> "unop", class_of x, "n/a"
    | _ -> "other", "n/a", "n/a" in
  let card =
    if Ws.is_top ws then "top"
    else
      match Cbat_word.to_int (Ws.cardinality ws) with
      | Ok k -> string_of_int k
      | Error _ -> "big" in
  let i64_of_word (w : Cbat_word.t) : string =
    match Cbat_word.to_int64 w with
    | Ok v -> Printf.sprintf "%Ld" v
    | Error _ -> "?" in
  let ext =
    match Ws.min_elem ws, Ws.max_elem ws with
    | Some lo, Some hi ->
      Printf.sprintf "%s..%s" (i64_of_word lo) (i64_of_word hi)
    | _ -> "n/a" in
  Printf.printf "DIAG_DEF\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n"
    bname (Sub.name sub') (Tid.to_string (Term.tid b))
    (Tid.to_string (Term.tid d)) (Var.name (Def.lhs d))
    (classify_operand ws) card ext kind op1 op2 (def_to_string d);
  flush stdout

(* One DIAG_ACC line: the access address's class, its offset extrema
   (segment-relative) and absolute extrema under the tag-meet view, and
   its offset extrema under the def's before-state (the production
   denotation). *)
let diag_acc (bname : string) (sub' : sub term) (b : blk term) (d : def term)
    (stack : bool) (ws : Ws.t) (a : exp) (st_before : AI.t) : unit =
  let i64_of_word (w : Cbat_word.t) : string =
    match Cbat_word.to_int64 w with
    | Ok v -> Printf.sprintf "%Ld" v
    | Error _ -> "?" in
  let offs_of ws' = match Ws.offset_extrema ws' with
    | Some (lo, hi) -> Printf.sprintf "%s..%s" (i64_of_word lo) (i64_of_word hi)
    | None -> "n/a" in
  let abs = match Ws.min_elem ws, Ws.max_elem ws with
    | Some lo, Some hi ->
      Printf.sprintf "%s..%s" (i64_of_word lo) (i64_of_word hi)
    | _ -> "n/a" in
  let pre = match Vsa.Test_seam.denote_imm_exp a st_before with
    | Ok ws' -> offs_of ws'
    | Error _ -> "err" in
  let signed_of ws' = match Ws.min_elem_signed ws', Ws.max_elem_signed ws' with
    | Some mn, Some mx -> Printf.sprintf "%s..%s" (i64_of_word mn) (i64_of_word mx)
    | _ -> "n/a" in
  Printf.printf "DIAG_ACC\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%d\t%d\t%s\n"
    bname (Sub.name sub') (Tid.to_string (Term.tid b))
    (Tid.to_string (Term.tid d)) (def_to_string d)
    (classify_operand ws) (offs_of ws) pre abs (if stack then 1 else 0)
    (Ws.bitwidth ws) (signed_of ws);
  flush stdout

(* Walk blocks in def order, re-denote, classify. *)
(* The seeding predicate and the tag-state meet come from the shared probe
   seam. *)
let is_stack_access st addr =
  match Vsa.Test_seam.denote_imm_exp addr st with
  | Error _ -> false
  | Ok ws -> Rows.is_stack_value ws

let st_tag_of ~(tags : Vsa.vsa_sol) (blk : blk term) (addr : exp)
    (st_before : AI.t) : AI.t =
  Exp.free_vars addr
  |> Core.Set.fold ~init:st_before ~f:(fun acc v ->
      match Var.typ v with
      | Type.Imm w ->
        let tag_v = AI.find_word w
            (Graphlib.Std.Solution.get tags (Term.tid blk)) v in
        let cur = AI.find_word w acc v in
        let mm = Ws.meet cur tag_v in
        if Cbat_word.is_zero (Ws.cardinality mm) || Ws.equal mm cur
        then acc
        else AI.add_word acc ~key:v ~data:mm
      | Type.Mem _ | Type.Unk -> acc)

let collect_stats (bname : string) (sub' : sub term)
    (sol : Vsa.vsa_sol) (tags : Vsa.vsa_sol) : Sub_stats.t =
  let s = Sub_stats.create (Sub.name sub') in
  (* L2a counters: bottom defs, live vs dead. *)
  let bottom_live = ref 0 in
  let bottom_dead = ref 0 in
  Term.enum blk_t sub'
  |> Seq.iter ~f:(fun b ->
      (* Per-block entry state from the fixpoint solution. *)
      (* Per-block TAG state is the block's IN-state ([tags = sol]). *)
      let st0 = Graphlib.Std.Solution.get tags (Term.tid b) in
      (* Frame relation lives in the state; no walk mirroring needed. *)
      (* Bottom defs count dead iff entry state is bottom. *)
      let input_bottom = AI.equal st0 AI.bottom in
      let st = ref st0 in
      Term.enum def_t b
      |> Seq.iter ~f:(fun d ->
          let st_before = !st in
          (* Sequential denotation, like the fixpoint. *)
          st := Vsa.Test_seam.denote_def d !st;
          (* Word-lhs defs only; bottom split by entry state. *)
          (match Var.typ (Def.lhs d) with
           | Type.Imm w ->
             let ws = AI.find_word w !st (Def.lhs d) in
              (* Gate-free: every def is denoted (spec §2.1). *)
             if defs_on () then diag_def bname sub' b d st_before ws;
             let stack = Rows.is_stack_value ws in
             let shape = Rows.shape_of ws in
             let b =
               match classify_def ws with
               | `Bottom ->
                 (* Env-gated operand dump for bottom defs. *)
                 if input_bottom then begin
                   incr bottom_dead;
                   if diag_on () then
                     diag_bottom bname sub' b d input_bottom
                       st_before
                 end else begin
                   incr bottom_live;
                   if diag_on () then
                     diag_bottom bname sub' b d input_bottom
                       st_before
                 end;
                 if input_bottom then `Bottom_dead else `Bottom_live
               | `Exact -> `Exact
               | `B2_3 -> `B2_3
               | `B4_8 -> `B4_8
               | `B9_64 -> `B9_64
               | `B65p -> `B65p
               | `Top -> `Top
             in
             Sub_stats.add_def s ~stack ~shape b
           | Type.Mem _ | Type.Unk -> ());
          (* Address metric in the PRE-def state. *)
          (match addr_exp_of_rhs (Def.rhs d) with
           | Some a ->
             let stack = is_stack_access st_before a in
             (* Addresses denoted with block IN-state, not re-denoted values. *)
              let st_tag = st_tag_of ~tags b a st_before in
             (match Vsa.Test_seam.denote_imm_exp a st_tag with
              | Error _ ->
                s.Sub_stats.ld_denote_err <- s.Sub_stats.ld_denote_err + 1
              | Ok ws ->
                if acc_on () then diag_acc bname sub' b d stack ws a st_before;
                (* Bottom split uses [input_bottom], as the def series. *)
                let lb = classify_ld ws input_bottom in
                Sub_stats.add_ld s ~stack ~shape:(Rows.shape_of ws) lb;
                (* Window buckets: stack-flagged finite non-top only. *)
                if stack && (lb = `Exact || lb = `Bounded) then begin
                  let wb, win = Rows.window_metric_of ws in
                  Sub_stats.add_window s wb;
                  match win with
                  | Some v ->
                    if Int64.compare v s.Sub_stats.ldstk_w_max > 0 then
                      s.Sub_stats.ldstk_w_max <- v
                  | None -> ()
                end)
           | None -> ())));
  (* Env-gated per-sub summary; consistent with the columns. *)
  if diag_on () then
    Printf.printf "DIAG_SUM\t%s\t%s\t%d\t%d\n" bname (Sub.name sub')
      !bottom_live !bottom_dead;
  flush stdout;
  s

(* Per-binary driver. *)

type bin_report = {
  bname : string;
  mutable nsubs : int;
  mutable nok : int;
  mutable ncrashes : int;
  mutable nloadfail : int;
  (* summed columns for the BIN rollup line *)
  mutable sum : Sub_stats.t;
}

(* Per-sub columns as strings (binary prefixed by caller). *)
let row_of (s : Sub_stats.t) : string list =
  [ s.Sub_stats.sname;
    string_of_int s.Sub_stats.def_exact;
    string_of_int s.Sub_stats.def_b2_3;
    string_of_int s.Sub_stats.def_b4_8;
    string_of_int s.Sub_stats.def_b9_64;
    string_of_int s.Sub_stats.def_b65p;
    string_of_int s.Sub_stats.def_top;
    string_of_int s.Sub_stats.def_bottom_live;
    string_of_int s.Sub_stats.def_bottom_dead;
    string_of_int s.Sub_stats.ld_exact;
    string_of_int s.Sub_stats.ld_bounded;
    string_of_int s.Sub_stats.ld_top;
    string_of_int s.Sub_stats.ld_bottom_live;
    string_of_int s.Sub_stats.ld_bottom_dead;
    string_of_int s.Sub_stats.ld_denote_err;
    string_of_int s.Sub_stats.ldstk_exact;
    string_of_int s.Sub_stats.ldstk_bounded;
    string_of_int s.Sub_stats.ldstk_top;
    string_of_int s.Sub_stats.ldstk_bottom_live;
    string_of_int s.Sub_stats.ldstk_bottom_dead;
    string_of_int s.Sub_stats.ldstk_w_b64;
    string_of_int s.Sub_stats.ldstk_w_4k;
    string_of_int s.Sub_stats.ldstk_w_2m;
    string_of_int s.Sub_stats.ldstk_w_big;
    Int64.to_string s.Sub_stats.ldstk_w_max;
    string_of_int s.Sub_stats.ldstk_sh_stack;
    string_of_int s.Sub_stats.ldstk_sh_window;
    string_of_int s.Sub_stats.ldstk_sh_other;
    string_of_int s.Sub_stats.ldstk_sh_lost;
    string_of_int s.Sub_stats.defstk_sh_stack;
    string_of_int s.Sub_stats.defstk_sh_window;
    string_of_int s.Sub_stats.defstk_sh_other;
    string_of_int s.Sub_stats.defstk_sh_lost ]

let print_sub_line (path : string) (s : Sub_stats.t) : unit =
  Printf.printf "%s\n" (String.concat "\t" (path :: row_of s));
  flush stdout

(* BIN rollup: summed columns + the exact, full, and bound
   percentages.  The bound rate is the address-precision headline;
   [ldstk_exact] alone is shape-blind. *)
let print_bin_line (r : bin_report) : unit =
  let s = r.sum in
  let denom_filtered = s.Sub_stats.ldstk_exact + s.Sub_stats.ldstk_bounded
                       + s.Sub_stats.ldstk_top
                       + s.Sub_stats.ldstk_bottom_live in
  let denom_full = denom_filtered + s.Sub_stats.ldstk_bottom_dead in
  let pct n d =
    if d = 0 then "n/a"
    else Printf.sprintf "%.2f" (100.0 *. float n /. float d) in
  let pct_filtered = pct s.Sub_stats.ldstk_exact denom_filtered in
  let pct_full = pct s.Sub_stats.ldstk_exact denom_full in
  let pct_bound =
    pct (s.Sub_stats.ldstk_exact + s.Sub_stats.ldstk_bounded) denom_filtered in
  (* BIN reuses the sub layout ("BIN", basename, sums). *)
  let cols = Filename.basename r.bname :: List.tl (row_of s) in
  Printf.printf "%s\n"
    (String.concat "\t" ("BIN" :: cols @ [ pct_filtered; pct_full; pct_bound ]));
  flush stdout

(* One sub measured over the production solve: the block IN-states the
   discovery worklist solved (with its summaries and resolved edges); a
   block the solve never reached reads bottom. *)
let run_sub (bname : string) (facts : Hike.Kb.facts) (sub : sub term) : outcome =
  try
    let sol =
      Graphlib.Std.Solution.create
        (Core.Map.map facts.Hike.Kb.envs ~f:fst) AI.bottom in
    (* The walk re-denotes defs, so it reads the images the solve read. *)
    let st =
      Vsa.with_images facts.Hike.Kb.images
        (fun () -> collect_stats bname sub sol sol) in
    Ok st
  with e ->
    Crash (describe_exn e, Printexc.get_backtrace ())

let run_binary (path : string) : bin_report =
  let r = { bname = path; nsubs = 0; nok = 0; ncrashes = 0; nloadfail = 0;
            sum = Sub_stats.create "BIN" } in
  let bname = Filename.basename path in
  let run_one facts sub =
    r.nsubs <- r.nsubs + 1;
    match run_sub bname facts sub with
    | Ok st ->
      r.nok <- r.nok + 1;
      Sub_stats.add_sum r.sum st;
      print_sub_line path st
    | Crash (es, bt) ->
      r.ncrashes <- r.ncrashes + 1;
      Printf.printf "CRASH\t%s\t%s\t%s\n" path (Sub.name sub) es;
      (match bt with
       | "" -> ()
       | _ -> Printf.printf "  backtrace:\n%s\n" bt);
      flush stdout
  in
  match Probe_common.ws_run_discovered path run_one with
  | Ok _ -> print_bin_line r; r
  | Error (Probe_common.Load_error e) ->
    r.nloadfail <- 1;
    ws_load_fail path e;
    r
  | Error (Probe_common.Run_error e) ->
    r.nloadfail <- 1;
    ws_load_exn path e;
    r

let () =
  let paths = List.tl (Array.to_list Sys.argv) in
  match paths with
  | [] -> ws_usage Sys.argv.(0)
  | _ ->
    (* Init the BAP environment. *)
    ws_init "precision_probe";
    Printf.printf "=== precision probe (gate-free) ===\n";
    flush stdout;
    let reports = List.map run_binary paths in
    Printf.printf "\n=== precision probe summary ===\n";
    Printf.printf "%-28s %7s %6s %8s %10s\n"
      "binary" "subs" "ok" "crashes" "loadfail";
    List.iter
      (fun r ->
        Printf.printf "%-28s %7d %6d %8d %10d\n"
          (Filename.basename r.bname) r.nsubs r.nok r.ncrashes r.nloadfail)
      reports;
    let crashes = List.fold_left (fun acc r -> acc + r.ncrashes) 0 reports in
    let loadfails = List.fold_left (fun acc r -> acc + r.nloadfail) 0 reports in
    ws_finish ~pass:"PRECISION PROBE: PASS (no crashes)"
      ~fail:"PRECISION PROBE: FAIL (crashes present)" crashes loadfails
