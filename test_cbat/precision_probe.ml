(* Precision measurement driver: per-sub fixpoint, TSV precision buckets + BIN rollup.
   Usage: dune exec test_cbat/precision_probe.exe -- <binary> [<binary> ...]
   Gate-free: every def is denoted; entry is [Vsa.init_sol sub] (AI.top).
   Columns: binary, sub, sub_ms, 8 def, 9 tagged, 6 ld, 5 ldstk, 5 ldstk_w (see [row_of]).
   L2a diag mode (HIKE_VSA_DIAG_BOTTOM=1) adds DIAG/DIAG_SUM lines; OFF output is plain. *)

open Bap.Std
open Probe_common

module AI = Cbat_vsa.AI
module Mem = Cbat_vsa.Mem
module Vsa = Cbat_vsa

(* Set-composite domain of AI word values. *)
module Ws = Cbat_clp_set_composite
module W = Word

(* Default OFF; HIKE_VSA_DIAG_BOTTOM=1 enables L2a diag mode. *)
let diag_on () : bool =
  match Sys.getenv_opt "HIKE_VSA_DIAG_BOTTOM" with
  | Some "1" -> true
  | _ -> false

(* Fixpoint entry solution: production default. *)
let init_sol_of (sub' : sub term) : Vsa.vsa_sol =
  Vsa.init_sol sub'

let () = Printexc.record_backtrace true

(* Classification buckets. *)

(* Bottom bucket split by the block's entry state. *)
type def_bucket =
  [ `Exact | `B2_3 | `B4_8 | `B9_64 | `B65p | `Top
  | `Bottom_live | `Bottom_dead ]

(* Bottom bucket split by the block's input state (L1). *)
type ld_bucket =
  [ `Exact | `Bounded | `Top | `Bottom_live | `Bottom_dead ]

(* Window buckets over stack-flagged finite non-top addresses. *)
type win_bucket = [ `W_b64 | `W_4k | `W_2m | `W_big ]

(* Per-sub statistics record. *)

module Sub_stats = struct
  type t = {
    sname : string;
    mutable sub_ms : int;
    (* all-defs series (8 buckets) *)
    mutable def_exact : int;
    mutable def_b2_3 : int;
    mutable def_b4_8 : int;
    mutable def_b9_64 : int;
    mutable def_b65p : int;
    mutable def_top : int;
    mutable def_bottom_live : int;
    mutable def_bottom_dead : int;
    (* tagged-defs-only series (8 buckets + count) *)
    mutable def_tagged_exact : int;
    mutable def_tagged_b2_3 : int;
    mutable def_tagged_b4_8 : int;
    mutable def_tagged_b9_64 : int;
    mutable def_tagged_b65p : int;
    mutable def_tagged_top : int;
    mutable def_tagged_bottom_live : int;
    mutable def_tagged_bottom_dead : int;
    mutable def_tagged_count : int;
    (* load/store address series (6) *)
    mutable ld_exact : int;
    mutable ld_bounded : int;
    mutable ld_top : int;
    mutable ld_bottom_live : int;
    mutable ld_bottom_dead : int;
    mutable ld_denote_err : int;
    (* stack-flagged address subset (5) *)
    mutable ldstk_exact : int;
    mutable ldstk_bounded : int;
    mutable ldstk_top : int;
    mutable ldstk_bottom_live : int;
    mutable ldstk_bottom_dead : int;
    (* window-size buckets (5) *)
    mutable ldstk_w_b64 : int;
    mutable ldstk_w_4k : int;
    mutable ldstk_w_2m : int;
    mutable ldstk_w_big : int;
    mutable ldstk_w_max : int64;
  }

  let create (name : string) : t =
    { sname = name; sub_ms = 0;
      def_exact = 0; def_b2_3 = 0; def_b4_8 = 0; def_b9_64 = 0;
      def_b65p = 0; def_top = 0; def_bottom_live = 0;
      def_bottom_dead = 0;
      def_tagged_exact = 0; def_tagged_b2_3 = 0; def_tagged_b4_8 = 0;
      def_tagged_b9_64 = 0; def_tagged_b65p = 0; def_tagged_top = 0;
      def_tagged_bottom_live = 0; def_tagged_bottom_dead = 0;
      def_tagged_count = 0;
      ld_exact = 0; ld_bounded = 0; ld_top = 0; ld_bottom_live = 0;
      ld_bottom_dead = 0; ld_denote_err = 0;
      ldstk_exact = 0; ldstk_bounded = 0; ldstk_top = 0;
      ldstk_bottom_live = 0; ldstk_bottom_dead = 0;
      ldstk_w_b64 = 0; ldstk_w_4k = 0; ldstk_w_2m = 0; ldstk_w_big = 0;
      ldstk_w_max = 0L }

  (* Count a word def into both series when tagged. *)
  let add_def (s : t) (tagged : bool) (b : def_bucket) : unit =
    (match b with
     | `Exact -> s.def_exact <- s.def_exact + 1
     | `B2_3 -> s.def_b2_3 <- s.def_b2_3 + 1
     | `B4_8 -> s.def_b4_8 <- s.def_b4_8 + 1
     | `B9_64 -> s.def_b9_64 <- s.def_b9_64 + 1
     | `B65p -> s.def_b65p <- s.def_b65p + 1
     | `Top -> s.def_top <- s.def_top + 1
     | `Bottom_live -> s.def_bottom_live <- s.def_bottom_live + 1
     | `Bottom_dead -> s.def_bottom_dead <- s.def_bottom_dead + 1);
    if tagged then begin
      s.def_tagged_count <- s.def_tagged_count + 1;
      match b with
      | `Exact -> s.def_tagged_exact <- s.def_tagged_exact + 1
      | `B2_3 -> s.def_tagged_b2_3 <- s.def_tagged_b2_3 + 1
      | `B4_8 -> s.def_tagged_b4_8 <- s.def_tagged_b4_8 + 1
      | `B9_64 -> s.def_tagged_b9_64 <- s.def_tagged_b9_64 + 1
      | `B65p -> s.def_tagged_b65p <- s.def_tagged_b65p + 1
      | `Top -> s.def_tagged_top <- s.def_tagged_top + 1
      | `Bottom_live ->
        s.def_tagged_bottom_live <- s.def_tagged_bottom_live + 1
      | `Bottom_dead ->
        s.def_tagged_bottom_dead <- s.def_tagged_bottom_dead + 1
    end

  let add_ld (s : t) (stack : bool) (b : ld_bucket) : unit =
    match b with
    | `Exact ->
      s.ld_exact <- s.ld_exact + 1;
      if stack then s.ldstk_exact <- s.ldstk_exact + 1
    | `Bounded ->
      s.ld_bounded <- s.ld_bounded + 1;
      if stack then s.ldstk_bounded <- s.ldstk_bounded + 1
    | `Top ->
      s.ld_top <- s.ld_top + 1;
      if stack then s.ldstk_top <- s.ldstk_top + 1
    | `Bottom_live ->
      s.ld_bottom_live <- s.ld_bottom_live + 1;
      if stack then s.ldstk_bottom_live <- s.ldstk_bottom_live + 1
    | `Bottom_dead ->
      s.ld_bottom_dead <- s.ld_bottom_dead + 1;
      if stack then s.ldstk_bottom_dead <- s.ldstk_bottom_dead + 1

  let add_window (s : t) (b : win_bucket) : unit =
    match b with
    | `W_b64 -> s.ldstk_w_b64 <- s.ldstk_w_b64 + 1
    | `W_4k -> s.ldstk_w_4k <- s.ldstk_w_4k + 1
    | `W_2m -> s.ldstk_w_2m <- s.ldstk_w_2m + 1
    | `W_big -> s.ldstk_w_big <- s.ldstk_w_big + 1
end

type outcome =
  | Ok of Sub_stats.t
  | Crash of string * string (* exception description * backtrace *)

(* Classification. *)

(* TOP/BOTTOM first; cardn buckets by size; unconvertible is b65p. *)
let classify_def (ws : Ws.t) :
    [ `Exact | `B2_3 | `B4_8 | `B9_64 | `B65p | `Top | `Bottom ] =
  if Ws.is_top ws then `Top
  else if Ws.is_bottom ws then `Bottom
  else
    let cardn = Ws.cardinality ws in
    match Cbat_word.to_int cardn with
    | Error _ -> `B65p
    | Ok n ->
      if n = 1 then `Exact
      else if n <= 3 then `B2_3
      else if n <= 8 then `B4_8
      else if n <= 64 then `B9_64
      else `B65p

(* Bottom first; exact/bounded/top/split-bottom. *)
let classify_ld (ws : Ws.t) (input_bottom : bool) : ld_bucket =
  if Ws.is_bottom ws then
    (if input_bottom then `Bottom_dead else `Bottom_live)
  else if Ws.is_top ws then `Top
  else
    match Cbat_word.to_int (Ws.cardinality ws) with
    | Ok 1 -> `Exact
    | _ -> `Bounded

(* Operand class: empty/exact/fin:k/big/top. *)
let classify_operand (ws : Ws.t) : string =
  if Ws.is_top ws then "top"
  else if Ws.is_bottom ws then "empty"
  else
    match Cbat_word.to_int (Ws.cardinality ws) with
    | Error _ -> "big"
    | Ok 0 -> "empty"
    | Ok 1 -> "exact"
    | Ok k when k <= 64 -> Printf.sprintf "fin:%d" k
    | Ok _ -> "big"

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

(* Signed-span window bucket + int64 value for w_max. *)
let window_metric_of (ws : Ws.t) : win_bucket * int64 option =
  if Ws.bitwidth ws > 64 then (`W_big, None)
  else
    match Ws.min_elem_signed ws, Ws.max_elem_signed ws with
    | Some mn, Some mx ->
      let w = Ws.bitwidth ws in
      let win = Cbat_word.add (Cbat_word.sub mx mn) (Cbat_word.one w) in
      (match Cbat_word.to_int64 win with
       | Ok v when v < 0L -> (`W_big, Some Int64.max_int)
       | Ok 0L -> (`W_big, Some Int64.max_int)
       | Ok v ->
         (if v <= 64L then `W_b64
          else if v <= 4096L then `W_4k
          else if v <= 1048576L then `W_2m
          else `W_big), Some v
       | Error _ -> (`W_big, Some Int64.max_int))
    | _ -> (`W_big, None)

(* Per-sub measurement. *)

(* Address argument of either BIL Load/Store form. *)
let addr_exp_of_rhs (e : exp) : exp option =
  match e with
  | Bil.Load (_, a, _, _) -> Some a
  | Bil.Store (_, a, _, _, _) -> Some a
  | _ -> None

(* One L2a DIAG line for a bottom word def. *)
let diag_bottom (bname : string) (sub' : sub term) (b : blk term)
    (d : def term) (input_bottom : bool) (tagged : bool)
    (frame : Vsa.frame option) (st_before : AI.t) : unit =
  let class_of (e : exp) : string =
    match Vsa.denote_imm_exp e st_before with
    | Error _ -> "err"
    | Ok ws -> classify_operand ws in
  let kind, op1, op2 =
    match Def.rhs d with
    | Bil.BinOp (op, x, y) -> binop_name op, class_of x, class_of y
    | Bil.Load (_, a, _, _) ->
      "load", class_of (Vsa.rewrite_addr frame a), "n/a"
    | Bil.Cast (ct, _, _) -> "cast:" ^ cast_name ct, "n/a", "n/a"
    | _ -> "other", "n/a", "n/a" in
  Printf.printf "DIAG\t%s\t%s\t%s\t%s\t%d\t%d\t%s\t%s\t%s\t%s\n"
    bname (Sub.name sub') (Tid.to_string (Term.tid b))
    (Tid.to_string (Term.tid d))
    (if input_bottom then 1 else 0) (if tagged then 1 else 0)
    (Var.name (Def.lhs d)) kind op1 op2;
  flush stdout

(* Walk blocks in def order, re-denote, classify. *)
let collect_stats (bname : string) (sub' : sub term)
    (sol : Vsa.vsa_sol) (tags : Vsa.vsa_sol) : Sub_stats.t =
  let s = Sub_stats.create (Sub.name sub') in
  (* L2a counters: bottom defs, live vs dead. *)
  let bottom_live = ref 0 in
  let bottom_dead = ref 0 in
  (* Stack iff the name is RSP/RBP (spec §2.1: every def is denoted). *)
  let is_stack_addr (a : exp) : bool =
    Exp.free_vars a
    |> Core.Set.exists ~f:(fun v ->
        let n = Var.name v in
        String.equal n "RSP" || String.equal n "RBP") in
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
          st := Vsa.denote_def d !st;
          (* Word-lhs defs only; bottom split by entry state. *)
          (match Var.typ (Def.lhs d) with
           | Type.Imm w ->
             let ws = AI.find_word w !st (Def.lhs d) in
              (* Gate-free: every def is denoted (spec §2.1). *)
              let tagged = true in
             let b =
               match classify_def ws with
               | `Bottom ->
                 (* Env-gated operand dump for bottom defs. *)
                 if input_bottom then begin
                   incr bottom_dead;
                   if diag_on () then
                     diag_bottom bname sub' b d input_bottom tagged
                       (Vsa.frame_of_state st_before) st_before
                 end else begin
                   incr bottom_live;
                   if diag_on () then
                     diag_bottom bname sub' b d input_bottom tagged
                       (Vsa.frame_of_state st_before) st_before
                 end;
                 if input_bottom then `Bottom_dead else `Bottom_live
               | `Exact -> `Exact
               | `B2_3 -> `B2_3
               | `B4_8 -> `B4_8
               | `B9_64 -> `B9_64
               | `B65p -> `B65p
               | `Top -> `Top
             in
             Sub_stats.add_def s tagged b
           | Type.Mem _ | Type.Unk -> ());
          (* Address metric in the PRE-def state. *)
          (match addr_exp_of_rhs (Def.rhs d) with
           | Some a ->
             let stack = is_stack_addr a in
             let a' =
               Vsa.rewrite_addr (Vsa.frame_of_state st_before) a in
             (* Addresses denoted with block IN-state, not re-denoted values. *)
             (* M6 meet is [st_tag_of] (genuine-subset gate). *)
             let st_tag =
               Vsa.Cbat_extraction.st_tag_of ~tags b a' st_before in
             (match Vsa.denote_imm_exp a' st_tag with
              | Error _ ->
                s.Sub_stats.ld_denote_err <- s.Sub_stats.ld_denote_err + 1
              | Ok ws ->
                (* Bottom split uses [input_bottom], as the def series. *)
                let lb = classify_ld ws input_bottom in
                Sub_stats.add_ld s stack lb;
                (* Window buckets: stack-flagged finite non-top only. *)
                if stack && (lb = `Exact || lb = `Bounded) then begin
                  let wb, win = window_metric_of ws in
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
  [ s.Sub_stats.sname; string_of_int s.Sub_stats.sub_ms;
    string_of_int s.Sub_stats.def_exact;
    string_of_int s.Sub_stats.def_b2_3;
    string_of_int s.Sub_stats.def_b4_8;
    string_of_int s.Sub_stats.def_b9_64;
    string_of_int s.Sub_stats.def_b65p;
    string_of_int s.Sub_stats.def_top;
    string_of_int s.Sub_stats.def_bottom_live;
    string_of_int s.Sub_stats.def_bottom_dead;
    string_of_int s.Sub_stats.def_tagged_exact;
    string_of_int s.Sub_stats.def_tagged_b2_3;
    string_of_int s.Sub_stats.def_tagged_b4_8;
    string_of_int s.Sub_stats.def_tagged_b9_64;
    string_of_int s.Sub_stats.def_tagged_b65p;
    string_of_int s.Sub_stats.def_tagged_top;
    string_of_int s.Sub_stats.def_tagged_bottom_live;
    string_of_int s.Sub_stats.def_tagged_bottom_dead;
    string_of_int s.Sub_stats.def_tagged_count;
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
    Int64.to_string s.Sub_stats.ldstk_w_max ]

let print_sub_line (path : string) (s : Sub_stats.t) : unit =
  Printf.printf "%s\n" (String.concat "\t" (path :: row_of s));
  flush stdout

(* Accumulate one sub into the BIN sum (w_max takes max). *)
let add_sum (dst : Sub_stats.t) (src : Sub_stats.t) : unit =
  dst.Sub_stats.sub_ms <- dst.Sub_stats.sub_ms + src.Sub_stats.sub_ms;
  dst.Sub_stats.def_exact <- dst.Sub_stats.def_exact + src.Sub_stats.def_exact;
  dst.Sub_stats.def_b2_3 <- dst.Sub_stats.def_b2_3 + src.Sub_stats.def_b2_3;
  dst.Sub_stats.def_b4_8 <- dst.Sub_stats.def_b4_8 + src.Sub_stats.def_b4_8;
  dst.Sub_stats.def_b9_64 <- dst.Sub_stats.def_b9_64 + src.Sub_stats.def_b9_64;
  dst.Sub_stats.def_b65p <- dst.Sub_stats.def_b65p + src.Sub_stats.def_b65p;
  dst.Sub_stats.def_top <- dst.Sub_stats.def_top + src.Sub_stats.def_top;
  dst.Sub_stats.def_bottom_live <-
    dst.Sub_stats.def_bottom_live + src.Sub_stats.def_bottom_live;
  dst.Sub_stats.def_bottom_dead <-
    dst.Sub_stats.def_bottom_dead + src.Sub_stats.def_bottom_dead;
  dst.Sub_stats.def_tagged_exact <-
    dst.Sub_stats.def_tagged_exact + src.Sub_stats.def_tagged_exact;
  dst.Sub_stats.def_tagged_b2_3 <-
    dst.Sub_stats.def_tagged_b2_3 + src.Sub_stats.def_tagged_b2_3;
  dst.Sub_stats.def_tagged_b4_8 <-
    dst.Sub_stats.def_tagged_b4_8 + src.Sub_stats.def_tagged_b4_8;
  dst.Sub_stats.def_tagged_b9_64 <-
    dst.Sub_stats.def_tagged_b9_64 + src.Sub_stats.def_tagged_b9_64;
  dst.Sub_stats.def_tagged_b65p <-
    dst.Sub_stats.def_tagged_b65p + src.Sub_stats.def_tagged_b65p;
  dst.Sub_stats.def_tagged_top <-
    dst.Sub_stats.def_tagged_top + src.Sub_stats.def_tagged_top;
  dst.Sub_stats.def_tagged_bottom_live <-
    dst.Sub_stats.def_tagged_bottom_live + src.Sub_stats.def_tagged_bottom_live;
  dst.Sub_stats.def_tagged_bottom_dead <-
    dst.Sub_stats.def_tagged_bottom_dead + src.Sub_stats.def_tagged_bottom_dead;
  dst.Sub_stats.def_tagged_count <-
    dst.Sub_stats.def_tagged_count + src.Sub_stats.def_tagged_count;
  dst.Sub_stats.ld_exact <- dst.Sub_stats.ld_exact + src.Sub_stats.ld_exact;
  dst.Sub_stats.ld_bounded <- dst.Sub_stats.ld_bounded + src.Sub_stats.ld_bounded;
  dst.Sub_stats.ld_top <- dst.Sub_stats.ld_top + src.Sub_stats.ld_top;
  dst.Sub_stats.ld_bottom_live <-
    dst.Sub_stats.ld_bottom_live + src.Sub_stats.ld_bottom_live;
  dst.Sub_stats.ld_bottom_dead <-
    dst.Sub_stats.ld_bottom_dead + src.Sub_stats.ld_bottom_dead;
  dst.Sub_stats.ld_denote_err <-
    dst.Sub_stats.ld_denote_err + src.Sub_stats.ld_denote_err;
  dst.Sub_stats.ldstk_exact <-
    dst.Sub_stats.ldstk_exact + src.Sub_stats.ldstk_exact;
  dst.Sub_stats.ldstk_bounded <-
    dst.Sub_stats.ldstk_bounded + src.Sub_stats.ldstk_bounded;
  dst.Sub_stats.ldstk_top <- dst.Sub_stats.ldstk_top + src.Sub_stats.ldstk_top;
  dst.Sub_stats.ldstk_bottom_live <-
    dst.Sub_stats.ldstk_bottom_live + src.Sub_stats.ldstk_bottom_live;
  dst.Sub_stats.ldstk_bottom_dead <-
    dst.Sub_stats.ldstk_bottom_dead + src.Sub_stats.ldstk_bottom_dead;
  dst.Sub_stats.ldstk_w_b64 <-
    dst.Sub_stats.ldstk_w_b64 + src.Sub_stats.ldstk_w_b64;
  dst.Sub_stats.ldstk_w_4k <-
    dst.Sub_stats.ldstk_w_4k + src.Sub_stats.ldstk_w_4k;
  dst.Sub_stats.ldstk_w_2m <-
    dst.Sub_stats.ldstk_w_2m + src.Sub_stats.ldstk_w_2m;
  dst.Sub_stats.ldstk_w_big <-
    dst.Sub_stats.ldstk_w_big + src.Sub_stats.ldstk_w_big;
  if Int64.compare src.Sub_stats.ldstk_w_max
      dst.Sub_stats.ldstk_w_max > 0 then
    dst.Sub_stats.ldstk_w_max <- src.Sub_stats.ldstk_w_max

(* BIN rollup: summed columns + filtered/full percentages. *)
let print_bin_line (r : bin_report) : unit =
  let s = r.sum in
  let denom_filtered = s.Sub_stats.ldstk_exact + s.Sub_stats.ldstk_bounded
                       + s.Sub_stats.ldstk_top
                       + s.Sub_stats.ldstk_bottom_live in
  let denom_full = denom_filtered + s.Sub_stats.ldstk_bottom_dead in
  let pct_filtered =
    if denom_filtered = 0 then "n/a"
    else Printf.sprintf "%.2f"
        (100.0 *. float s.Sub_stats.ldstk_exact /. float denom_filtered) in
  let pct_full =
    if denom_full = 0 then "n/a"
    else Printf.sprintf "%.2f"
        (100.0 *. float s.Sub_stats.ldstk_exact /. float denom_full) in
  (* BIN reuses the sub layout ("BIN", basename, sums). *)
  let cols = Filename.basename r.bname :: List.tl (row_of s) in
  Printf.printf "%s\n"
    (String.concat "\t" ("BIN" :: cols @ [ pct_filtered; pct_full ]));
  flush stdout

let rec run_binary (path : string) : bin_report =
  let r = { bname = path; nsubs = 0; nok = 0; ncrashes = 0; nloadfail = 0;
            sum = Sub_stats.create "BIN" } in
  try
    match Project.create (Project.Input.file ~loader:"llvm" ~filename:path) with
    | Error e ->
      r.nloadfail <- 1;
      ws_load_fail path e;
      r
    | Ok proj ->
      let prog = Project.program proj in
      let bname = Filename.basename path in
      let sp = Hike.Abi.sp (Project.target proj) in
      Term.enum sub_t prog
      |> Seq.iter ~f:(fun sub ->
          r.nsubs <- r.nsubs + 1;
          match run_sub sp prog bname sub with
          | Ok st ->
            r.nok <- r.nok + 1;
            add_sum r.sum st;
            print_sub_line path st
          | Crash (es, bt) ->
            r.ncrashes <- r.ncrashes + 1;
            Printf.printf "CRASH\t%s\t%s\t%s\n" path (Sub.name sub) es;
            (match bt with
             | "" -> ()
             | _ -> Printf.printf "  backtrace:\n%s\n" bt);
            flush stdout);
      print_bin_line r;
      r
  with e ->
    (* Project.create / enumeration blew up. *)
    r.nloadfail <- 1;
    ws_load_exn path e;
    r

(* One sub, one fixpoint + measurement walk. *)
and run_sub (_sp : var) (_prog : program term) (bname : string)
    (sub : sub term) : outcome =
  try
    let prog' = Program.create ~subs:[ sub ] () in
    let t0 = Unix.gettimeofday () in
    let sol =
      Vsa.static_graph_vsa [] prog' sub (init_sol_of sub) in
    let t1 = Unix.gettimeofday () in
    (* Per-block TAG state is the IN-state ([tags = sol]). *)
    let st = collect_stats bname sub sol sol in
    st.Sub_stats.sub_ms <- int_of_float ((t1 -. t0) *. 1000.0);
    Ok st
  with e ->
    Crash (describe_exn e, Printexc.get_backtrace ())

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
