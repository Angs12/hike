(* Real-operand census for candidate B (the Cbat_word substrate).
   Baseline gauge (ls, 2026-09-07, word-substrate verification):
     operands sampled: 36,994
     small (fits int63): 33,983 (91.9%)
     wide: 3,011 (8.1%)
     tags produced: 18,668

   clpequiv sweeps synthetic small values, so it cannot answer "what
   magnitude are the values a REAL fixpoint feeds the domain?" This
   drives the production fixpoint over real subs and samples the
   abstract state's actual word operands, classifying each by whether
   its MAGNITUDE fits the int63 fast path (|v| <= 2^62) — the declared
   width is irrelevant to the fast path, the value is what matters.

   Bar: >=80% small-magnitude operands justifies building B. *)

open Bap.Std
open Probe_common

let small_bound = 0x3FFF_FFFF_FFFF_FFFFL  (* 2^62 - 1 *)

(* Classify by magnitude, ignoring declared width (a 64-bit word holding
   3 is small; the fast path is chosen on value, not on type). *)
let tags_total = ref 0
let small = ref 0
let wide = ref 0

(* The producer's tag values are int64: the domain's OUTPUT magnitudes
   on real code. A stack offset is small regardless of the 64/65/129-bit
   word that carried it. *)
let census_i (v : int64) : unit =
  if Int64.unsigned_compare v small_bound <= 0 then incr small else incr wide

let () =
  let args = Array.to_list Sys.argv |> List.tl in
  init ();
  match args with
  | [] -> usage Sys.argv.(0) "<binary> [subname ...]"
  | path :: subs ->
    let proj = load_project path in
    let prog = Project.program proj in
    let target = Project.target proj in
    let sp = sp_of proj in
    let wanted = match subs with [] -> None | ss -> Some ss in
    let t_start = Unix.gettimeofday () in
    Term.enum sub_t prog
    |> Seq.iter ~f:(fun sub ->
        let nm = Sub.name sub in
        match wanted with
        | Some ss when not (Core.List.mem ss nm ~equal:String.equal) -> ()
        | _ ->
          let info = Hike.Vsa.offsets_of_sub target sp sub in
          (* Census the domain's REAL outputs: the k_ranges are the
             frame-relative offsets the analysis computed. *)
          Core.Map.iteri info.Hike.Convutils.k_ranges ~f:(fun ~key:_ ~data:(lo, hi) ->
              census_i lo; census_i hi);
          let n = Core.Map.length info.Hike.Convutils.offsets in
          tags_total := !tags_total + n;
          if n > 0 then
            Printf.printf "  %-26s tags=%d\n" nm n);
    let tot = !small + !wide in
    let tags_total = !tags_total in
    let elapsed = Unix.gettimeofday () -. t_start in
    Printf.printf "\n=== word census (magnitude-based) ===\n";
    Printf.printf "producer time: %.2fs  (%s)\n" elapsed path;
    Printf.printf "operands sampled: %d\n" tot;
    if tot > 0 then
      Printf.printf "small (fits int63): %d (%.1f%%)\nwide: %d (%.1f%%)\n"
        !small (100.0 *. float !small /. float tot)
        !wide (100.0 *. float !wide /. float tot)
    else
      Printf.printf "(no operands sampled — the state walk reached none)\n";
    Printf.printf "tags produced: %d\n" tags_total;
    if elapsed > 0. then
      Printf.printf "throughput: %.0f tags/s, %.0f operands/s\n"
        (float tags_total /. elapsed) (float tot /. elapsed)

