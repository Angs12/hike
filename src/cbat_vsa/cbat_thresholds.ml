(* ************************************************************************* *)
(*  *)
(* Copyright (C) Draper Laboratory. Licensed under project LICENSE. *)
(*  *)
(* This file is provided under the license found in the LICENSE file in *)
(* the top-level directory of this project. *)
(*  *)
(* This work is funded in part by ONR/NAWC Contract N6833518C0107. Its *)
(* content does not necessarily reflect the position or policy of the US *)
(* Government and no official endorsement should be inferred. *)
(*  *)
(* ************************************************************************* *)

(* Cbat_thresholds — widening-threshold collection (the Astrée-style bounded extrapolation; docs/widening-thresholds-plan.md). *)

open Bap.Std

module W = Word

type t = (int * W.t list) list

(* [geometric width]: The default rung family per width — the 8-aligned series {8*2^k, 8*2^k - 1} for k in [0, 17] (8*2^17 = 2^20, the cap for stack-scale spans; larger bounds are genuinely unbounded and widen to infinity), their. *)
let geometric (width : int) : W.t list =
  let pow k = W.of_int ~width (1 lsl k) in
  let maxk = min 17 (width - 4) in
  let rungs =
    if maxk < 0 then []
    else
      List.init (maxk + 1) (fun k ->
          let p = pow (k + 3) in   (* 8*2^k and 8*2^k - 1 *)
          [ p; W.pred p ])
      |> List.concat in
  let pos = List.sort_uniq W.compare (W.zero width :: rungs) in
  List.sort_uniq W.compare (pos @ List.map W.neg pos)

(* Recursive walk collecting every [Bil.Int] of an exp. *)
let rec add_exp_consts (acc : W.t list) (e : exp) : W.t list =
  match e with
  | Bil.Var _ -> acc
  | Bil.Int w -> w :: acc
  | Bil.Load (_, a, _, _) -> add_exp_consts acc a
  | Bil.Store (_, a, u, _, _) -> add_exp_consts (add_exp_consts acc a) u
  | Bil.BinOp (_, x, y) -> add_exp_consts (add_exp_consts acc x) y
  | Bil.UnOp (_, x) -> add_exp_consts acc x
  | Bil.Cast (_, _, x) -> add_exp_consts acc x
  | Bil.Let (_, x, y) -> add_exp_consts (add_exp_consts acc x) y
  | Bil.Ite (c, x, y) ->
    add_exp_consts (add_exp_consts (add_exp_consts acc c) x) y
  | Bil.Extract (_, _, x) -> add_exp_consts acc x
  | Bil.Concat (x, y) -> add_exp_consts (add_exp_consts acc x) y
  | Bil.Unknown _ -> acc

(* [collect sub]: The per-bitwidth ladders for one fixpoint run — geometric defaults ∪ the sub's program constants, deduped and sorted. *)
let collect (sub : sub term) : t =
  let consts = ref [] in
  Term.enum blk_t sub |> Seq.iter ~f:(fun b ->
      Term.enum def_t b |> Seq.iter ~f:(fun d ->
          List.iter (fun w -> consts := w :: !consts)
            (add_exp_consts [] (Def.rhs d)));
      Term.enum jmp_t b |> Seq.iter ~f:(fun jmp ->
        Seq.iter (Jmp.exps jmp) ~f:(fun e ->
            List.iter (fun w -> consts := w :: !consts)
              (add_exp_consts [] e))));
  let widths =
    List.sort_uniq Int.compare (List.map W.bitwidth !consts) in
  List.map (fun width ->
      let of_width =
        List.filter (fun w -> W.bitwidth w = width) !consts in
      let ladder = List.sort_uniq W.compare (geometric width @ of_width) in
      (width, ladder)) widths
