(* The production-config non-convergence diagnostic: replicates the
   pass's per-sub solve (jump -> split-mem terms, whole-program kill
   summaries) and on Fixpoint_not_converged prints the widening heads
   and the head states.
   Usage: vsa_gap.exe <binary> <subname> [raw|jump|split|both] *)

open Bap.Std
open Bap_core_theory
open Probe_common

module AI = Cbat_vsa.AI
module Vsa = Cbat_vsa

(* The CFG view lives in Probe_common (shared with conv_diag). *)
let cfg_of = cfg_of
let cyclic_heads = cyclic_heads

(* The jump lines of a block - the guard shapes. *)
let jmps_line (b : blk term) : string =
  Term.enum jmp_t b
  |> Seq.map ~f:(fun j ->
      match Jmp.kind j with
      | Goto (Direct t) -> "goto " ^ Tid.name t
      | Goto (Indirect e) ->
        "goto [" ^ Format.asprintf "%a" Exp.pp e ^ "]"
      | Ret _ -> "ret"
      | Int _ -> "int"
      | Call c ->
        "call ret="
        ^ (match Call.return c with
           | Some l -> target_to_string l
           | None -> "none"))
  |> Seq.to_list
  |> Base.String.concat ~sep:" ; "

let usage_text = "<binary> <subname> [raw|jump|split|both]"

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  init ();
  match args with
  | [] -> usage Sys.argv.(0) usage_text
  | path :: subname :: rest -> (
    let mode = match rest with m :: _ -> m | [] -> "both" in
    let written_mode = match rest with _ :: w :: _ -> w | _ -> "whole" in
    let proj = load_project path in
    let prog = Project.program proj in
    let target = Project.target proj in
    let raw =
      match find_sub prog subname with
      | Some s -> s
      | None -> usage Sys.argv.(0) usage_text
    in
    (* The callee regime: each program sub's own writes, or ("none")
       every callee unknown. *)
    let callee =
      match written_mode with
      | "none" -> fun _ -> Vsa.Call_effects.Summary None
      | _ -> callee_of prog
    in
    Vsa.set_addr_bits (Hike.Abi.addr_size_bits target);
    (* The pass's transforms, in chain order. *)
    let sub =
      match mode with
      | "raw" -> raw
      | "jump" -> Hike.Jump.compile_sub target raw
      | "split" -> Hike.Split_mem.split_sub raw
      | "both" -> Hike.Split_mem.split_sub (Hike.Jump.compile_sub target raw)
      | _ -> usage Sys.argv.(0) usage_text
    in
    let nblk = Term.enum blk_t sub |> Seq.length in
    let ndefs =
      Term.enum blk_t sub
      |> Seq.fold ~init:0 ~f:(fun acc b ->
             acc + (Term.enum def_t b |> Seq.length))
    in
    Printf.printf "=== vsa_gap %s (%s) mode=%s written=%s  %d blk %d defs ===\n%!"
      (Filename.basename path) (Sub.name raw) mode written_mode nblk ndefs;
    let abi = Hike.Abi.of_target target in
    let t0 = Unix.gettimeofday () in
    match
      static_graph_vsa ~abi ~callee ~sub_lookup:(fun _ -> None) sub
        (Vsa.init_sol ~abi sub)
    with
    | sol ->
      Printf.printf "CONVERGED in %.3fs\n%!" (Unix.gettimeofday () -. t0);
      ignore sol
    | exception Vsa.Fixpoint_not_converged (n, sol) ->
      Printf.printf "NOT CONVERGED after %d visits (%.3fs)\n%!"
        n (Unix.gettimeofday () -. t0);
      let cfg = cfg_of sub in
      let heads = cyclic_heads cfg in
      Printf.printf "widening-point set: %d cyclic SCCs\n%!"
        (List.length heads);
      List.iter
        (fun (head, members) ->
          let blk =
            Term.enum blk_t sub
            |> Seq.find_exn ~f:(fun b -> Tid.equal (Term.tid b) head)
          in
          Printf.printf "HEAD %s  (members: %s)\n" (Tid.name head)
            (Base.String.concat ~sep:", "
               (Base.List.map members ~f:Tid.name));
          Printf.printf "  jmps: %s\n" (jmps_line blk);
          let vars =
            Base.List.dedup_and_sort
              (Base.List.concat_map members
                 ~f:(fun t ->
                     match
                       Term.enum blk_t sub
                       |> Seq.find ~f:(fun b -> Tid.equal (Term.tid b) t)
                     with
                     | Some b ->
                       Term.enum def_t b
                       |> Seq.map ~f:(fun d -> Var.base (Def.lhs d))
                       |> Seq.to_list
                     | None -> []))
              ~compare:(fun a b -> String.compare (Var.name a) (Var.name b))
          in
          let st = Graphlib.Std.Solution.get sol head in
          Printf.printf "  head state (%d vars):\n" (List.length vars);
          List.iter
            (fun v ->
              let ws = AI.find_word 64 st v in
              let desc =
                if Cbat_vsa.WordSet.is_top ws then "TOP"
                else if Cbat_vsa.WordSet.is_bottom ws then "BOT"
                else
                  match
                    Cbat_vsa.WordSet.min_elem ws, Cbat_vsa.WordSet.max_elem ws
                  with
                  | Some lo, Some hi ->
                    Printf.sprintf "[%s .. %s]%s"
                      (word_to_hex (Cbat_word.to_word lo))
                      (word_to_hex (Cbat_word.to_word hi))
                      (if Cbat_vsa.WordSet.is_infinite ws then " inf" else "")
                  | _ -> "?"
              in
              if desc <> "BOT" then
                Printf.printf "    %s = %s\n" (Var.name v) desc)
            vars)
        heads)
  | _ -> usage Sys.argv.(0) usage_text
