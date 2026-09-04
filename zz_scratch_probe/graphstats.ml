(* CFG shape + fan-in stats behind the fixpoint join cost.
   Usage: graphstats.exe <binary> [subname ...] *)

open Bap.Std
open Probe_common
module CKL = Core_kernel.List
module G = Graphs.Tid

let () =
  init ();
  let args = List.tl (Array.to_list Sys.argv) in
  match args with
  | [] -> usage Sys.argv.(0) "<binary> [subname...]"
  | path :: rest ->
    let proj = load_project path in
    let prog = Project.program proj in
    let subs =
      match rest with
      | [] -> all_subs prog
      | names ->
        CKL.filter_map names ~f:(fun n ->
            match find_sub prog n with
            | Some s -> Some s
            | None -> None)
    in
    Printf.printf "=== graphstats %s ===\n" (Filename.basename path);
    Printf.printf "%-12s %6s %6s %6s %7s %7s %7s %7s\n"
      "sub" "blks" "defs" "edges" "maxin" "avg_in" "in>=4" "sum_in";
    CKL.iter subs ~f:(fun sub ->
        let cfg = Sub.to_graph sub in
        let nodes = G.nodes cfg in
        let nblk = Seq.length nodes in
        let ndefs =
          Term.enum blk_t sub
          |> Seq.fold ~init:0 ~f:(fun a b -> a + Seq.length (Term.enum def_t b))
        in
        let ins =
          Seq.fold nodes ~init:[] ~f:(fun acc n ->
              (Seq.length (G.Node.preds n cfg)) :: acc)
        in
        let sum = List.fold_left (fun a x -> a + x) 0 ins in
        let maxin = List.fold_left max 0 ins in
        let avg = if nblk = 0 then 0. else float sum /. float nblk in
        let big = List.length (List.filter (fun x -> x >= 4) ins) in
        Printf.printf "%-12s %6d %6d %6d %7d %7.2f %7d %7d\n"
          (Sub.name sub) nblk ndefs sum maxin avg big sum)
