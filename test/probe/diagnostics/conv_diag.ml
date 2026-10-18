(* Reports fixpoint verdict, widening-point set, head BIR, and head states.
   Usage: conv_diag.exe <binary> [subname] (default "main"). *)

open Bap.Std
open Probe_common

(* The CFG view lives in Probe_common (shared with vsa_gap). *)
let cfg_of = cfg_of
let cyclic_heads = cyclic_heads

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  init ();
  match args with
  | [] -> usage Sys.argv.(0) "<binary> [subname]"
  | path :: rest ->
    let proj = load_project path in
    let prog = Project.program proj in
    let name = match rest with n :: _ -> n | [] -> "main" in
    let sub =
      match find_sub prog name with
      | Some s -> s
      | None ->
        usage Sys.argv.(0)
          (Printf.sprintf "<binary> [subname] - %s not found" name)
    in
    Printf.printf "=== conv_diag %s (%s) ===\n" (Filename.basename path)
      (Sub.name sub);
    let sub' = sub in
    let sol, converged =
      try (Probe_common.run_sub_fixpoint ~synth:Hike.Synth.empty sub', true)
      with Vsa.Fixpoint_not_converged (n, sol) ->
        Printf.printf "FIXPOINT NOT CONVERGED after %d rounds\n" n;
        (sol, false)
    in
    Printf.printf
      "%s\n"
      (if converged then "FIXPOINT CONVERGED"
       else "PARTIAL SOLUTION (widening-point SCCs follow)");
    let cfg = cfg_of sub' in
    let heads = cyclic_heads cfg in
    Printf.printf "WIDENING-POINT set (%d cyclic SCCs):\n" (List.length heads);
    List.iter
      (fun (head, members) ->
        Printf.printf "  head %s  (cycle members: %s)\n" (Tid.name head)
          (Base.String.concat ~sep:", "
             (Base.List.map members ~f:(fun t -> Tid.name t))))
      heads;
    List.iter
      (fun (head, _members) ->
        match
          Term.enum blk_t sub'
          |> Seq.find ~f:(fun b -> Tid.equal (Term.tid b) head)
        with
        | Some b -> Printf.printf "%s\n" (blk_bil_to_string b)
        | None -> ())
      heads;
    List.iter
      (fun (head, members) ->
        let st = Graphlib.Std.Solution.get sol head in
        let vars =
          members
          |> Base.List.concat_map ~f:(fun t ->
              Term.enum blk_t sub'
              |> Seq.find ~f:(fun b -> Tid.equal (Term.tid b) t)
              |> Option.to_list)
          |> Base.List.concat_map ~f:(fun b ->
              Term.enum def_t b
              |> Seq.map ~f:(fun d -> Var.base (Def.lhs d))
              |> Seq.to_list)
          |> Base.List.dedup_and_sort ~compare:(fun a b -> String.compare (Var.name a) (Var.name b))
        in
        Printf.printf "  head %s gap-successor state: %s\n" (Tid.name head)
          (state_summary vars st))
      heads
