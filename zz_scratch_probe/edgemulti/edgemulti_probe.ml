(* edgemulti_probe.ml — owner-decision keep (closed duplicate-pred-phi question,
   answered and recorded; do not delete unilaterally).
   WHY does the %0006ef1c-class phi get ONE entry for a
   pred that LLVM lists twice? Reproduce the emitter's own pred accounting on
   subs holding [when c goto L; goto L] pairs, printing the jmp-term shape the
   emission actually sees (the RAW program; filter_subs' simplify_jmps splits
   happen in the pass, replicated here by inspecting what it does: it only
   splits blocks whose jmps are >1 AND non-all-goto — check both shapes).

   Usage: edgemulti_probe <binary>   (finds subs with same-target jmp pairs) *)

open Bap.Std
open Probe_common

let () =
  init ();
  match List.tl (Array.to_list Sys.argv) with
  | [ path ] ->
    let proj = load_project path in
    let prog = Project.program proj in
    Term.enum sub_t prog
    |> Seq.iter ~f:(fun sub ->
        let bad =
          Term.enum blk_t sub
          |> Seq.filter_map ~f:(fun b ->
              let targets =
                Term.enum jmp_t b
                |> Seq.filter_map ~f:(fun j ->
                    match Jmp.kind j with
                    | Goto (Direct t) | Ret (Direct t) -> Some t
                    | _ -> None)
                |> Seq.to_list
              in
              let conds =
                Term.enum jmp_t b |> Seq.length
              in
              match targets with
              | t1 :: t2 :: _ when Tid.equal t1 t2 ->
                  Some
                    (Printf.sprintf "blk %s: %d jmps, same-target %s x%d"
                       (Tid.to_string (Term.tid b)) conds
                       (Tid.to_string t1) (List.length targets))
              | _ -> None)
          |> Seq.to_list
        in
        if bad <> [] then begin
          Printf.printf "sub %s:\n" (Sub.name sub);
          let rec emit = function [] -> () | s :: tl -> Printf.printf "  %s\n" s; emit tl in emit bad
        end)
  | _ -> Printf.eprintf "usage: %s <binary>\n%!" Sys.argv.(0)
