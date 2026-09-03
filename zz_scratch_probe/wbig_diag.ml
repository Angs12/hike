(* Prints one line per def whose address window is >= 2^63, plus per-sub counts.
   Usage: wbig_diag.exe <binary>; unfiltered subs that fail tagging report and skip. *)

open Bap.Std
open Probe_common

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  init ();
  match args with
  | [] -> usage Sys.argv.(0) "<binary>"
  | path :: _ ->
    let proj = load_project path in
    let prog = Project.program proj in
    let target = Project.target proj in
    let sp = sp_of proj in
    let total = ref 0 in
    let skipped = ref 0 in
    all_subs prog
    |> List.iter (fun sub ->
        try
          let n = ref 0 in
          let sub', sol = analyze_and_fixpoint sp prog sub in
          let info = Hike.Vsa.offsets_of_sub target sp sub' in
          let kind_of = info.Hike.Convutils.offsets in
          Term.enum blk_t sub'
          |> Seq.iter ~f:(fun b ->
              let has_call =
                Term.enum jmp_t b
                |> Seq.exists ~f:(fun j ->
                    match Jmp.kind j with Call _ -> true | _ -> false)
              in
              let st = ref (Graphlib.Std.Solution.get sol (Term.tid b)) in
              Term.enum def_t b
              |> Seq.iter ~f:(fun d ->
                  (match Def.rhs d with
                   | Bil.Load (_, addr, _, _) | Bil.Store (_, addr, _, _, _) ->
                     (match Vsa.denote_imm_exp addr !st with
                      | Ok ws when ws_window_big ws ->
                        incr n;
                        Printf.printf "w_big\t%s\t%s\t%s\t%s\tcall=%b\tkind=%s\n"
                          (Sub.name sub') (Tid.name (Term.tid b))
                          (def_to_string d) (ws_to_string ws) has_call
                          (match Core_kernel.Map.find kind_of (Term.tid d) with
                           | Some k -> vsa_kind_to_string k
                           | None -> "-")
                      | _ -> ())
                   | _ -> ());
                  st := Vsa.denote_def d !st));
          Printf.printf "=== %s: %d w_big access(es)\n" (Sub.name sub') !n;
          total := !total + !n
        with e ->
          incr skipped;
          Printf.printf "=== %s: SKIPPED (%s)\n" (Sub.name sub)
            (Printexc.to_string e));
    Printf.printf "TOTAL w_big accesses: %d (%d sub(s) skipped)\n" !total !skipped
