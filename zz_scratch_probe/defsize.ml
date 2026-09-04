(* Counts total/VLA/var-rhs defs per sub; vararm scales the map rebuild.
   Usage: defsize.exe <binary>... Prints only subs with VLA defs > 0. *)

open Bap.Std
open Probe_common

let count (alloc_tids : Tid.Set.t) (sub : sub term) : int * int * int =
  Term.enum blk_t sub
  |> Seq.fold ~init:(0, 0, 0) ~f:(fun (total, tagged, vararm) blk ->
      Term.enum def_t blk
      |> Seq.fold ~init:(total, tagged, vararm)
          ~f:(fun (total, tagged, vararm) d ->
            let total = total + 1 in
            if Core.Set.mem alloc_tids (Term.tid d) then
              let vararm =
                match Def.rhs d with Bil.Var _ -> vararm + 1 | _ -> vararm
              in
              (total, tagged + 1, vararm)
            else (total, tagged, vararm)))

let () =
  init ();
  let args = List.tl (Array.to_list Sys.argv) in
  if List.is_empty args then usage Sys.argv.(0) "<binary>...";
  let g_total = ref 0 and g_tagged = ref 0 and g_vararm = ref 0
  and g_cost = ref 0 and g_linear = ref 0 and g_subs = ref 0 in
  (* CSV columns stay machine-readable for diffing/summing. *)
  Printf.printf "binary,sub,total,tagged,vararm,rebuild_cost,linear_cost\n";
  Base.List.iter args ~f:(fun path ->
      let proj = load_project path in
      let sp = sp_of proj in
      let prog = Project.program proj in
      Base.List.iter (all_subs prog) ~f:(fun sub ->
          let alloc_tids = Cbat_vsa.Cbat_extraction.detect_dynamic_alloc sp sub in
          let total, tagged, vararm = count alloc_tids sub in
          if tagged > 0 then (
            let cost = vararm * total in
            let linear = total + vararm in
            g_total := !g_total + total;
            g_tagged := !g_tagged + tagged;
            g_vararm := !g_vararm + vararm;
            g_cost := !g_cost + cost;
            g_linear := !g_linear + linear;
            incr g_subs;
            Printf.printf "%s,%s,%d,%d,%d,%d,%d\n"
              (Core_kernel.Filename.basename path) (Sub.name sub)
              total tagged vararm cost linear)));
  Printf.eprintf
    "\nsubs_with_dyn_alloc=%d total_defs=%d tagged=%d vararm=%d\n\
     rebuild_cost=%d linear_cost=%d ratio=%.2fx\n"
    !g_subs !g_total !g_tagged !g_vararm !g_cost !g_linear
    (if !g_linear = 0 then 0.0
     else Float.of_int !g_cost /. Float.of_int !g_linear)
