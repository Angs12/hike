(* Memo hit-rate census over a whole binary (vsa-debug profile).
   Usage: memostats.exe <bin> [subname]  — full run if no subname. *)

open Bap.Std
open Probe_common
module CK = Core_kernel

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  init ();
  match args with
  | [] -> usage Sys.argv.(0) "<binary> [subname]"
  | path :: rest ->
    let proj = load_project path in
    let target = Project.target proj in
    let sp = sp_of proj in
    let subs =
      match rest with
      | [] -> all_subs (Project.program proj)
      | n :: _ ->
        (match find_sub (Project.program proj) n with
         | Some s -> [ s ]
         | None -> [])
    in
    CK.List.iter subs ~f:(fun sub ->
        Cbat_vsa__Cbat_memo.reset_stats ();
        let t0 = Unix.gettimeofday () in
        let _ = Hike.Vsa.offsets_of_sub target sp sub in
        let dt = Unix.gettimeofday () -. t0 in
        let l = !Cbat_vsa__Cbat_memo.lookups in
        let h = !Cbat_vsa__Cbat_memo.hits in
        let s = !Cbat_vsa__Cbat_memo.stores in
        let st = !Cbat_vsa__Cbat_memo.stale in
        if l > 0 then
          Printf.printf "%-14s %6.3fs lookups %8d hits %8d (%4.1f%%) stores %7d stale %7d (%4.1f%%)\n"
            (Sub.name sub) dt l h (100. *. float h /. float l) s st
            (100. *. float st /. float l))
