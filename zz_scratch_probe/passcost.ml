(* Times seed-detect, vsa, stl, dce per sub; counts DCE sweep rounds.
   Usage: passcost.exe <binary>... CSV on stdout, summary on stderr. *)

open Bap.Std
open Bap_core_theory
open Probe_common

let time1 (f : unit -> 'a) : 'a * float =
  let t0 = Unix.gettimeofday () in
  let r = f () in
  let t1 = Unix.gettimeofday () in
  (r, t1 -. t0)

(* Infers the round count from the def-count trajectory. *)
let dce_rounds (target : Theory.Target.t) (sub : sub term) : int * int =
  let n0 =
    Term.enum blk_t sub
    |> Seq.fold ~init:0 ~f:(fun n blk -> n + Seq.length (Term.enum def_t blk))
  in
  (* dce runs its own sweep to stability, so re-running it must be a no-op. *)
  let rec go sub prev_n rounds =
    let sub' = Hike__Hike_dce.dce ~target sub in
    let n' =
      Term.enum blk_t sub'
      |> Seq.fold ~init:0 ~f:(fun n blk ->
             n + Seq.length (Term.enum def_t blk))
    in
    if n' = prev_n then rounds
    else if rounds > 20 then rounds
    else go sub' n' (rounds + 1)
  in
  let rounds = go sub n0 1 in
  (rounds, n0)

let () =
  init ();
  let args = List.tl (Array.to_list Sys.argv) in
  if Base.List.is_empty args then usage Sys.argv.(0) "<binary>...";
  Printf.printf "binary,sub,ndefs,seed_s,vsa_s,stl_s,dce_s,dce_rounds\n";
  let tot = ref 0.0 in
  Base.List.iter args ~f:(fun path ->
      let proj = load_project path in
      let sp = sp_of proj in
      let target = Project.target proj in
      let prog = Project.program proj in
      Base.List.iter (all_subs prog) ~f:(fun sub ->
          let ndefs =
            Term.enum blk_t sub
            |> Seq.fold ~init:0 ~f:(fun n blk ->
                   n + Seq.length (Term.enum def_t blk))
          in
          let _alloc_tids, t_rel =
            time1 (fun () -> Cbat_vsa.Cbat_extraction.detect_dynamic_alloc sp sub)
          in
          let _info, t_vsa =
            time1 (fun () -> Hike.Vsa.offsets_of_sub target sp sub)
          in
          (* stl and dce read the KB that offsets_of_sub populates. *)
          let stl_sub, t_stl =
            time1 (fun () ->
                Hike.Stack_to_locals.stack_to_locals target sp sub)
          in
          let _dced, t_dce =
            time1 (fun () -> Hike__Hike_dce.dce ~target stl_sub)
          in
          let rounds, _ = dce_rounds target stl_sub in
          tot := !tot +. t_vsa;
          Printf.printf "%s,%s,%d,%.4f,%.4f,%.4f,%.4f,%d\n"
            (Core_kernel.Filename.basename path) (Sub.name sub) ndefs t_rel
            t_vsa t_stl t_dce rounds));
  Printf.eprintf "\ntotal vsa time = %.2fs\n" !tot
