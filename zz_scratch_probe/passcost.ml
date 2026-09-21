(* Times seed-detect, vsa, stl, dce per sub; counts DCE sweep rounds.
   Usage: passcost.exe <binary>... CSV on stdout, summary on stderr. *)

open Bap.Std
open Bap_core_theory
open Probe_common

(* Infers the round count from the def-count trajectory. *)
let dce_rounds (target : Theory.Target.t) (sub : sub term) : int * int =
  let n0 =
    Term.enum blk_t sub
    |> Seq.fold ~init:0 ~f:(fun n blk -> n + Seq.length (Term.enum def_t blk))
  in
  (* dce runs its own sweep to stability, so re-running it must be a no-op. *)
  let rec go sub prev_n rounds =
    let sub' = Dce.dce ~target sub in
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
  Printf.printf "binary,sub,ndefs,vla_s,vsa_s,dce_s,dce_rounds\n";
  let tot = ref 0.0 in
  Base.List.iter args ~f:(fun path ->
      let proj = load_project path in
      let target = Project.target proj in
      let prog = Project.program proj in
      let facts =
        Hike.Kb.build ~block_envs:Tid.Map.empty
          ~block_addrs:(Core.Map.empty (module Addr)) ~target
      in
      Base.List.iter (all_subs prog) ~f:(fun sub ->
          let ndefs =
            Term.enum blk_t sub
            |> Seq.fold ~init:0 ~f:(fun n blk ->
                   n + Seq.length (Term.enum def_t blk))
          in
          let _events, t_rel =
            time (fun () -> Hike.Promote.dynamic_alloc_tids_of ~facts sub)
          in
          let _envs, t_vsa =
            time (fun () ->
                Hike.Vsa.fixpoint target ~prog:(Program.create ~subs:[ sub ] ())
                  ~symtab:None ~images:[]
                  ~written:(Hike.Vsa.kill_summaries ~abi:facts.Hike.Kb.abi prog)
                  ~block_addrs:(Core.Map.empty (module Addr)) sub)
          in
          let _dced, t_dce = time (fun () -> Dce.dce ~target sub) in
          let rounds, _ = dce_rounds target sub in
          tot := !tot +. t_vsa;
          Printf.printf "%s,%s,%d,%.4f,%.4f,%.4f,%d\n"
            (Core.Filename.basename path) (Sub.name sub) ndefs t_rel
            t_vsa t_dce rounds));
  Printf.eprintf "\ntotal vsa time = %.2fs\n" !tot
