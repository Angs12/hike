(* Cost census for review finding 8, via exported seams. *)

open Bap.Std
open Probe_common

let () =
  let args = Array.to_list Sys.argv |> List.tl in
  init ();
  match args with
  | [] -> usage Sys.argv.(0) "<binary>"
  | path :: _ ->
    let proj = load_project path in
    let prog = Project.program proj in
    let target = Project.target proj in
    let sp = sp_of proj in
    let subs = all_subs prog in
    let nsubs = Core.List.length subs in

    (* ---- A: detect_dynamic_alloc ---- *)
    let n_calls_producer = ref 0 in
    let n_calls_model = ref 0 in      (* has_vla_dynamic_alloc, gated *)
    let n_calls_emitter = ref 0 in
    let t_detect = ref 0. in
    let n_subs_with_vla = ref 0 in
    let n_vla_defs = ref 0 in
    (* model site: gated by convertible <> []; approximate the gate by
       "has any convertible region" = regions with convertible flag. *)
    Core.List.iter subs ~f:(fun sub ->
        let info = Hike.Vsa.offsets_of_sub target sp sub in
        incr n_calls_producer;
        let s, dt = time (fun () ->
            Cbat_vsa.Cbat_extraction.detect_dynamic_alloc sp sub) in
        t_detect := !t_detect +. dt;
        if not (Core.Set.is_empty s) then begin
          incr n_subs_with_vla;
          n_vla_defs := !n_vla_defs + Core.Set.length s
        end;
        (* model gate *)
        let convertible =
          Core.List.filter info.Hike.Convutils.regions
            ~f:(fun r -> r.Hike.Convutils.convertible)
        in
        if convertible <> [] then incr n_calls_model;
        ignore (Cbat_vsa.Cbat_extraction.stack_address_of_rhs (Bil.Int Word.b1)));
    (* emitter: one call per sub, unconditional *)
    n_calls_emitter := nsubs;

    (* ---- C: Sub.to_graph ---- *)
    let t_tograph = ref 0. in
    Core.List.iter subs ~f:(fun sub ->
        let _, dt = time (fun () -> ignore (Sub.to_graph sub)) in
        t_tograph := !t_tograph +. dt);

    (* ---- D: ABI record per call ---- *)
    let t_abi = ref 0. in
    let n_abi = ref 0 in
    Core.List.iter subs ~f:(fun _sub ->
        for _ = 1 to 100 do
          let _, dt = time (fun () -> ignore (Hike.Abi.of_target_opt target)) in
          t_abi := !t_abi +. dt; incr n_abi
        done);

    (* ---- E: dce cost per sub (exported seam) ---- *)
    let t_dce = ref 0. in
    Core.List.iter subs ~f:(fun sub ->
        let _, dt = time (fun () -> ignore (Hike.Dce.dce ~target sub)) in
        t_dce := !t_dce +. dt);

    Printf.printf "\n=== finding 8 census: %s ===\n" path;
    Printf.printf "subs: %d\n\n" nsubs;
    Printf.printf "A. detect_dynamic_alloc (3 sites/sub):\n";
    Printf.printf "  one call avg      : %.4f ms\n"
      (1000.0 *. !t_detect /. float !n_calls_producer);
    Printf.printf "  site1 producer    : %d calls (unconditional)\n" !n_calls_producer;
    Printf.printf "  site2 stack_model : %d calls (gated: convertible<>[])\n" !n_calls_model;
    Printf.printf "  site3 emitter     : %d calls (unconditional)\n" !n_calls_emitter;
    Printf.printf "  total time all 3  : %.3f s (x3 the one-call cost x nsubs)\n"
      (3.0 *. !t_detect);
    Printf.printf "  subs with any VLA : %d   VLA defs: %d\n\n"
      !n_subs_with_vla !n_vla_defs;
    Printf.printf "C. Sub.to_graph (emitter x3/sub):\n";
    Printf.printf "  total per pass    : %.3f s   (x3 = %.3f s)\n"
      !t_tograph (3.0 *. !t_tograph);
    Printf.printf "  per sub           : %.4f ms\n\n"
      (1000.0 *. !t_tograph /. float nsubs);
    Printf.printf "D. Abi.of_target_opt x100/sub:\n";
    Printf.printf "  per call          : %.4f us  (dce keep(): up to xndefs/sub)\n"
      (1e6 *. !t_abi /. float !n_abi);
    Printf.printf "  per binary (x5 calls/sub, dce-only est.): %.3f s\n\n"
      (1e6 *. !t_abi /. float !n_abi *. 5.0 *. float nsubs /. 1e6);
    Printf.printf "E. Hike.Dce.dce per sub:\n";
    Printf.printf "  total             : %.3f s\n" !t_dce;
    Printf.printf "  per sub           : %.4f ms\n"
      (1000.0 *. !t_dce /. float nsubs)
