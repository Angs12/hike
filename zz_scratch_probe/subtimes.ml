(* subtimes — the per-sub cost-distribution driver (profiling, 2026-09-01:
   the performance architecture pass). For EVERY sub of the project, run the
   PRODUCTION per-sub path [Hike.Vsa.offsets_of_sub] (the exact function the
   hike-vsa pass calls per sub) and print name / block count / def count /
   wall time, sorted by time with the cumulative share. Usage:

     dune exec zz_scratch_probe/subtimes.exe -- <binary> *)

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
    let subs = all_subs prog in
    Printf.printf "# subs: %d\n" (List.length subs);
    let rows =
      List.rev_map
        (fun sub ->
          let name = Sub.name sub in
          let nblk =
            Term.enum blk_t sub |> Seq.fold ~init:0 ~f:(fun acc _ -> acc + 1)
          in
          let ndefs =
            Term.enum blk_t sub
            |> Seq.fold ~init:0 ~f:(fun acc b ->
                   let n =
                     Term.enum def_t b
                     |> Seq.fold ~init:0 ~f:(fun a _ -> a + 1)
                   in
                   acc + n)
          in
          let t0 = Unix.gettimeofday () in
          let info = Hike.Vsa.offsets_of_sub target sp sub in
          let dt = Unix.gettimeofday () -. t0 in
          let ntags =
            Core.Map.length info.Hike.Convutils.offsets
          in
          (dt, name, nblk, ndefs, ntags))
        subs
    in
    let rows = List.sort (fun (a, _, _, _, _) (b, _, _, _, _) -> compare a b) rows in
    let total =
      List.fold_left (fun acc (t, _, _, _, _) -> acc +. t) 0.0 rows
    in
    Printf.printf "total offsets_of_sub time: %.3fs over %d subs\n\n" total
      (List.length rows);
    Printf.printf "%10.3fs  %5.1f%%  %6d blk %7d defs %5d tags  %s\n" total 100.0
      0 0 0 "(ALL)";
    List.iteri
      (fun i (dt, name, nblk, ndefs, ntags) ->
        Printf.printf "%10.3fs  %5.1f%%  %6d blk %7d defs %5d tags  %s\n"
          dt (100.0 *. dt /. total) nblk ndefs ntags name;
        if i mod 20 = 0 then flush stdout)
      rows;
    (* concentration: share of the slowest decile *)
    let n = List.length rows in
    let head = ref 0.0 in
    List.iteri
      (fun i (dt, _, _, _, _) ->
        if 10 * i < n then head := !head +. dt)
      rows;
    Printf.printf "\nslowest 10%% of subs = %.1f%% of total time\n"
      (100.0 *. !head /. total)
