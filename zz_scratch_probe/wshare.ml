(* Walk-share census for candidate 1: how much do same-block backward
   walks overlap? Drives one producer run, then analyzes the recorded
   (guard, jmp, seeds, read-set) tuples: per guard block with >=2 edges,
   mean/min/max pairwise Jaccard over cross-edge walk pairs, the
   union-savings ratio (the sharing prize directly), and the seed mix.
   Usage: wshare.exe <binary> <subname> *)

open Bap.Std
open Probe_common

let jaccard a b =
  let inter = Core.Set.length (Core.Set.inter a b) in
  let union = Core.Set.length (Core.Set.union a b) in
  if union = 0 then 1.0 else float inter /. float union

let () =
  let args = Array.to_list Sys.argv |> List.tl in
  init ();
  match args with
  | [] -> usage Sys.argv.(0) "<binary> <subname>"
  | [ _ ] -> usage Sys.argv.(0) "<binary> <subname>"
  | path :: name :: _ ->
    let proj = load_project path in
    let prog = Project.program proj in
    let target = Project.target proj in
    let sp = sp_of proj in
    let sub =
      match find_sub prog name with
      | Some s -> s
      | None -> usage Sys.argv.(0) "sub not found"
    in
    Vsa.walk_records_reset ();
    let _info = Hike.Vsa.offsets_of_sub target sp sub in
    let recs = Vsa.walk_records_dump () in
    Printf.printf "=== wshare %s (%s): %d walks recorded ===\n" name path
      (Core.List.length recs);
    (* Group by guard block. *)
    let by_guard : (tid, Vsa.walk_record list) Hashtbl.t =
      Hashtbl.create 64
    in
    Core.List.iter recs ~f:(fun r ->
        let cur =
          try Hashtbl.find by_guard r.Vsa.wr_guard with Not_found -> []
        in
        Hashtbl.replace by_guard r.Vsa.wr_guard (r :: cur));
    let multi = ref 0 in
    let tot_save_num = ref 0.0 in
    let tot_save_den = ref 0.0 in
    let tot_pairs = ref 0 in
    Hashtbl.iter
      (fun guard rs ->
        let jmps =
          Core.List.dedup_and_sort rs ~compare:(fun a b ->
              Tid.compare a.Vsa.wr_jmp b.Vsa.wr_jmp)
          |> Core.List.map ~f:(fun r -> r.Vsa.wr_jmp)
        in
        if Core.List.length jmps >= 2 then begin
          incr multi;
          (* Cross-edge pairs only (different jmp), each walk's own set. *)
          let pairs = ref [] in
          Core.List.iter rs ~f:(fun r1 ->
              Core.List.iter rs ~f:(fun r2 ->
                  if Tid.compare r1.Vsa.wr_jmp r2.Vsa.wr_jmp < 0 then
                    pairs := (r1, r2) :: !pairs));
          let js =
            Core.List.map !pairs ~f:(fun (r1, r2) ->
                jaccard r1.Vsa.wr_reads r2.Vsa.wr_reads)
          in
          let union =
            Core.List.fold_left rs ~init:Tid.Set.empty
              ~f:(fun u r -> Core.Set.union u r.Vsa.wr_reads)
          in
          let sum =
            Core.List.fold_left rs ~init:0 ~f:(fun s r ->
                s + Core.Set.length r.Vsa.wr_reads)
          in
          let savings =
            if sum = 0 then 0.0
            else 1.0 -. float (Core.Set.length union) /. float sum
          in
          let nvar =
            Core.List.fold_left rs ~init:0 ~f:(fun s r -> s + r.Vsa.wr_nvar)
          in
          let ncell =
            Core.List.fold_left rs ~init:0 ~f:(fun s r -> s + r.Vsa.wr_ncell)
          in
          tot_save_num := !tot_save_num +. float (sum - Core.Set.length union);
          tot_save_den := !tot_save_den +. float sum;
          tot_pairs := !tot_pairs + Core.List.length js;
          let mean =
            if js = [] then 0.0
            else
              Core.List.fold_left js ~init:0.0 ~f:( +. )
              /. float (Core.List.length js)
          in
          let mn =
            match js with
            | [] -> 0.0
            | h :: t -> Core.List.fold_left t ~init:h ~f:Float.min
          in
          let mx =
            match js with
            | [] -> 0.0
            | h :: t -> Core.List.fold_left t ~init:h ~f:Float.max
          in
          let sizes =
            Core.List.map rs ~f:(fun r -> Core.Set.length r.Vsa.wr_reads)
          in
          let szmin =
            Core.List.fold_left sizes ~init:1073741823 ~f:min
          in
          let szmax =
            Core.List.fold_left sizes ~init:0 ~f:max
          in
          (* smallest symmetric difference among cross pairs *)
          let best =
            Core.List.fold_left !pairs ~init:None ~f:(fun best (r1, r2) ->
                let d =
                  Core.Set.length
                    (Core.Set.union
                       (Core.Set.diff r1.Vsa.wr_reads r2.Vsa.wr_reads)
                       (Core.Set.diff r2.Vsa.wr_reads r1.Vsa.wr_reads))
                in
                match best with
                | None -> Some d
                | Some b -> Some (min b d))
          in
          Printf.printf
            "  guard %s: %d edges %d walks pairs=%d jacc mean=%.2f min=%.2f \
             max=%.2f savings=%.2f seeds=V%d/C%d setsize=[%d,%d] bestdiff=%d\n"
            (Tid.name guard) (Core.List.length jmps) (Core.List.length rs)
            (Core.List.length js) mean mn mx savings nvar ncell szmin szmax
            (Option.value best ~default:(-1))
        end)
      by_guard;
    let overall =
      if !tot_save_den = 0.0 then 0.0 else !tot_save_num /. !tot_save_den
    in
    Printf.printf
      "SUMMARY multi-edge guards=%d cross-pairs=%d overall-union-savings=%.2f\n"
      !multi !tot_pairs overall
