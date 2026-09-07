(* Regions-of-sub determinism: N fresh in-process computations of one sub,
   deduped signatures. Usage: sweepcheck.exe <binary> [subname] *)
open Bap.Std
open Probe_common
let () =
  let args = List.tl (Array.to_list Sys.argv) in
  init ();
  match args with
  | [] -> usage Sys.argv.(0) "<binary> [subname]"
  | path :: subname_opt ->
  let name = match subname_opt with n :: _ -> n | [] -> "main" in
  let proj = load_project path in
  let prog = Project.program proj in
  let target = Project.target proj in
  let sp = sp_of proj in
  let sub = match find_sub prog name with Some s -> s | None -> failwith ("no " ^ name) in
  let sigs = ref [] in
  for _i = 1 to 5 do
    let info = Hike.Vsa.offsets_of_sub target sp sub in
    let regions =
      if info.Hike.Convutils.regions <> [] then info.Hike.Convutils.regions
      else Hike.Stack_model.regions_of_sub sp target sub info ~frame_escaped:(Hike.Stack_model.frame_escapes sp target sub)
    in
    let sig_ =
      String.concat ","
        (Base.List.map regions ~f:(fun r ->
             Printf.sprintf "(%Ld,%Ld,%d,%s)"
               (fst r.Hike.Convutils.span) (snd r.Hike.Convutils.span)
               r.Hike.Convutils.id
               (String.concat "|"
                  (Base.List.map r.Hike.Convutils.members ~f:(fun (t,_) -> Tid.name t)))))
    in
    sigs := sig_ :: !sigs
  done;
  let uniq = Base.List.dedup_and_sort ~compare:String.compare !sigs in
  Printf.printf "%s region signatures: %d distinct of %d runs\n"
    name (List.length uniq) (List.length !sigs);
  Base.List.iter uniq ~f:(fun s -> Printf.printf "  %s\n" s)
