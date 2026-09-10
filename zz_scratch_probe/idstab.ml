(* Cross-process region-id stability: print @main's region (id, span, members) signature.
   Usage: idstab.exe <binary> [subname] *)
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
  let info = Hike.Vsa.offsets_of_sub target sp ~symtab:None ~prog:(Program.create ~subs:[ sub ] ()) sub in
  (* The record IS the regions (the producer built them). *)
  let regions = info.Hike.Stack_model.regions in
  let plan = Hike.Stack_model.split_plan sub info in
  Printf.printf "regions: %d\n" (List.length regions);
  Base.List.iter regions ~f:(fun r ->
      Printf.printf "  r%d span=(%Ld,%Ld) conv=%b members=%d\n"
        r.Hike.Stack_model.id
        (fst r.Hike.Stack_model.span) (snd r.Hike.Stack_model.span)
        r.Hike.Stack_model.convertible (List.length r.Hike.Stack_model.members));
  Printf.printf "plan: %d\n" (List.length plan);
  Base.List.iter plan ~f:(fun r ->
      Printf.printf "  plan r%d span=(%Ld,%Ld)\n"
        r.Hike.Stack_model.id
        (fst r.Hike.Stack_model.span) (snd r.Hike.Stack_model.span))
