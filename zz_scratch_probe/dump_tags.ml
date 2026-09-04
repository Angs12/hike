(* Prints one TSV line per def: tid, lhs, tags, offset kind, region.
   Usage: dump_tags.exe <binary> [subname] (default "main"). Diff two runs to compare. *)

open Bap.Std
open Probe_common

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  init ();
  match args with
  | [] -> usage Sys.argv.(0) "<binary> [subname]"
  | path :: rest ->
    let proj = load_project path in
    let prog = Project.program proj in
    let target = Project.target proj in
    let sp = sp_of proj in
    let name = match rest with n :: _ -> n | [] -> "main" in
    let sub =
      match find_sub prog name with
      | Some s -> s
      | None -> usage Sys.argv.(0) (Printf.sprintf "<binary> [subname] — %s not found" name)
    in
    let info = Hike.Vsa.offsets_of_sub target sp sub in
    let kind_of = info.Hike.Convutils.offsets in
    (* Region id whose span holds the def's tag; "-" when in no region. *)
    let region_of =
      Base.List.fold info.Hike.Convutils.regions ~init:Tid.Map.empty
        ~f:(fun m r ->
          Base.List.fold r.Hike.Convutils.members ~init:m
            ~f:(fun m (tid, _) ->
              Core_kernel.Map.set m ~key:tid
                ~data:
                  (if r.Hike.Convutils.convertible then
                     Printf.sprintf "r%d" r.Hike.Convutils.id
                   else
                     Printf.sprintf "-r%d" r.Hike.Convutils.id)))
    in    Term.enum blk_t sub
    |> Seq.iter ~f:(fun b ->
        Term.enum def_t b
        |> Seq.iter ~f:(fun d ->
            (* Stack-ness is [vsa_info] membership (spec §2.2). *)
            let tags =
              (if Core_kernel.Map.mem info.Hike.Convutils.offsets (Term.tid d)
               then "stack_access"
               else "")
              ^ (if Core_kernel.Map.mem info.Hike.Convutils.vla_bounds (Term.tid d)
                 then ",dynamic_alloc"
                 else "")
            in
            let kind =
              match Core_kernel.Map.find kind_of (Term.tid d) with
              | Some k -> vsa_kind_to_string k
              | None -> "-"
            in
            let region =
              match Core_kernel.Map.find region_of (Term.tid d) with
              | Some r -> r
              | None -> "-"
            in
            Printf.printf "%s\t%s\t%s\t%s\t%s\n"
              (Tid.to_string (Term.tid d)) (Var.name (Def.lhs d)) tags kind
              region))