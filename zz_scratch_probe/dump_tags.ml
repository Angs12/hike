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
    let info = Hike.Vsa.offsets_of_sub target sp ~symtab:None ~prog:(Program.create ~subs:[ sub ] ()) sub in
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
               then "stack"
               else "")
              ^ (if Core_kernel.Set.mem info.Hike.Convutils.vla_alloc_tids (Term.tid d)
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
(* T4: the promotion record of the sub (recomputed: the probe's main
   scope owns the original [info]). *)
let () =
  let args = List.tl (Array.to_list Sys.argv) in
  let proj = load_project (List.hd args) in
  let prog = Project.program proj in
  let target = Project.target proj in
  let sp = sp_of proj in
  let name = match List.tl args with n :: _ -> n | [] -> "main" in
  let sub = Base.Option.value_exn (find_sub prog name) in
  let info =
    Hike.Vsa.offsets_of_sub target sp ~symtab:None
      ~prog:(Program.create ~subs:[ sub ] ())
      sub
  in
  Core.List.iter info.Hike.Convutils.sp_extents
    ~f:(fun (lo, hi) -> Printf.printf "EXTENT\t%Ld..%Ld\n" lo hi);
  Printf.printf "PROM\tarity=%d\twindow=%b\tretaddr=%d\n"
    info.Hike.Convutils.prom_arity info.Hike.Convutils.prom_window
    (List.length (Core_kernel.Set.to_list info.Hike.Convutils.prom_retaddr));
  Core_kernel.List.iter
    (Core_kernel.Map.to_alist info.Hike.Convutils.prom_sites)
    ~f:(fun (key, data) ->
      Printf.printf "SITE\t%s\tslots=[%s]\n"
        (Tid.name key)
        (String.concat ","
           (Core_kernel.List.map
              data.Hike.Convutils.site_slots
              ~f:(fun (i, dtid) ->
                Printf.sprintf "%d->%s" i (Tid.name dtid)))));
  Core_kernel.List.iter
    (Core_kernel.Map.to_alist info.Hike.Convutils.prom_resolved)
    ~f:(fun (key, data) ->
      Printf.printf "RESOLVED\t%s\t%s\n" (Tid.name key)
        (match data with
         | Some t -> "some " ^ Tid.name t
         | None -> "none"))
