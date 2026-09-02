(* dump_tags — the per-def TAG matrix (the tag-diff tool). Recreated
   2026-08-31 (Item 1 of the architecture program).

   Usage: dump_tags.exe <binary> [subname]   (default subname "main")

   Runs [Hike.Relevance.analyze] on the named sub and
   [Hike.Vsa.offsets_of_sub] (the full producer), then prints one TSV line
   per def: tid, lhs, the tag set (relevant / stack_access / dynamic_alloc),
   and — for a stack_access def — its vsa offset kind. Textual-diffing two
   runs (before/after a change) is the intended use:

     dump_tags.exe a bin | sort > a.tsv ; dump_tags.exe b bin | sort > b.tsv ; diff a.tsv b.tsv *)

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
    let tagged = Hike.Relevance.analyze sp sub in
    let info = Hike.Vsa.offsets_of_sub target sp tagged in
    let kind_of = info.Hike.Convutils.offsets in
    (* mem-fission (2026-09-02): the REGION column — the region id whose
       span contains the def's tag (the fission's per-region mem var /
       alloca).  "-" when the def belongs to no region (the fallback
       path). *)
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
    in    Term.enum blk_t tagged
    |> Seq.iter ~f:(fun b ->
        Term.enum def_t b
        |> Seq.iter ~f:(fun d ->
            let tags =
              [ (Hike.Relevance.relevant, "relevant");
                (Hike.Relevance.stack_access, "stack_access");
                (Hike.Relevance.dynamic_alloc, "dynamic_alloc") ]
              |> Base.List.filter_map ~f:(fun (t, n) ->
                  if Term.has_attr d t then Some n else None)
              |> Base.String.concat ~sep:","
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