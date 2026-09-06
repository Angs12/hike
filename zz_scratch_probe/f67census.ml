(* Cost census for report articles 6 + 7, via exported seams + BAP APIs.
   Article 6: time Model.frame_escapes / sp_escaped / frame_addr_alias
   per sub (exported in Hike.Stack_model).
   Article 7: replicate the bss/copy-reloc Ogre queries (pure reads over
   Project.specification, same as hike.ml) to census how often the
   copy_reloc_addrs_val block provably returns [], and time the block's
   walk pattern (3 full-program def walks with to_list materialization).
   Usage: f67census.exe <binary> *)

open Bap.Std
open Probe_common

let time f =
  let t0 = Unix.gettimeofday () in
  let r = f () in
  r, Unix.gettimeofday () -. t0

(* --- article 7: Ogre queries replicated from hike.ml --- *)

type region = { addr : int64; size : int64; info : string }

let get_named_region_info proj =
  let open Ogre in
  let region addr size info = { addr; size; info } in
  let addr = Type.("addr" %: int) in
  let size = Type.("size" %: int) in
  let name = Type.("name" %: str) in
  let table_type = Type.(scheme addr $ size $ name) in
  let named_region () = Ogre.declare ~name:"named-region" table_type region in
  let regions = Ogre.collect Query.(select (from named_region)) in
  fst (Ogre.run regions (Project.specification proj) |> Core.Or_error.ok_exn)

let get_copy_relocations proj ~bss_addr ~bss_size =
  let open Ogre in
  let at = Type.("at" %: int) in
  let name = Type.("name" %: str) in
  let nr_tbl = Type.(scheme at $ name) in
  let name_ref () =
    Ogre.declare ~name:"llvm:name-reference" nr_tbl (fun a n -> (a, n))
  in
  let rows =
    Ogre.collect Query.(select (from name_ref)) |> fun c ->
    fst (Ogre.run c (Project.specification proj) |> Core.Or_error.ok_exn)
  in
  Base.Sequence.to_list rows
  |> Base.List.filter_map ~f:(fun (fixup, _name) ->
      let off = Int64.sub fixup bss_addr in
      if Int64.compare off 0L >= 0 && Int64.compare off bss_size < 0 then
        Some off
      else None)

(* The copy_reloc_addrs_val block's walk pattern, timed in isolation:
   per sub, loads-walk + stores-walk (each materializing blk + def lists),
   twice over (loads_and_stores + stores_only). *)
let walk_pattern_cost prog =
  let one_pass () =
    Term.enum sub_t prog
    |> Seq.iter ~f:(fun sub ->
        Term.enum blk_t sub |> Seq.to_list
        |> Base.List.iter ~f:(fun blk ->
            Term.enum def_t blk |> Seq.to_list |> ignore))
  in
  let _, t1 = time one_pass in
  let _, t2 = time one_pass in
  let _, t3 = time one_pass in
  t1 +. t2 +. t3

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
    Printf.printf "=== articles 6+7 census: %s ===\n" path;
    Printf.printf "subs: %d\n" (Core.List.length subs);
    (* article 7 *)
    let regions = get_named_region_info proj in
    let bss =
      Seq.find regions ~f:(fun { info; _ } -> String.equal info ".bss")
    in
    (match bss with
    | None -> Printf.printf "A7: no .bss region -> block returns []\n"
    | Some { addr; size; _ } ->
      let relocs = get_copy_relocations proj ~bss_addr:addr ~bss_size:size in
      Printf.printf "A7: .bss present, copy relocs in bss: %d%s\n"
        (Core.List.length relocs)
        (if relocs = [] then " -> block returns []" else ""));
    let wc = walk_pattern_cost prog in
    Printf.printf "A7: 3x full-program def-walk cost: %.4fs\n" wc;
    (* article 6 *)
    let t_esc = ref 0. in
    let t_alias = ref 0. in
    let rows = ref [] in
    let rows_alias = ref [] in
    Core.List.iter subs ~f:(fun sub ->
        let nm = Sub.name sub in
        let _, dt1 =
          time (fun () -> ignore (Hike.Stack_model.sp_escaped sp target sub))
        in
        let _, dt2 =
          time (fun () -> ignore (Hike.Stack_model.frame_addr_alias sp target sub))
        in
        t_esc := !t_esc +. dt1;
        t_alias := !t_alias +. dt2;
        rows :=
          (dt1, nm,
           Term.enum blk_t sub |> Seq.length,
           Term.enum blk_t sub
           |> Seq.concat_map ~f:(Term.enum def_t)
           |> Seq.length)
          :: !rows;
        rows_alias := (dt2, nm) :: !rows_alias);
    let rows =
      Core.List.sort !rows ~compare:(fun (a, _, _, _) (b, _, _, _) ->
          Float.compare b a)
    in
    Printf.printf "A6: sp_escaped total: %.3fs, frame_addr_alias total: %.3fs\n"
      !t_esc !t_alias;
    Printf.printf "A6: top subs by escape-analysis cost:\n";
    Core.List.iter (Core.List.take rows 8) ~f:(fun (t, nm, nb, nd) ->
        Printf.printf "  %7.3fs  %-28s %4d blk %6d defs\n" t nm nb nd);
    let rows_alias =
      Core.List.sort !rows_alias ~compare:(fun (a, _) (b, _) ->
          Float.compare b a)
    in
    Printf.printf "A6: top subs by frame_addr_alias alone:\n";
    Core.List.iter (Core.List.take rows_alias 5) ~f:(fun (t, nm) ->
        Printf.printf "  %7.3fs  %s\n" t nm)
