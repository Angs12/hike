(* Per-sub cost distribution over the production per-sub path, slowest first.
   Usage: subtimes.exe <binary>
   The inputs replicate pass_vsa exactly: the .rodata image, the symtab,
   the whole-program kill summaries, and the block-address map. *)

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
    let subs = all_subs prog in
    Printf.printf "# subs: %d\n" (List.length subs);
    (* pass_vsa's image set: the .rodata section only. *)
    let images =
      Hike.Image.get_section_mem ".rodata" proj
      |> Hike.Image.get_section_data
      |> Base.Option.map ~f:(fun (arr, min_addr, max_addr) ->
             [ { Cbat_vsa.img_lo = Word.to_int64_exn min_addr;
                 img_hi = Word.to_int64_exn max_addr;
                 img_bytes = arr } ])
      |> Base.Option.value ~default:[]
    in
    Printf.eprintf "probe: .rodata image %d bytes\n%!"
      (match images with
       | [ im ] -> Bytes.length im.Cbat_vsa.img_bytes
       | _ -> 0);
    let symtab = Some (Project.symbols proj) in
    let written = Hike.Vsa.kill_summaries ~abi:(Hike.Abi.of_target target) prog in
    let block_addrs =
      Term.enum sub_t prog
      |> Seq.concat_map ~f:(Term.enum blk_t)
      |> Seq.filter_map ~f:(fun b ->
             Base.Option.map (Term.get_attr b address)
               ~f:(fun a -> (a, Term.tid b)))
      |> Seq.to_list
      |> Core.Map.of_alist_exn (module Addr)
    in
    Printf.eprintf "probe: %d block addrs; solving subs one by one\n%!"
      (Core.Map.length block_addrs);
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
          Printf.eprintf "probe: solving %s (%d blk %d defs)\n%!" name nblk ndefs;
          let t0 = Unix.gettimeofday () in
          let _envs, _sub', _ =
            Hike.Vsa.fixpoint target ~prog ~symtab ~images ~written
              ~block_addrs sub
            |> Base.Option.value
                 ~default:(Tid.Map.empty, sub, Core.Map.empty (module Addr))
          in
          let dt = Unix.gettimeofday () -. t0 in
          let facts =
            Hike.Kb.build ~block_envs:Tid.Map.empty
              ~block_addrs:(Core.Map.empty (module Addr)) ~target
          in
          let ntags = Core.Set.length (Hike.Promote.dynamic_alloc_tids_of ~facts sub) in
          Printf.eprintf "probe: %s done in %.3fs\n%!" name dt;
          (dt, name, nblk, ndefs, ntags))
        subs
    in
    let rows = List.sort (fun (a, _, _, _, _) (b, _, _, _, _) -> compare b a) rows in
    let total =
      List.fold_left (fun acc (t, _, _, _, _) -> acc +. t) 0.0 rows
    in
    Printf.printf "total producer time: %.3fs over %d subs\n\n" total
      (List.length rows);
    Printf.printf "%10.3fs  %5.1f%%  %6d blk %7d defs %5d tags  %s\n" total 100.0
      0 0 0 "(ALL)";
    List.iteri
      (fun i (dt, name, nblk, ndefs, ntags) ->
        Printf.printf "%10.3fs  %5.1f%%  %6d blk %7d defs %5d tags  %s\n"
          dt (100.0 *. dt /. total) nblk ndefs ntags name;
        if i mod 20 = 0 then flush stdout)
      rows;
    (* Share of the slowest decile. *)
    let n = List.length rows in
    let head = ref 0.0 in
    List.iteri
      (fun i (dt, _, _, _, _) ->
        if 10 * i < n then head := !head +. dt)
      rows;
    Printf.printf "\nslowest 10%% of subs = %.1f%% of total time\n"
      (100.0 *. !head /. total)
