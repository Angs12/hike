(* Per-sub cost distribution over the production per-sub path, slowest first.
   Usage: subtimes.exe <binary>
   The inputs replicate pass_vsa exactly: the .rodata image, the symtab,
   the whole-program kill summaries, and the block-address map. *)

open Bap.Std
open Probe_common

(* passcost mode: times seed-detect, vsa, stl and dce per sub, and counts DCE
   sweep rounds.  CSV on stdout, summary on stderr.  Initially its own probe;
   folded in here. *)

(* Infers the round count from the def-count trajectory. *)
let dce_rounds (target : Bap_core_theory.Theory.Target.t) (sub : sub term) : int * int =
  let n0 =
    Term.enum blk_t sub
    |> Seq.fold ~init:0 ~f:(fun n blk -> n + Seq.length (Term.enum def_t blk))
  in
  (* dce runs its own sweep to stability, so re-running it must be a no-op. *)
  let rec go sub prev_n rounds =
    let sub' = Dce.dce ~target sub in
    let n' =
      Term.enum blk_t sub'
      |> Seq.fold ~init:0 ~f:(fun n blk -> n + Seq.length (Term.enum def_t blk))
    in
    if n' = prev_n then rounds
    else if rounds > 20 then rounds
    else go sub' n' (rounds + 1)
  in
  let rounds = go sub n0 1 in
  (rounds, n0)

let passcost_main (args : string list) : unit =
  if Base.List.is_empty args then usage Sys.argv.(0) "<binary>...";
  Printf.printf "binary,sub,ndefs,vla_s,vsa_s,dce_s,dce_rounds\n";
  let tot = ref 0.0 in
  Base.List.iter args ~f:(fun path ->
      let proj = load_project path in
      let target = Project.target proj in
      let prog = Project.program proj in
      let facts =
        Hike.Kb.build ~block_envs:Tid.Map.empty
          ~block_addrs:(Core.Map.empty (module Addr)) ~target
      in
      Base.List.iter (all_subs prog) ~f:(fun sub ->
          let ndefs =
            Term.enum blk_t sub
            |> Seq.fold ~init:0 ~f:(fun n blk ->
                   n + Seq.length (Term.enum def_t blk))
          in
          let _events, t_rel =
            time (fun () -> Hike.Promote.dynamic_alloc_tids_of ~facts sub)
          in
          let _envs, t_vsa =
            time (fun () ->
                Hike.Vsa.fixpoint target ~prog:(Program.create ~subs:[ sub ] ())
                  ~symtab:None ~images:[]
                  ~written:(Hike.Vsa.kill_summaries ~abi:facts.Hike.Kb.abi prog)
                  ~lift_at:(fun _ -> None)
                  ~block_addrs:(Core.Map.empty (module Addr)) sub)
          in
          let _dced, t_dce = time (fun () -> Dce.dce ~target sub) in
          let rounds, _ = dce_rounds target sub in
          tot := !tot +. t_vsa;
          Printf.printf "%s,%s,%d,%.4f,%.4f,%.4f,%d\n"
            (Core.Filename.basename path) (Sub.name sub) ndefs t_rel t_vsa t_dce
            rounds));
  Printf.eprintf "\ntotal vsa time = %.2fs\n" !tot

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  init ();
  match args with
  | "--passcost" :: rest -> passcost_main rest
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
              ~lift_at:(fun _ -> None)
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
