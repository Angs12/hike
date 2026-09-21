(* The ~written A/B for one sub: the production fixpoint under different
   kill-summary regimes.
   Usage: sm3_ab.exe <binary> <subname> prod|self|empty
   prod  - whole-program kill summaries (the pass's input)
   self  - kill summaries of the single-sub program
   empty - no summaries at all (every callee unknown) *)

open Bap.Std
open Probe_common

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  init ();
  match args with
  | [ path; subname; mode ] ->
    let proj = load_project path in
    let prog = Project.program proj in
    let target = Project.target proj in
    let sub =
      match find_sub prog subname with
      | Some s -> s
      | None -> usage Sys.argv.(0) "<binary> <subname> prod|self|empty"
    in
    let images =
      Hike.Image.get_section_mem ".rodata" proj
      |> Hike.Image.get_section_data
      |> Base.Option.map ~f:(fun (arr, min_addr, max_addr) ->
             [ { Cbat_vsa.img_lo = Word.to_int64_exn min_addr;
                 img_hi = Word.to_int64_exn max_addr;
                 img_bytes = arr } ])
      |> Base.Option.value ~default:[]
    in
    let symtab = Some (Project.symbols proj) in
    let block_addrs =
      Term.enum sub_t prog
      |> Seq.concat_map ~f:(Term.enum blk_t)
      |> Seq.filter_map ~f:(fun b ->
             Base.Option.map (Term.get_attr b address)
               ~f:(fun a -> (a, Term.tid b)))
      |> Seq.to_list
      |> Core.Map.of_alist_exn (module Addr)
    in
    let written =
      match mode with
      | "prod" -> Hike.Vsa.kill_summaries ~abi:(Hike.Abi.of_target target) prog
      | "self" ->
        Hike.Vsa.kill_summaries ~abi:(Hike.Abi.of_target target)
          (Program.create ~subs:[ sub ] ())
      | "empty" -> Tid.Map.empty
      | _ -> usage Sys.argv.(0) "<binary> <subname> prod|self|empty"
    in
    Printf.printf "=== sm3_ab %s (%s) mode=%s ===\n%!" (Sub.name sub) mode
      (if Core.Map.is_empty written then "empty"
       else Printf.sprintf "%d summaries" (Core.Map.length written));
    let t0 = Unix.gettimeofday () in
    let envs, _, _ =
      Hike.Vsa.fixpoint target ~prog ~symtab ~images ~written ~block_addrs sub
      |> Base.Option.value
           ~default:(Tid.Map.empty, sub, Core.Map.empty (module Addr))
    in
    let dt = Unix.gettimeofday () -. t0 in
    Printf.printf "AB %s fixpoint %.3fs  envs=%d\n%!" mode dt
      (Core.Map.length envs)
  | _ -> usage Sys.argv.(0) "<binary> <subname> prod|self|empty"
