(* The overlap census (T25 step 7): the block bytes the worklist's
   functions duplicate.  A block start held by n functions counts its
   length n - 1 times; lengths come from BAP's decode.
   Usage: dune exec test/probe/research/overlap.exe -- <binary> ... *)

open Bap.Std

let census (path : string) : unit =
  let proj = Probe_common.load_project path in
  let file = Hike.Decode.file_of proj in
  let program = (Hike.Drive.run proj).program in
  let state = Hike.Decode.scan proj ~file ~roots:[] in
  let starts sub =
    Term.enum blk_t sub
    |> Seq.filter_map ~f:(fun b -> Term.get_attr b address)
    |> Seq.to_list |> Core.Set.of_list (module Addr)
  in
  let holders =
    Term.enum sub_t program
    |> Seq.fold ~init:Addr.Map.empty ~f:(fun acc sub ->
        Core.Set.fold (starts sub) ~init:acc ~f:(fun acc a ->
            Core.Map.update acc a ~f:(fun n -> 1 + Base.Option.value n ~default:0)))
  in
  let length =
    Term.enum sub_t program
    |> Seq.fold ~init:Addr.Map.empty ~f:(fun acc sub ->
        match Term.get_attr sub address with
        | None -> acc
        | Some entry ->
          Hike.Decode.function_cfg ~file state ~entry
            ~is_entry:(Disasm.Driver.is_subroutine state)
          |> Graphs.Cfg.nodes
          |> Seq.fold ~init:acc ~f:(fun acc b ->
              Core.Map.set acc ~key:(Block.addr b) ~data:(Memory.length (Block.memory b))))
  in
  let blocks, bytes =
    Core.Map.fold holders ~init:(0, 0) ~f:(fun ~key ~data:n (blocks, bytes) ->
        if n < 2 then (blocks, bytes)
        else
          (blocks + n - 1,
           bytes + (n - 1) * Base.Option.value (Core.Map.find length key) ~default:0))
  in
  Printf.printf "%s\tfunctions=%d\tduplicated_blocks=%d\tduplicated_bytes=%d\n%!"
    (Filename.basename path) (Term.length sub_t program) blocks bytes

let () =
  Probe_common.init ();
  match Array.to_list Sys.argv with
  | _ :: (_ :: _ as paths) -> List.iter census paths
  | _ -> Probe_common.ws_usage Sys.argv.(0)
