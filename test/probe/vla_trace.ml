(* The VLA round-trip tracer: solves a sub and prints, for every def
   whose rhs reads or writes memory, the address denotation's origin
   and bounds — the through-pointer chain's demotion finder.  vsa-debug
   only.  Usage: vla_trace.exe <binary> <sub-name> *)
open Bap.Std
open Probe_common

module Ws = Cbat_vsa.WordSet

let () =
  init ();
  let bin = Sys.argv.(1) in
  let name = Sys.argv.(2) in
  let proj = load_project bin in
  let prog = Project.program proj in
  match find_sub prog name with
  | None -> Printf.eprintf "no sub %s\n%!" name
  | Some sub0 ->
    let norm = Vsa.Test_seam.normalize_round sub0 in
    Term.enum blk_t norm
    |> Seq.iter ~f:(fun blk ->
           Term.enum def_t blk |> Seq.iter ~f:(fun d ->
               match Def.rhs d with
               | Bil.BinOp (Bil.LSHIFT, _, Bil.Int _) ->
                   Printf.printf "NORM-LSHIFT %s\n%!" (Var.name (Def.lhs d))
               | _ -> ()));
    (Term.enum blk_t sub0
    |> Seq.iter) ~f:(fun blk ->
           let ds = Term.enum def_t blk |> Seq.to_list in
           Base.List.iteri ds ~f:(fun i d ->
               match Def.rhs d with
               | Bil.BinOp (Bil.RSHIFT, _, Bil.Int _)
                 when i + 1 < Base.List.length ds -> (
                   match Def.rhs (Base.List.nth_exn ds (i + 1)) with
                   | Bil.BinOp (Bil.LSHIFT, Bil.Var v, Bil.Int _) ->
                       Printf.printf "PAIR %s >> then << %s same=%b\n%!"
                         (Var.name (Def.lhs d)) (Var.name v)
                         (Var.equal v (Def.lhs d))
                   | _ -> ())
               | _ -> ()));
    let envs, sub', _ =
      Hike.Vsa.fixpoint (Project.target proj)
        ~lookup:(fun _ -> None)
        ~sub_addrs:(Core.Map.empty (module Addr)) ~images:[]
        ~written:(Hike.Vsa.kill_summaries ~abi:Hike.Abi.x86_64_sysv
                    (Program.create ~subs:[ sub0 ] ()))
        ~lift_at:(fun _ ~block_addrs:_ -> None)
        ~block_addrs:(Core.Map.empty (module Addr)) sub0
    in
    Hike.Kb.install
      (Hike.Kb.build ~lookup:(fun _ -> None) ~block_envs:envs
         ~block_addrs:(Core.Map.empty (module Addr))
         ~target:(Project.target proj));
    let facts = Hike.Kb.facts () in
    Printf.printf "vla_extents: %s\n%!"
      (Core.Map.to_alist facts.Hike.Kb.vla_extents
      |> Base.List.map ~f:(fun (t, (l, h)) ->
             Printf.sprintf "%s[%Ld..%Ld]" (Tid.to_string t)
               (Stdlib.Int64.sub l Ws.stack_base)
               (Stdlib.Int64.sub h Ws.stack_base))
      |> String.concat ", ");
    let show ~blk ~d e =
      match facts.Hike.Kb.denote ~blk ~def:d e with
      | Error err -> "err " ^ Type.Error.to_string err
      | Ok ws ->
          Printf.sprintf "%s %s"
            (match Ws.origin ws with
             | Some o -> Hike_origin.name o
             | None ->
                 if Ws.is_top ws then "TOP"
                 else if Ws.is_bottom ws then "BOT"
                 else "plain")
            (match Ws.stack_bounds ws with
             | Some (l, h) -> Printf.sprintf "[%Ld..%Ld]" l h
             | None -> "")
    in
    Term.enum blk_t sub'
    |> Seq.iter ~f:(fun blk ->
           Term.enum def_t blk
           |> Seq.iter ~f:(fun d ->
                  match Hike.Stack_model.addr_of_rhs (Def.rhs d) with
                  | Some (a, _) ->
                      let loaded =
                        match Def.rhs d with
                        | Bil.Load _ -> (
                            match
                              Core.Map.find envs (Term.tid blk)
                            with
                            | Some (_, post) ->
                                " :: loads "
                                ^ show ~blk ~d (Bil.Var (Def.lhs d))
                                ^ " (post)"
                            | None -> "")
                        | _ ->
                            Base.Option.value_map
                              (Hike.Stack_model.store_data_of_rhs (Def.rhs d))
                              ~default:"" ~f:(fun data ->
                                 " :: data " ^ show ~blk ~d data)
                      in
                      Printf.printf "%s %-10s addr %s%s\n%!"
                        (Tid.to_string (Term.tid d))
                        (Var.name (Def.lhs d))
                        (show ~blk ~d a) loaded
                  | None -> ()))
