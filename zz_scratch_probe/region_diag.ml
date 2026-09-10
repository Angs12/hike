(* Prints one sub's stack-access denotations and its region plan: per call
   block, each pointer-arg register's denotation (stack-symbolic or not);
   the region partition with every member's tag and rhs.
   Usage: region_diag.exe <binary> [subname] (default "main"). *)

open Bap.Std
open Probe_common

module Abi = Hike_abi

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
      | None -> usage Sys.argv.(0) (Printf.sprintf "<binary> — %s not found" name)
    in
    (* Replicates hike_vsa's flow: fixpoint, then the solution. *)
    let prog' = Program.create ~subs:[ sub ] () in
    let sol =
      try Some (Vsa.static_graph_vsa [] prog' sub (Vsa.init_sol sub))
      with Vsa.Fixpoint_not_converged _ ->
        Printf.printf "NOT-CONVERGED\n";
        None
    in
    match sol with
    | None -> ()
    | Some sol ->
      let arg_regs = Abi.param_regs target in
      Printf.printf "sub %s: %d blocks\n" name
        (Seq.length (Term.enum blk_t sub));
      Term.enum blk_t sub
      |> Seq.iter ~f:(fun blk ->
          let calls =
            Term.enum jmp_t blk
            |> Seq.filter ~f:(fun j ->
                match Jmp.kind j with Call _ -> true | _ -> false)
            |> Seq.to_list
          in
          if calls <> [] then begin
            let btid = Term.tid blk in
            Printf.printf "block %s:\n" (Tid.name btid);
            let st =
              Vsa.Test_seam.denote_defs blk (Graphlib.Std.Solution.get sol btid)
            in
            Base.List.iter arg_regs ~f:(fun r ->
                let d = Vsa.Test_seam.denote_imm_exp (Bil.Var r) st in
                let sa = Vsa.Cbat_extraction.is_stack_access st (Bil.Var r) in
                (match d with
                 | Error e ->
                  Printf.printf "  %s: ERROR stack=%b\n"
                    (Var.name r) sa
                | Ok ws ->
                  let kind =
                    if Ws.is_top ws then "TOP"
                    else if Ws.is_bottom ws then "BOTTOM"
                    else
                      (match Ws.as_stack ws with
                       | Some _ -> "StackOff"
                       | None ->
                         (match Ws.stack_bounds ws with
                          | Some (lo, hi) ->
                            Printf.sprintf "plain[%Ld..%Ld]" lo hi
                          | _ -> "plain?"))
                  in
                  Printf.printf "  %s: %s stack=%b\n"
                    (Var.name r) kind sa));
            Base.List.iter calls ~f:(fun j ->
                match Jmp.kind j with
                | Call c ->
                  let tgt =
                    match Call.target c with
                    | Direct t -> Printf.sprintf "direct %s" (Tid.name t)
                    | Indirect e ->
                      let sa = Vsa.Cbat_extraction.is_stack_access st e in
                      Printf.sprintf "indirect (stack-symbolic=%b)" sa
                  in
                  Printf.printf "  call %s return=%b\n" tgt
                    (Option.is_some (Call.return c))
                | _ -> ())
          end);
      (* The region plan the model builds from the extraction's tags. *)
      let info0 =
        Hike.Stack_model.mk_vsa_info_maps
          ~offsets:(Vsa.Cbat_extraction.extract
                      ~dynamic_alloc:(fun _ -> false)
                      ~alloc_tids:(Vsa.Cbat_extraction.detect_dynamic_alloc sp sub)
                      ~sol sub)
          ~degraded:false ~vla_alloc_tids:Tid.Set.empty ()
          ~regions:[] ~stack_plan:[]
      in
      (* Tagged defs whose tag is a suspicious singleton. *)
      Term.enum blk_t sub
      |> Seq.iter ~f:(fun blk ->
          Term.enum def_t blk
          |> Seq.iter ~f:(fun d ->
              match Core.Map.find info0.Hike.Stack_model.offsets (Term.tid d) with
              | Some (Hike.Stack_model.Range (lo, hi)) when Int64.equal lo hi ->
                Printf.printf "SINGLETON %s: %s = %s\n" (Tid.name (Term.tid d))
                  (Var.name (Def.lhs d))
                  (Format.asprintf "%a" Exp.pp (Def.rhs d))
              | _ -> ()));
      let defs =
        Term.enum blk_t sub
        |> Seq.concat_map ~f:(Term.enum def_t)
        |> Seq.fold ~init:(Core.Map.empty (module Tid)) ~f:(fun m d ->
            Core.Map.set m ~key:(Term.tid d) ~data:(Def.rhs d))
      in
      let rs = Hike.Stack_model.regions_of_sub sub info0 in
      Base.List.iter rs ~f:(fun r ->
          Printf.printf "region r%d span=(%Ld,%Ld) convertible=%b members=%d\n"
            r.Hike.Stack_model.id (fst r.Hike.Stack_model.span) (snd r.Hike.Stack_model.span)
            r.Hike.Stack_model.convertible (Base.List.length r.Hike.Stack_model.members);
          Base.List.iter r.Hike.Stack_model.members ~f:(fun (tid, (lo, hi)) ->
              Printf.printf "  member %s (%Ld,%Ld): %s = %s\n" (Tid.name tid) lo hi
                (match Core.Map.find info0.Hike.Stack_model.offsets tid with
                 | Some k -> vsa_kind_to_string k
                 | None -> "-")
                (match Core.Map.find defs tid with
                 | Some rhs -> Format.asprintf "%a" Exp.pp rhs
                 | None -> "?")))
