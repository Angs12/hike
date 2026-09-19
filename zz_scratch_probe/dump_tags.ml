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
    let facts =
      let _envs, _sub' =
        Hike.Vsa.fixpoint target sp ~prog:(Program.create ~subs:[ sub ] ())
          ~images:[] ~block_addrs:[] sub
        |> Base.Option.value
             ~default:(Tid.Map.empty, sub)
      in
      Hike.Sections.{ prom_arity = 0;
                      prom_sites = Tid.Map.empty;
                      prom_resolved = Tid.Map.empty }
    in
    let sol =
      Vsa.static_graph_vsa ~abi:Hike_abi.x86_64_sysv
        ~resolved:Tid.Map.empty []
        (Program.create ~subs:[ sub ] ()) sub
        (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv sub)
    in
    let opt (r : ('a, 'b) Result.t) : 'a option =
      match r with Ok w -> Some w | Error _ -> None in
    let kind_of =
      Term.enum blk_t sub
      |> Seq.fold ~init:Tid.Map.empty ~f:(fun m blk ->
          Seq.fold (Term.enum def_t blk) ~init:m ~f:(fun m d ->
              let k =
                let open Base.Option in
                Base.Option.bind
                  (Vsa.Cbat_extraction.stack_address_of_rhs (Def.rhs d))
                  ~f:(fun addr ->
                    opt
                      (Vsa.denote_exp_at
                         ~pre:(Graphlib.Std.Solution.get sol (Term.tid blk))
                         ~blk ~def:d addr))
                >>= fun ws ->
                if Ws.is_bottom ws || Ws.in_stack_segment ws then
                  Some
                    (Vsa.Cbat_extraction.caller_split
                       (Vsa.Cbat_extraction.classify ws))
                else if Ws.is_top ws then
                  Some Hike.Stack_model.unbounded_span
                else None
              in
              match k with
              | Some k -> Core.Map.set m ~key:(Term.tid d) ~data:k
              | None -> m))
    in
    (* Region membership lives in the attribution trees now. *)
    let region_of = Tid.Map.empty in
    ignore region_of;
    ignore kind_of;
    Term.enum blk_t sub
    |> Seq.concat_map ~f:(Term.enum def_t)
    |> Seq.iter ~f:(fun d ->
           Printf.printf "%s\t%s\t%s\n"
             (Tid.to_string (Term.tid d))
             (Var.name (Def.lhs d))
             (match Core.Map.find kind_of (Term.tid d) with
              | Some (Cbat_vsa.Cbat_extraction.Range (l, h)) ->
                  Printf.sprintf "Range(%Lx,%Lx)" l h
              | Some (Cbat_vsa.Cbat_extraction.Infinite (l, h)) ->
                  Printf.sprintf "Infinite(%Lx,%Lx)" l h
              | Some (Cbat_vsa.Cbat_extraction.Caller (l, h)) ->
                  Printf.sprintf "Caller(%Lx,%Lx)" l h
              | Some (Cbat_vsa.Cbat_extraction.Mixed (l, h)) ->
                  Printf.sprintf "Mixed(%Lx,%Lx)" l h
              | Some Cbat_vsa.Cbat_extraction.Dead -> "Dead"
              | None -> "-"));
  Printf.printf "PROM\tarity=%d\n" facts.Hike.Sections.prom_arity;
  Core.List.iter
    (Core.Map.to_alist facts.Hike.Sections.prom_sites)
    ~f:(fun (key, data) ->
      Printf.printf "SITE\t%s\tslots=[%s]\n"
        (Tid.name key)
        (String.concat ","
           (Core.List.map
              data.Hike.Stack_model.site_slots
              ~f:(fun (i, dtid) ->
                Printf.sprintf "%d->%s" i (Tid.name dtid)))));
  Core.List.iter
    (Core.Map.to_alist facts.Hike.Sections.prom_resolved)
    ~f:(fun (key, data) ->
      Printf.printf "RESOLVED\t%s\t%s\n" (Tid.name key)
        (match data with
         | Some t -> "some " ^ Tid.name t
         | None -> "none"))

(* The indirect-call target denotations of the sub. *)
let () =
  let args = List.tl (Array.to_list Sys.argv) in
  let proj = load_project (List.hd args) in
  let prog = Project.program proj in
  let name = match List.tl args with n :: _ -> n | [] -> "main" in
  let sub = Base.Option.value_exn (find_sub prog name) in
  let sol =
    Vsa.static_graph_vsa ~abi:Hike_abi.x86_64_sysv [] (Program.create ~subs:[ sub ] ()) sub
      (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv sub)
  in
  let dump lbl st_end (j : jmp term) =
    match Jmp.kind j with
    | Call c -> (
        let lbl = lbl ^ " jmp=" ^ Tid.name (Term.tid j) in
        match Call.target c with
        | Indirect texp -> (
            match Vsa.Test_seam.denote_imm_exp texp st_end with
            | Error _ -> Printf.printf "TGT %s error\n" lbl
            | Ok ws ->
                Printf.printf "TGT %s top=%b min=%s max=%s\n" lbl
                  (Vsa.WordSet.is_top ws)
                  (match Vsa.WordSet.min_elem ws with
                  | Some w -> Cbat_word.to_string w
                  | None -> "-")
                  (match Vsa.WordSet.max_elem ws with
                  | Some w -> Cbat_word.to_string w
                  | None -> "-"))
        | Direct _ -> Printf.printf "TGT %s direct\n" lbl)
    | _ -> ()
  in
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun blk ->
      let st0 = Graphlib.Std.Solution.get sol (Term.tid blk) in
      let st_end =
        Base.List.fold_left (Term.enum def_t blk |> Seq.to_list)
          ~init:st0
          ~f:(fun st d -> Vsa.Test_seam.denote_def d st)
      in
      let lbl = Tid.name (Term.tid blk) in
      Term.enum jmp_t blk |> Seq.iter ~f:(dump lbl st_end))
