(* Dumps per-def audit data for PROD unbounded-span stack accesses.
   Usage: audit02.exe <binary> [subname] (default "main", "ALL" scans all). *)

open Bap.Std
open Bap_core_theory
open Probe_common

(* Replica rule (pinned — owner decision keeps this probe): the walk below
   replicates the production producer's per-def logic; a PROD-vs-replica
   divergence is investigated in production, never papered over in the replica. *)

let ws_str (w : Ws.t) : string =
  if Ws.is_top w then "TOP"
  else if Ws.is_bottom w then "BOTTOM"
  else
    let lo = match Ws.min_elem w with Some m -> Cbat_word.to_string m | None -> "?" in
    let hi = match Ws.max_elem w with Some m -> Cbat_word.to_string m | None -> "?" in
    if Ws.is_infinite w then Printf.sprintf "{%s..%s}^inf" lo hi
    else Printf.sprintf "{%s..%s}" lo hi

let exp_str (e : exp) : string = Format.asprintf "%a" Exp.pp e

(* Walks the sub like the production producer; `on_unbounded` compares replica vs production. *)
let audit_sub ~synth (sub : sub term) : unit =
  Printf.printf "  raw defs: %d\n"
    (Term.enum blk_t sub |> Seq.concat_map ~f:(Term.enum def_t) |> Seq.length);
  (* The production per-def verdict, recomputed from the denotations. *)
  let sol = run_sub_fixpoint ~synth sub in
  (* The seam reads the defs' Env Tags: audit the sweep's stamped sub. *)
  let _, sub = Vsa.stamp_envs_of_sol ~synth ~sol sub in
  let kind_of (blk : blk term) (d : def term) : Ws.kind option =
    let open Base.Option in
    Base.Option.bind
      (Vsa.Test_seam.mem_addr_of (Def.rhs d))
      ~f:(fun addr ->
        Result.to_option
          (Vsa.denote_exp_at ~synth
             ~pre:(Graphlib.Std.Solution.get sol (Term.tid blk))
             ~blk ~def:d addr))
    >>= fun ws ->
    if Ws.in_stack_segment ws then
      Some (Ws.caller_split (Ws.classify ws))
    else if Ws.is_top ws then Some Ws.unbounded_span
    else None
  in
  let prod_map =
    Term.enum blk_t sub
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m blk ->
        Seq.fold (Term.enum def_t blk) ~init:m ~f:(fun m d ->
            match kind_of blk d with
            | Some k -> Core.Map.set m ~key:(Term.tid d) ~data:k
            | None -> m))
  in
  let prod_unbounded : (Tid.t, unit) Hashtbl.t = Hashtbl.create 16 in
  Core.Map.iteri prod_map ~f:(fun ~key:tid ~data:k ->
      match k with
      | Ws.Infinite (lo, hi) when Ws.is_unbounded_span lo hi ->
          Hashtbl.add prod_unbounded tid ()
      | _ -> ());
  let prod_unbounded_count = Hashtbl.length prod_unbounded in
  let stack_count = Core.Map.length prod_map in
  Printf.printf "=== sub %s (%s) — stack=%d unbounded-span(PROD)=%d ===\n"
    (Sub.name sub) (Tid.to_string (Term.tid sub))
    stack_count prod_unbounded_count;
  if stack_count = 0 then ()
  else begin
    let tags = sol in
    Term.enum blk_t sub
    |> Seq.iter ~f:(fun blk ->
        let defs = Term.enum def_t blk |> Seq.to_list in
        let _ =
          Base.List.fold_left defs
            ~init:(Graphlib.Std.Solution.get tags (Term.tid blk))
            ~f:(fun st d ->
                 let st_before = st in
                 let st_after = Vsa.Test_seam.denote_def ~synth d st in
                 (match Def.rhs d with
                  | Bil.Load (_, addr, _, _) | Bil.Store (_, addr, _, _, _)
                  | Bil.Cast (_, _, Bil.Load (_, addr, _, _))
                  | Bil.Cast (_, _, Bil.Store (_, addr, _, _, _))
                    when Core.Map.mem prod_map (Term.tid d) ->
                      let is_prod_ub = Hashtbl.mem prod_unbounded (Term.tid d) in
                      if is_prod_ub then begin
                        let st_tag =
                          Exp.free_vars addr
                          |> Core.Set.fold ~init:st_before ~f:(fun acc v ->
                              match Var.typ v with
                              | Type.Imm w ->
                                let tag_v = AI.find_word w
                                    (Graphlib.Std.Solution.get tags (Term.tid blk)) v in
                                let cur = AI.find_word w acc v in
                                let mm = Ws.meet cur tag_v in
                                if Ws.is_top cur && Cbat_word.is_one (Ws.cardinality mm)
                                   || Cbat_word.is_zero (Ws.cardinality mm)
                                   || Ws.equal mm cur
                                then acc
                                else AI.add_word acc ~key:v ~data:mm
                              | Type.Mem _ | Type.Unk -> acc) in
                        let ws_before = Vsa.Test_seam.denote_imm_exp ~synth addr st_before in
                        let ws_tag = Vsa.Test_seam.denote_imm_exp ~synth addr st_tag in
                        Printf.printf "  DEF %s (blk %s): %s\n"
                          (Tid.to_string (Term.tid d))
                          (Tid.to_string (Term.tid blk))
                          (exp_str (Def.rhs d));
                        Printf.printf "    raw addr     : %s\n" (exp_str addr);
                        Printf.printf "    addr (used)  : %s\n" (exp_str addr);
                        (match ws_before with
                         | Ok ws -> Printf.printf "    denote(before): %s\n" (ws_str ws)
                         | Error _ -> Printf.printf "    denote(before): ERROR\n");
                        (match ws_tag with
                         | Ok ws -> Printf.printf "    denote(tag)   : %s\n" (ws_str ws)
                         | Error _ -> Printf.printf "    denote(tag)   : ERROR\n");
                        Exp.free_vars addr |> Core.Set.iter ~f:(fun v ->
                            match Var.typ v with
                            | Type.Imm w ->
                              let cur = AI.find_word w st_before v in
                              let tag_v = AI.find_word w
                                  (Graphlib.Std.Solution.get tags (Term.tid blk)) v in
                              Printf.printf "    free var %s: cur(before)=%s tag=%s\n"
                                (Var.name v) (ws_str cur) (ws_str tag_v)
                            | _ -> ());
                        (* Classify the failure from the candidates. *)
                        let diag =
                          match ws_before, ws_tag with
                          | Ok ws, _ when Ws.is_top ws ->
                            "candidate 1: the address denotes TOP (no stack word in scope)"
                          | Error _, _ -> "candidate 3: denote_imm_exp returned Error (val_as_imm failure)"
                          | Ok _, Ok _ ->
                            (match ws_before, ws_tag with
                             | Ok b, Ok t when not (Ws.equal b t) ->
                               "candidate 4: partitioned tag value differs from sequential (free-var divergence)"
                             | _ ->
                               (match ws_before with
                                | Ok ws ->
                                  Printf.sprintf "unclassified: ws=%s"
                                    (ws_str ws)
                                | _ -> "unclassified: unknown"))
                          | _ -> "unclassified: unknown" in
                        Printf.printf "    DIAGNOSIS: %s\n" diag
                      end
                    | _ -> ());
                   st_after) in
          ())
  end

(* wbig mode: one line per def whose address window is >= 2^63, plus per-sub
   counts.  Initially its own probe; folded in here.  Subs that fail the
   fixpoint report and skip. *)
let wbig_main (path : string) : unit =
  let proj = load_project path in
  let synth, prog = production_input proj in
  let total = ref 0 in
  let skipped = ref 0 in
  all_subs prog
  |> List.iter (fun sub ->
      try
        let n = ref 0 in
        let sub', sol = analyze_and_fixpoint ~synth sub in
        (* The analyze pass's solution is the kind source — no re-solve. *)
        let kind_of = Probe_common.seam_kinds_of ~synth sol sub' in
        Term.enum blk_t sub'
        |> Seq.iter ~f:(fun b ->
            let has_call =
              Term.enum jmp_t b
              |> Seq.exists ~f:(fun j ->
                  match Jmp.kind j with Call _ -> true | _ -> false)
            in
            let st = ref (Graphlib.Std.Solution.get sol (Term.tid b)) in
            Term.enum def_t b
            |> Seq.iter ~f:(fun d ->
                (match Def.rhs d with
                 | Bil.Load (_, addr, _, _) | Bil.Store (_, addr, _, _, _) ->
                   (match Vsa.Test_seam.denote_imm_exp ~synth addr !st with
                    | Ok ws when ws_window_big ws ->
                      incr n;
                      Printf.printf "w_big\t%s\t%s\t%s\t%s\tcall=%b\tkind=%s\n"
                        (Sub.name sub') (Tid.name (Term.tid b))
                        (def_to_string d) (ws_to_string ws) has_call
                        (match Core.Map.find kind_of (Term.tid d) with
                         | Some k -> vsa_kind_to_string k
                         | None -> "-")
                    | _ -> ())
                 | _ -> ());
                st := Vsa.Test_seam.denote_def ~synth d !st));
        Printf.printf "=== %s: %d w_big access(es)\n" (Sub.name sub') !n;
        total := !total + !n
      with e ->
        incr skipped;
        Printf.printf "=== %s: SKIPPED (%s)\n" (Sub.name sub)
          (Printexc.to_string e));
  Printf.printf "TOTAL w_big accesses: %d (%d sub(s) skipped)\n" !total !skipped

let () =
  let paths = Array.to_list Sys.argv |> List.tl in
  match paths with
  | "--wbig" :: binary :: _ -> init (); wbig_main binary
  | [] -> Printf.printf "usage: %s <binary> [subname] | --wbig <binary>\n" Sys.argv.(0); exit 0
  | binary :: rest ->
    init ();
    let subname = match rest with hd :: _ -> hd | [] -> "main" in
    (match Project.create (Project.Input.file ~loader:"llvm" ~filename:binary) with
     | Error e ->
       Printf.printf "LOAD-FAIL %s: %s\n" binary (Core.Error.to_string_hum e); exit 1
     | Ok proj ->
       (* The address width follows the loaded target ABI. *)
       let target = Project.target proj in
         Vsa.set_addr_bits (Hike.Abi.addr_size_bits target);
       let synth, prog = production_input proj in
       (if String.equal subname "ALL" then
          Term.enum sub_t prog |> Seq.iter ~f:(fun sub -> audit_sub ~synth sub)
        else
          match Seq.find (Term.enum sub_t prog) ~f:(fun s -> String.equal (Sub.name s) subname) with
          | Some sub -> audit_sub ~synth sub
          | None -> Printf.printf "sub '%s' not found\n" subname);
       flush stdout)
