(* Dumps per-def audit data for PROD-Unbounded stack accesses.
   Usage: audit02.exe <binary> [subname] (default "main", "ALL" scans all). *)

open Bap.Std
open Bap_core_theory
open Probe_common

(* Replica rule (pinned — owner decision keeps this probe): the walk below
   replicates production's offsets_of_sub per-def logic; a PROD-vs-replica
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

let dump_frame (label : string) (st : AI.t) : unit =
  match AI.frame_of st with
  | None -> Printf.printf "      %s: frame=BOTTOM\n" label
  | Some f ->
    if List.is_empty f then Printf.printf "      %s: frame=[]\n" label
    else
      List.iter (fun (v, (t : AI.frame_term)) ->
          let open AI in
          let fvstr =
            String.concat ","
              (List.map (fun (fv, k) -> Printf.sprintf "%s*%d" (Var.name fv) k) t.fvars) in
          Printf.printf "      %s: %s -> %s fvars=[%s]\n"
            label (Var.name v) (ws_str t.fconst) fvstr) f

(* Walks the sub like offsets_of_sub; `on_unbounded` compares replica vs production. *)
let audit_sub (sp : var) (sub : sub term) : unit =
  Printf.printf "  raw defs: %d\n"
    (Term.enum blk_t sub |> Seq.concat_map ~f:(Term.enum def_t) |> Seq.length);
  (* PROD verdict for cross-checking the replica. *)
  let info = Hike.Vsa.offsets_of_sub Theory.Target.unknown sp sub in
  let prod_unbounded : (Tid.t, unit) Hashtbl.t = Hashtbl.create 16 in
  Core.Map.iteri info.offsets ~f:(fun ~key:tid ~data:k ->
      match k with
      | Hike.Convutils.Unbounded -> Hashtbl.add prod_unbounded tid ()
      | _ -> ());
  let prod_unbounded_count = Hashtbl.length prod_unbounded in
  let stack_count = Core.Map.length info.Hike.Convutils.offsets in
  Printf.printf "=== sub %s (%s) — stack=%d offsets=%d Unbounded(PROD)=%d ===\n"
    (Sub.name sub) (Tid.to_string (Term.tid sub))
    stack_count (Core.Map.length info.offsets) prod_unbounded_count;
  if stack_count = 0 then ()
  else begin
    let prog' = Program.create ~subs:[ sub ] () in
    let sol = Vsa.static_graph_vsa [] prog' sub (Vsa.init_sol sub) in
    let tags = sol in
    ignore tags;
    Term.enum blk_t sub
    |> Seq.iter ~f:(fun blk ->
        let defs = Term.enum def_t blk |> Seq.to_list in
        let _ =
          Base.List.fold_left defs
            ~init:(Graphlib.Std.Solution.get tags (Term.tid blk))
            ~f:(fun st d ->
                 let st_before = st in
                 let st_after = Vsa.denote_def d st in
                 (match Def.rhs d with
                  | Bil.Load (_, addr, _, _) | Bil.Store (_, addr, _, _, _)
                  | Bil.Cast (_, _, Bil.Load (_, addr, _, _))
                  | Bil.Cast (_, _, Bil.Store (_, addr, _, _, _))
                    when Core.Map.mem info.Hike.Convutils.offsets (Term.tid d) ->
                      let is_prod_ub = Hashtbl.mem prod_unbounded (Term.tid d) in
                      if is_prod_ub then begin
                        let frame = Vsa.frame_of_state st_before in
                        let addr' = Vsa.rewrite_addr frame addr in
                        let st_tag =
                          Exp.free_vars addr'
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
                        let ws_before = Vsa.denote_imm_exp addr' st_before in
                        let ws_tag = Vsa.denote_imm_exp addr' st_tag in
                        Printf.printf "  DEF %s (blk %s): %s\n"
                          (Tid.to_string (Term.tid d))
                          (Tid.to_string (Term.tid blk))
                          (exp_str (Def.rhs d));
                        Printf.printf "    raw addr     : %s\n" (exp_str addr);
                        Printf.printf "    rewrite_addr : %s\n" (exp_str addr');
                        (match ws_before with
                         | Ok ws -> Printf.printf "    denote(before): %s\n" (ws_str ws)
                         | Error _ -> Printf.printf "    denote(before): ERROR\n");
                        (match ws_tag with
                         | Ok ws -> Printf.printf "    denote(tag)   : %s\n" (ws_str ws)
                         | Error _ -> Printf.printf "    denote(tag)   : ERROR\n");
                        Exp.free_vars addr' |> Core.Set.iter ~f:(fun v ->
                            match Var.typ v with
                            | Type.Imm w ->
                              let cur = AI.find_word w st_before v in
                              let tag_v = AI.find_word w
                                  (Graphlib.Std.Solution.get tags (Term.tid blk)) v in
                              Printf.printf "    free var %s: cur(before)=%s tag=%s\n"
                                (Var.name v) (ws_str cur) (ws_str tag_v)
                            | _ -> ());
                        (* Classify the failure from the four candidates. *)
                        let diag =
                          let addr_unchanged = Exp.equal addr addr' in
                          match ws_before, ws_tag with
                          | Ok ws, _ when Ws.is_top ws && addr_unchanged ->
                            "candidate 1: rewrite_addr returned addr unchanged AND value is TOP"
                          | Ok ws, _ when Ws.is_top ws ->
                            Printf.sprintf "candidate 2: denote_imm_exp returned TOP (rewrite DID change addr to %s)"
                              (exp_str addr')
                          | Error _, _ -> "candidate 3: denote_imm_exp returned Error (val_as_imm failure)"
                          | Ok _, Ok _ ->
                            (match ws_before, ws_tag with
                             | Ok b, Ok t when not (Ws.equal b t) ->
                               "candidate 4: partitioned tag value differs from sequential (free-var divergence)"
                             | _ ->
                               (match ws_before with
                                | Ok ws ->
                                  Printf.sprintf "unclassified: ws=%s addr_unchanged=%b"
                                    (ws_str ws) addr_unchanged
                                | _ -> "unclassified: unknown"))
                          | _ -> "unclassified: unknown" in
                        Printf.printf "    DIAGNOSIS: %s\n" diag
                      end
                    | _ -> ());
                   st_after) in
          ())
  end

let () =
  let paths = Array.to_list Sys.argv |> List.tl in
  match paths with
  | [] -> Printf.printf "usage: %s <binary> [subname]\n" Sys.argv.(0); exit 0
  | binary :: rest ->
    init ();
    let subname = match rest with hd :: _ -> hd | [] -> "main" in
    (match Project.create (Project.Input.file ~loader:"llvm" ~filename:binary) with
     | Error e ->
       Printf.printf "LOAD-FAIL %s: %s\n" binary (Core_kernel.Error.to_string_hum e); exit 1
     | Ok proj ->
       let sp = sp_of proj in
       (* One set: Hike.Vsa.set_addr_bits is the same cell (Hike_vsa pass-through). *)
       Vsa.set_addr_bits 64;
       let prog = Project.program proj in
       (if String.equal subname "ALL" then
          Term.enum sub_t prog |> Seq.iter ~f:(fun sub -> audit_sub sp sub)
        else
          match Seq.find (Term.enum sub_t prog) ~f:(fun s -> String.equal (Sub.name s) subname) with
          | Some sub -> audit_sub sp sub
          | None -> Printf.printf "sub '%s' not found\n" subname);
       flush stdout)
