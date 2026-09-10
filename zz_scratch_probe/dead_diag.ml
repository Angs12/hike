(* Diagnoses Dead-classified stack defs (ticket 02): for every
   stack-addressed def, prints the seeding verdict, the rewritten address,
   the tag-state denotation, and the classified kind — the full chain that
   ends in [classify ws = Some Dead] at the emitter's poison arm.  Also
   flags conditional edges whose refinement kills RSP and jumps pruned as
   infeasible by [reachable_jumps].
   Usage: dead_diag.exe <binary> [subname] (default "main"). *)

open Bap.Std
open Probe_common

module Vsa = Cbat_vsa

let ws_summary (ws : Vsa.WordSet.t) : string =
  Printf.sprintf "{bot=%b top=%b circ=%b asc=%b inf=%b}"
    (Vsa.WordSet.is_bottom ws)
    (Vsa.WordSet.is_top ws)
    (Vsa.WordSet.is_circular ws)
    (Vsa.WordSet.is_ascending ws)
    (Vsa.WordSet.is_infinite ws)

let pp_exp e = Format.asprintf "%a" Exp.pp e

let conds_of (blk : blk term) : (Tid.t * exp) list =
  Term.enum jmp_t blk
  |> Seq.map ~f:(fun j -> (Term.tid j, Jmp.cond j))
  |> Seq.to_list

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  init ();
  match args with
  | [] -> usage Sys.argv.(0) "<binary> [subname]"
  | path :: rest ->
    let proj = load_project path in
    let prog = Project.program proj in
    let sp = sp_of proj in
    let name = match rest with n :: _ -> n | [] -> "main" in
    let sub =
      match find_sub prog name with
      | Some s -> s
      | None -> usage Sys.argv.(0) (Printf.sprintf "%s not found" name)
    in
    let prog' = Program.create ~subs:[ sub ] () in
    let sol = Vsa.static_graph_vsa [] prog' sub (Vsa.init_sol sub) in
    Printf.printf "sp = %s\n" (Var.name sp);
    let entry =
      match Term.enum blk_t sub |> Seq.next with
      | Some (b, _) -> Term.tid b
      | None -> usage Sys.argv.(0) "sub has no blocks"
    in
    Printf.printf "ENTRY %s sp_ws=%s\n" (Tid.to_string entry)
      (ws_summary (Vsa.AI.find_word 64 (Graphlib.Std.Solution.get sol entry) sp));
    let blocks = Term.enum blk_t sub |> Seq.to_list in
    (* Per conditional edge: RSP before/after the taken-refinement, and
       whether [reachable_jumps] prunes the jump. *)
    Base.List.iter blocks ~f:(fun blk ->
        let st_blk = Graphlib.Std.Solution.get sol (Term.tid blk) in
        let before = Vsa.AI.find_word 64 st_blk sp in
        Base.List.iter (conds_of blk) ~f:(fun (jt, cond) ->
            let j = Term.find_exn jmp_t blk jt in
              let st_after = Vsa.Test_seam.assume_jump_cond st_blk j in
              let after = Vsa.AI.find_word 64 st_after sp in
              if Vsa.WordSet.is_bottom after && not (Vsa.WordSet.is_bottom before)
              then
                Printf.printf "EDGE-KILLS-RSP blk=%s jmp=%s  %s -> %s\n"
                  (Tid.to_string (Term.tid blk)) (Tid.to_string jt)
                  (ws_summary before) (ws_summary after);
              let kept =
                Vsa.Test_seam.reachable_jumps st_blk (Seq.return j)
                |> Seq.to_list in
              if kept = [] then
                Printf.printf "PRUNED blk=%s jmp=%s sp_ws=%s cond_ws=%s kind=%s cond=%s\n"
                  (Tid.to_string (Term.tid blk)) (Tid.to_string jt)
                  (ws_summary before)
                  (ws_summary
                     (match Vsa.Test_seam.denote_imm_exp cond st_blk with
                      | Ok w -> w
                      | Error _ -> Vsa.WordSet.bottom 1))
                  (match Vsa.Test_seam.denote_imm_exp cond st_blk with
                   | Ok w ->
                     (match Vsa.Cbat_extraction.classify w with
                      | Some k -> vsa_kind_to_string k
                      | None -> "none")
                   | Error _ -> "error")
                  (pp_exp cond)));
    (* Per stack-addressed def: the full Dead chain. *)
    Base.List.iter blocks ~f:(fun blk ->
        let st_blk = Graphlib.Std.Solution.get sol (Term.tid blk) in
        let sp_ws = Vsa.AI.find_word 64 st_blk sp in
        (* RSP defs: state before/after, and the after-kind. *)
        let _, rsp_trace =
          Base.List.fold (Term.enum def_t blk |> Seq.to_list)
            ~init:(st_blk, [])
            ~f:(fun (st, acc) d ->
                let b4 = Vsa.AI.find_word 64 st sp in
                let st' = Vsa.Test_seam.denote_def d st in
                let af = Vsa.AI.find_word 64 st' sp in
                let acc =
                  if Var.equal (Def.lhs d) sp && not (Vsa.WordSet.equal b4 af)
                  then
                    let ka =
                      match Vsa.Cbat_extraction.classify af with
                      | Some k -> vsa_kind_to_string k
                      | None -> "none" in
                    (Tid.to_string (Term.tid d), ws_summary b4, ws_summary af, ka)
                    :: acc
                  else acc
                in
                (st', acc))
        in
        Base.List.iter rsp_trace
          ~f:(fun (t, b, a, ka) ->
            Printf.printf "RSP-DEF blk=%s def=%s  %s -> %s  after_kind=%s\n"
              (Tid.to_string (Term.tid blk)) t b a ka);
        Base.List.iter (Term.enum def_t blk |> Seq.to_list) ~f:(fun d ->
            match Vsa.Cbat_extraction.stack_address_of_rhs (Def.rhs d) with
            | None -> ()
            | Some addr ->
              let seeded = Vsa.Cbat_extraction.is_stack_access st_blk addr in
              let st_tag =
                Vsa.Cbat_extraction.st_tag_of ~tags:sol blk addr st_blk in
              let ws_tag = Vsa.Test_seam.denote_imm_exp addr st_tag in
              let ws_plain = Vsa.Test_seam.denote_imm_exp addr st_blk in
              (* The tag universe is the denotation's offset-space twin. *)
              let kind =
                match ws_tag with
                | Ok ws ->
                  (match Vsa.Cbat_extraction.classify
                           (Option.value ~default:ws (Ws.relativize ws)) with
                   | Some k -> vsa_kind_to_string k
                   | None -> "none")
                | Error _ -> "denote-error"
              in
              Printf.printf
                "DEF blk=%s %s  lhs=%s\n  rhs   = %s\n  addr = %s\n  \
                 seeded=%b sp_ws=%s\n  plain=%s; tag=%s; kind=%s\n"
                (Tid.to_string (Term.tid blk))
                (Tid.to_string (Term.tid d))
                (Var.name (Def.lhs d))
                (pp_exp (Def.rhs d))
                (pp_exp addr)
                seeded (ws_summary sp_ws)
                (match ws_plain with Ok w -> ws_summary w | Error _ -> "error")
                (match ws_tag with Ok w -> ws_summary w | Error _ -> "error")
                kind))
