(* Diagnoses Dead-classified stack defs: for every
   stack-addressed def, prints the seeding verdict, the rewritten address,
   the tag-state denotation, and the classified kind — the full chain that
   ends in [classify ws = Some Dead] at the emitter's poison arm.  Also
   flags conditional edges whose refinement kills RSP and jumps pruned as
   infeasible by [reachable_jumps].
   Usage: dead_diag.exe <binary> [subname] (default "main"). *)

open Bap.Std
open Probe_common

module Vsa = Cbat_vsa

(* The seeding predicate and the tag-state meet for one address — the
   probes' copies of the extraction's arms. *)
let is_stack_access st addr =
  match Vsa.Test_seam.denote_imm_exp addr st with
  | Error _ -> false
  | Ok ws -> Vsa.WordSet.is_bottom ws || Vsa.WordSet.in_stack_segment ws

let st_tag_of ~(tags : Vsa.vsa_sol) (blk : blk term) (addr : exp)
    (st_before : Vsa.AI.t) : Vsa.AI.t =
  Exp.free_vars addr |> Core.Set.fold ~init:st_before ~f:(fun acc v ->
      match Var.typ v with
      | Type.Imm w ->
        let tag_v = Vsa.AI.find_word w
            (Graphlib.Std.Solution.get tags (Term.tid blk)) v in
        let cur = Vsa.AI.find_word w acc v in
        let mm = Vsa.WordSet.meet cur tag_v in
        if Cbat_word.is_zero (Vsa.WordSet.cardinality mm)
           || Vsa.WordSet.equal mm cur
        then acc
        else Vsa.AI.add_word acc ~key:v ~data:mm
      | Type.Mem _ | Type.Unk -> acc)

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
    let sol = Vsa.static_graph_vsa ~abi:Hike_abi.x86_64_sysv [] prog' sub (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv sub) in
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
              let st_after = Vsa.Test_seam.constrain_edge ~env:st_blk (Jmp.cond j) in
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
                   | Ok w -> vsa_kind_to_string (Vsa.Cbat_extraction.classify w)
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
                    let ka = vsa_kind_to_string (Vsa.Cbat_extraction.classify af) in
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
              let seeded = is_stack_access st_blk addr in
              let st_tag = st_tag_of ~tags:sol blk addr st_blk in
              let ws_tag = Vsa.Test_seam.denote_imm_exp addr st_tag in
              let ws_plain = Vsa.Test_seam.denote_imm_exp addr st_blk in
              (* The tag IS the denotation (T15): classify reads it in
                 place; the kind's positions are absolute. *)
              let kind =
                match ws_tag with
                | Ok ws -> vsa_kind_to_string (Vsa.Cbat_extraction.classify ws)
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
