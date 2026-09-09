(* Finds ill-typed defs: lhs var width vs rhs inferred width mismatches —
   the root of the emitter's phi type crashes (ticket 02 follow-up).
   Usage: width_diag.exe <binary> [subname] (default "main"). *)

open Bap.Std
open Probe_common

let rhs_width (e : Bil.exp) : int =
  match Type.infer e with
  | Ok (Type.Imm n) -> n
  | _ -> 0

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  init ();
  match args with
  | [] -> usage Sys.argv.(0) "<binary> [subname]"
  | path :: rest ->
    let proj = load_project path in
    let prog = Project.program proj in
    let name = match rest with n :: _ -> n | [] -> "main" in
    let sub =
      match find_sub prog name with
      | Some s -> s
      | None -> usage Sys.argv.(0) (Printf.sprintf "%s not found" name)
    in
    Term.enum blk_t sub
    |> Seq.iter ~f:(fun blk ->
        Term.enum def_t blk
        |> Seq.iter ~f:(fun d ->
            let lw =
              match Var.typ (Def.lhs d) with
              | Type.Imm n -> n
              | _ -> 0
            in
            let rw = rhs_width (Def.rhs d) in
            if rw <> 0 && lw <> 0 && rw <> lw then
              Printf.printf "MISMATCH blk=%s def=%s lhs=%s:%d rhs=%dbit\n  \
                 rhs = %s\n"
                (Tid.to_string (Term.tid blk))
                (Tid.to_string (Term.tid d))
                (Var.name (Def.lhs d)) lw rw
                (Format.asprintf "%a" Exp.pp (Def.rhs d))))
