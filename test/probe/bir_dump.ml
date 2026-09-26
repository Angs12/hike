(* The lifted BIR def dump: one line per def of a named sub, with the
   name, width, and rhs.  Usage: bir_dump.exe <binary> <sub-name> *)
open Bap.Std
open Probe_common

let () =
  init ();
  let bin = Sys.argv.(1) in
  let name = Sys.argv.(2) in
  let proj = load_project bin in
  let prog = Project.program proj in
  match find_sub prog name with
  | None -> Printf.eprintf "no sub %s\n%!" name
  | Some sub ->
    Term.enum blk_t sub
    |> Seq.iter ~f:(fun blk ->
        Printf.printf "block %s:\n" (Tid.name (Term.tid blk));
        Term.enum def_t blk
        |> Seq.iter ~f:(fun d ->
            let lhs = Var.name (Def.lhs d) in
            let w =
              match Var.typ (Def.lhs d) with
              | Type.Imm n -> string_of_int n
              | _ -> "?" in
            let rhs =
              let bs = Buffer.create 200 in
              let fmt = Format.formatter_of_buffer bs in
              Format.pp_set_margin fmt 1_000_000;
              Format.fprintf fmt "%a" Exp.pp (Def.rhs d);
              Format.pp_print_flush fmt ();
              Buffer.contents bs in
            Printf.printf "  %s:%s := %s\n" lhs w rhs));
    let jms =
      Term.enum blk_t sub
      |> Seq.concat_map ~f:(fun blk ->
          Term.enum jmp_t blk |> Seq.map ~f:(fun _ -> blk))
      |> Seq.to_list in
    Printf.printf "blocks-with-jumps: %d\n" (Base.List.length jms)
