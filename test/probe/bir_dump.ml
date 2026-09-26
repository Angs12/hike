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
  | Some sub0 ->
    let sub =
      let envs, sub', _ =
        Hike.Vsa.fixpoint (Project.target proj)
          ~lookup:(fun _ -> None) ~images:[]
          ~written:(Hike.Vsa.kill_summaries ~abi:Hike.Abi.x86_64_sysv
                      (Program.create ~subs:[ sub0 ] ()))
          ~lift_at:(fun _ ~block_addrs:_ -> None)
          ~block_addrs:(Core.Map.empty (module Addr)) sub0
      in
      ignore envs;
      sub'
    in
    let solved = sub in
    (* The emitter input: the split runs after the attribution. *)
    let split = Hike.Split_blocks.split_sub solved in
    let names regs = Base.List.map regs ~f:Var.name |> String.concat "," in
    Printf.printf "bap-free before: [%s]\n"
      (names (Sub.free_vars solved |> Core.Set.to_list));
    Printf.printf "bap-free after:  [%s]\n"
      (names (Sub.free_vars split |> Core.Set.to_list));
    Printf.printf "regs before: [%s]\n"
      (names (Hike.Split_blocks.free_regs solved));
    Printf.printf "regs after:  [%s]\n"
      (names (Hike.Split_blocks.free_regs split));
    let sub = split in
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
          Term.enum jmp_t blk
          |> Seq.map ~f:(fun j ->
              let tgt =
                match Jmp.kind j with
                | Goto l -> (
                    match l with
                    | Direct tid -> Tid.name tid
                    | Indirect _ -> "indirect")
                | _ -> "non-goto"
              in
              let cond =
                if
                  Hike.Stack_model.is_true_cond (Jmp.cond j)
                then "true-cond"
                else "guarded"
              in
              (blk, Printf.sprintf "jmp %s -> %s" cond tgt)))
      |> Seq.to_list in
    Base.List.iter jms ~f:(fun (blk, s) ->
        Printf.printf "  [%s] %s\n" (Tid.name (Term.tid blk)) s);
    Printf.printf "blocks: %d\n"
      (Term.enum blk_t sub |> Seq.to_list |> Base.List.length);
    Printf.printf "blocks-with-jumps: %d\n" (Base.List.length jms)
