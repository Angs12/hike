(* Prints, for each block of a sub that ends in an indirect goto, the
   block's defs with the value each left-hand side takes after the def.
   Usage: indirect_state.exe <binary> <subname> *)

open Bap.Std
open Probe_common

module AI = Cbat_vsa.AI
module Vsa = Cbat_vsa

let usage_text = "<binary> <subname>"

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  init ();
  match args with
  | [ path; subname ] ->
    let proj = load_project path in
    let target = Project.target proj in
    let synth, prog = production_input proj in
    let sub =
      match find_sub prog subname with
      | Some s -> s
      | None -> usage Sys.argv.(0) usage_text
    in
    Vsa.set_addr_bits (Hike.Abi.addr_size_bits target);
    let abi = Hike.Abi.of_target target in
    let callee = callee_of ~synth prog in
    let sol =
      Vsa.with_images (section_images proj) (fun () ->
          static_graph_vsa ~synth ~abi ~callee ~sub_lookup:(fun _ -> None) sub
            (Vsa.init_sol ~abi sub))
    in
    Term.enum blk_t sub
    |> Seq.iter ~f:(fun b ->
        let indirect =
          Term.enum jmp_t b
          |> Seq.exists ~f:(fun j ->
              match Jmp.kind j with
              | Goto (Indirect _) -> true
              | Call c -> (match Call.target c with Indirect _ -> true | _ -> false)
              | _ -> false)
        in
        if indirect then begin
          Printf.printf "=== block %s ===\n" (Tid.name (Term.tid b));
          let pre = Graphlib.Std.Solution.get sol (Term.tid b) in
          let (), _ =
            Vsa.fold_block_states ~synth ~sol b ~init:() ~f:(fun _ after d () ->
                Printf.printf "  %s\n      -> %s\n" (def_to_string d)
                  (ws_to_string (AI.find_word 64 after (Var.base (Def.lhs d)))))
          in
          Printf.printf "  entry state: %s\n"
            (state_summary (lhs_vars_of sub |> List.filter (fun v -> List.mem (Var.name v) ["RAX";"RDI";"RSI";"RCX"])) pre);
          Term.enum jmp_t b
          |> Seq.iter ~f:(fun j -> Printf.printf "  %s\n" (jmp_to_string j))
        end)
  | _ -> usage Sys.argv.(0) usage_text
