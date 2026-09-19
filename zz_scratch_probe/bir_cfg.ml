(* Lane diagnostic: dump the disassembler's global CFG (blocks + edges)
   and the per-sub symtab CFGs — the return-edge dig's ground truth.
   Usage: bir_cfg.exe <binary> [name]  (name filters the symtab dump) *)

open Bap.Std
open Probe_common
module Cfg = Graphs.Cfg

let pp_addr = Format.asprintf "%a" Addr.pp_hex

let block_id blk = pp_addr (Block.addr blk)

let dump_insn mem insn =
  Printf.printf "    %s  %s\n" (pp_addr (Memory.min_addr mem))
    (Insn.asm insn)

let dump_cfg title cfg =
  Printf.printf "  %s:\n" title;
  Base.Sequence.iter (Cfg.nodes cfg) ~f:(fun blk ->
      Printf.printf "  blk %s\n" (block_id blk);
      Base.List.iter (Block.insns blk) ~f:(fun (mem, i) -> dump_insn mem i));
  Base.Sequence.iter (Cfg.edges cfg) ~f:(fun e ->
      Printf.printf "  edge %s -[%s]-> %s\n"
        (block_id (Cfg.Edge.src e))
        (match Cfg.Edge.label e with
         | `Fall -> "fall" | `Cond -> "cond" | `Jump -> "jump")
        (block_id (Cfg.Edge.dst e)))

let () =
  init ();
  let path, wanted = match Sys.argv with
    | [| _; path |] -> (path, None)
    | [| _; path; name |] -> (path, Some name)
    | _ -> Printf.printf "usage: bir_cfg.exe <binary> [subname]\n"; exit 0
  in
  let proj = load_project path in
  let dis = Project.disasm proj in
  Printf.printf "=== global cfg (%d insns total)\n"
    (Base.Sequence.length (Disasm.insns dis));
  Base.Sequence.iter (Disasm.insns dis) ~f:(fun (mem, i) -> dump_insn mem i);
  dump_cfg "global" (Disasm.cfg dis);
  let symtab = Project.symbols proj in
  Base.Sequence.iter (Symtab.to_sequence symtab) ~f:(fun (name, entry, cfg) ->
      let show = match wanted with
        | None -> true
        | Some n -> Base.String.is_substring name ~substring:n in
      if show then begin
        Printf.printf "=== sub %s entry %s\n" name (block_id entry);
        dump_cfg ("cfg of " ^ name) cfg
      end)
