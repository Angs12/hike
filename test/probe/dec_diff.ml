(* The decode-context diff: prints, for one instruction address, the
   insn (name, asm, operands) and the BIL from the primary project lift
   and from a fresh Disasm_expert.Recursive.run — the re-lift seam's
   decode.  Probe-only forensics for the decode-context class. *)

open Bap.Std
open Bap_core_theory
open Probe_common

let addr_of_string s = Addr.of_int64 (Int64.of_string ("0x" ^ s))

let dump_sema what addr (sema : insn) =
  Printf.printf "%s @%Lx\n" what (Word.to_int64_exn addr);
  Printf.printf "  name: %s\n" (Insn.name sema);
  Printf.printf "  asm: %s\n" (Insn.asm sema);
  Array.iteri
    (fun i (op : Op.t) ->
      let kind =
        match op with
        | Op.Reg r -> "reg:" ^ Reg.name r
        | Op.Imm x -> Printf.sprintf "imm:%Ld" (Imm.to_int64 x)
        | Op.Fmm _ -> "fmm"
      in
      Printf.printf "  op[%d] %s\n" i kind)
    (Insn.ops sema);
  Format.printf "  bil: %a@\n" Bil.pp (Insn.bil sema)

let find_insn cfg a =
  let found = ref None in
  Graphs.Cfg.nodes cfg
  |> Seq.iter ~f:(fun b ->
         Base.List.iter (Block.insns b) ~f:(fun (mem, insn) ->
                if Addr.equal (Memory.min_addr mem) a then
                  found := Some (mem, insn)));
  !found

let () =
  init ();
  let bin = Sys.argv.(1) in
  let a = addr_of_string Sys.argv.(2) in
  let proj = load_project bin in
  (* The primary lift's insn, out of the project's own disassembly. *)
  let disasm = Project.disasm proj in
  (match find_insn (Disasm.cfg disasm) a with
   | None -> Printf.printf "primary: no insn at that address\n"
   | Some (_, sema) -> dump_sema "PRIMARY" a sema);
  (* The seam's decode: Recursive.run over a view from that address. *)
  let seg =
    match Seq.to_list (Memmap.lookup (Project.memory proj) a) with
    | [] -> failwith "no segment"
    | (seg, _) :: _ -> seg
  in
  let view = Memory.view_exn seg in
  let module KB = Bap_knowledge.Knowledge in
  (* The region unit's target: the same claim the primary lift's loader
     makes for its own units.  [Unit.for_region] interns per bounds, so
     this is the unit the recursive run's rule hands to every label in
     the view; with the target known, the semantics reify through the
     desugared theory (the alias-expanded register forms). *)
  let seam_run view =
    let open KB.Syntax in
    let lower = Word.to_bitvec (Memory.min_addr view)
    and upper = Word.to_bitvec (Memory.max_addr view) in
    let run : unit Toplevel.var = Toplevel.var "dec-diff-seam" in
    Toplevel.put run
      (Theory.Unit.for_region ~lower ~upper >>= fun unit ->
           KB.provide Theory.Unit.target unit (Project.target proj)
           >>= fun () ->
           KB.provide Image.Spec.slot unit
             (Project.specification proj));
    Disasm_expert.Recursive.run (Project.arch proj) view
  in
  match seam_run view with
  | Error e ->
    Printf.printf "recursive failed: %s\n" (Core.Error.to_string_hum e)
  | Ok rec_t -> (
    match find_insn (Disasm_expert.Recursive.cfg rec_t) a with
    | None -> Printf.printf "seam: no insn at that address\n"
    | Some (_, sema) -> dump_sema "SEAM" a sema)
