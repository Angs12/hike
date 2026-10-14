(* The program producer (ADR 0032).  On a project loaded without BAP's
   disassembly, Hike's decoder is the sole decoder: the initial decode,
   BAP's subroutine partition and the symbol table are computed here
   from the project's memory and image facts, so it discovers the same
   program as a project loaded with them. *)

open Bap.Std
open Bap_core_theory
module Kb = Bap_core_theory.KB

type result = {
  program : program term;
  facts : Hike_kb.facts;
  symtab : Symtab.t;
}

(* The unit facts BAP's project creation provides only while it
   disassembles: the decoder reads the target, and the loader's
   promises read the specification, bias and memory, through the
   unit. *)
let provide_unit (proj : Project.t) ~(file : string) : unit =
  let spec = Project.specification proj in
  let target = Project.target proj in
  let width = Theory.Target.code_addr_size target in
  let bias =
    match Ogre.eval (Ogre.request Image.Scheme.bias) spec with
    | Ok bias -> Core.Option.map bias ~f:(fun x -> Bitvec.(int64 x mod modulus width))
    | Error err ->
      Core.invalid_argf "malformed ogre specification: %s" (Core.Error.to_string_hum err) ()
  in
  let out : unit Toplevel.var = Toplevel.var "hike-drive-unit" in
  Toplevel.put out
    (let open Kb.Syntax in
     Theory.Unit.for_file file >>= fun unit ->
     Kb.sequence [
       Kb.provide Image.Spec.slot unit spec;
       Kb.provide Theory.Unit.bias unit bias;
       Kb.provide Theory.Unit.target unit target;
       Kb.provide Theory.Unit.path unit (Some file);
       Kb.provide Project.memory_slot unit (Project.memory proj);
     ]);
  Toplevel.get out

let load ?(loader = "llvm") (path : string) : Project.t Core.Or_error.t =
  let empty = Project.state (Project.empty Theory.Target.unknown) in
  Core.Or_error.bind
    (Project.create ~package:path ~state:empty (Project.Input.load ~loader path))
    ~f:(fun proj ->
        Core.Or_error.try_with (fun () ->
            provide_unit proj ~file:(Hike_decode.file_of proj);
            proj))

(* The initial decode and its symbol table: BAP's own when the project
   was created with its disassembly, else the same scan and partition
   computed here. *)
let source (proj : Project.t) ~(file : string) : Disasm.Driver.state * Symtab.t =
  let state = Project.State.disassembly (Project.state proj) in
  if Core.Set.is_empty (Disasm.Driver.subroutines state) then
    let state = Hike_decode.scan proj ~file ~roots:[] in
    (state, Hike_decode.symtab ~file state)
  else (state, Project.symbols proj)

let run (proj : Project.t) : result =
  let file = Hike_decode.file_of proj in
  let state, symtab = source proj ~file in
  let subroutines =
    Symtab.to_sequence symtab
    |> Seq.map ~f:(fun (_, entry, _) -> Word.to_int64_exn (Block.addr entry))
    |> Seq.to_list
  in
  let { Hike_worklist.program; facts } =
    Hike_worklist.run proj ~file ~state ~subroutines
  in
  { program; facts; symtab }
