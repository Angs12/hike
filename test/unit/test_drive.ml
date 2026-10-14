(* Drive pins (ADR 0032): discovery over the decoder's own scan, on a
   project loaded without BAP's disassembly and on one loaded with it.
   Fixtures are hand-assembled binaries (code at 0x400078, the entry). *)

open Bap.Std
open Hike_test.Harness

let sole = Hike.Drive.load

(* A sub's address, name and block addresses. *)
let shape (prog : program term) =
  Term.enum sub_t prog |> Seq.to_list
  |> List.map (fun s ->
      ( Term.get_attr s address,
        Sub.name s,
        Term.enum blk_t s |> Seq.filter_map ~f:(fun b -> Term.get_attr b address)
        |> Seq.to_list ))

let symbols (symtab : Symtab.t) =
  Symtab.to_sequence symtab |> Seq.to_list
  |> List.map (fun (name, entry, _) -> (name, Block.addr entry))

(* call f; call g; ret; f: test edi,edi; je L; call g; L: ret; g: lea
   rax,[rip+2]; jmp rax; mov eax,42; ret *)
let calls_and_dispatch =
  "\xe8\x06\x00\x00\x00\xe8\x0a\x00\x00\x00\xc3\x85\xff\x74\x05\xe8\x01\x00\x00\x00\xc3\
   \x48\x8d\x05\x02\x00\x00\x00\xff\xe0\xb8\x2a\x00\x00\x00\xc3"

let tests = [
  pin "DRIVE-01" "a project loaded without BAP's disassembly discovers its program and facts"
    (fun () ->
      with_binary ~load:sole calls_and_dispatch (fun proj ->
          check "DRIVE-01.no-backend" (Term.length sub_t (Project.program proj) = 0);
          let result = Hike.Drive.run proj in
          check "DRIVE-01.program" (List.length (shape result.program) >= 3);
          check "DRIVE-01.facts" (not (Core.Map.is_empty result.facts.envs));
          check "DRIVE-01.symtab" (symbols result.symtab <> [])));

  pin "DRIVE-02" "discovery is the same with and without BAP's disassembly" (fun () ->
      let discover load =
        with_binary ~load calls_and_dispatch (fun proj ->
            let result = Hike.Drive.run proj in
            (shape result.program, symbols result.symtab))
      in
      let program, symtab = discover sole in
      let program', symtab' =
        discover (fun file -> Project.create (Project.Input.load ~loader:"llvm" file)) in
      check "DRIVE-02.program" (program = program');
      check "DRIVE-02.symtab" (symtab = symtab'));

  pin "DRIVE-03" "a fresh scan's symbol table is the one BAP's disassembly builds" (fun () ->
      with_binary calls_and_dispatch (fun proj ->
          let file = Hike.Decode.file_of proj in
          let state = Hike.Decode.scan proj ~file ~roots:[] in
          check "DRIVE-03"
            (symbols (Hike.Decode.symtab ~file state) = symbols (Project.symbols proj))));
]

let () = run "drive" tests
