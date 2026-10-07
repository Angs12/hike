open Bap.Std
open Bap_core_theory
open Hike_test.Harness

(* A minimal x86-64 ELF avoids a compiler or external corpus dependency. *)
let with_binary code f =
  let names = "\000.text\000.shstrtab\000" in
  let names_off = 120 + String.length code in
  let sections_off = names_off + String.length names in
  let bytes = Bytes.make (sections_off + 3 * 64) '\000' in
  let put off size value =
    for i = 0 to size - 1 do
      Bytes.set bytes (off + i)
        (Char.chr (Int64.to_int (Int64.logand
          (Int64.shift_right_logical value (8 * i)) 255L)))
    done in
  Bytes.blit_string "\x7fELF\x02\x01\x01" 0 bytes 0 7;
  put 16 2 2L; put 18 2 62L; put 20 4 1L;
  put 24 8 0x400078L; put 32 8 64L;
  put 40 8 (Int64.of_int sections_off); put 60 2 3L; put 62 2 2L;
  put 52 2 64L; put 54 2 56L; put 56 2 1L; put 58 2 64L;
  put 64 4 1L; put 68 4 5L;
  put 80 8 0x400000L; put 88 8 0x400000L;
  put 96 8 (Int64.of_int (Bytes.length bytes));
  put 104 8 (Int64.of_int (Bytes.length bytes)); put 112 8 4096L;
  Bytes.blit_string code 0 bytes 120 (String.length code);
  Bytes.blit_string names 0 bytes names_off (String.length names);
  let text = sections_off + 64 in
  put text 4 1L; put (text + 4) 4 1L; put (text + 8) 8 6L;
  put (text + 16) 8 0x400078L; put (text + 24) 8 120L;
  put (text + 32) 8 (Int64.of_int (String.length code));
  put (text + 48) 8 1L;
  let strings = sections_off + 128 in
  put strings 4 7L; put (strings + 4) 4 3L;
  put (strings + 24) 8 (Int64.of_int names_off);
  put (strings + 32) 8 (Int64.of_int (String.length names));
  put (strings + 48) 8 1L;
  let file = Filename.temp_file "hike-drive" ".elf" in
  Fun.protect ~finally:(fun () -> Sys.remove file) (fun () ->
      let out = open_out_bin file in
      output_bytes out bytes;
      close_out out;
      match Project.create (Project.Input.load ~loader:"llvm" file) with
      | Ok project -> f project
      | Error error -> failwith (Core.Error.to_string_hum error))

let tests = [
  pin "DRIVE-01" "discovery returns raw BIR without installing final analysis facts"
    (fun () ->
      with_binary "\xb8\x2a\x00\x00\x00\xc3" (fun project ->
          let before = Hike.Kb.facts_opt () in
          let program = Hike.Drive.run project in
          check "decoded sub survives" (Term.length sub_t program > 0);
          check "final analysis remains owned by VSA" (Hike.Kb.facts_opt () == before);
          let defs = Term.enum sub_t program |> Seq.concat_map ~f:(Term.enum blk_t)
                     |> Seq.concat_map ~f:(Term.enum def_t) in
          check "analysis stamps do not escape the discovery copy"
            (Seq.for_all defs ~f:(fun d -> Option.is_none (Hike.Vsa.Def_origin.def_origin d)))));
  pin "DRIVE-02" "discovery preserves conditional CFG and original terms for later passes"
    (fun () ->
      with_binary "\x85\xff\x74\x06\xb8\x2a\x00\x00\x00\xc3\x31\xc0\xc3"
        (fun project ->
          let program = Hike.Drive.run project in
          let sub = Base.Option.value_exn (Term.first sub_t program) in
          check "both branch arms survive" (Term.length blk_t sub >= 3);
          check "raw flag condition survives for the jump pass"
            (Term.enum blk_t sub |> Seq.concat_map ~f:(Term.enum jmp_t)
             |> Seq.exists ~f:(fun j -> not (Core.Set.is_empty (Exp.free_vars (Jmp.cond j)))))));
  pin "DRIVE-03" "resolved indirect jumps stay blocks of their owning function"
    (fun () ->
      (* lea rax,[rip+2]; jmp rax; mov eax,42; ret *)
      with_binary "\x48\x8d\x05\x02\x00\x00\x00\xff\xe0\xb8\x2a\x00\x00\x00\xc3"
        (fun project ->
          let program = Hike.Drive.run project in
          check "jump destination is not a function entry"
            (Term.length sub_t program = 1);
          let sub = Base.Option.value_exn (Term.first sub_t program) in
          check "jump destination is decoded in its owner"
            (Term.enum blk_t sub |> Seq.exists ~f:(fun b ->
                 match Term.get_attr b address with
                 | Some a -> Word.to_int64_exn a = 0x400081L
                 | None -> false))));
  pin "DRIVE-04" "BAP classifies resolved indirect call destinations as functions"
    (fun () ->
      (* lea rax,[rip+3]; call rax; ret; mov eax,42; ret *)
      with_binary "\x48\x8d\x05\x03\x00\x00\x00\xff\xd0\xc3\xb8\x2a\x00\x00\x00\xc3"
        (fun project ->
          let program = Hike.Drive.run project in
          check "call destination becomes a separate function"
            (Term.enum sub_t program |> Seq.exists ~f:(fun sub ->
                 match Term.get_attr sub address with
                 | Some a -> Word.to_int64_exn a = 0x400082L
                 | None -> false))))
]

let () = run "drive" tests
