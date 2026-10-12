open Bap.Std
open Bap_core_theory
open Hike_test.Harness

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
                 | None -> false))));
  pin "DRIVE-05" "BAP carries the decoded atomic operation and captures inputs before it"
    (fun () ->
      with_binary "\xf0\x48\x01\x37\xc3" (fun project ->
          let program = Hike.Drive.run project in
          let targets = Term.enum sub_t program
            |> Seq.concat_map ~f:(Term.enum blk_t)
            |> Seq.concat_map ~f:(Term.enum jmp_t)
            |> Seq.filter_map ~f:(fun j -> match Jmp.kind j with
                 | Call c -> (match Call.target c with Direct t -> Some (Tid.name t) | _ -> None)
                 | _ -> None) |> Seq.to_list in
          check "explicit atomic add reaches BIR"
            (Base.List.exists targets ~f:(fun n -> String.equal (Hike.Abi.strip_at n) "intrinsic:x86:atomic_add_64"));
          check "generic lock markers are absent"
            (not (Base.List.exists targets ~f:Hike.Abi.is_lock_marker))))
]

let () = run "drive" tests
