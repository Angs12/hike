(* Worklist pins: callee-first discovery over hand-assembled binaries
   (code at 0x400078, the image entry).  Each pin runs the production
   worklist and reads the program it returns. *)

open Bap.Std
open Hike_test.Harness

let at (prog : program term) (a : int64) : sub term option =
  Term.enum sub_t prog
  |> Seq.find ~f:(fun s ->
      Base.Option.equal Addr.equal (Term.get_attr s address) (Some (Addr.of_int64 a)))

let calls (sub : sub term) : Call.t list =
  Term.enum blk_t sub |> Seq.concat_map ~f:(Term.enum jmp_t)
  |> Seq.filter_map ~f:(fun j ->
      if Hike_return.is_jmp j then None
      else match Jmp.kind j with Call c -> Some c | _ -> None)
  |> Seq.to_list

let lift code = with_binary code (fun p -> (Hike.Drive.run ~signatures:Hike.Signatures.empty p).program)

let starts_at a t =
  Base.Option.equal Addr.equal (Term.get_attr t address) (Some (Addr.of_int64 a))

let tests = [
  pin "WL-01" "a call to a callee that never returns keeps no fallthrough" (fun () ->
      (* call g; ret; g: jmp g *)
      let prog = lift "\xe8\x01\x00\x00\x00\xc3\xeb\xfe" in
      check_bound "WL-01" (at prog 0x400078L) (fun s ->
          Term.length blk_t s = 1
          && (match calls s with [ c ] -> Call.return c = None | _ -> false)));

  pin "WL-02" "a recursive cycle is solved to its least fixpoint from the optimistic side"
    (fun () ->
      (* call f; ret; f: test edi,edi; je L; call g; L: ret; g: call f; ret *)
      let prog =
        lift "\xe8\x01\x00\x00\x00\xc3\x85\xff\x74\x05\xe8\x01\x00\x00\x00\xc3\
              \xe8\xf1\xff\xff\xff\xc3" in
      let f = at prog 0x40007eL |> Base.Option.value_exn in
      let g = at prog 0x400088L |> Base.Option.value_exn in
      let check_call caller callee =
        match calls caller with
        | [ call ] ->
          check "recursive call reaches its callee"
            (Call.target call = Direct (Term.tid callee));
          check_bound "recursive call returns within its caller" (Call.return call)
            (function Direct t -> Term.find blk_t caller t <> None | Indirect _ -> false)
        | _ -> Alcotest.fail "expected one call in each recursive function" in
      check_call f g;
      check_call g f);

  pin "WL-03" "a block two functions reach gets one tid per function" (fun () ->
      (* call f; call g; ret; f: jmp L; g: jmp L; L: ret *)
      let prog =
        lift "\xe8\x06\x00\x00\x00\xe8\x03\x00\x00\x00\xc3\xeb\x02\xeb\x00\xc3" in
      let tids =
        Term.enum sub_t prog |> Seq.concat_map ~f:(Term.enum blk_t) |> Seq.to_list
        |> List.concat_map (fun b ->
            Term.tid b :: Seq.to_list (Seq.map (Term.enum def_t b) ~f:Term.tid)) in
      (* Each function's body holds its jump and L's return. *)
      let holds_l a = check_bound "WL-03.both" (at prog a) (fun s -> Term.length blk_t s = 2) in
      holds_l 0x400083L;
      holds_l 0x400085L;
      check "WL-03.unique"
        (List.length (List.sort_uniq Tid.compare tids) = List.length tids));

  pin "WL-04" "main is the address every entry call names" (fun () ->
      let is_main prog a =
        match at prog a with
        | Some s -> Term.has_attr s Hike.Stack_model.main_role
        | None -> false in
      (* mov edi, f; call f; ret; f: ret *)
      let agreed = lift "\xbf\x83\x00\x40\x00\xe8\x01\x00\x00\x00\xc3\xc3" in
      check "WL-04.agreed" (is_main agreed 0x400083L);
      check_bound "WL-04.entry" (at agreed 0x400078L) (fun s ->
          Term.has_attr s Sub.entry_point);
      (* mov edi, f; call f; mov edi, 0x40008c; call f; ret; f: ret *)
      let message = "different main addresses" in
      let program = ref None in
      let err =
        capture_stderr (fun () ->
            program :=
              Some (lift "\xbf\x8d\x00\x40\x00\xe8\x0b\x00\x00\x00\xbf\x8c\x00\x40\x00\
                          \xe8\x01\x00\x00\x00\xc3\xc3")) in
      check "WL-04.diag" (contains_substring err message);
      check_bound "WL-04.none" !program (fun prog ->
          not (Seq.exists (Term.enum sub_t prog) ~f:(fun s ->
              Term.has_attr s Hike.Stack_model.main_role))));

  pin "WL-05" "a recursive call names the function itself, not its entry block" (fun () ->
      (* call f; ret; f: test edi,edi; je L; call f; L: ret *)
      let prog =
        lift "\xe8\x01\x00\x00\x00\xc3\x85\xff\x74\x05\xe8\xf7\xff\xff\xff\xc3" in
      check_bound "WL-05" (at prog 0x40007eL) (fun f ->
          List.exists (fun c -> Call.target c = Direct (Term.tid f)) (calls f)));

  pin "WL-06" "both arms of a conditional survive discovery" (fun () ->
      (* test edi,edi; je +6; mov eax,42; ret; xor eax,eax; ret *)
      let prog = lift "\x85\xff\x74\x06\xb8\x2a\x00\x00\x00\xc3\x31\xc0\xc3" in
      check_bound "WL-06" (at prog 0x400078L) (fun s ->
          let block a = Term.enum blk_t s |> Seq.find_exn ~f:(starts_at a) in
          let entry = block 0x400078L in
          let taken = block 0x400082L and fallthrough = block 0x40007cL in
          let targets = Term.enum jmp_t entry
            |> Seq.filter_map ~f:(fun j -> match Jmp.kind j with
                | Goto (Direct t) -> Some t | _ -> None)
            |> Seq.to_list in
          List.mem (Term.tid taken) targets && List.mem (Term.tid fallthrough) targets));

  pin "WL-07" "a resolved indirect jump's target is a block of its function" (fun () ->
      (* lea rax,[rip+2]; jmp rax; mov eax,42; ret *)
      let prog = lift "\x48\x8d\x05\x02\x00\x00\x00\xff\xe0\xb8\x2a\x00\x00\x00\xc3" in
      check "WL-07.no-function" (at prog 0x400081L = None);
      check_bound "WL-07.block" (at prog 0x400078L) (fun s ->
          Seq.exists (Term.enum blk_t s) ~f:(starts_at 0x400081L)));

  pin "WL-08" "a resolved indirect call's destination is a function" (fun () ->
      (* lea rax,[rip+3]; call rax; ret; mov eax,42; ret *)
      with_binary "\x48\x8d\x05\x03\x00\x00\x00\xff\xd0\xc3\xb8\x2a\x00\x00\x00\xc3"
        (fun project ->
          let result = Hike.Drive.run ~signatures:Hike.Signatures.empty project in
          let caller = at result.program 0x400078L |> Base.Option.value_exn in
          check "destination is a discovered function" (at result.program 0x400082L <> None);
          let direct =
            calls caller
            |> Base.List.filter ~f:(fun c ->
                   match Call.target c with Direct _ -> true | Indirect _ -> false)
          in
          (match direct with
           | [ call ] ->
             check "call retains its return edge" (Call.return call <> None);
             check "direct target is the discovered function"
               (match Call.target call with
                | Direct t ->
                  Base.Option.equal Tid.equal
                    (Base.Option.map (Term.find sub_t result.program t)
                       ~f:Term.tid)
                    (Base.Option.map (at result.program 0x400082L)
                       ~f:Term.tid)
                | Indirect _ -> false)
           | _ -> Alcotest.fail "expected one direct call arm");
          check "indirect fallback retained"
            (Base.List.exists (calls caller) ~f:(fun c ->
                 match Call.target c with Indirect _ -> true | Direct _ -> false))));
  pin "WL-09" "successive decode growth keeps the warm SSA values"
    (fun () ->
      (* eax := 7; jump to add 1; jump to add 1; ret. Each indirect
         transfer reveals the next body only after its own solve. *)
      with_binary ~pie:true
        "\xb8\x07\x00\x00\x00\x48\x8d\x0d\x02\x00\x00\x00\xff\xe1\x83\xc0\x01\
         \x48\x8d\x0d\x02\x00\x00\x00\xff\xe1\x83\xc0\x01\xc3"
        (fun project ->
          let result = Hike.Drive.run ~signatures:Hike.Signatures.empty project in
          let sub = at result.program 0x400078L |> Base.Option.value_exn in
          let block = Term.enum blk_t sub
            |> Seq.find_exn ~f:(starts_at 0x400092L) in
          let r = List.hd result.facts.Hike.Kb.abi.Hike.Abi.return_regs in
          let r = Hike.Stack_model.version_at_end block r in
          check "WL-09 exact value after both additions"
            (match result.facts.Hike.Kb.denote ~blk:block (Bil.Var r) with
             | Ok ws -> Cbat_vsa.WordSet.equal ws
                 (Cbat_vsa.WordSet.singleton (Cbat_word.of_int ~width:64 9))
             | Error _ -> false)));

]

let () = run "worklist" tests
