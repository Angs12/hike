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
  |> Seq.filter_map ~f:(fun j -> match Jmp.kind j with Call c -> Some c | _ -> None)
  |> Seq.to_list

(* Every direct call comes back (a raw [ret] is an indirect one). *)
let returns_after_every_call sub =
  List.for_all (fun c ->
      match Call.target c with Direct _ -> Call.return c <> None | Indirect _ -> true)
    (calls sub)

let lift code = with_binary code Hike.Worklist.run

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
      check_bound "WL-02.f" (at prog 0x40007eL) returns_after_every_call;
      check_bound "WL-02.g" (at prog 0x400088L) returns_after_every_call);

  pin "WL-03" "a block two functions reach gets one tid per function" (fun () ->
      (* call f; call g; ret; f: jmp L; g: jmp L; L: ret *)
      let prog =
        lift "\xe8\x06\x00\x00\x00\xe8\x03\x00\x00\x00\xc3\xeb\x02\xeb\x00\xc3" in
      let blocks =
        Term.enum sub_t prog |> Seq.concat_map ~f:(Term.enum blk_t) |> Seq.to_list in
      let tids =
        List.concat_map (fun b ->
            Term.tid b
            :: (Seq.to_list (Seq.map (Term.enum def_t b) ~f:Term.tid)
                @ Seq.to_list (Seq.map (Term.enum jmp_t b) ~f:Term.tid)))
          blocks in
      let at_l =
        List.filter (fun b -> Term.get_attr b address = Some (Addr.of_int64 0x400087L))
          blocks in
      check "WL-03.both" (List.length at_l >= 2);
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
]

let () = run "worklist" tests
