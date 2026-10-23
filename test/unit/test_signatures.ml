(* Signature pins: the dynamic-linking tables the import versions are read
   from, and the user's S-expression files. *)

open Hike_test.Harness
open Hike_test.Common
module Sg = Hike_signatures
module Img = Hike.Image

(* ---- hand-built dynamic-linking tables ---- *)

let le16 b v =
  Buffer.add_char b (Char.chr (v land 0xff));
  Buffer.add_char b (Char.chr ((v lsr 8) land 0xff))

let le32 b v = le16 b (v land 0xffff); le16 b ((v lsr 16) land 0xffff)

(* A string table: the offset of each string, the table's bytes. *)
let strtab strings =
  let b = Buffer.create 64 in
  Buffer.add_char b '\000';
  let offsets =
    List.map (fun s ->
        let off = Buffer.length b in
        Buffer.add_string b s; Buffer.add_char b '\000'; (s, off)) strings in
  (offsets, Buffer.to_bytes b)

(* A .dynsym of (name offset, section index) rows after the null row. *)
let dynsym rows =
  let b = Buffer.create 128 in
  Buffer.add_string b (String.make 24 '\000');
  List.iter (fun (name, shndx) ->
      le32 b name; Buffer.add_char b '\018'; Buffer.add_char b '\000';
      le16 b shndx; Buffer.add_string b (String.make 16 '\000')) rows;
  Buffer.to_bytes b

let versym indices =
  let b = Buffer.create 32 in
  List.iter (le16 b) (0 :: indices);
  Buffer.to_bytes b

(* A .gnu.version_r: per library file, its (version name, index) auxes,
   chained through the vn_next / vna_next byte offsets. *)
let verneed ~off files =
  let b = Buffer.create 128 in
  let nfiles = List.length files in
  List.iteri (fun i (file, auxes) ->
      let naux = List.length auxes in
      le16 b 1; le16 b naux; le32 b (off file); le32 b 16;
      le32 b (if i = nfiles - 1 then 0 else 16 + (16 * naux));
      List.iteri (fun j (version, index) ->
          le32 b 0; le16 b 0; le16 b index; le32 b (off version);
          le32 b (if j = naux - 1 then 0 else 16)) auxes) files;
  Buffer.to_bytes b

let imports ~symbols ~versions ~files =
  let strings =
    List.map fst symbols
    @ List.concat_map (fun (f, auxes) -> f :: List.map fst auxes) files in
  let offsets, dynstr = strtab strings in
  let off s = List.assoc s offsets in
  Img.imports_of_sections
    ~dynsym:(dynsym (List.map (fun (n, shndx) -> (off n, shndx)) symbols))
    ~dynstr
    ~versym:(versym versions)
    ~verneed:(verneed ~off files)

(* ---- the user's files ---- *)

let parses text = Core.Or_error.is_ok (Sg.of_string text)

let records_of text = Core.Or_error.ok_exn (Sg.of_string text)

let find ?(library = "libc.so.6") ?(version = "GLIBC_2.2.5") db name =
  Sg.find (Sg.create ~target:(x86_target ()) db
              ~imports:(fun _ -> Some (library, version))) name

let tests : unit Alcotest.test list =
  [
    pin "SG-01"
      "imports take the library and version of each symbol's requirement, \
       across several files and auxiliary entries"
      (fun () ->
        let got =
          imports
            ~symbols:[ ("strlen", 0); ("sin", 0); ("memcpy", 0); ("kept", 0) ]
            ~versions:[ 2; 4; 3; 2 ]
            ~files:
              [ ("libc.so.6", [ ("GLIBC_2.2.5", 2); ("GLIBC_2.14", 3) ]);
                ("libm.so.6", [ ("GLIBC_2.2.5", 4) ]) ] in
        check "versions follow the index, not the order"
          (got = [ ("strlen", ("libc.so.6", "GLIBC_2.2.5"));
                   ("sin", ("libm.so.6", "GLIBC_2.2.5"));
                   ("memcpy", ("libc.so.6", "GLIBC_2.14"));
                   ("kept", ("libc.so.6", "GLIBC_2.2.5")) ]));

    pin "SG-02"
      "a defined symbol, an unversioned one and a hidden-bit index are read \
       from the table as the loader reads them"
      (fun () ->
        let got =
          imports
            ~symbols:[ ("local", 11); ("plain", 0); ("hidden", 0);
                       ("global", 0) ]
            ~versions:[ 2; 1; 0x8002; 0 ]
            ~files:[ ("libc.so.6", [ ("GLIBC_2.2.5", 2) ]) ] in
        check "only the undefined, requirement-versioned symbol"
          (got = [ ("hidden", ("libc.so.6", "GLIBC_2.2.5")) ]));

    pin "SG-03" "a table with no version requirements has no imports"
      (fun () ->
        let offsets, dynstr = strtab [ "strlen" ] in
        check "none"
          (Img.imports_of_sections
             ~dynsym:(dynsym [ (List.assoc "strlen" offsets, 0) ])
             ~dynstr ~versym:(versym [ 0 ]) ~verneed:Bytes.empty = []));

    pin "SG-04" "a file is a sequence of entries with comments and defaults"
      (fun () ->
        let db =
          records_of
            {|; the C library
              ((library libc.so.6) (version GLIBC_2.2.5) (symbol memcpy)
               (return Pointer) (returned 0)
               (params (((ty Pointer) (access Write_only) (captured false))
                        ((ty Pointer) (access Read_only) (captured false))
                        ((ty Long))))
               (memory (Argmem May_write)))
              #;((library dropped) (version x) (symbol y) (params ()))
              ((library libc.so.6) (version GLIBC_2.2.5) (symbol printf)
               (return Int) (params (((ty Pointer)))) (variadic true))
              ((library libc.so.6) (version GLIBC_2.2.5) (symbol abort)
               (params ()) (noreturn true) (memory None_))|} in
        let memcpy = Option.get (find db "memcpy")
        and printf = Option.get (find db "printf")
        and abort = Option.get (find db "abort") in
        check "memcpy"
          (memcpy.Sg.returned = Some 0
           && memcpy.Sg.memory = Sg.Argmem Sg.May_write
           && (match memcpy.Sg.params with
               | [ { Sg.access = Sg.Write_only; captured = false; _ };
                   { Sg.access = Sg.Read_only; captured = false; _ };
                   { Sg.ty = Hike_sysv.Scalar Hike_sysv.Long; access = Sg.May_write; captured = true } ] ->
                 true
               | _ -> false));
        check "printf is variadic with a may-write, captured format"
          (printf.Sg.variadic && printf.Sg.return = Some (Hike_sysv.Scalar Hike_sysv.Int));
        check "abort" (abort.Sg.noreturn && abort.Sg.memory = Sg.None_);
        check "the datum-commented entry is gone"
          (find ~library:"dropped" ~version:"x" db "y" = None));

    pin "SG-05" "a malformed file is refused" (fun () ->
        check "a missing symbol" (not (parses "((library l) (version v))"));
        check "an unknown type"
          (not (parses
                  "((library l) (version v) (symbol s) (params (((ty Quad)))))"));
        check "an unknown field"
          (not (parses
                  "((library l) (version v) (symbol s) (params ()) (bogus 1))"));
        check "unbalanced input" (not (parses "((library l) (version v)"));
        check "a stray atom" (not (parses "libc"));
        check "an empty file has no entries" (parses ""));

    pin "SG-06" "a record applies only on the exact library, version and symbol"
      (fun () ->
        let db =
          records_of
            "((library libc.so.6) (version GLIBC_2.2.5) (symbol exit) \
             (params (((ty Int)))) (noreturn true))" in
        check "exact" (find db "exit" <> None);
        check "other version" (find ~version:"GLIBC_2.34" db "exit" = None);
        check "other library" (find ~library:"libm.so.6" db "exit" = None);
        check "other symbol" (find db "_exit" = None);
        check "an unversioned import"
          (Sg.find (Sg.create ~target:(x86_target ()) db ~imports:(fun _ -> None))
             "exit" = None));


    pin "SG-07" "the shipped glibc file loads and describes real functions"
      (fun () ->
        let db = Core.Or_error.ok_exn (Sg.load [ "../../data/glibc.sexp" ]) in
        check "thousands of entries" (Sg.cardinal db > 3000);
        let get ?(library = "libc.so.6") version name =
          match find ~library ~version db name with
          | Some r -> r
          | None -> Alcotest.failf "no entry for %s@%s" name version in
        let strlen = get "GLIBC_2.2.5" "strlen" in
        check "strlen reads its argument only"
          (strlen.Sg.memory = Sg.Argmem Sg.Read_only
           && strlen.Sg.return = Some (Hike_sysv.Scalar Hike_sysv.Long));
        check "memcpy returns its destination"
          ((get "GLIBC_2.14" "memcpy").Sg.returned = Some 0
           && (get "GLIBC_2.2.5" "memcpy").Sg.returned = Some 0);
        check "exit never returns" (get "GLIBC_2.2.5" "exit").Sg.noreturn;
        check "__stack_chk_fail never returns"
          (get "GLIBC_2.4" "__stack_chk_fail").Sg.noreturn;
        check "printf is variadic" (get "GLIBC_2.2.5" "printf").Sg.variadic;
        check "__isoc23_sscanf takes the scanf prototype"
          (get "GLIBC_2.38" "__isoc23_sscanf").Sg.variadic;
        check "sinl takes and returns a long double"
          (let r = get ~library:"libm.so.6" "GLIBC_2.2.5" "sinl" in
           r.Sg.return = Some (Hike_sysv.Scalar (Hike_sysv.Real Hike_sysv.Long_double))
           && List.map (fun p -> p.Sg.ty) r.Sg.params
              = [ Hike_sysv.Scalar (Hike_sysv.Real Hike_sysv.Long_double) ]);
        check "div returns its pair by value, in registers"
          (match (get "GLIBC_2.2.5" "div").Sg.return with
           | Some ty ->
               Hike_sysv.place_return (Some ty)
               = Hike_sysv.Returned_in [ Hike_sysv.Integer_return 0 ]
           | None -> false));

    pin "SG-08"
      "the signatures describe x86-64 System V on GNU/Linux: any other target is refused"
      (fun () ->
        let refused target =
          match Sg.create ~target Sg.empty ~imports:(fun _ -> None) with
          | exception Failure msg ->
              Base.String.is_substring msg ~substring:"x86_64-gnu-elf"
              && Base.String.is_substring msg ~substring:"System V"
          | _ -> false in
        check "an unknown target" (refused Bap_core_theory.Theory.Target.unknown);
        List.iter (fun name ->
            check name
              (refused (Bap_core_theory.Theory.Target.of_string name)))
          [ "bap:armv7-linux-eabi"; "bap:aarch64-linux-gnu"; "bap:x86-linux-gnu";
            "bap:x86_64-windows-pe" ];
        check "x86_64-gnu-elf is accepted"
          (match Sg.create ~target:(x86_target ()) Sg.empty
                   ~imports:(fun _ -> None) with
           | _ -> true));

    pin "SG-09" "placement is defined through the ABI's calling convention"
      (fun () ->
        let abi = Hike_abi.of_target (x86_target ()) in
        check "the convention is System V x86-64 GNU"
          (abi.Hike_abi.convention = Hike_abi.Sysv_x86_64_gnu);
        let db =
          records_of
            "((library l) (version v) (symbol f) (return Int) \
             (params (((ty Pointer)) ((ty Double)) ((ty Long)))))" in
        let record = Option.get (find ~library:"l" ~version:"v" db "f") in
        let call = Sg.place ~abi record in
        check "pointer in %rdi, double in %xmm0, long in %rsi"
          (call.Hike_sysv.arguments
           = [ { Hike_sysv.location = Registers [ Integer_register 0 ];
                 indirect = false };
               { location = Registers [ Vector_register { index = 0; eightbytes = 1 } ];
                 indirect = false };
               { location = Registers [ Integer_register 1 ]; indirect = false } ]);
        check "the registers it names are the ABI's"
          (Option.map Bap.Std.Var.name (Sg.integer_register ~abi 1) = Some "RSI"
           && Option.map Bap.Std.Var.name (Sg.vector_register ~abi 0) = Some "YMM0"));

    pin "SG-10"
      "the shipped file is the only source of noreturn: every never-returning libc entry point is marked"
      (fun () ->
        let db = Core.Or_error.ok_exn (Sg.load [ "../../data/glibc.sexp" ]) in
        List.iter (fun (name, version) ->
            match find db ~version name with
            | Some r -> check (name ^ " never returns") r.Sg.noreturn
            | None -> Alcotest.failf "no entry for %s@%s" name version)
          [ ("exit", "GLIBC_2.2.5"); ("_exit", "GLIBC_2.2.5");
            ("_Exit", "GLIBC_2.2.5"); ("abort", "GLIBC_2.2.5");
            ("quick_exit", "GLIBC_2.10"); ("__stack_chk_fail", "GLIBC_2.4");
            ("__assert_fail", "GLIBC_2.2.5"); ("longjmp", "GLIBC_2.2.5");
            ("siglongjmp", "GLIBC_2.2.5"); ("pthread_exit", "GLIBC_2.2.5");
            ("__libc_start_main", "GLIBC_2.34") ]);
  ]

let () = run "signatures" tests
