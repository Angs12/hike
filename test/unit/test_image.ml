(* Image pins: the relocated-word substitution, PT_TLS, and the
   never-written ranges the analysis images are restricted to. *)

open Bap.Std
open Hike_test.Harness

module Img = Hike.Image

(* Little-endian 64-bit word at [off]. *)
let u64_le (b : Bytes.t) (off : int) : int64 =
  let acc = ref 0L in
  for k = 0 to 7 do
    acc :=
      Int64.logor !acc
        (Int64.shift_left
           (Int64.of_int (Char.code (Bytes.get b (off + k))))
           (8 * k))
  done;
  !acc

let put_u64_le (b : Bytes.t) (off : int) (v : int64) : unit =
  for k = 0 to 7 do
    Bytes.set b (off + k)
      (Char.chr
         (Int64.to_int
            (Int64.logand (Int64.shift_right_logical v (8 * k)) 0xffL)))
  done

(* A RELA section's bytes over [rows] of (site, type, addend). *)
let section_bytes (words : int64 list) : Bytes.t =
  let b = Bytes.create (8 * List.length words) in
  List.iteri (fun i w -> put_u64_le b (i * 8) w) words;
  b

(* An ELF without sections or symbols: PT_TLS is the only ownership fact. *)
let with_tls_image ~filesz ~memsz f =
  let bytes = Bytes.make 208 '\000' in
  let put off size value =
    for i = 0 to size - 1 do
      Bytes.set bytes (off + i)
        (Char.chr (Int64.to_int (Int64.logand
            (Int64.shift_right_logical value (8 * i)) 255L)))
    done in
  Bytes.blit_string "\x7fELF\x02\x01\x01" 0 bytes 0 7;
  put 16 2 2L; put 18 2 62L; put 20 4 1L;
  put 24 8 0x4000b0L; put 32 8 64L;
  put 52 2 64L; put 54 2 56L; put 56 2 2L; put 58 2 64L;
  put 64 4 1L; put 68 4 5L;
  put 80 8 0x400000L; put 88 8 0x400000L;
  put 96 8 208L; put 104 8 208L; put 112 8 4096L;
  put 120 4 7L; put 124 4 4L; put 128 8 195L;
  put 136 8 0x4000c3L; put 144 8 0x4000c3L;
  put 152 8 filesz; put 160 8 memsz; put 168 8 16L;
  Bytes.set bytes 176 '\xc3';
  Bytes.blit_string "abc" 0 bytes 195 3;
  let path = Filename.temp_file "hike-tls-image" ".elf" in
  Fun.protect ~finally:(fun () -> Sys.remove path) (fun () ->
      let out = open_out_bin path in
      output_bytes out bytes; close_out out;
      let project = Project.create (Project.Input.load ~loader:"llvm" path)
                    |> Core.Or_error.ok_exn in
      f project)

(* An ELF whose program headers are [phdrs] rows of
   (type, flags, offset, vaddr, filesz, memsz); no sections.  The entry
   at 0x400100 is a [ret]. *)
let with_phdrs (phdrs : (int64 * int64 * int64 * int64 * int64 * int64) list)
    ~(file_size : int) f =
  let bytes = Bytes.make file_size '\000' in
  let put off size value =
    for i = 0 to size - 1 do
      Bytes.set bytes (off + i)
        (Char.chr (Int64.to_int (Int64.logand
            (Int64.shift_right_logical value (8 * i)) 255L)))
    done in
  Bytes.blit_string "\x7fELF\x02\x01\x01" 0 bytes 0 7;
  put 16 2 2L; put 18 2 62L; put 20 4 1L;
  put 24 8 0x400100L; put 32 8 64L;
  put 52 2 64L; put 54 2 56L; put 56 2 (Int64.of_int (List.length phdrs));
  put 58 2 64L;
  List.iteri (fun i (typ, flags, off, vaddr, filesz, memsz) ->
      let h = 64 + (56 * i) in
      put h 4 typ; put (h + 4) 4 flags; put (h + 8) 8 off;
      put (h + 16) 8 vaddr; put (h + 24) 8 vaddr;
      put (h + 32) 8 filesz; put (h + 40) 8 memsz; put (h + 48) 8 4096L)
    phdrs;
  Bytes.set bytes 0x100 '\xc3';
  let path = Filename.temp_file "hike-phdrs" ".elf" in
  Fun.protect ~finally:(fun () -> Sys.remove path) (fun () ->
      let out = open_out_bin path in
      output_bytes out bytes; close_out out;
      let project = Project.create (Project.Input.load ~loader:"llvm" path)
                    |> Core.Or_error.ok_exn in
      f project)

let tests : unit Alcotest.test list =
  [
    pin "IMG-06"
      "only read-only PT_LOAD segments and page-rounded PT_GNU_RELRO \
       ranges are never written"
      (fun () ->
        with_phdrs ~file_size:0x2800
          [ (1L, 5L, 0L, 0x400000L, 0x200L, 0x200L);
            (1L, 6L, 0x1000L, 0x401000L, 0x1800L, 0x1800L);
            (0x6474e552L, 4L, 0x1000L, 0x401000L, 0x1100L, 0x1100L) ]
          (fun project ->
            let ranges =
              List.sort compare (Img.protections project ~page:4096L) in
            check "IMG-06.ranges"
              (ranges = [ (0x400000L, 0x4001ffL, Hike_section.Read_only);
                          (0x401000L, 0x401fffL, Hike_section.Relro) ])));

    pin "IMG-08" "a range's access is the protection covering it wholly"
      (fun () ->
        let prot =
          [ (0x1000L, 0x1fffL, Hike_section.Read_only);
            (0x3000L, 0x3fffL, Hike_section.Relro);
            (0x3800L, 0x38ffL, Hike_section.Read_only) ] in
        let access lo hi = Img.access prot ~lo ~hi in
        check "IMG-08.read-only" (access 0x1000L 0x1fffL = Hike_section.Read_only);
        check "IMG-08.relro" (access 0x3000L 0x30ffL = Hike_section.Relro);
        check "IMG-08.read-only-first" (access 0x3800L 0x3807L = Hike_section.Read_only);
        check "IMG-08.straddle" (access 0x1f00L 0x2fffL = Hike_section.Writable);
        check "IMG-08.outside" (access 0x2000L 0x2007L = Hike_section.Writable));

    pin "IMG-07" "an image keeps only its bytes inside the ranges"
      (fun () ->
        let bytes = Bytes.init 0x30 (fun i -> Char.chr i) in
        let frags =
          Img.clip_image (bytes, 0x1000L, 0x102fL)
            [ (0x0L, 0x100fL); (0x1020L, 0x1023L); (0x2000L, 0x2fffL) ] in
        check "IMG-07.fragments"
          (match frags with
           | [ (b0, 0x1000L, 0x100fL); (b1, 0x1020L, 0x1023L) ] ->
             Bytes.equal b0 (Bytes.sub bytes 0 0x10)
             && Bytes.equal b1 (Bytes.sub bytes 0x20 4)
           | _ -> false));

    pin "IMG-04"
      "PT_TLS alone supplies the image, extent, alignment and Variant-II offset"
      (fun () ->
        with_tls_image ~filesz:3L ~memsz:13L (fun project ->
            let tls = Base.Option.value_exn (Img.tls_spec project) in
            check "IMG-04.layout"
              (tls.tls_lo = 0x4000c3L && tls.tls_memsz = 13L
               && tls.tls_align = 16 && tls.tls_prefix = 3 && tls.tls_base = -13L);
            check "IMG-04.bytes" (Bytes.to_string tls.tls_image = "abc")));

    pin "IMG-05"
      "a tbss-only PT_TLS has no file image; invalid extents fail loudly"
      (fun () ->
        with_tls_image ~filesz:0L ~memsz:5L (fun project ->
            let tls = Base.Option.value_exn (Img.tls_spec project) in
            check "IMG-05.zero-tail" (Bytes.length tls.tls_image = 0 && tls.tls_memsz = 5L));
        with_tls_image ~filesz:3L ~memsz:2L (fun project ->
            let refused = try ignore (Img.tls_spec project); false
              with Failure _ -> true in
            check "IMG-05.invalid" refused));

    pin "IMG-02"
      "a RELATIVE word takes its runtime value, an externally-relocated \
       word is dropped, the rest keep the file bytes"
      (fun () ->
        let lo = 0x1000L in
        let bytes = section_bytes [ 0xaaaaL; 0xbbbbL; 0xccccL; 0xddddL ] in
        let frags =
          Img.substitute_relocated_words ~bytes ~lo ~hi:0x101fL
            ~relocated:[ 0x1008L; 0x1010L ]
            ~relative:[ (0x1008L, 0xdeadbeefL) ] ~word:8
        in
        check "IMG-02 fragments" (List.length frags = 2);
        match frags with
        | [ (b0, lo0, hi0); (b1, lo1, hi1) ] ->
          check "IMG-02 f0 bounds" (lo0 = 0x1000L && hi0 = 0x100fL);
          check "IMG-02 f0 word0" (u64_le b0 0 = 0xaaaaL);
          check "IMG-02 f0 word1" (u64_le b0 8 = 0xdeadbeefL);
          check "IMG-02 f1 bounds" (lo1 = 0x1018L && hi1 = 0x101fL);
          check "IMG-02 f1 word3" (u64_le b1 0 = 0xddddL)
        | _ -> check "IMG-02 shape" false);

    pin "IMG-03"
      "a section with only externally-relocated words yields no image; a \
       relocation-free section is its own bytes"
      (fun () ->
        let lo = 0x2000L in
        let bytes = section_bytes [ 0x1L; 0x2L ] in
        check "IMG-03 dropped"
          (Img.substitute_relocated_words ~bytes ~lo ~hi:0x200fL
             ~relocated:[ 0x2000L; 0x2008L ] ~relative:[] ~word:8
          = []);
        let frags =
          Img.substitute_relocated_words ~bytes ~lo ~hi:0x200fL
            ~relocated:[] ~relative:[] ~word:8
        in
        check "IMG-03 identity"
          (match frags with
           | [ (b, l, h) ] -> Bytes.equal b bytes && l = lo && h = 0x200fL
           | _ -> false));
  ]

let () = run "image" tests
