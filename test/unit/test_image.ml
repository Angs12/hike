(* Image pins: the RELA addend parse and the relocated-word
   substitution.  One Alcotest group per pin; each pin builds its own
   fixture, so no state crosses pins. *)

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

let tests : unit Alcotest.test list =
  [
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
            ~relative:[ (0x1008L, 0xdeadbeefL) ]
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
             ~relocated:[ 0x2000L; 0x2008L ] ~relative:[]
          = []);
        let frags =
          Img.substitute_relocated_words ~bytes ~lo ~hi:0x200fL
            ~relocated:[] ~relative:[]
        in
        check "IMG-03 identity"
          (match frags with
           | [ (b, l, h) ] -> Bytes.equal b bytes && l = lo && h = 0x200fL
           | _ -> false));
  ]

let () = run "image" tests
