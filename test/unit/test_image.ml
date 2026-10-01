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
let rela_bytes (rows : (int64 * int64 * int64) list) : Bytes.t =
  let b = Bytes.create (24 * List.length rows) in
  List.iteri
    (fun i (site, typ, addend) ->
      put_u64_le b (i * 24) site;
      put_u64_le b ((i * 24) + 8) typ;
      put_u64_le b ((i * 24) + 16) addend)
    rows;
  b

(* A section image: [words] little-endian. *)
let section_bytes (words : int64 list) : Bytes.t =
  let b = Bytes.create (8 * List.length words) in
  List.iteri (fun i w -> put_u64_le b (i * 8) w) words;
  b

let tests : unit Alcotest.test list =
  [
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
