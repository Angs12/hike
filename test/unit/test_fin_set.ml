(* Cbat_fin_set pins.  One Alcotest group per pin; each pin builds its own
   fixture, so no state crosses pins. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

let tests : unit Alcotest.test list =
  [
    pin "FS-01" "FS1: of_list basics (cardn/bitwidth/min/max/elem)"
      (fun () ->
        let s = Fs.of_list ~width:32 [ w32 1; w32 2; w32 3 ] in
        check "FS-01"
          (Fs.bitwidth s = 32
          && Cbat_word.to_int_exn (Fs.cardinality s) = 3
          && Fs.min_elem s = Some (w32 1)
          && Fs.max_elem s = Some (w32 3)
          && Fs.elem (w32 2) s
          && not (Fs.elem (w32 4) s)));



    pin "FS-03" "FS2: lift1 unops are involutive (neg, lnot)"
      (fun () ->
        let s = Fs.of_list ~width:32 [ w32 1; w32 2; w32 3 ] in
        check "FS-03"
          (Fs.equal (Fs.neg (Fs.neg s)) s && Fs.equal (Fs.lnot (Fs.lnot s)) s));

    pin "FS-04" "FS3: lift2 union/intersection"
      (fun () ->
        check "FS-04"
          (let a = Fs.of_list ~width:32 [ w32 1; w32 2 ] in
           let b = Fs.of_list ~width:32 [ w32 2; w32 3 ] in
           Fs.equal (Fs.union a b) (Fs.of_list ~width:32 [ w32 1; w32 2; w32 3 ])
           && Fs.equal (Fs.intersection a b) (Fs.of_list ~width:32 [ w32 2 ])));







    pin "FS-08" "FS7: add: {1,2} + {10} = {11,12}"
      (fun () ->
        check "FS-08"
          (let a = Fs.of_list ~width:32 [ w32 1; w32 2 ] in
           let r = Fs.add a (Fs.singleton (w32 10)) in
           Fs.elem (w32 11) r && Fs.elem (w32 12) r
           && Cbat_word.to_int_exn (Fs.cardinality r) = 2));

    pin "FS-09" "FS8: extract/cast/concat width sanity"
      (fun () ->
        check "FS-09"
          (let one = Fs.singleton (w32 1) in
           Fs.bitwidth (Fs.extract ~hi:7 ~lo:0 one) = 8
           && Fs.bitwidth (Fs.cast Bil.UNSIGNED 64 one) = 64
           && Fs.bitwidth (Fs.concat one (Fs.singleton (Cbat_word.of_int ~width:16 1))) = 48));

    pin "FS-10" "FS9 (delta #1): equal on width-mismatched sets is false (no assert)"
      (fun () ->
        let f32 = Fs.of_list ~width:32 [ w32 1; w32 2 ] in
        let f64 = Fs.of_list ~width:64 [ w64 1; w64 2 ] in
        check "FS-10" ((not (Fs.equal f32 f64)) && not (Fs.equal f64 f32)));











    (* The FinSet->Clp->FinSet loop: one pin, aggregate over the sampled sets. *)

  ]

let () = run "fin_set" tests
