(* Cbat_clp.Exact pins.  One Alcotest group per pin; each pin builds its own
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
        let s = Ex.of_list ~width:32 [ w32 1; w32 2; w32 3 ] in
        check "FS-01"
          (Ex.bitwidth s = 32
          && Cbat_word.to_int_exn (Ex.cardinality s) = 3
          && Ex.min_elem s = Some (w32 1)
          && Ex.max_elem s = Some (w32 3)
          && Ex.elem (w32 2) s
          && not (Ex.elem (w32 4) s)));



    pin "FS-03" "FS2: lift1 unops are involutive (neg, lnot)"
      (fun () ->
        let s = Ex.of_list ~width:32 [ w32 1; w32 2; w32 3 ] in
        check "FS-03"
          (Ex.equal (Ex.neg (Ex.neg s)) s && Ex.equal (Ex.lnot (Ex.lnot s)) s));

    pin "FS-04" "FS3: lift2 union/intersection"
      (fun () ->
        check "FS-04"
          (let a = Ex.of_list ~width:32 [ w32 1; w32 2 ] in
           let b = Ex.of_list ~width:32 [ w32 2; w32 3 ] in
           Ex.equal (Ex.union a b) (Ex.of_list ~width:32 [ w32 1; w32 2; w32 3 ])
           && Ex.equal (Ex.intersection a b) (Ex.of_list ~width:32 [ w32 2 ])));







    pin "FS-08" "FS7: add: {1,2} + {10} = {11,12}"
      (fun () ->
        check "FS-08"
          (let a = Ex.of_list ~width:32 [ w32 1; w32 2 ] in
           let r = Ex.add a (Ex.singleton (w32 10)) in
           Ex.elem (w32 11) r && Ex.elem (w32 12) r
           && Cbat_word.to_int_exn (Ex.cardinality r) = 2));

    pin "FS-09" "FS8: extract/cast/concat width sanity"
      (fun () ->
        check "FS-09"
          (let one = Ex.singleton (w32 1) in
           Ex.bitwidth (Ex.extract ~hi:7 ~lo:0 one) = 8
           && Ex.bitwidth (Ex.cast Bil.UNSIGNED 64 one) = 64
           && Ex.bitwidth (Ex.concat one (Ex.singleton (Cbat_word.of_int ~width:16 1))) = 48));

    pin "FS-10" "FS9 (delta #1): equal on width-mismatched sets is false (no assert)"
      (fun () ->
        let f32 = Ex.of_list ~width:32 [ w32 1; w32 2 ] in
        let f64 = Ex.of_list ~width:64 [ w64 1; w64 2 ] in
        check "FS-10" ((not (Ex.equal f32 f64)) && not (Ex.equal f64 f32)));











  ]

let () = run "exact" tests
