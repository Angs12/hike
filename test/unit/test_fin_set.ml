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

    pin "FS-02" "FS1: singleton"
      (fun () ->
        check "FS-02"
          (let one = Fs.singleton (w32 7) in
           Fs.elem (w32 7) one && Cbat_word.to_int_exn (Fs.cardinality one) = 1));

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

    pin "FS-05" "FS4: join/meet are the lattice aliases of union/intersection"
      (fun () ->
        check "FS-05"
          (let a = Fs.of_list ~width:32 [ w32 1; w32 2 ] in
           let b = Fs.of_list ~width:32 [ w32 2; w32 3 ] in
           Fs.equal (Fs.join a b) (Fs.union a b)
           && Fs.equal (Fs.meet a b) (Fs.of_list ~width:32 [ w32 2 ])));

    pin "FS-06" "FS5: precedes/equal"
      (fun () ->
        let s = Fs.of_list ~width:32 [ w32 1; w32 2; w32 3 ] in
        check "FS-06"
          (Fs.precedes (Fs.singleton (w32 1)) s
          && (not (Fs.precedes s (Fs.singleton (w32 1))))
          && Fs.equal s s
          && not (Fs.equal (Fs.singleton (w32 1)) s)));

    pin "FS-07" "FS6: bottom absorption"
      (fun () ->
        let s = Fs.of_list ~width:32 [ w32 1; w32 2; w32 3 ] in
        check "FS-07"
          (let b = Fs.bottom 32 in
           Fs.equal (Fs.join s b) s
           && Fs.equal (Fs.join b s) s
           && Fs.equal (Fs.meet s b) b
           && Cbat_word.to_int_exn (Fs.cardinality (Fs.meet s b)) = 0));

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

    pin "FS-11" "FS9 (delta #1): precedes on width-mismatched sets is false"
      (fun () ->
        let f32 = Fs.of_list ~width:32 [ w32 1; w32 2 ] in
        let f64 = Fs.of_list ~width:64 [ w64 1; w64 2 ] in
        check "FS-11" ((not (Fs.precedes f32 f64)) && not (Fs.precedes f64 f32)));

    pin "FS-12" "D1-1: fin_set elem on a width-mismatched word -> false (no assert)"
      (fun () ->
        let f32 = Fs.of_list ~width:32 [ w32 1; w32 2 ] in
        let f64 = Fs.of_list ~width:64 [ w64 1; w64 2 ] in
        check "FS-12" ((not (Fs.elem (w32 1) f64)) && not (Fs.elem (w64 1) f32)));

    pin "FS-13" "D1-2: fin_set overlap on width-mismatched sets -> false (no assert)"
      (fun () ->
        let f32 = Fs.of_list ~width:32 [ w32 1; w32 2 ] in
        let f64 = Fs.of_list ~width:64 [ w64 1; w64 2 ] in
        check "FS-13" ((not (Fs.overlap f32 f64)) && not (Fs.overlap f64 f32)));

    pin "FS-14" "D1-3: fin_set nearest_pred on a width-mismatched word -> None"
      (fun () ->
        let f64 = Fs.of_list ~width:64 [ w64 1; w64 2 ] in
        check "FS-14" (Fs.nearest_pred (w32 1) f64 = None));

    pin "FS-15" "D1-4: intersect_generic width mismatch -> input unchanged (no assert)"
      (fun () ->
        let f32 = Fs.of_list ~width:32 [ w32 1; w32 2 ] in
        check "FS-15"
          (let r = Fs.intersect_generic (module Clp) f32 (Clp.of_list ~width:64 [ w64 1 ]) in
           Fs.bitwidth r = 32 && Fs.elem (w32 1) r && Fs.elem (w32 2) r));

    (* The FinSet->Clp->FinSet loop: one pin, aggregate over the sampled sets. *)
    pin "FS-16" "property FinSet->Clp->FinSet round-trip on small sets"
      (fun () ->
        let fin_sets : Fs.t list =
          [
            Fs.of_list ~width:32 [ w32 1; w32 2; w32 3 ];
            Fs.of_list ~width:32 [ w32 5 ];
            Fs.of_list ~width:8 [ Cbat_word.of_int ~width:8 1; Cbat_word.of_int ~width:8 2 ];
            Fs.of_list ~width:16 [ Cbat_word.of_int ~width:16 10; Cbat_word.of_int ~width:16 20 ];
            Fs.of_list ~width:32 [ w32 0; w32 2; w32 4; w32 6; w32 8 ];
          ]
        in
        check "FS-16"
          (List.for_all
             (fun s ->
               let p = Clp.of_list ~width:(Fs.bitwidth s) (Fs.iter s) in
               let s2 = Fs.of_list ~width:(Clp.bitwidth p) (Clp.iter p) in
               Fs.equal s s2)
             fin_sets));
  ]

let () = run "fin_set" tests
