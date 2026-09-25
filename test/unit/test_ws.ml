(* Cbat_clp_set_composite pins.  One Alcotest group per pin; each pin
   builds its own fixture, so no state crosses pins. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

(* Interval builder: [lo, hi] step 1. *)
let int32 ~lo ~hi =
  Clp.create ~width:32 ~step:(w32 1) ~cardn:(Cbat_word.of_int ~width:33 (hi - lo + 1)) (w32 lo)

(* The blind-bits fixture vocabulary. *)
let pw_w x = Ws.singleton (Cbat_word.of_int ~width:64 x)
let pw_word ?(width = 64) x = Cbat_word.of_int ~width x

let pw_exact ?(width = 64) v r =
  let v = Cbat_word.of_int ~width v in
  match Ws.min_elem r, Ws.max_elem r, Ws.stack_offsets r with
  | Some lo, Some hi, None -> Cbat_word.equal lo v && Cbat_word.equal hi v
  | _ -> false

let tests : unit Alcotest.test list =
  [
    pin "WS-01" "W7: the FinSet diffs — exact; the mixed-width pair shares no elements"
      (fun () ->
        check "WS-01"
          (Ws.equal
             (Ws.diff (Ws.of_list ~width:32 [ w32 1; w32 2; w32 3 ]) (Ws.of_list ~width:32 [ w32 2 ]))
             (Ws.of_list ~width:32 [ w32 1; w32 3 ])
          && Ws.equal
               (Ws.diff
                  (Ws.of_list ~width:32 [ w32 0; w32 1; w32 2; w32 3; w32 4 ])
                  (Ws.of_clp (int32 ~lo:1 ~hi:3)))
               (Ws.of_list ~width:32 [ w32 0; w32 4 ])
          && Ws.equal
               (Ws.diff (Ws.of_list ~width:32 [ w32 1; w32 2 ]) (Ws.of_list ~width:64 [ w64 1; w64 2 ]))
               (Ws.of_list ~width:32 [ w32 1; w32 2 ])));

    pin "WS-02" "W8: the Clp\\FinSet — the boundary-touch run removed exactly: [0,10] \\ {0,1,2} = {3..10}"
      (fun () ->
        let p8 = Ws.of_clp (int32 ~lo:0 ~hi:10) in
        let d8 = Ws.diff p8 (Ws.of_list ~width:32 [ w32 0; w32 1; w32 2 ]) in
        check "WS-02"
          (Cbat_word.to_int_exn (Ws.cardinality d8) = 8
          && List.for_all
               (fun w -> Ws.elem w d8)
               [ w32 3; w32 4; w32 5; w32 6; w32 7; w32 8; w32 9; w32 10 ]
          && (not (Ws.elem (w32 0) d8))
          && not (Ws.elem (w32 2) d8)));

    pin "WS-03"
      "W8b: the Clp\\FinSet interior run — EXACT: [0,10] \\ {3,4,5} = [0,2] ∪ [6,10]"
      (fun () ->
        let p8 = Ws.of_clp (int32 ~lo:0 ~hi:10) in
        let d8i = Ws.diff p8 (Ws.of_list ~width:32 [ w32 3; w32 4; w32 5 ]) in
        check "WS-03"
          (Ws.equal d8i
             (Ws.of_list ~width:32
                [ w32 0; w32 1; w32 2; w32 6; w32 7; w32 8; w32 9; w32 10 ])
          && (not (Ws.elem (w32 3) d8i))
          && not (Ws.elem (w32 5) d8i)));

    pin "WS-04"
      "W8c: the Clp\\FinSet with gaps — EXACT: [0,10] \\ {3,5} keeps its pieces (the \
       survivors, 3 and 4 apart, never hull)"
      (fun () ->
        let p8 = Ws.of_clp (int32 ~lo:0 ~hi:10) in
        let d8c = Ws.diff p8 (Ws.of_list ~width:32 [ w32 3; w32 5 ]) in
        check "WS-04"
          (Ws.equal d8c
             (Ws.of_list ~width:32
                [ w32 0; w32 1; w32 2; w32 4; w32 6; w32 7; w32 8; w32 9; w32 10 ])
          && (not (Ws.elem (w32 3) d8c))
          && not (Ws.elem (w32 5) d8c)));

    pin "WS-05" "D1-5: composite meet on width-mismatched sets -> no assert, not bottom"
      (fun () ->
        check "WS-05"
          (let r = Ws.meet (Ws.of_list ~width:32 [ w32 1; w32 2 ]) (Ws.of_list ~width:64 [ w64 1 ]) in
           (not (Ws.is_bottom r)) && Ws.bitwidth r = 64 && Ws.elem (w64 1) r));

    pin "WS-06" "D1-6: composite meet on matching widths is still exact"
      (fun () ->
        check "WS-06"
          (let a = Ws.of_list ~width:32 [ w32 1; w32 2 ] in
           let b = Ws.of_list ~width:32 [ w32 2; w32 3 ] in
           Ws.equal (Ws.meet a b) (Ws.of_list ~width:32 [ w32 2 ])));

    pin "WS-07" "D5-6: composite rshift on mixed-width CLPs COMPUTES (lane A) — non-top, no assert"
      (fun () ->
        let big32 = Ws.of_list ~width:32 (List.init 11 (fun i -> w32 (i * 2))) in
        let big64 = Ws.of_list ~width:64 (List.init 11 (fun i -> w64 (i * 2))) in
        check "WS-07" (not (Ws.is_top (Ws.rshift big32 big64))));

    pin "WS-08" "D5-7: composite arshift on mixed-width CLPs COMPUTES (lane A) — non-top, no assert"
      (fun () ->
        let big32 = Ws.of_list ~width:32 (List.init 11 (fun i -> w32 (i * 2))) in
        let big64 = Ws.of_list ~width:64 (List.init 11 (fun i -> w64 (i * 2))) in
        check "WS-08" (not (Ws.is_top (Ws.arshift big32 big64))));

    pin "WS-09" "D5-8: composite rshift on same-width singletons still exact"
      (fun () ->
        check "WS-09"
          (let r = Ws.rshift (Ws.singleton (w32 16)) (Ws.singleton (w32 2)) in
           Ws.elem (w32 4) r && (not (Ws.is_top r)) && not (Ws.is_bottom r)));

    (* The sampled-pair overlap loop: one pin, aggregate over the pairs. *)
    pin "WS-10" "property WordSet.overlap vs meet is_bottom (7 sampled pairs)"
      (fun () ->
        let pairs : (Ws.t * Ws.t) list =
          [
            (Ws.of_list ~width:32 [ w32 1; w32 2 ], Ws.of_list ~width:32 [ w32 2; w32 3 ]);
            (Ws.of_list ~width:32 [ w32 1 ], Ws.of_list ~width:32 [ w32 2 ]);
            (Ws.top 32, Ws.of_list ~width:32 [ w32 5 ]);
            ( Ws.of_list ~width:8 [ Cbat_word.of_int ~width:8 1; Cbat_word.of_int ~width:8 2 ],
              Ws.of_list ~width:8 [ Cbat_word.of_int ~width:8 3 ] );
            ( Ws.of_clp (Clp.create (w32 0) ~step:(w32 2) ~cardn:(Cbat_word.of_int ~width:33 5)),
              Ws.of_clp (Clp.create (w32 1) ~step:(w32 2) ~cardn:(Cbat_word.of_int ~width:33 5)) );
            (Ws.singleton (w32 10), Ws.of_list ~width:32 [ w32 10; w32 20 ]);
            (Ws.singleton (w32 10), Ws.of_list ~width:32 [ w32 20; w32 30 ]);
          ]
        in
        check "WS-10"
          (List.for_all
             (fun (a, b) -> Ws.overlap a b = not (Ws.is_bottom (Ws.meet a b)))
             pairs));

    pin "WS-11" "property WordSet.overlap width-mismatch → false (pinned convention, FinSet/FinSet)"
      (fun () ->
        let a32 = Ws.of_list ~width:32 [ w32 1 ] in
        let a64 = Ws.of_list ~width:64 [ w64 1 ] in
        check "WS-11" (not (Ws.overlap a32 a64)));

    pin "WS-12" "property WordSet.meet width-mismatch → wider operand (non-bottom)"
      (fun () ->
        let a32 = Ws.of_list ~width:32 [ w32 1 ] in
        let a64 = Ws.of_list ~width:64 [ w64 1 ] in
        check "WS-12" (not (Ws.is_bottom (Ws.meet a32 a64))));

    pin "WS-13"
      "property m6 overlap = not is_bottom o meet enumerated (300 random equal-width trials, \
       representation-aware)"
      (fun () ->
        Random.init 20260822;
        let failures = ref 0 in
        let rand_ws (w : int) : Ws.t * [ `fs | `clp ] =
          match Random.int 4 with
          | 0 ->
              (* Small explicit set (FinSet arm). *)
              let n = 1 + Random.int 5 in
              let rec els acc i =
                if i <= 0 then acc
                else els (Cbat_word.of_int ~width:w (Random.bits () land ((1 lsl w) - 1)) :: acc) (i - 1)
              in
              (Ws.of_list ~width:w (els [] n), `fs)
          | 1 ->
              (* Random progression. *)
              let base = Cbat_word.of_int ~width:w (Random.bits () land ((1 lsl w) - 1)) in
              let step = Cbat_word.of_int ~width:w (1 + Random.int 3) in
              let c = if Random.bool () then 1 + Random.int 6 else 11 + Random.int 30 in
              ( Ws.of_clp (Clp.create base ~step ~cardn:(Cbat_word.of_int ~width:(w + 1) c)),
                if c <= 10 (* Utils.fin_set_size *) then `fs else `clp )
          | 2 ->
              (* Top (demotes by width). *)
              (Ws.top w, if w <= 3 then `fs else `clp)
          | _ -> (Ws.singleton (Cbat_word.of_int ~width:w (Random.bits () land ((1 lsl w) - 1))), `fs)
        in
        for _i = 1 to 300 do
          let w = [| 3; 5; 8 |].(Random.int 3) in
          let a, ta = rand_ws w in
          let b, tb = rand_ws w in
          if Ws.bitwidth a = Ws.bitwidth b then begin
            let ov = Ws.overlap a b in
            let mb = Ws.is_bottom (Ws.meet a b) in
            if ov && mb then incr failures;
            if (ta = `fs || tb = `fs) && ov <> not mb then incr failures
          end
        done;
        check "WS-13" (!failures = 0));

    pin "WS-14" "CARDN-W1: the |segment|*|offs| product saturates past the exact threshold"
      (fun () ->
        let b =
          Cbat_word.mul (Cbat_word.of_int ~width:65 8)
            (Cbat_word.of_int ~width:65 0x1000000000000000)
        in
        let offs = Clp.create ~width:64 ~step:(Cbat_word.one 64) ~cardn:b (Cbat_word.zero 64) in
        check "WS-14" (Cbat_word.equal (Ws.cardinality (Ws.stack_word offs)) (Cbat_word.ones 65)));

    pin "WS-15" "PW-S1: a singleton stack address's extrema are the exact address"
      (fun () ->
        let addr o = Cbat_word.of_int64 ~width:64 (Int64.add Ws.stack_base o) in
        let p1 = Ws.stack_word_i64 (-8L) in
        check "WS-15"
          (match Ws.min_elem p1, Ws.max_elem p1 with
           | Some lo, Some hi -> Cbat_word.equal lo (addr (-8L)) && Cbat_word.equal hi (addr (-8L))
           | _ -> false));

    pin "WS-16" "PW-S2: an offset interval projects to its exact address hull"
      (fun () ->
        let addr o = Cbat_word.of_int64 ~width:64 (Int64.add Ws.stack_base o) in
        let p2 =
          Ws.stack_word
            (Clp.interval ~width:64
               (Cbat_word.of_int64 ~width:64 (-16L))
               (Cbat_word.of_int64 ~width:64 (-8L)))
        in
        check "WS-16"
          (match Ws.min_elem p2, Ws.max_elem p2 with
           | Some lo, Some hi -> Cbat_word.equal lo (addr (-16L)) && Cbat_word.equal hi (addr (-8L))
           | _ -> false));

    pin "WS-17" "PW-B1: an AND confined to the certified nibble computes the ABI truth"
      (fun () ->
        let p = Ws.stack_word_i64 (-72L) in
        check "WS-17" (pw_exact 0 (Ws.logand p (pw_w 15))));

    pin "WS-18" "PW-B2: a shift keeps unknown bits and answers top"
      (fun () ->
        let p = Ws.stack_word_i64 (-72L) in
        check "WS-18" (Ws.is_top (Ws.rshift p (pw_w 4))));

    pin "WS-19" "PW-B3: an extract confined to the certified nibble computes"
      (fun () ->
        let p = Ws.stack_word_i64 (-72L) in
        check "WS-19" (pw_exact ~width:4 0 (Ws.extract ~hi:3 ~lo:0 p)));

    pin "WS-20" "PW-B4: a wide low cast keeps unknown bits and answers top"
      (fun () ->
        let p = Ws.stack_word_i64 (-72L) in
        check "WS-20" (Ws.is_top (Ws.cast Bil.LOW 32 p)));

    pin "WS-21" "PW-B5: add keeps the stack shape with exact offsets"
      (fun () ->
        let p = Ws.stack_word_i64 (-72L) in
        let b =
          match Ws.stack_offsets (Ws.add p (pw_w 0x38)) with
          | Some offs -> (
              match Clp.min_elem offs, Clp.max_elem offs with
              | Some lo, Some hi ->
                  Cbat_word.to_int64 lo = Ok (-16L) && Cbat_word.to_int64 hi = Ok (-16L)
              | _ -> false)
          | None -> false
        in
        check "WS-21" b);

    pin "WS-22" "PW-B6: plain singletons keep the exact bitwise AND"
      (fun () ->
        check "WS-22"
          (match Ws.logand (pw_w 15) (pw_w 8) with
           | t -> (
               match Ws.min_elem t, Ws.max_elem t with
               | Some lo, Some hi ->
                   Cbat_word.equal lo (Cbat_word.of_int ~width:64 8)
                   && Cbat_word.equal hi (Cbat_word.of_int ~width:64 8)
               | _ -> false)));

    pin "WS-23" "PW-R1: the certified AND answers the true residue"
      (fun () ->
        let q = Ws.stack_word_i64 (-66L) in
        check "WS-23" (pw_exact 6 (Ws.logand q (pw_w 15))));

    pin "WS-24" "PW-R2: a sub-nibble mask keeps its bits"
      (fun () ->
        let q = Ws.stack_word_i64 (-66L) in
        check "WS-24" (pw_exact 2 (Ws.logand q (pw_w 2))));

    pin "WS-25" "PW-R3: a certified extract answers the masked bits"
      (fun () ->
        let q = Ws.stack_word_i64 (-66L) in
        check "WS-25" (pw_exact ~width:2 1 (Ws.extract ~hi:3 ~lo:2 q)));

    pin "WS-26" "PW-R4: a certified narrow cast answers the low bits"
      (fun () ->
        let q = Ws.stack_word_i64 (-66L) in
        check "WS-26" (pw_exact ~width:4 6 (Ws.cast Bil.SIGNED 4 q)));

    pin "WS-27" "PW-R5: a certified AND over an offset interval answers the residue hull"
      (fun () ->
        check "WS-27"
          (match
             Ws.min_elem
               (Ws.logand
                  (Ws.stack_word
                     (Clp.interval ~width:64
                        (Cbat_word.of_int64 ~width:64 (-72L))
                        (Cbat_word.of_int64 ~width:64 (-64L))))
                  (pw_w 15)),
             Ws.max_elem
               (Ws.logand
                  (Ws.stack_word
                     (Clp.interval ~width:64
                        (Cbat_word.of_int64 ~width:64 (-72L))
                        (Cbat_word.of_int64 ~width:64 (-64L))))
                  (pw_w 15))
           with
           | Some lo, Some hi -> Cbat_word.equal lo (pw_word 0) && Cbat_word.equal hi (pw_word 8)
           | _ -> false));

    pin "WS-28" "PW-R6: a bit-op past the enumeration budget answers top"
      (fun () ->
        let big =
          Ws.stack_word
            (Clp.interval ~width:64
               (Cbat_word.of_int64 ~width:64 (-1073741824L))
               (Cbat_word.of_int64 ~width:64 1073741824L))
        in
        check "WS-28" (Ws.is_top (Ws.logand big (pw_w 15))));

    pin "WS-29" "PW-R7: an unconfined mask keeps fabricated bits and answers top"
      (fun () ->
        let p = Ws.stack_word_i64 (-72L) in
        check "WS-29" (Ws.is_top (Ws.logand p (pw_w 0xFF0))));

    pin "WS-30" "PW-R8: two stack addresses' AND answers top"
      (fun () ->
        let p = Ws.stack_word_i64 (-72L) in
        let q = Ws.stack_word_i64 (-66L) in
        check "WS-30" (Ws.is_top (Ws.logand p q)));

    pin "WS-31" "PW-R9: a HIGH cast keeps the unknown bits and answers top"
      (fun () ->
        let p = Ws.stack_word_i64 (-72L) in
        check "WS-31" (Ws.is_top (Ws.cast Bil.HIGH 4 p)));

    pin "WS-32" "DOM-44: a blind stack binop keeps the wider operand width"
      (fun () ->
        let stack = Ws.stack_word_i64 0L in
        let plain = Ws.singleton (w32 1) in
        let left = Ws.logor stack plain in
        let right = Ws.logor plain stack in
        check "WS-32"
          (Ws.bitwidth left = 64 && Ws.bitwidth right = 64
          && Ws.is_top left && Ws.is_top right));

    pin "WS-33"
      "UT1-42: the composite mixed-step meet is EXACT — {10,12,14,16,18} ∩ \
       {16,17,18,19} = {16,18}"
      (fun () ->
        let a = Ws.of_list ~width:32 [ w32 10; w32 12; w32 14; w32 16; w32 18 ] in
        let b = Ws.of_list ~width:32 [ w32 16; w32 17; w32 18; w32 19 ] in
        let m = Ws.meet a b in
        check "WS-33"
          (Ws.equal m (Ws.of_list ~width:32 [ w32 16; w32 18 ])
          && Cbat_word.to_int_exn (Ws.cardinality m) = 2
          && (not (Ws.elem (w32 10) m))
          && (not (Ws.elem (w32 17) m))
          && not (Ws.elem (w32 19) m)));

    pin "WS-34"
      "the disjoint union: two case targets stay two pieces — the union never \
       hulls {0,100} into [0,100]"
      (fun () ->
        let u = Ws.union (Ws.singleton (w32 0)) (Ws.singleton (w32 100)) in
        check "WS-34"
          (Ws.equal u (Ws.of_list ~width:32 [ w32 0; w32 100 ])
          && Ws.elem (w32 0) u
          && Ws.elem (w32 100) u
          && (not (Ws.elem (w32 50) u))
          && (not (Ws.elem (w32 1) u))
          && not (Ws.elem (w32 99) u)));
  ]

let () = run "ws" tests
