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





    pin "WS-05" "D1-5: composite meet on width-mismatched sets -> no assert, not bottom"
      (fun () ->
        check "WS-05"
          (let r = Ws.meet (Ws.of_list ~width:32 [ w32 1; w32 2 ]) (Ws.of_list ~width:64 [ w64 1 ]) in
           (not (Ws.is_bottom r)) && Ws.bitwidth r = 64 && Ws.elem (w64 1) r));



    pin "WS-07" "D5-6: composite rshift on mixed-width CLPs COMPUTES (lane A) — non-top, no assert"
      (fun () ->
        let big32 = Ws.of_list ~width:32 (List.init 11 (fun i -> w32 (i * 2))) in
        let big64 = Ws.of_list ~width:64 (List.init 11 (fun i -> w64 (i * 2))) in
        check "WS-07" (not (Ws.is_top (Ws.rshift big32 big64))));





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



    pin "WS-17" "PW-B1: an AND confined to the certified nibble computes the ABI truth"
      (fun () ->
        let p = Ws.stack_word_i64 (-72L) in
        check "WS-17" (pw_exact 0 (Ws.logand p (pw_w 15))));





























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

    pin "WS-35"
      "the wrapped SP piece measures — a stack value whose offsets wrap the \
       modulus ({-16, 0} as a wrapped pair) keeps signed extrema and \
       segment-relative bounds (-16, 0) instead of answering None"
      (fun () ->
        let w64 = Cbat_word.of_int ~width:64 in
        (* The vasnprintf shape: a wrapped finite offsets piece whose
           elements are {-16, 0, 16} — the traversal crosses the
           modulus. *)
        let offs =
          Clp.create ~width:64 ~step:(w64 16) ~cardn:(Cbat_word.of_int ~width:65 3)
            (Cbat_word.neg (w64 16)) in
        let v = Ws.stack_word offs in
        (* stack_base 2^62+8: the absolute signed extrema are
           stack_base-16 and stack_base+16. *)
        let base = 0x3FFF_FFFF_FFFF_FFF8L in
        check "WS-35"
          (Clp.is_wrapped offs
          && (match Ws.stack_bounds v with
              | Some (lo, hi) ->
                Stdlib.Int64.equal lo (-16L) && Stdlib.Int64.equal hi 16L
              | None -> false)
          && (match Ws.min_elem_signed v, Ws.max_elem_signed v with
              | Some mn, Some mx ->
                Stdlib.Int64.equal (Cbat_word.to_int64_exn mn) base
                && Stdlib.Int64.equal (Cbat_word.to_int64_exn mx)
                  (Int64.add base 32L)
              | None, _ | _, None -> false)));

    pin "WS-36"
      "a symbolic stack top is not the lattice top (structural equality; the map \
       lattice must test [equal], not [is_top], before dropping a top binding)"
      (fun () ->
        let st = Ws.stack_word (Clp.top 64) in
        check "WS-36"
          (Ws.is_top st
          && (not (Ws.equal st (Ws.top 64)))
          && not (Ws.equal (Ws.top 64) st)));
    pin "WS-37"
      "C5: an all-ones 64-bit mask is the identity on the stack line — at s = 64 the round-\
       down image is the offsets themselves, origin unchanged"
      (fun () ->
        let p = Ws.stack_word (Clp.interval ~width:64 (w64 8) (w64 40)) in
        let ones = Ws.singleton (Cbat_word.ones 64) in
        let r = Ws.logand p ones in
        (* The AND with all-ones is the identity: the image IS the
           input band (offsets stay relative to the same base). *)
        check "WS-37 (exactness: the image is the input band, not a singleton)"
          (match Ws.stack_offsets r with
           | Some offs ->
             (match Clp.min_elem offs, Clp.max_elem offs with
              | Some lo, Some hi ->
                Cbat_word.equal lo (w64 8) && Cbat_word.equal hi (w64 40)
              | _ -> false)
           | None -> false);
        check "WS-37 (the same origin: the result stays stack-symbolic)"
          (Ws.origin r = Ws.origin p));

    pin "WS-38"
      "a relative value and its plain in-band twin keep the origin through \
       the union and the widen: the cell stays stack-symbolic"
      (fun () ->
        let rel = Ws.stack_word_i64 (-200L) in
        let plain =
          Ws.singleton (q64 (Stdlib.Int64.add Ws.stack_base (-200L)))
        in
        let keeps_origin (v : Ws.t) =
          Option.equal Ws.Origin.equal (Ws.origin v) (Some Ws.Origin.Stack)
          && (match Ws.stack_offsets v with
              | Some offs ->
                (match Clp.min_elem offs, Clp.max_elem offs with
                 | Some lo, Some hi ->
                   Cbat_word.equal lo (q64 (-200L))
                   && Cbat_word.equal hi (q64 (-200L))
                 | _ -> false)
              | None -> false)
        in
        check "WS-38 (union)" (keeps_origin (Ws.union rel plain));
        check "WS-38 (widen_join)" (keeps_origin (Ws.widen_join rel plain)));

    (* WS-39: the interior exclusion widens as two pieces — the x != k
       complement keeps its hole under widening instead of hulling it
       shut. *)
    pin "WS-39"
      "widen_join keeps a two-piece value's hole (the interior exclusion survives widening)"
      (fun () ->
        let five = Cbat_word.of_int ~width:64 5 in
        let hole = Ws.diff (Ws.top 64) (Ws.singleton five) in
        (* Stability: widening the exclusion with itself is the
           identity, hole intact. *)
        let stable = Ws.widen_join hole hole in
        let keeps_hole t =
          not (Ws.elem five t) && Ws.elem (Cbat_word.of_int ~width:64 4) t
          && Ws.elem (Cbat_word.of_int ~width:64 6) t
        in
        check "WS-39 (stable)" (keeps_hole stable);
        (* Growth: one side grows past the hole, the widened value
           still excludes nothing it did not exclude. *)
        let grown = Ws.union hole (Ws.singleton five) in
        let w = Ws.widen_join hole grown in
        check "WS-39 (growth)" (Ws.elem five w && Ws.precedes hole w))
  ]

let () = run "ws" tests
