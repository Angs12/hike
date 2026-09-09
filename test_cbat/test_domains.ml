(* Abstract-domain unit pins: CLP, FinSet, Map, word ops, diff, policy, widening, Int64/Big agreement. *)
open Bap.Std
open Bap_core_theory
open Test_common
open Test_fixtures

let clp1 =
  let c = Clp.create (w32 10) in
  check "CLP1: create n is a 32-bit singleton (bitwidth/min/max/cardn)"
    (Clp.bitwidth c = 32
    && Clp.min_elem c = Some (w32 10)
    && Clp.max_elem c = Some (w32 10)
    && Cbat_word.to_int_exn (Clp.cardinality c) = 1);
  check "CLP1: elem of the singleton {10}" (Clp.elem (w32 10) c && not (Clp.elem (w32 11) c));
  c

(* create b ~step ~cardn = {b + step*i | 0 <= i < cardn} *)
let clp2 = Clp.create ~width:32 ~step:(w32 2) ~cardn:(w33 5) (w32 10)

(* Int64-vs-Big agreement pins: [clp_agree] asserts equal + cardn + elems + extrema,
   the path-independent contract every representation must satisfy. *)

(* Two CLPs agree: equal, same cardn, same elems, same extrema. *)
let clp_agree (name : string) (a : Clp.t) (b : Clp.t) : unit =
  let elems p = List.sort compare (Clp.iter p) in
  check (name ^ " [equal]") (Clp.equal a b);
  check (name ^ " [cardn]") (Clp.cardinality a = Clp.cardinality b);
  check (name ^ " [iter]") (elems a = elems b);
  check (name ^ " [extrema]") (Clp.min_elem a = Clp.min_elem b && Clp.max_elem a = Clp.max_elem b)

let run_base () =
(  check "CLP2: interval {10,12,14,16,18}: bounds sane"
    (Clp.bitwidth clp2 = 32
    && Clp.min_elem clp2 = Some (w32 10)
    && Clp.max_elem clp2 = Some (w32 18)
    && Cbat_word.to_int_exn (Clp.cardinality clp2) = 5);
  check "CLP2: interval membership (14 in, 15 not in)"
    (Clp.elem (w32 14) clp2 && not (Clp.elem (w32 15) clp2));
  check "CLP2: iter enumerates the interval (descending; sorted = the set)"
    (List.sort compare (List.map Cbat_word.to_int_exn (Clp.iter clp2)) = [ 10; 12; 14; 16; 18 ]);
  check "CLP2: cardinality equals the iter length (bounds sanity)"
    (Cbat_word.to_int_exn (Clp.cardinality clp2) = List.length (Clp.iter clp2));
  check "CLP3: of_list ~width:16 [3;1;2] -> {1,2,3} (sorted, deduped)"
    (let c = Clp.of_list ~width:16 [ w32 3; w32 1; w32 2 ] in
     Clp.bitwidth c = 16
     && Cbat_word.to_int_exn (Clp.cardinality c) = 3
     && Clp.min_elem c = Some (Cbat_word.of_int ~width:16 1)
     && Clp.max_elem c = Some (Cbat_word.of_int ~width:16 3)
     && Clp.elem (Cbat_word.of_int ~width:16 2) c);
  check "CLP4: of_list [] is bottom" (Clp.is_bottom (Clp.of_list ~width:32 []));
  check "CLP5: bottom: cardn 0, empty iter, no min elem"
    (let b = Clp.bottom 32 in
     Clp.is_bottom b
     && Cbat_word.to_int_exn (Clp.cardinality b) = 0
     && Clp.iter b = []
     && Clp.min_elem b = None);
  check "CLP6: top: is_top, not bottom, absorbs by subset"
    (let t = Clp.top 32 in
     Clp.is_top t && (not (Clp.is_bottom t)) && Clp.subset clp1 t && Clp.subset t t);
  check "CLP7a: create_ascending basic properties and bounds"
    (let asc = Clp.create_ascending ~width:64 ~base:(Cbat_word.of_int ~width:64 8) ~step:(Cbat_word.of_int ~width:64 8) in
     Clp.is_ascending asc
     && Clp.is_infinite asc
     && not (Clp.is_descending asc)
     && not (Clp.is_circular asc)
     && Clp.min_elem asc = Some (Cbat_word.of_int ~width:64 8)
     && Clp.min_elem_signed asc = Some (Cbat_word.of_int ~width:64 8));
  check "CLP7b: create_descending basic properties and bounds"
    (let desc = Clp.create_descending ~width:64 ~base:(Cbat_word.of_int ~width:64 64) ~step:(Cbat_word.of_int ~width:64 8) in
     Clp.is_descending desc
     && Clp.is_infinite desc
     && not (Clp.is_ascending desc)
     && not (Clp.is_circular desc)
     && Clp.max_elem desc = Some (Cbat_word.of_int ~width:64 64)
     && Clp.max_elem_signed desc = Some (Cbat_word.of_int ~width:64 64));
  check "CLP7c: directional rays canonicalize singletons to Finite"
    (let asc1 = Clp.create_ascending ~width:64 ~base:(Cbat_word.ones 64) ~step:(Cbat_word.of_int ~width:64 8) in
     let desc1 = Clp.create_descending ~width:64 ~base:(Cbat_word.of_int ~width:64 7) ~step:(Cbat_word.of_int ~width:64 8) in
     not (Clp.is_ascending asc1)
     && not (Clp.is_infinite asc1)
     && not (Clp.is_descending desc1)
     && not (Clp.is_infinite desc1));
  ())
;
(  let s5 = Clp.create (w32 5) in
  let s9 = Clp.create (w32 9) in
  let u = Clp.join s5 s9 in
  check "CLP8: join of disjoint singletons contains both operands"
    (Clp.elem (w32 5) u && Clp.elem (w32 9) u);
  check "CLP8: join is above its operands (precedes = subset)"
    (Clp.precedes s5 u && Clp.precedes s9 u);
  check "CLP9: join is commutative" (Clp.equal (Clp.join s5 s9) (Clp.join s9 s5));
  check "CLP10: bottom is the join identity (both orders)"
    (Clp.equal (Clp.join s5 (Clp.bottom 32)) s5 && Clp.equal (Clp.join (Clp.bottom 32) s5) s5);
  check "CLP11: top absorbs in join" (Clp.is_top (Clp.join s5 (Clp.top 32)));
  check "CLP19: join of equal single points is the point" (Clp.equal (Clp.join s5 s5) s5);

  (* Overlapping meet: {10,12,14,16,18} n {14,16,18} = {14,16,18} exactly. *)
  let q = Clp.of_list ~width:32 [ w32 14; w32 16; w32 18 ] in
  let m = Clp.meet clp2 q in
  check "CLP12: meet of overlapping intervals: intersection members only"
    (Clp.elem (w32 14) m
    && Clp.elem (w32 16) m
    && Clp.elem (w32 18) m
    && (not (Clp.elem (w32 10) m))
    && not (Clp.elem (w32 17) m));
  check "CLP13: top is the meet identity; bottom is the meet zero"
    (Clp.equal (Clp.meet clp2 (Clp.top 32)) clp2 && Clp.is_bottom (Clp.meet clp2 (Clp.bottom 32)));
  check "CLP14: meet absorption: (p U q) n p = p"
    (let p = clp2 and q2 = Clp.create (w32 20) in
     let un = Clp.join p q2 in
     Clp.equal (Clp.meet un p) p && Clp.equal (Clp.meet p un) p);
  check "CLP15: meet of disjoint single points is bottom"
    (Clp.is_bottom (Clp.meet (Clp.create (w32 10)) (Clp.create (w32 11))));
  check "CLP16: single-point meet: {10} n {10,12,14,16,18} = {10}"
    (Clp.equal (Clp.meet (Clp.create (w32 10)) clp2) (Clp.create (w32 10)));
  check "CLP17: meet is below join" (Clp.precedes (Clp.meet clp2 q) (Clp.join clp2 q));
  check "CLP18: widen_join p p = p; widen_join bottom {5} = top"
    (Clp.equal (Clp.widen_join s5 s5) s5 && Clp.is_top (Clp.widen_join (Clp.bottom 32) s5));
  ())
;
(  let s = Fs.of_list ~width:32 [ w32 1; w32 2; w32 3 ] in
  check "FS1: of_list basics (cardn/bitwidth/min/max/elem)"
    (Fs.bitwidth s = 32
    && Cbat_word.to_int_exn (Fs.cardinality s) = 3
    && Fs.min_elem s = Some (w32 1)
    && Fs.max_elem s = Some (w32 3)
    && Fs.elem (w32 2) s
    && not (Fs.elem (w32 4) s));
  check "FS1: singleton"
    (let one = Fs.singleton (w32 7) in
     Fs.elem (w32 7) one && Cbat_word.to_int_exn (Fs.cardinality one) = 1);
  check "FS2: lift1 unops are involutive (neg, lnot)"
    (Fs.equal (Fs.neg (Fs.neg s)) s && Fs.equal (Fs.lnot (Fs.lnot s)) s);
  check "FS3: lift2 union/intersection"
    (let a = Fs.of_list ~width:32 [ w32 1; w32 2 ] in
     let b = Fs.of_list ~width:32 [ w32 2; w32 3 ] in
     Fs.equal (Fs.union a b) (Fs.of_list ~width:32 [ w32 1; w32 2; w32 3 ])
     && Fs.equal (Fs.intersection a b) (Fs.of_list ~width:32 [ w32 2 ]));
  check "FS4: join/meet are the lattice aliases of union/intersection"
    (let a = Fs.of_list ~width:32 [ w32 1; w32 2 ] in
     let b = Fs.of_list ~width:32 [ w32 2; w32 3 ] in
     Fs.equal (Fs.join a b) (Fs.union a b)
     && Fs.equal (Fs.meet a b) (Fs.of_list ~width:32 [ w32 2 ]));
  check "FS5: precedes/equal"
    (Fs.precedes (Fs.singleton (w32 1)) s
    && (not (Fs.precedes s (Fs.singleton (w32 1))))
    && Fs.equal s s
    && not (Fs.equal (Fs.singleton (w32 1)) s));
  check "FS6: bottom absorption"
    (let b = Fs.bottom 32 in
     Fs.equal (Fs.join s b) s
     && Fs.equal (Fs.join b s) s
     && Fs.equal (Fs.meet s b) b
     && Cbat_word.to_int_exn (Fs.cardinality (Fs.meet s b)) = 0);
  check "FS7: add: {1,2} + {10} = {11,12}"
    (let a = Fs.of_list ~width:32 [ w32 1; w32 2 ] in
     let r = Fs.add a (Fs.singleton (w32 10)) in
     Fs.elem (w32 11) r && Fs.elem (w32 12) r && Cbat_word.to_int_exn (Fs.cardinality r) = 2);
  check "FS8: extract/cast/concat width sanity"
    (let one = Fs.singleton (w32 1) in
     Fs.bitwidth (Fs.extract ~hi:7 ~lo:0 one) = 8
     && Fs.bitwidth (Fs.cast Bil.UNSIGNED 64 one) = 64
     && Fs.bitwidth (Fs.concat one (Fs.singleton (Cbat_word.of_int ~width:16 1))) = 48);

  (* Width mismatch yields false, not an assert abort. *)
  let f32 = Fs.of_list ~width:32 [ w32 1; w32 2 ] in
  let f64 = Fs.of_list ~width:64 [ w64 1; w64 2 ] in
  check "FS9 (delta #1): equal on width-mismatched sets is false (no assert)"
    ((not (Fs.equal f32 f64)) && not (Fs.equal f64 f32));
  check "FS9 (delta #1): precedes on width-mismatched sets is false"
    ((not (Fs.precedes f32 f64)) && not (Fs.precedes f64 f32));
  ())
;
(  check "ML1: add on bottom stays bottom" (Map.equal (Map.add Map.bottom ~key:0 ~data:1) Map.bottom);
  check "ML2: join_add/meet_add on bottom stay bottom"
    (Map.equal (Map.join_add Map.bottom ~key:3 ~data:(-1)) Map.bottom
    && Map.equal (Map.meet_add Map.bottom ~key:23 ~data:(-21)) Map.bottom);
  check "ML3: find on bottom/top returns bottom/top"
    (Map.find () Map.bottom 10 = IntLattice.bottom && Map.find () Map.top 10 = IntLattice.top);
  check "ML4: meet/join top-bottom combos"
    (Map.equal (Map.meet Map.top Map.bottom) Map.bottom
    && Map.equal (Map.meet Map.bottom Map.top) Map.bottom
    && Map.equal (Map.join Map.top Map.bottom) Map.top
    && Map.equal (Map.join Map.bottom Map.top) Map.top
    && Map.equal (Map.meet Map.top Map.top) Map.top
    && Map.equal (Map.join Map.bottom Map.bottom) Map.bottom);
  check "ML5: add then find roundtrip; missing key reads top"
    (let m = Map.add Map.top ~key:5 ~data:42 in
     Map.find () m 5 = 42 && Map.find () m 6 = IntLattice.top);
  check "ML6: join_add/meet_add merge with the stored value"
    (let m = Map.join_add (Map.add Map.top ~key:5 ~data:3) ~key:5 ~data:10 in
     Map.find () m 5 = 10
     && Map.find () (Map.meet_add (Map.add Map.top ~key:5 ~data:10) ~key:5 ~data:3) 5 = 3);
  check "ML7: equal/precedes on small maps"
    (Map.equal Map.bottom Map.bottom
    && (not (Map.equal Map.bottom Map.top))
    && Map.precedes Map.bottom Map.top
    && (not (Map.precedes Map.top Map.bottom))
    && Map.precedes (Map.add Map.top ~key:1 ~data:2) (Map.add Map.top ~key:1 ~data:3));
  ())
;
(  check "WO1: dom_size i ~width:w = 2^i as a w-bit word (zero if w = i)"
    (Cbat_word.to_int_exn (Wo.dom_size 3 ~width:4) = 8
    && Cbat_word.bitwidth (Wo.dom_size 3 ~width:4) = 4
    && Cbat_word.to_int_exn (Wo.dom_size 60 ~width:61) = 0x1000000000000000
    && Cbat_word.is_zero (Wo.dom_size 3 ~width:3));
  check "WO2: cap_at_width keeps small words, saturates large ones"
    (let c255 = Wo.cap_at_width ~width:8 (Cbat_word.of_int ~width:32 255) in
     Cbat_word.to_int_exn c255 = 255
     && Cbat_word.bitwidth c255 = 8
     && Cbat_word.to_int_exn (Wo.cap_at_width ~width:2 (Cbat_word.of_int ~width:8 5)) = 3);
  check "WO3: add_exact/mul_exact widen to the exact result"
    (let s = Wo.add_exact (Cbat_word.of_int ~width:8 200) (Cbat_word.of_int ~width:8 100) in
     Cbat_word.bitwidth s = 9
     && Cbat_word.to_int_exn s = 300
     &&
     let p = Wo.mul_exact (Cbat_word.of_int ~width:4 15) (Cbat_word.of_int ~width:4 15) in
     Cbat_word.bitwidth p = 8 && Cbat_word.to_int_exn p = 225);
  check "WO4: factor_2s pulls out the 2-power"
    (let odd, twos = Wo.factor_2s (Cbat_word.of_int ~width:8 12) in
     Cbat_word.to_int_exn odd = 3
     && twos = 2
     &&
     let odd', twos' = Wo.factor_2s (Cbat_word.of_int ~width:8 16) in
     Cbat_word.to_int_exn odd' = 1 && twos' = 4);
  check "WO5: lead_1_bit"
    (Wo.lead_1_bit (Cbat_word.of_int ~width:8 5) = Some 2
    && Wo.lead_1_bit (Cbat_word.of_int ~width:8 128) = Some 7
    && Wo.lead_1_bit (Cbat_word.zero 8) = None);
  check "WO6: is_one / succ_exact / lshift_exact"
    (Wo.is_one (Cbat_word.of_int ~width:8 1)
    && (not (Wo.is_one (Cbat_word.of_int ~width:8 0)))
    &&
    let s = Wo.succ_exact (Cbat_word.of_int ~width:8 255) in
    Cbat_word.bitwidth s = 9
    && Cbat_word.to_int_exn s = 256
    &&
    let l = Wo.lshift_exact (Cbat_word.of_int ~width:8 1) 4 in
    Cbat_word.bitwidth l = 12 && Cbat_word.to_int_exn l = 16);
  check "WO7: gt_int" (Wo.gt_int (Cbat_word.of_int ~width:8 7) 5 && not (Wo.gt_int (Cbat_word.of_int ~width:8 3) 5));
  ())
(* Set difference: exact when representable, identity otherwise — never a stop. *)
;
(  let w3 = Cbat_word.of_int ~width:3 in
  (* Interval builder: [lo, hi] step 1. *)
  let int32 ~lo ~hi =
    Clp.create ~width:32 ~step:(w32 1) ~cardn:(Cbat_word.of_int ~width:33 (hi - lo + 1)) (w32 lo)
  in
  (* W1: interior run is two pieces — identity. *)
  let a = int32 ~lo:0 ~hi:9 in
  let b = int32 ~lo:3 ~hi:5 in
  check
    "W1: [0,9] \\ [3,5] — the interior run is two pieces, not one CLP: the identity (the sound \
     over-approximation)"
    (Clp.equal (Clp.diff a b) a && Clp.subset (Clp.diff a b) a);
  (* W1b: boundary-touch runs are exact single CLPs. *)
  let d_s = Clp.diff a (int32 ~lo:0 ~hi:2) in
  let d_e = Clp.diff a (int32 ~lo:7 ~hi:9) in
  check "W1b: the boundary-touch runs are exact — [0,9] \\ [0,2] = {3..9}; [0,9] \\ [7,9] = {0..6}"
    (Clp.cardinality d_s = w33 7
    && Clp.elem (w32 3) d_s
    && Clp.elem (w32 9) d_s
    && (not (Clp.elem (w32 2) d_s))
    && Clp.cardinality d_e = w33 7
    && Clp.elem (w32 0) d_e
    && Clp.elem (w32 6) d_e
    && not (Clp.elem (w32 7) d_e));
  (* W2: full domain minus singleton = wrapped complement. *)
  let c = w64 0x2a in
  let d2 = Clp.diff (Clp.top 64) (Clp.create c) in
  check "W2: full64 \\ {0x2a} = the wrapped complement (cardn 2^64 − 1, exact)"
    (Clp.cardinality d2
     = Cbat_word.sub (Cbat_word.lshift (Cbat_word.of_int ~width:65 1) (Cbat_word.of_int ~width:65 64)) (Cbat_word.of_int ~width:65 1)
    && Clp.elem (w64 0x2b) d2
    && Clp.elem (w64 0x29) d2
    && not (Clp.elem c d2));
  (* W3: bottom/absorption cases. *)
  check
    "W3: the bottom/absorption — diff bottom a = bottom; diff a bottom = a; diff a a = bottom; the \
     singleton cases"
    (Clp.is_bottom (Clp.diff (Clp.bottom 32) a)
    && Clp.equal (Clp.diff a (Clp.bottom 32)) a
    && Clp.is_bottom (Clp.diff a a)
    && Clp.is_bottom (Clp.diff (Clp.create (w32 5)) (Clp.create (w32 5)))
    && Clp.equal (Clp.diff (Clp.create (w32 5)) (Clp.create (w32 7))) (Clp.create (w32 5)));
  (* W4: diff contract on exact cases — disjoint, ⊆ a, complete. *)
  check "W4: the diff contract — (diff a b) ∩ b = ∅ element-wise; diff ⊆ a; a\\b ⊆ diff"
    (List.for_all (fun w -> not (Clp.elem w (int32 ~lo:0 ~hi:2))) (Clp.iter d_s)
    && Clp.subset d_s a
    && List.for_all
         (fun w -> (Clp.elem w a && not (Clp.elem w (int32 ~lo:0 ~hi:2))) = Clp.elem w d_s)
         (Clp.iter a)
    && List.for_all (fun w -> not (Clp.elem w (int32 ~lo:7 ~hi:9))) (Clp.iter d_e)
    && Clp.subset d_e a
    && not (Clp.elem c (Clp.diff (Clp.top 64) (Clp.create c))));
  (* W5: gapped subtraction is the identity. *)
  let a5 = Clp.create ~width:32 ~step:(w32 2) ~cardn:(w33 5) (w32 0) in
  (* {0,2,4,6,8} *)
  let b5 = Clp.create ~width:32 ~step:(w32 4) ~cardn:(w33 3) (w32 0) in
  (* {0,4,8} *)
  check
    "W5: the gapped subtraction is the identity — {0,2,4,6,8} \\ {0,4,8} = {0,2,4,6,8} (not a run)"
    (Clp.equal (Clp.diff a5 b5) a5);
  (* W6: singleton removal — exact at boundaries, identity inside. *)
  let a6 = int32 ~lo:0 ~hi:10 in
  let d6b = Clp.diff a6 (Clp.create (w32 0)) in
  let d6e = Clp.diff a6 (Clp.create (w32 10)) in
  let d6i = Clp.diff a6 (Clp.create (w32 4)) in
  check
    "W6: the singleton removal — the boundary singletons exact ([0,10] \\ {0} = {1..10}; \\ {10} = \
     {0..9}); the interior singleton is the identity"
    (Clp.cardinality d6b = w33 10
    && Clp.elem (w32 1) d6b
    && (not (Clp.elem (w32 0) d6b))
    && Clp.cardinality d6e = w33 10
    && Clp.elem (w32 0) d6e
    && (not (Clp.elem (w32 10) d6e))
    && Clp.equal d6i a6);
  (* W7: FinSet diffs — exact; mixed-width pair shares nothing. *)
  check "W7: the FinSet diffs — exact; the mixed-width pair shares no elements"
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
         (Ws.of_list ~width:32 [ w32 1; w32 2 ]));
  (* W8: Clp\\FinSet — boundary runs exact; interior and gaps fall back to identity. *)
  let p8 = Ws.of_clp (int32 ~lo:0 ~hi:10) in
  let d8 = Ws.diff p8 (Ws.of_list ~width:32 [ w32 0; w32 1; w32 2 ]) in
  check "W8: the Clp\\FinSet — the boundary-touch run removed exactly: [0,10] \\ {0,1,2} = {3..10}"
    (Ws.cardinality d8 = Cbat_word.of_int ~width:33 8
    && List.for_all
         (fun w -> Ws.elem w d8)
         [ w32 3; w32 4; w32 5; w32 6; w32 7; w32 8; w32 9; w32 10 ]
    && (not (Ws.elem (w32 0) d8))
    && not (Ws.elem (w32 2) d8));
  let d8i = Ws.diff p8 (Ws.of_list ~width:32 [ w32 3; w32 4; w32 5 ]) in
  check "W8b: the Clp\\FinSet interior run — the identity (the two pieces are not one CLP)"
    (Ws.equal d8i p8);
  let d8c = Ws.diff p8 (Ws.of_list ~width:32 [ w32 3; w32 5 ]) in
  check "W8c: the Clp\\FinSet with gaps — the identity (the sound over-approximation)"
    (Ws.equal d8c p8);
  (* W9: lnot/neg exact mirror rows. *)
  let l9 = Clp.create ~width:3 ~step:(w3 2) ~cardn:(Cbat_word.of_int ~width:4 3) (w3 0) in
  (* {0,2,4} *)
  check
    "W9: lnot/neg — the exact mirror rows: lnot {0,2,4} = {7,5,3}; neg {0,2,4} = {0,6,4}; the top \
     fixed; the singleton mirrors"
    (Clp.elem (w3 7) (Clp.lnot l9)
    && Clp.elem (w3 5) (Clp.lnot l9)
    && Clp.elem (w3 3) (Clp.lnot l9)
    && (not (Clp.elem (w3 0) (Clp.lnot l9)))
    && Clp.elem (w3 0) (Clp.neg l9)
    && Clp.elem (w3 6) (Clp.neg l9)
    && Clp.elem (w3 4) (Clp.neg l9)
    && (not (Clp.elem (w3 2) (Clp.neg l9)))
    && Ws.is_top (Ws.lnot (Ws.top 32))
    && Ws.is_top (Ws.neg (Ws.top 32))
    && Ws.equal (Ws.lnot (Ws.of_list ~width:3 [ w3 5 ])) (Ws.of_list ~width:3 [ w3 2 ])
    && Ws.equal (Ws.neg (Ws.of_list ~width:3 [ w3 5 ])) (Ws.of_list ~width:3 [ w3 3 ]));
  ())
let run_policy () =
(* not_implemented degrades to top and logs. *)
(  check "P5: not_implemented ~top degrades to top without raising"
    (Cbat_vsa_utils.not_implemented ~top:42 "policy5-probe" = 42);
  let raised f =
    try
      f ();
      false
    with Cbat_vsa_utils.NotImplemented _ -> true
  in
  check "P5: not_implemented without a top still raises NotImplemented"
    (raised (fun () -> Cbat_vsa_utils.not_implemented "no-top-probe"));

  (* Every hit logs; subscribe to the BAP event stream and check. *)
  let hits = ref [] in
  Bap_future.Std.Stream.observe Bap.Std.Event.stream (fun ev ->
      match ev with
      | Event.Log.Message info -> hits := (info.section, info.message) :: !hits
      | _ -> ());
  ignore (Cbat_vsa_utils.not_implemented ~top:7 "policy5-log-probe");
  check "P5: the top-path hit emits a warning log line (section cbat_vsa)"
    (List.exists
       (fun (sec, msg) -> sec = "cbat_vsa" && contains_substring msg "policy5-log-probe")
       !hits);
  ())
(* CLP meet wrap returns the safe operand, not bottom. *)
;
(  let a = Clp.of_list ~width:32 [ w32 10; w32 12; w32 14; w32 16; w32 18 ] in
  let b = Clp.of_list ~width:32 [ w32 16; w32 17; w32 18; w32 19 ] in
  (* Wrapping intersection returns the wider operand containing the true meet. *)
  let m = Clp.meet a b in
  check "A1: meet wrap {10..18} n {16..19} is NOT bottom (live path)" (not (Clp.is_bottom m));
  check "A1: ... and still contains the true intersection {16,18}"
    (Clp.elem (w32 16) m && Clp.elem (w32 18) m);
  check "A1: ... it is the wider operand {10,12,14,16,18} (over-approx)"
    (Clp.elem (w32 10) m && Clp.elem (w32 12) m && Clp.elem (w32 14) m);
  (* Second wrap pair, both finite: {3,4,5} n {0,2,4} = {4}. *)
  let m2 =
    Clp.meet
      (Clp.of_list ~width:32 [ w32 3; w32 4; w32 5 ])
      (Clp.of_list ~width:32 [ w32 0; w32 2; w32 4 ])
  in
  check "A2: wrap {3,4,5} n {0,2,4} not bottom, contains 4"
    ((not (Clp.is_bottom m2)) && Clp.elem (w32 4) m2);
  (* Genuinely-empty meets stay bottom. *)
  check "A3: genuinely disjoint meets are still bottom (unchanged)"
    (Clp.is_bottom (Clp.meet (Clp.create (w32 10)) (Clp.create (w32 11))));
  check "A3: bottom is still the meet zero; top the meet identity"
    (Clp.is_bottom (Clp.meet clp2 (Clp.bottom 32)) && Clp.equal (Clp.meet clp2 (Clp.top 32)) clp2);
  ())
(* div/sdiv: a zero-containing non-singleton divisor returns top; exactly
   {0} is the word semantics (x/0 = ones), never bottom. *)
;
(  let d1 = Clp.of_list ~width:32 [ w32 1; w32 2 ] in
  let d0 = Clp.of_list ~width:32 [ w32 0; w32 1 ] in
  check "D3-1: div by a set containing 0 -> top, no raise" (Clp.is_top (Clp.div d1 d0));
  check "D3-2: sdiv by a set containing 0 -> top, no raise" (Clp.is_top (Clp.sdiv d1 d0));
  check "D3-3: div by exactly {0} -> the word semantics (x/0 = ones)"
    (let r = Clp.div d1 (Clp.create (Cbat_word.zero 32)) in
     Clp.min_elem r = Some (Cbat_word.ones 32)
     && Clp.max_elem r = Some (Cbat_word.ones 32));
  check "D3-4: sdiv by exactly {0} -> the word semantics (x/0 = ones)"
    (let r = Clp.sdiv d1 (Clp.create (Cbat_word.zero 32)) in
     Clp.min_elem r = Some (Cbat_word.ones 32)
     && Clp.max_elem r = Some (Cbat_word.ones 32));
  check "D3-5: div by a nonzero singleton still computes (no regression)"
    (let r = Clp.div (Clp.create (w32 10)) (Clp.create (w32 2)) in
     Clp.min_elem r = Some (w32 5) && Clp.max_elem r = Some (w32 5));
  ())
(* Width-mismatch totality: mismatched ops return safe values, never raise. *)
;
(  let f32 = Fs.of_list ~width:32 [ w32 1; w32 2 ] in
  let f64 = Fs.of_list ~width:64 [ w64 1; w64 2 ] in
  check "D1-1: fin_set elem on a width-mismatched word -> false (no assert)"
    ((not (Fs.elem (w32 1) f64)) && not (Fs.elem (w64 1) f32));
  check "D1-2: fin_set overlap on width-mismatched sets -> false (no assert)"
    ((not (Fs.overlap f32 f64)) && not (Fs.overlap f64 f32));
  check "D1-3: fin_set nearest_pred on a width-mismatched word -> None"
    (Fs.nearest_pred (w32 1) f64 = None);
  check "D1-4: intersect_generic width mismatch -> input unchanged (no assert)"
    (let r = Fs.intersect_generic (module Clp) f32 (Clp.of_list ~width:64 [ w64 1 ]) in
     Fs.bitwidth r = 32 && Fs.elem (w32 1) r && Fs.elem (w32 2) r);
  check "D1-5: composite meet on width-mismatched sets -> no assert, not bottom"
    (let r = Ws.meet (Ws.of_list ~width:32 [ w32 1; w32 2 ]) (Ws.of_list ~width:64 [ w64 1 ]) in
     (not (Ws.is_bottom r)) && Ws.bitwidth r = 64 && Ws.elem (w64 1) r);
  check "D1-6: composite meet on matching widths is still exact"
    (let a = Ws.of_list ~width:32 [ w32 1; w32 2 ] in
     let b = Ws.of_list ~width:32 [ w32 2; w32 3 ] in
     Ws.equal (Ws.meet a b) (Ws.of_list ~width:32 [ w32 2 ]));
  ())
(* widen_join fallbacks: non-subset inputs join instead of asserting. *)
;
(  let s5 = Clp.create (w32 5) in
  let s9 = Clp.create (w32 9) in
  let w = Clp.widen_join s5 s9 in
  check "D2-1: CLP widen_join of non-subset singletons -> join, no assert"
    (Clp.elem (w32 5) w && Clp.elem (w32 9) w);
  check "D2-2: CLP widen_join of equal inputs is still the input"
    (Clp.equal (Clp.widen_join s5 s5) s5);
  check "D2-3: CLP widen_join of a subset pair still widens (bottom {5} -> top)"
    (Clp.is_top (Clp.widen_join (Clp.bottom 32) s5));
  (* Val cells with mismatched indices. *)
  let v32 = Mem.Val.create (Ws.of_list ~width:32 [ w32 1 ]) LittleEndian in
  let v64 = Mem.Val.create (Ws.of_list ~width:64 [ w64 1 ]) LittleEndian in
  let vbe = Mem.Val.create (Ws.of_list ~width:32 [ w32 1 ]) BigEndian in
  check "D2-4: Val.equal/precedes on idx-mismatched cells -> false (no assert)"
    ((not (Mem.Val.equal v32 v64))
    && (not (Mem.Val.precedes v32 v64))
    && not (Mem.Val.equal v32 vbe));
  check "D2-5: Val.join on idx-mismatched cells -> top fallback (no assert)"
    (Mem.Val.is_top (Mem.Val.join v32 v64) && Mem.Val.is_top (Mem.Val.join v32 vbe));
  check "D2-6: Val.meet on idx-mismatched cells -> bottom fallback (no assert)"
    (Mem.Val.is_bottom (Mem.Val.meet v32 v64));
  check "D2-7: Val.widen_join on idx-mismatched cells -> top fallback (no assert)"
    (Mem.Val.is_top (Mem.Val.widen_join v32 v64));
  check "D2-8: Val ops on matching indices still work (no regression)"
    (let v1 = Mem.Val.create (Ws.of_list ~width:32 [ w32 1 ]) LittleEndian in
     Mem.Val.equal v1 v32 && Ws.elem (w32 1) (Mem.Val.data (Mem.Val.join v1 v32)));
  (* widen_join on non-preceding maps falls back to join. *)
  let m1 = mk_mem ~key:(Ws.singleton (w32 0)) ~data:(Ws.of_list ~width:32 [ w32 1; w32 2 ]) in
  let m2 = mk_mem ~key:(Ws.singleton (w32 0)) ~data:(Ws.of_list ~width:32 [ w32 3; w32 4 ]) in
  let mw = Mem.widen_join m1 m2 in
  check "D2-9: Mem.widen_join of non-preceding maps -> join fallback (no assert)"
    (let v =
       Mem.find
         (Mem.Val.get_idx (Mem.Val.create (Ws.of_list ~width:32 [ w32 0 ]) LittleEndian))
         mw
         (key_of (Ws.singleton (w32 0)))
     in
     let d = Mem.Val.data v in
     Ws.elem (w32 1) d && Ws.elem (w32 2) d && Ws.elem (w32 3) d && Ws.elem (w32 4) d);
  check "D2-10: Mem.widen_join of equal maps stays equal (no regression)"
    (Mem.equal (Mem.widen_join m1 m1) m1);
  ())
(* Landmark extrapolation: stable bounds kept, unstable translated by growth·steps. *)
;
(  (* Widening soundness pins: widen_join contains the join. *)
  let q9 = Clp.interval ~width:32 (w32 0) (w32 1) in
  let g9 = Clp.interval ~width:32 (w32 0) (w32 2) in
  let r1 = Clp.widen_join q9 g9 in
  check "EX1: widen_join contains join (extrapolate stub)" (Clp.subset g9 r1);
  check "EX1b: the extrapolation contains the join (soundness)" (Clp.subset g9 r1);
  let r2 = Clp.widen_join q9 g9 in
  check "EX2: widen_join sound" (Clp.subset g9 r2);
  let d1 = Clp.create (Cbat_word.neg (w32 16)) ~step:(w32 8) ~cardn:(w32 1) in
  let d2 = Clp.create (Cbat_word.neg (w32 24)) ~step:(w32 8) ~cardn:(w32 2) in
  let r3 = Clp.widen_join d1 d2 in
  check "EX3: widen_join sound" (Clp.subset d2 r3);
  check "EX4: widen_join idempotent" (Clp.equal (Clp.widen_join g9 g9) g9);
  let big1 = Clp.interval ~width:64 (w64 0) (Cbat_word.of_int ~width:64 0x100000000) in
  let big2 = Clp.interval ~width:64 (w64 0) (Cbat_word.of_int ~width:64 0x10000000000) in
  let r5 = Clp.widen_join big1 big2 in
  check "EX5: widen_join sound" (Clp.subset big2 r5);
  let s1 = Clp.interval ~width:32 (w32 0) (w32 0) in
  let s2 = Clp.create (w32 0) ~step:(w32 3) ~cardn:(w32 2) in
  let r6 = Clp.widen_join s1 s2 in
  check "EX6: widen_join sound" (Clp.subset s2 r6);
  ())
let run_agreement () =
(  let w3 = Cbat_word.of_int ~width:3 in
  let w4 = Cbat_word.of_int ~width:4 in
  let w63 = Cbat_word.of_int ~width:63 in
  let w64i (v : int64) = Cbat_word.of_int64 ~width:64 v in
  let w63i (v : int64) = Cbat_word.of_int64 ~width:63 v in
  let ones64 = w64i (-1L) in
  let max63 = w63i Int64.max_int in

  (* G1: width-64 singleton with top bit set stays unsigned. *)
  let c1 = Clp.create ones64 in
  check
    "O4c-1: width-64 singleton 0xFFFF_FFFF_FFFF_FFFF is unsigned — min = max = itself, elem holds, \
     0 not in"
    (Clp.min_elem c1 = Some ones64
    && Clp.max_elem c1 = Some ones64
    && Clp.elem ones64 c1
    && (not (Clp.elem (w64 0) c1))
    && (not (Clp.is_top c1))
    && not (Clp.is_bottom c1));

  (* G2: top 64 has cardn 2^64 — the Big-fallback class. *)
  let t64 = Clp.top 64 in
  check
    "O4c-2: top 64 is the 2^64-cardinality class — is_top/is_infinite, absorbs a singleton (the \
     Big fallback, not I64-truncated)"
    (Clp.is_top t64 && Clp.is_infinite t64
    && (not (Clp.is_bottom t64))
    && Clp.subset (Clp.create (w64 0)) t64
    && Clp.elem ones64 t64
    && Clp.elem (w64 0) t64);

  (* G3: top 63 fits Int64 — the I64 boundary. *)
  let t63 = Clp.top 63 in
  check
    "O4c-3: top 63 is the 2^63-cardinality class (fits Int64 — the I64 boundary) — \
     is_top/is_infinite"
    (Clp.is_top t63 && Clp.is_infinite t63 && not (Clp.is_bottom t63));

  (* G4: width-63 singleton at 2^63−1 — no sign extension. *)
  let c4 = Clp.create max63 in
  check
    "O4c-4: width-63 singleton 2^63−1 is unsigned and exact (top bit of a 63-bit word; min = max = \
     itself)"
    (Clp.min_elem c4 = Some max63
    && Clp.max_elem c4 = Some max63
    && Clp.elem max63 c4
    && (not (Clp.elem (w63 0) c4))
    && Cbat_word.to_int64_exn max63 = Int64.max_int);

  (* G5: 64-bit wrap add — {0xFFFF_FFFF_FFFF_FFFF} + {1} = {0}. *)
  let a5 = Clp.add (Clp.create ones64) (Clp.create (w64 1)) in
  check "O4c-5: 64-bit wrap add — {0xFFFF_FFFF_FFFF_FFFF} + {1} = {0}"
    (Clp.equal a5 (Clp.create (w64 0)) && Clp.elem (w64 0) a5 && not (Clp.elem (w64 1) a5));

  (* G6: 63-bit wrap sub — {0} − {1} = {2^63 − 1}. *)
  let a6 = Clp.sub (Clp.create (w63 0)) (Clp.create (w63 1)) in
  check "O4c-6: 63-bit wrap sub — {0} − {1} = {2^63 − 1}"
    (Clp.equal a6 (Clp.create max63) && Clp.elem max63 a6 && not (Clp.elem (w63 0) a6));

  (* G7: path-independent algebraic contract. *)
  let p = Clp.create ~width:64 ~step:(w64 2) ~cardn:(Cbat_word.of_int ~width:65 5) (w64 10) in
  let q = Clp.create ~width:64 ~step:(w64 4) ~cardn:(Cbat_word.of_int ~width:65 3) (w64 6) in
  clp_agree "O4c-7a: add commutative" (Clp.add p q) (Clp.add q p);
  clp_agree "O4c-7b: meet commutative" (Clp.meet p q) (Clp.meet q p);
  clp_agree "O4c-7c: join commutative" (Clp.join p q) (Clp.join q p);
  clp_agree "O4c-7d: meet idempotent" (Clp.meet p p) p;

  (* G8: step 0 canonizes to the singleton. *)
  let s8 = Clp.create ~width:32 ~step:(w32 0) ~cardn:(w33 1) (w32 10) in
  check "O4c-8: step 0 with cardn 1 canonizes to the singleton {10}"
    (Clp.equal s8 (Clp.create (w32 10))
    && Clp.iter s8 = [ w32 10 ]
    && Clp.elem (w32 10) s8
    && not (Clp.elem (w32 11) s8));

  (* G9: cardn 0 is bottom. *)
  let s9 = Clp.create ~width:32 ~step:(w32 1) ~cardn:(w33 0) (w32 10) in
  check "O4c-9: cardn 0 is bottom (empty iter, no min)"
    (Clp.is_bottom s9 && Clp.iter s9 = [] && Clp.min_elem s9 = None);

  (* G10: cardn-2 wrap flips the pair to ascending order. *)
  let s10 = Clp.create ~width:32 ~step:(w32 0xFFFFFFFE) ~cardn:(w33 2) (w32 0xFFFFFFF0) in
  check "O4c-10: cardn-2 wrap flips the pair to ascending order (min 0xFFFFFFEE, max 0xFFFFFFF0)"
    (Clp.min_elem s10 = Some (w32 0xFFFFFFEE)
    && Clp.max_elem s10 = Some (w32 0xFFFFFFF0)
    && Clp.elem (w32 0xFFFFFFEE) s10
    && Clp.elem (w32 0xFFFFFFF0) s10
    && not (Clp.elem (w32 0xFFFFFFEF) s10));

  (* G11: step·cardn = 2^w is infinite but not top. *)
  let s11 = Clp.create ~width:3 ~step:(w3 2) ~cardn:(w4 4) (w3 0) in
  check "O4c-11: step·cardn = 2^w (2·4 = 8 = 2^3) is infinite — {0,2,4,6}, cardn 4, 7 not in"
    (Clp.is_infinite s11
    && (not (Clp.is_top s11))
    && Clp.cardinality s11 = w4 4
    && Clp.elem (w3 6) s11
    && not (Clp.elem (w3 7) s11));

  (* G12: intersection anchor clamps to the minimum — no spurious top element. *)
  let lo12 = Clp.create ~width:32 ~step:(w32 1) ~cardn:(w33 9) (w32 0) in
  let circ12 = Clp.create ~width:32 ~step:(w32 1) ~cardn:(w33 10) (w32 0xFFFFFFFF) in
  let m12 = Clp.meet lo12 circ12 in
  check
    "O4c-12: R2-1 — meet {0..8} with the circular hull {0xFFFFFFFF,0..8} = {0..8} exactly (no \
     spurious 0xFFFFFFFF)"
    (Clp.equal m12 lo12
    && Clp.cardinality m12 = w33 9
    && (not (Clp.elem (w32 0xFFFFFFFF) m12))
    && Clp.elem (w32 0) m12
    && Clp.elem (w32 8) m12);
  ())
(* op_add contract pins: [meet_add] fills a fresh gap with d; [join_add] leaves it top. *)
;
(  let idx32 = { Mem.addr_width = 32; Mem.addressable_width = 8 } in
  let key_of ws =
    match Mem.Key.of_wordset ws with
    | Some k -> k
    | None -> failwith "opadd key_of: of_wordset None"
  in
  let point c = key_of (Ws.singleton (w32 c)) in
  let range lo hi = key_of (Ws.of_clp (Clp.interval ~width:32 (w32 lo) (w32 hi))) in
  let cell n = Mem.Val.create (Ws.singleton (w32 n)) LittleEndian in
  (* [find] reads at a cell's lower bound; interior reads are top. *)
  let read32 m c = Mem.Val.data (Mem.find (32, LittleEndian) m (point c)) in
  let empty = Mem.top idx32 in
  (* Range cell with real value via meet_add (meet d top = d). *)
  let range_cell lo hi n = Mem.meet_add empty ~key:(range lo hi) ~data:(cell n) in

  (* (a) key inside one node: flanks keep old, middle joins new. *)
  let m = range_cell 10 20 1 in
  let m = Mem.join_add m ~key:(range 12 18) ~data:(cell 2) in
  check
    "opadd-a: join a key fully inside one node — interval_diff `two (low flank lo 10 = {1}, middle \
     lo 12 = {1,2}, high flank lo 19 = {1})"
    (Ws.equal (read32 m 10) (Ws.singleton (w32 1))
    && Ws.equal (read32 m 12) (Ws.of_list ~width:32 [ w32 1; w32 2 ])
    && Ws.equal (read32 m 19) (Ws.singleton (w32 1))
    && Ws.is_top (read32 m 11)
    && Ws.is_top (read32 m 9)
    && Ws.is_top (read32 m 21));

  (* (b) key spanning nodes: node-lo reads are top (gap pollution). *)
  let m = Mem.meet_add (range_cell 10 12 1) ~key:(range 14 16) ~data:(cell 2) in
  let m = Mem.join_add m ~key:(range 10 16) ~data:(cell 3) in
  check
    "opadd-b: join a key spanning several nodes — the [gaps] cells duplicate the node lo \
     addresses, so the node lo reads are top (structural-only observation)"
    (Ws.is_top (read32 m 10) && Ws.is_top (read32 m 14) && Ws.is_top (read32 m 13));

  (* (c1) covering key: meet fills the fresh gap with d. *)
  let m = range_cell 10 20 1 in
  let m =
    Mem.meet_add m ~key:(range 0 30)
      ~data:(Mem.Val.create (Ws.of_list ~width:32 [ w32 1; w32 2 ]) LittleEndian)
  in
  check
    "opadd-c1: meet a key covering the node (interval_diff `none) — the fresh gap becomes {1,2} \
     (meet fills it); the node narrows"
    (Ws.equal (read32 m 0) (Ws.of_list ~width:32 [ w32 1; w32 2 ]) && Ws.is_top (read32 m 15));

  (* (c2) low-half overlap: high flank keeps value; joined lo is top. *)
  let m = range_cell 10 20 1 in
  let m = Mem.join_add m ~key:(range 5 15) ~data:(cell 2) in
  check
    "opadd-c2: join a key overlapping the node's low half (interval_diff `one) — the high flank lo \
     16 keeps {1}; the joined cell's lo 10 is top (gap pollution)"
    (Ws.equal (read32 m 16) (Ws.singleton (w32 1))
    && Ws.is_top (read32 m 10)
    && Ws.is_top (read32 m 7));

  (* (c3) high-half overlap: low flank keeps value. *)
  let m = range_cell 10 20 1 in
  let m = Mem.join_add m ~key:(range 15 25) ~data:(cell 2) in
  check
    "opadd-c3: join a key overlapping the node's high half (interval_diff `one) — the low flank lo \
     10 keeps {1}, the joined cell lo 15 = {1,2}"
    (Ws.equal (read32 m 10) (Ws.singleton (w32 1))
    && Ws.equal (read32 m 15) (Ws.of_list ~width:32 [ w32 1; w32 2 ])
    && Ws.is_top (read32 m 23));

  (* (d1) circular WordSet approximates as the full span. *)
  let wrap_ws = Ws.of_clp (Clp.interval ~width:32 (w32 0xFFFFFFF0) (w32 0x0F)) in
  let m = Mem.meet_add empty ~key:(key_of wrap_ws) ~data:(cell 7) in
  check
    "opadd-d1: a circular WordSet -> Key.of_wordset is the FULL span [0, 0xFFFFFFFF] (lo 0 = {7}, \
     interior 0x50 and 0xFFFFFFF0 are misaligned top)"
    (Ws.equal (read32 m 0) (Ws.singleton (w32 7))
    && Ws.is_top (read32 m 0x50)
    && Ws.is_top (read32 m 0xFFFFFFF0));

  (* (d2) key ending at max spills no wrapped cell onto 0. *)
  let m = range_cell 10 20 1 in
  let m = Mem.meet_add m ~key:(range 10 0xFFFFFFFF) ~data:(cell 1) in
  check
    "opadd-d2: a key with hi = 0xFFFFFFFF — the finishing gap terminates at max (lo 10 = {1}; no \
     wrapped spill at address 0)"
    (Ws.equal (read32 m 10) (Ws.singleton (w32 1)) && Ws.is_top (read32 m 0));

  (* (e) bottom map stays bottom under every entry point. *)
  let bot = Mem.bottom idx32 in
  check "opadd-e: the bottom map stays bottom under add/meet_add/join_add/meet_range"
    (Mem.equal (Mem.add bot ~key:(point 10) ~data:(cell 1)) bot
    && Mem.equal (Mem.meet_add bot ~key:(range 0 20) ~data:(cell 1)) bot
    && Mem.equal (Mem.join_add bot ~key:(range 0 20) ~data:(cell 1)) bot
    && Mem.equal (Mem.meet_range bot ~key:(range 0 20) ~data:(cell 1)) bot);

  (* (f) width-mismatched data meets per-cell; joins to top. *)
  let m = range_cell 10 10 5 in
  let d64 = Mem.Val.create (Ws.singleton (w64 5)) LittleEndian in
  let m = Mem.meet_add m ~key:(point 10) ~data:d64 in
  check "opadd-f: a 64-bit {5} meets a 32-bit {5} cell via meet_poly (widened to 64, no crash)"
    (let v = Mem.Val.data (Mem.find (64, LittleEndian) m (point 10)) in
     Ws.equal v (Ws.singleton (w64 5)));
  let m = range_cell 10 10 5 in
  let m = Mem.join_add m ~key:(point 10) ~data:d64 in
  check
    "opadd-f2: a 64-bit {5} joins a 32-bit {5} cell -> top (the idx-mismatched join fallback), no \
     crash"
    (let v = Mem.Val.data (Mem.find (64, LittleEndian) m (point 10)) in
     Ws.is_top v);
  ())

(* Shift-semantics families in one home (the CLP shift contract): Lane A
   (pure-CLP, moved from test_backward.ml) + D5/D7-shift/E2eC-shift (moved
   from test_vsa.ml), sharing operand fixtures, the wrapped-guard component
   strings, and one zero-image predicate. Family check names preserved. *)
let run_shifts () =
(* Shared operand fixtures + the wrapped-guard component strings. *)
  let lshift_comp = "During lshift, maximum element of CLP2 is >= CLP1's width" in
  let rshift_comp = "During rshift, maximum element of CLP2 is >= CLP1's width" in
  let arshift_comp = "During arshift, maximum element of CLP2 is >= CLP1's width" in
  let sh16 = Clp.create (w64 16) in
  let amt64 = Clp.of_list ~width:64 [ w64 64 ] in
  let straddle = Clp.create ~width:64 ~step:(w64 2) ~cardn:(Cbat_word.of_int ~width:65 32) (w64 8) in
  let antipodal64 = Clp.of_list ~width:64 [ w64 1; Cbat_word.lshift (w64 1) (w64 63) ] in
  (* An all-overshifted image is exactly {zero}: min/max/cardn agree, non-top. *)
  let is_zero_clp (zero : Cbat_word.t) (r : Clp.t) : bool =
    Clp.min_elem r = Some zero
    && Clp.max_elem r = Some zero
    && Cbat_word.to_int_exn (Clp.cardinality r) = 1
    && (not (Clp.is_top r))
    && not (Clp.is_bottom r)
  in
(* Lane A: mixed-width shifts via coerce-to-max. *)
(  (* A-1: mixed-width rshift exact. *)
  let r1 = Clp.rshift (Clp.create (w32 0xFF)) (Clp.create (w64 2)) in
  check
    "A-1: mixed-width rshift (32-bit {0xFF} >> 64-bit {2}) is EXACTLY {0x3F} at 32 bits (no guard \
     fire)"
    (Clp.equal r1 (Clp.create (w32 0x3F)));
  (* A-2: straddling amount gives non-top non-bottom. *)
  let amt40 = Clp.create ~width:64 ~step:(w64 1) ~cardn:(Cbat_word.of_int ~width:65 40) (w64 0) in
  let r2 = Clp.rshift (Clp.create (w32 1)) amt40 in
  check
    "A-2: the 252-hit shape (32-bit >> 64-bit [0,40)) — the coerced three-way split yields a \
     non-top, non-bottom result"
    ((not (Clp.is_top r2)) && (not (Clp.is_bottom r2)) && Clp.bitwidth r2 = 32);
  (* A-3: mixed-width overshift is exactly {0}. *)
  let r3 = Clp.rshift (Clp.create (w32 8)) (Clp.create (w64 40)) in
  check "A-3: mixed-width rshift overshift (32-bit >> 64-bit {40}) is EXACTLY {0} at 32 bits"
    (Clp.equal r3 (Clp.create (w32 0)));
  (* A-4: arshift sign-fills through the coercion. *)
  let r4 = Clp.arshift (Clp.create (w32 0xFFFFFFFF)) (Clp.create (w64 40)) in
  check
    "A-4: mixed-width arshift sign-fill (32-bit {all-ones} arshift 64-bit {40}) is EXACTLY \
     {all-ones} at 32 bits (the SIGN-extension)"
    (Clp.equal r4 (Clp.create (w32 0xFFFFFFFF)));
  (* A-5: antipodal equal-width overshift image. *)
  let r5 = Clp.arshift antipodal64 (Clp.create (w64 70)) in
  check
    "A-5: the antipodal overshift image (64-bit {1, 2^63} arshift {70}) is {0, all-ones} \
     (equal-width path, no coercion)"
    (Cbat_word.to_int_exn (Clp.cardinality r5) = 2
    && Clp.elem (w64 0) r5
    && Clp.elem (Cbat_word.ones 64) r5
    && (not (Clp.elem (w64 1) r5))
    && not (Clp.is_top r5));
  ())
;
(* D5: rshift/arshift width handling — mixed widths compute, overshift is zero. *)
(  let c32 = Clp.create (w32 16) in
  let c64 = sh16 in
  (* Mixed-width operands compute via coerce-to-max (16 >> 16 = 0). *)
  check
    "D5-1: CLP rshift on mixed-width operands COMPUTES (lane A) — {0} exactly, no assert, no top"
    (Clp.equal (Clp.rshift c32 c64) (Clp.create (w32 0)));
  check
    "D5-2: CLP arshift on mixed-width operands COMPUTES (lane A) — {0} exactly, no assert, no top"
    (Clp.equal (Clp.arshift c32 c64) (Clp.create (w32 0)));
  check "D5-3: CLP rshift/arshift on same-width singletons still exact"
    (let r = Clp.rshift (Clp.create (w32 16)) (Clp.create (w32 2)) in
     Clp.min_elem r = Some (w32 4)
     && Clp.max_elem r = Some (w32 4)
     &&
     let a = Clp.arshift (Clp.create (w32 16)) (Clp.create (w32 2)) in
     Clp.min_elem a = Some (w32 4) && Clp.max_elem a = Some (w32 4));
  (* Overshift amount (>= width) is bitvec zero, not top. *)
  check "D5-4: rshift by an amount >= the operand width -> {0} exactly (overshift=zero, no raise)"
    (let r = Clp.rshift (Clp.create (w32 1)) (Clp.create (w32 32)) in
     Clp.min_elem r = Some (w32 0)
     && Clp.max_elem r = Some (w32 0)
     && Cbat_word.to_int_exn (Clp.cardinality r) = 1
     && (not (Clp.is_top r))
     && not (Clp.is_bottom r));
  check "D5-5: rshift by an amount < the operand width still computes"
    (let r = Clp.rshift (Clp.create (w32 8)) (Clp.create (w32 3)) in
     Clp.min_elem r = Some (w32 1) && Clp.max_elem r = Some (w32 1));
  (* Composite level: mixed-width CLPs via WordSet. *)
  let big32 = Ws.of_list ~width:32 (List.init 11 (fun i -> w32 (i * 2))) in
  let big64 = Ws.of_list ~width:64 (List.init 11 (fun i -> w64 (i * 2))) in
  check "D5-6: composite rshift on mixed-width CLPs COMPUTES (lane A) — non-top, no assert"
    (not (Ws.is_top (Ws.rshift big32 big64)));
  check "D5-7: composite arshift on mixed-width CLPs COMPUTES (lane A) — non-top, no assert"
    (not (Ws.is_top (Ws.arshift big32 big64)));
  check "D5-8: composite rshift on same-width singletons still exact"
    (let r = Ws.rshift (Ws.singleton (w32 16)) (Ws.singleton (w32 2)) in
     Ws.elem (w32 4) r && (not (Ws.is_top r)) && not (Ws.is_bottom r));
  ())
;
(* D7-shift: degenerate sizes degrade; 2-bit amounts and overshifts compute. *)
(  (* 2-bit amount vs 64-bit operand: magnitudes compared, no spurious fire. *)
  let w2 = Cbat_word.of_int ~width:2 in
  let amt2 = Clp.of_list ~width:2 [ w2 2 ] in
  (* Guard's stderr line must NOT appear. *)
  let fire_l = fired lshift_comp (fun () -> ignore (Clp.lshift (sh16) amt2)) in
  let fire_r = fired rshift_comp (fun () -> ignore (Clp.rshift (sh16) amt2)) in
  let fire_a = fired arshift_comp (fun () -> ignore (Clp.arshift (sh16) amt2)) in
  let r = Clp.lshift (sh16) amt2 in
  check "D7-10: lshift 2-bit {2} amount vs 64-bit operand -> computes {64}, no spurious fire"
    (Clp.bitwidth r = 64 && Clp.min_elem r = Some (w64 64) && (not (Clp.is_top r)) && not fire_l);
  (* Overshift is bitvec zero ({0} exactly), no fire. *)
  check "D7-11: lshift overshift (6-bit {40} amount vs 32-bit operand) -> {0} exactly, no fire"
    (let r = Clp.lshift (Clp.create (w32 8)) (Clp.of_list ~width:6 [ Cbat_word.of_int ~width:6 40 ]) in
     is_zero_clp (w32 0) r && not fire_l);
  (* 2-bit amounts take the mixed-width path (sound top); wrapped guard stays silent. *)
  (* 2-bit amount coerces to operand width; shift computes. *)
  check
    "D7-12: rshift 2-bit {2} amount vs 64-bit operand COMPUTES {4} (lane A), wrapped guard never \
     fires"
    (Clp.equal (Clp.rshift (sh16) amt2) (Clp.create (w64 4)) && not fire_r);
  check
    "D7-13: arshift 2-bit {2} amount vs 64-bit operand COMPUTES {4} (lane A), wrapped guard never \
     fires"
    (Clp.equal (Clp.arshift (sh16) amt2) (Clp.create (w64 4)) && not fire_a);
  (* Same-width overshift: rshift/arshift give {0} exactly. *)
  check "D7-14: rshift/arshift overshift ({40} vs 32-bit) -> {0} exactly, no fire"
    (let r = Clp.rshift (Clp.create (w32 8)) (Clp.of_list ~width:32 [ w32 40 ]) in
     let a = Clp.arshift (Clp.create (w32 8)) (Clp.of_list ~width:32 [ w32 40 ]) in
     is_zero_clp (w32 0) r && is_zero_clp (w32 0) a && (not fire_r) && not fire_a);
  ()
)
;
(* E2eC-shift: overshift/straddle/antipodal/segment-width shift images. *)
(  (* Guard's stderr line must NOT appear. *)
  let fire_l =
    fired lshift_comp (fun () ->
        ignore (Clp.lshift (sh16) (amt64)))
  in
  let fire_r =
    fired rshift_comp (fun () ->
        ignore (Clp.rshift (sh16) (amt64)))
  in
  let fire_a =
    fired arshift_comp (fun () ->
        ignore (Clp.arshift (sh16) (amt64)))
  in
  (* Fully overshifted (min >= width): exactly {0}. *)
  check "E2eC-1: lshift {16} by {64} (min >= width) -> EXACTLY {0}, no fire"
    (is_zero_clp (w64 0) (Clp.lshift (sh16) (amt64)) && not fire_l);
  check "E2eC-2: lshift {16} by multi-card overshift {64,68,72} stride 4 -> {0}, no fire"
    (let amt = Clp.create ~width:64 ~step:(w64 4) ~cardn:(Cbat_word.of_int ~width:65 3) (w64 64) in
     is_zero_clp (w64 0) (Clp.lshift (sh16) amt) && not fire_l);
  check "E2eC-3: rshift {16} by {64} (min >= width) -> EXACTLY {0}, no fire"
    (is_zero_clp (w64 0) (Clp.rshift (sh16) (amt64)) && not fire_r);
  (* Overshift arshift: mixed-sign gives {0, all-ones}; pure signs collapse. *)
  check "E2eC-4: arshift overshift of a mixed-sign operand -> {0, all-ones}, no fire"
    (let r = Clp.arshift antipodal64 amt64 in
     Cbat_word.to_int_exn (Clp.cardinality r) = 2
     && Clp.elem (w64 0) r
     && Clp.elem (Cbat_word.ones 64) r
     && (not (Clp.elem (w64 1) r))
     && (not (Clp.is_top r))
     && not fire_a);
  check "E2eC-5: arshift overshift of a nonneg operand -> {0} exactly (sign-extension)"
    (is_zero_clp (w64 0) (Clp.arshift (sh16) (amt64))
    && not fire_a);
  check "E2eC-6: arshift overshift of a negative operand -> {all-ones} exactly"
    (let r =
       Clp.arshift (Clp.create (Cbat_word.lshift (w64 1) (w64 63))) (amt64)
     in
     Clp.min_elem r = Some (Cbat_word.ones 64)
     && Clp.max_elem r = Some (Cbat_word.ones 64)
     && Cbat_word.to_int_exn (Clp.cardinality r) = 1
     && (not (Clp.is_top r))
     && not fire_a);
  (* Straddling (min < width <= max): capped exact path UNION overshift class. *)
  check "E2eC-7: lshift {16} by straddling [8,70] step 2 -> non-top, contains capped image ∪ {0}"
    (let r = Clp.lshift (sh16) straddle in
     (not (Clp.is_top r))
     && (not (Clp.is_bottom r))
     && Clp.elem (w64 0) r (* overshift (and 16<<62 mod 2^64) *)
     && Clp.elem (w64 0x1000) r (* 16<<8 = capped min *)
     && Clp.elem (w64 0x4000) r (* 16<<10 *)
     && Clp.elem (w64 0x40000000) r (* 16<<30 *)
     && not fire_l);
  check "E2eC-8: rshift {2^40} by straddling [8,70] step 2 -> non-top, contains capped image ∪ {0}"
    (let r = Clp.rshift (Clp.create (Cbat_word.lshift (w64 1) (w64 40))) straddle in
     (not (Clp.is_top r))
     && (not (Clp.is_bottom r))
     && Clp.elem (w64 0) r (* 2^40>>a = 0 for a >= 41 *)
     && Clp.elem (w64 1) r (* 2^40>>40 *)
     && Clp.elem (w64 4) r (* 2^40>>38 *)
     && Clp.elem (w64 0x100000000) r (* 2^40>>8 = capped min *)
     && not fire_r);
  check
    "E2eC-9: arshift {2^63} by straddling [8,70] step 2 -> non-top, contains capped base ∪ \
     {all-ones}"
    (let r = Clp.arshift (Clp.create (Cbat_word.lshift (w64 1) (w64 63))) straddle in
     (not (Clp.is_top r))
     && (not (Clp.is_bottom r))
     && Clp.elem (Cbat_word.ones 64) r (* overshift: amount 70 *)
     && Clp.elem (Cbat_word.neg (Cbat_word.lshift (w64 1) (w64 55))) r (* amount 8: sign-ext of 2^63>>8 = -2^55 *)
     && not fire_a);
  (* Full capped image of straddling arshift not asserted element-wise (step collapse). *)
  (* TOP amount caps to [0, width-1] at reachable stride. *)
  check
    "E2eC-10: lshift {16} by top(64) amount -> stride-class result (non-bottom, contains 0 and \
     16), no fire"
    (let r = Clp.lshift (sh16) (Clp.top 64) in
     (not (Clp.is_bottom r)) && Clp.elem (w64 0) r && Clp.elem (w64 16) r && not fire_l);
  (* Segment-width shifts fully overshifted give exactly {0}. *)
  check "E2eC-11: array_local pattern — 32-bit operand shifted by {32} -> {0} exactly, no fire"
    (let r = Clp.lshift (Clp.create (w32 1)) (Clp.of_list ~width:32 [ w32 32 ]) in
     is_zero_clp (w32 0) r && not fire_l);
  check "E2eC-12: array_local pattern — 8-bit operand shifted by {8} -> {0} exactly, no fire"
    (let r =
       Clp.lshift (Clp.create (Cbat_word.of_int ~width:8 1)) (Clp.of_list ~width:8 [ Cbat_word.of_int ~width:8 8 ])
     in
     is_zero_clp (Cbat_word.of_int ~width:8 0) r && not fire_l);
  ()
)

(* Overlap/round-trip domain properties (moved from test_regression.ml: no BIL,
   no stack, no seam — pure Ws/Clp/FinSet properties, incl. the randomized m6
   enumerations). Check names preserved. *)
let run_overlap () =
(  (* C10/C11: overlap equals not-is_bottom-of-meet on sampled pairs. *)
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
  List.iter
    (fun (a, b) ->
      let overlap = Ws.overlap a b in
      let meet = Ws.meet a b in
      let is_bottom = Ws.is_bottom meet in
      check
        (Printf.sprintf "property WordSet.overlap vs meet is_bottom: overlap %b = not is_bottom %b"
           overlap is_bottom)
        (overlap = not is_bottom))
    pairs;
  (* Width-mismatched overlap is false (exact disjointness). *)
  let a32 = Ws.of_list ~width:32 [ w32 1 ] in
  let a64 = Ws.of_list ~width:64 [ w64 1 ] in
  check "property WordSet.overlap width-mismatch → false (pinned convention, FinSet/FinSet)"
    (not (Ws.overlap a32 a64));
  (* Mismatched meet returns the wider operand (non-bottom). *)
  check "property WordSet.meet width-mismatch → wider operand (non-bottom)"
    (not (Ws.is_bottom (Ws.meet a32 a64)));
  (* m6: randomized small-width enumeration of the same property. *)
  Random.init 20260822;
  let failures_before_m6_overlap = !failures in
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
      if ov && mb then begin
        Printf.printf "FAIL: property m6 overlap ⟹ meet non-bottom (w=%d, trial %d)\n" w _i;
        incr failures
      end;
      if (ta = `fs || tb = `fs) && ov <> not mb then begin
        Printf.printf
          "FAIL: property m6 overlap = ¬is_bottom∘meet (FinSet-arm meet, w=%d, trial %d)\n" w _i;
        incr failures
      end
    end
  done;
  if !failures = failures_before_m6_overlap then
    Printf.printf
      "ok: property m6 overlap = ¬is_bottom∘meet enumerated (300 random equal-width trials, \
       representation-aware)\n";
  ())
;
(  (* C11: FinSet↔Clp round-trip equivalence on small sets. *)
  let fin_sets : Fs.t list =
    [
      Fs.of_list ~width:32 [ w32 1; w32 2; w32 3 ];
      Fs.of_list ~width:32 [ w32 5 ];
      Fs.of_list ~width:8 [ Cbat_word.of_int ~width:8 1; Cbat_word.of_int ~width:8 2 ];
      Fs.of_list ~width:16 [ Cbat_word.of_int ~width:16 10; Cbat_word.of_int ~width:16 20 ];
      Fs.of_list ~width:32 [ w32 0; w32 2; w32 4; w32 6; w32 8 ];
    ]
  in
  List.iter
    (fun s ->
      let p = Clp.of_list ~width:(Fs.bitwidth s) (Fs.iter s) in
      let s2 = Fs.of_list ~width:(Clp.bitwidth p) (Clp.iter p) in
      check
        (Printf.sprintf "property FinSet->Clp->FinSet round-trip width %d cardn %d" (Fs.bitwidth s)
           (Cbat_word.to_int_exn (Fs.cardinality s)))
        (Fs.equal s s2))
    fin_sets;
  let clps : Clp.t list =
    [
      Clp.create (w32 10) ~step:(w32 2) ~cardn:(Cbat_word.of_int ~width:33 3);
      Clp.create (w32 0) ~step:(w32 1) ~cardn:(Cbat_word.of_int ~width:33 5);
      Clp.create (Cbat_word.of_int ~width:8 1) ~step:(Cbat_word.of_int ~width:8 1) ~cardn:(Cbat_word.of_int ~width:9 3);
    ]
  in
  List.iter
    (fun p ->
      let cardn = Clp.cardinality p in
      if (not (Cbat_word.is_zero cardn)) && Cbat_word.compare cardn (Cbat_word.of_int ~width:(Cbat_word.bitwidth cardn) 11) < 0 then
        let s = Fs.of_list ~width:(Clp.bitwidth p) (Clp.iter p) in
        let p2 = Clp.of_list ~width:(Fs.bitwidth s) (Fs.iter s) in
        check
          (Printf.sprintf "property Clp->FinSet->Clp round-trip cardn %d" (Cbat_word.to_int_exn cardn))
          (Clp.equal p p2))
    clps;
  (* m6: randomized round-trips — soundness always, exactness on wrap-free arcs. *)
  Random.init 20260822;
  let failures_before_m6_rt = !failures in
  for _i = 1 to 200 do
    let w = [| 4; 8; 12 |].(Random.int 3) in
    let dom = 1 lsl w in
    let base = Random.int dom in
    let step = 1 + Random.int 5 in
    let n = 1 + Random.int 10 in
    let rec els acc k =
      if k = n then acc else els (Cbat_word.of_int ~width:w ((base + (k * step)) mod dom) :: acc) (k + 1)
    in
    (* Exact-round-trip shape: no wrap AND seam gap step-multiple. *)
    let wrap_free = base + ((n - 1) * step) < dom in
    let seam_ok = (dom - (base + ((n - 1) * step) - base)) mod step = 0 in
    let exact_shape = wrap_free && seam_ok in
    let subset s1 s2 = List.for_all (fun x -> Fs.elem x s2) s1 in
    let expect b msg =
      if not b then begin
        Printf.printf "FAIL: property m6 %s (trial %d)\n" msg _i;
        incr failures
      end
    in
    (* FinSet -> Clp -> FinSet *)
    let s = Fs.of_list ~width:w (els [] 0) in
    let p = Clp.of_list ~width:(Fs.bitwidth s) (Fs.iter s) in
    let s2 = Fs.of_list ~width:(Clp.bitwidth p) (Clp.iter p) in
    expect (subset (Fs.iter s) s2) "FinSet->Clp->FinSet SOUND (s ⊆ s2)";
    expect
      (Cbat_word.compare (Fs.cardinality s) (Fs.cardinality s2) <= 0)
      "FinSet->Clp->FinSet cardn non-decreasing";
    if exact_shape then expect (Fs.equal s s2) "FinSet->Clp->FinSet EXACT (wrap-free arc)";
    (* Clp -> FinSet -> Clp *)
    let p3 =
      Clp.create (Cbat_word.of_int ~width:w base) ~step:(Cbat_word.of_int ~width:w step)
        ~cardn:(Cbat_word.of_int ~width:(w + 1) n)
    in
    let s3 = Fs.of_list ~width:(Clp.bitwidth p3) (Clp.iter p3) in
    let p4 = Clp.of_list ~width:(Fs.bitwidth s3) (Fs.iter s3) in
    expect (List.for_all (fun x -> Clp.elem x p4) (Clp.iter p3)) "Clp->FinSet->Clp SOUND (p3 ⊆ p4)";
    expect
      (Cbat_word.compare (Clp.cardinality p3) (Clp.cardinality p4) <= 0)
      "Clp->FinSet->Clp cardn non-decreasing";
    if exact_shape then expect (Clp.equal p3 p4) "Clp->FinSet->Clp EXACT (wrap-free arc)"
  done;
  if !failures = failures_before_m6_rt then
    Printf.printf
      "ok: property m6 FinSet↔Clp round-trips enumerated (200 random progression trials: soundness \
       always, exactness on wrap-free arcs)\n";
  ())

