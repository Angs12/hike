(* test_properties: soundness properties (logand R10b, interval-meet R5, contextual fixpoint R7), round-trip/overlap/of_list exactness, landmark loops + the F1-NEQ acceptance, and the Ticket-01 when-chain pins. *)
open Bap.Std
open Bap_core_theory
open Test_common

(* --- R10b: property test — logand soundness over a sampled operand corpus -- *)

(* The SWEET-lineage CLP logand's general branch picks the result step from the operands' msb
   structure; the step selection feeding the base/cardn computation carries the upstream TODO "this
   last branch is a guess; it is not explained in the paper" (the range-sep helper in cbat_clp.ml,
   since removed with [compute_range_sep]). An over-large chosen step would SKIP result elements —
   an unsound narrowing. This block verifies the soundness direction EXECUTABLY over a sampled
   operand corpus: for every sampled pair, EVERY elementwise AND of the enumerated operand elements
   must be a member of the domain's logand result (the CLP layer AND the composite WordSet lift).
   Over-approximation is allowed; excluding a reachable value FAILS. Pairs whose enumeration exceeds
   the caps are SKIPPED (counted), never weakened. *)

let r10b_enum_cap = 1024 (* max enumerated elements per side *)
let r10b_product_cap = 131072 (* max elementwise ANDs per pair *)
let r10b_pairs = ref 0 (* pairs fully checked *)
let r10b_skipped = ref 0 (* pairs skipped: enumeration/product caps *)
let r10b_prefix = ref 0 (* pairs using a prefix-sampled (>cap) side *)
let r10b_witnesses = ref 0 (* distinct elementwise ANDs checked *)
let r10b_bad_clp = ref 0 (* pairs violating the CLP-layer containment *)
let r10b_bad_ws = ref 0 (* pairs violating the composite containment *)

(* [r10b_cardn_gt cap c]: cardinality word [c] > [cap] WITHOUT the width trap ([Wo.gt_int] builds
   [cap] at [c]'s width — at widths where [cap] does not fit it wraps and the comparison lies). *)
let r10b_cardn_gt (cap : int) (c : word) : bool =
  if W.bitwidth c >= 11 then Wo.gt_int c cap (* 1024 fits: unsigned cmp ok *)
  else W.to_int_exn c > cap

(* [r10b_enum p]: ALL elements when cardinality <= cap (exact); otherwise a bounded prefix along the
   progression from min_elem via strict nearest_succ steps (stop on wrap-past-max / stuck / cap) — a
   sound partial witness set: the containment assertion stays exact per enumerated element. The bool
   reports whether a prefix sample was used. NOTE: [Clp.nearest_succ i] returns [i] ITSELF when [i]
   is a member (closest->= semantics), so the walk asks for the successor of [succ cur]. *)
let r10b_enum (p : Clp.t) : word list * bool =
  if r10b_cardn_gt r10b_enum_cap (Clp.cardinality p) then
    match Clp.min_elem p with
    | None -> ([], true)
    | Some m0 ->
        let mx = Clp.max_elem p in
        let rec go n cur acc =
          if n >= r10b_enum_cap then (List.rev acc, true)
          else
            match Clp.nearest_succ (W.succ cur) p with
            | None -> (List.rev (cur :: acc), true)
            | Some nxt ->
                if
                  W.equal nxt cur
                  || W.compare nxt cur <= 0
                  || match mx with Some mx -> W.compare nxt mx > 0 | None -> false
                then (List.rev (cur :: acc), true)
                else go (n + 1) nxt (cur :: acc)
        in
        go 0 m0 []
  else (Clp.iter p, false)

(* [r10b_check_pair w l1 p1 l2 p2]: the containment assertion for one unordered pair (ground truth
   computed once — AND is commutative). *)
let r10b_check_pair (w : int) (l1 : string) (p1 : Clp.t) (l2 : string) (p2 : Clp.t) : unit =
  let es1, pre1 = r10b_enum p1 in
  let es2, pre2 = r10b_enum p2 in
  if pre1 || pre2 then incr r10b_prefix;
  if List.length es1 * List.length es2 > r10b_product_cap then incr r10b_skipped
  else begin
    incr r10b_pairs;
    let res_c = Clp.logand p1 p2 in
    let res_ws = Ws.logand (Ws.of_clp p1) (Ws.of_clp p2) in
    let seen : (int64, unit) Hashtbl.t = Hashtbl.create 256 in
    let bad_c = ref [] and bad_ws = ref [] in
    List.iter
      (fun x ->
        List.iter
          (fun y ->
            let z = W.logand x y in
            let k = W.to_int64_exn z in
            if not (Hashtbl.mem seen k) then begin
              Hashtbl.add seen k ();
              incr r10b_witnesses;
              if not (Clp.elem z res_c) then bad_c := (x, y, z) :: !bad_c;
              if not (Ws.elem z res_ws) then bad_ws := (x, y, z) :: !bad_ws
            end)
          es2)
      es1;
    let report kind bad =
      match bad with
      | [] -> ()
      | _ ->
          if kind = "CLP" then incr r10b_bad_clp else incr r10b_bad_ws;
          Printf.printf "  property logand VIOLATION (%s) @w=%d: %s & %s: %d excluded value(s)\n"
            kind w l1 l2 (List.length bad);
          List.iteri
            (fun i (x, y, z) ->
              if i < 3 then
                Printf.printf "    x=%Ld y=%Ld -> x&y=%Ld not in result\n" (W.to_int64_exn x)
                  (W.to_int64_exn y) (W.to_int64_exn z))
            (List.rev bad)
    in
    report "CLP" !bad_c;
    report "WordSet" !bad_ws
  end

(* [r10b_operands w]: the sampled operand corpus at width [w] — singletons, contiguous ranges (incl.
   the wrapped/circular interval), stepped classes (incl. cardn-2, odd steps, wrapping),
   infinite/top classes. *)
let r10b_operands (w : int) : (string * Clp.t) list =
  let v n = W.of_int ~width:w n in
  let ones = W.ones w in
  let half = Wo.half w in
  let full_circle = Wo.dom_size ~width:(w + 1) w in
  [
    (* singletons *)
    ("{0}", Clp.create (v 0));
    ("{1}", Clp.create (v 1));
    ("{8}", Clp.create (v 8));
    ("{0xAA}", Clp.create (v 0xAA));
    ("{half}", Clp.create half);
    ("{ones}", Clp.create ones);
    (* contiguous ranges (incl. the wrapped/circular interval) *)
    ("[0,3]", Clp.interval ~width:w (v 0) (v 3));
    ("[1,17]", Clp.interval ~width:w (v 1) (v 17));
    ("[16,47]", Clp.interval ~width:w (v 16) (v 47));
    ("[0,99]", Clp.interval ~width:w (v 0) (v 99));
    ("[half-3,half+3]", Clp.interval ~width:w (W.sub half (v 3)) (W.add half (v 3)));
    ("[ones-8,ones]", Clp.interval ~width:w (W.sub ones (v 8)) ones);
    ("wrap[ones-1,1]", Clp.interval ~width:w ones (v 1));
    (* stepped classes *)
    ("evens[0..78]", Clp.create (v 0) ~step:(v 2) ~cardn:(v 40));
    ("step4[2..]", Clp.create (v 2) ~step:(v 4) ~cardn:(v 12));
    ("step8[8..]", Clp.create (v 8) ~step:(v 8) ~cardn:(v 10));
    ("step3[1..]", Clp.create (v 1) ~step:(v 3) ~cardn:(v 20));
    ("step5[3..]", Clp.create (v 3) ~step:(v 5) ~cardn:(v 15));
    ("step16[8..]", Clp.create (v 8) ~step:(v 16) ~cardn:(v 6));
    ("step12[4..]", Clp.create (v 4) ~step:(v 12) ~cardn:(v 9));
    ("two{8,24}", Clp.create (v 8) ~step:(v 16) ~cardn:(v 2));
    ("wrapstep{ones-4+8k}", Clp.create (W.sub ones (v 4)) ~step:(v 8) ~cardn:(v 4));
    (* cardn-2 ANTIPODAL pairs (Stage 0b): the two elements are half a circle apart — {0, 2^(w-1)}
       and {1, 1 + 2^(w-1)} — the class the arshift unwrap_signed note flags as
       representation-fragile *)
    ("anti{0,half}", Clp.create (v 0) ~step:half ~cardn:(v 2));
    ("anti{1,1+half}", Clp.create (v 1) ~step:half ~cardn:(v 2));
    (* infinite / top classes *)
    ("top", Clp.top w);
    ("inf*4", Clp.create (v 0) ~step:(v 4) ~cardn:full_circle);
    ("inf*6@6", Clp.create (v 6) ~step:(v 6) ~cardn:full_circle);
  ]
  (* Stage 0b: w=8 FULL-WRAP classes — spans that cross the seam the long way (the wrapped interval
     [200,100] covers 157 elements around the circle; the stepped class wraps past 2^8). Only
     sampled at w=8 where full-circle traversal is enumerable. *)
  @
  if w = 8 then
    [
      ("fullwrap[200,100]", Clp.interval ~width:w (v 200) (v 100));
      ("fullwrap step11[3+11k]", Clp.create (v 3) ~step:(v 11) ~cardn:(v 24));
    ]
  else []

(* --- R5: property test — the step-1 interval meet is EXACT -------------- *)

(* The CLP domain is CIRCULAR over Z_2^w: a finite step-1 CLP is the circular interval [start,
   start+len) (half-open; len <= 2^w - 1 after canonization — the full circle arrives as the
   infinite class). The meet of two such intervals is computed here INDEPENDENTLY by modular
   arithmetic at width w+1 (no diophantine anchoring, no hulling, no safe-operand fallback): the
   intersection of [s1,s1+l1) and [s2,s2+l2) on the circle is Empty, one Arc, or — when each operand
   sticks out of the other on both sides — Two pieces; in the two-piece case the OPTIMAL single-CLP
   sound answer is the smaller-cardinality operand (any single arc containing both pieces must
   bridge one of the two gaps, i.e. contain one whole operand; the smaller one is minimal). The
   domain's [intersection] must equal this reference exactly. Equality is asserted with [Clp.equal]
   against the freshly-built expected arc — sound because every producer funnels through the
   canonizing [create] (representation-equivalent canonized forms of one step-1 arc do not exist:
   the cardn-2 wrapped normalization maps back to the ascending form). Pairs involving stepped /
   infinite classes are probed for SOUNDNESS only (every true common element survives). *)

let r5_checked = ref 0 (* exactness pairs fully checked *)
let r5_two_piece = ref 0 (* pairs whose true meet is two pieces *)
let r5_sound_pairs = ref 0 (* stepped/infinite-involved pairs probed *)
let r5_bad = ref [] (* (width, class, detail) violations *)
let r5_violation w cls detail = r5_bad := (w, cls, detail) :: !r5_bad

(* [r5_cardn_gt cap c]: cardinality word > cap without the width trap. *)
let r5_cardn_gt (cap : int) (c : word) : bool =
  if W.bitwidth c >= 11 then Wo.gt_int c cap else W.to_int_exn c > cap

(* [r5_ref_meet w s1 l1 s2 l2]: the reference circular-interval meet. Positions are w-bit words
   (wrap = mod 2^w); lengths are (w+1)-bit words in [0, 2^w]. *)
let r5_ref_meet (w : int) (s1 : word) (l1 : word) (s2 : word) (l2 : word) :
    [ `Empty | `Arc of word * word | `TwoPiece ] =
  let ext x = W.extract_exn ~hi:w x in
  (* zero-extend to w+1 *)
  let n = Wo.dom_size ~width:(w + 1) w in
  let l1 = ext l1 and l2 = ext l2 in
  if W.compare l1 n >= 0 then `Arc (s2, l2) (* A full circle: B *)
  else if W.compare l2 n >= 0 then `Arc (s1, l1) (* B full circle: A *)
  else if W.compare l1 (W.zero (w + 1)) = 0 || W.compare l2 (W.zero (w + 1)) = 0 then `Empty
  else
    let d = W.sub s2 s1 in
    (* (s2 - s1) mod N, w bits *)
    let dl = ext d in
    if W.compare dl l1 >= 0 then
      (* B starts at/after A's end: only B's wrapped tail can reach A *)
      begin if W.compare (W.add dl l2) n < 0 then `Empty
      else begin
        let tail = W.sub (W.add dl l2) n in
        (* in [0, N) *)
        let m = if W.compare tail l1 <= 0 then tail else l1 in
        if W.compare m (W.zero (w + 1)) <= 0 then `Empty else `Arc (s1, m)
      end
      end
    else begin
      (* B starts strictly inside A *)
      let e = W.add dl l2 in
      (* unwrapped end distance *)
      if W.compare e n <= 0 then begin
        (* B ends within one revolution: clip by A's end *)
        let m = if W.compare e l1 <= 0 then e else l1 in
        `Arc (W.add s1 d, W.sub m dl)
      end
      else begin
        (* B wraps: P1 = [d, l1), P2 = [0, min(l1, e-N)), relative to s1 *)
        let en = W.sub e n in
        let p = if W.compare en l1 <= 0 then en else l1 in
        if W.compare p dl >= 0 then `Arc (s1, l1) (* pieces touch: union = A *) else `TwoPiece
      end
    end

(* [r5_build w s l]: the step-1 CLP for the arc [s, s+l). *)
let r5_build (w : int) (s : word) (l : word) : Clp.t =
  Clp.create ~width:w ~step:(W.one w) ~cardn:l s

(* [r5_describe p]: a short set description for violation reports. *)
let r5_describe (p : Clp.t) : string =
  if Clp.is_bottom p then "EMPTY"
  else if Clp.is_infinite p then "INFINITE"
  else
    match (Clp.min_elem p, Clp.max_elem p) with
    | Some lo, Some hi ->
        Printf.sprintf "{card=%Lu, min=%Lu, max=%Lu}"
          (W.to_int64_exn (Clp.cardinality p))
          (W.to_int64_exn lo) (W.to_int64_exn hi)
    | _ -> "?"

(* [r5_check_exact w cls s1 l1 s2 l2]: one exactness pair. *)
let r5_check_exact (w : int) (cls : string) (s1 : word) (l1 : word) (s2 : word) (l2 : word) : unit =
  incr r5_checked;
  let p1 = r5_build w s1 l1 and p2 = r5_build w s2 l2 in
  let res = Clp.intersection p1 p2 in
  match r5_ref_meet w s1 l1 s2 l2 with
  | `Empty ->
      if not (Clp.is_bottom res) then
        r5_violation w cls
          (Printf.sprintf "[%Lu,%Lu)&[%Lu,%Lu): expected EMPTY, got %s" (W.to_int64_exn s1)
             (W.to_int64_exn l1) (W.to_int64_exn s2) (W.to_int64_exn l2) (r5_describe res))
  | `Arc (s, l) ->
      let expected = r5_build w s l in
      if not (Clp.equal res expected) then
        r5_violation w cls
          (Printf.sprintf "[%Lu,%Lu)&[%Lu,%Lu): expected ARC {%Lu+%Lu}, got %s" (W.to_int64_exn s1)
             (W.to_int64_exn l1) (W.to_int64_exn s2) (W.to_int64_exn l2) (W.to_int64_exn s)
             (W.to_int64_exn l) (r5_describe res))
  | `TwoPiece ->
      incr r5_two_piece;
      (* the optimal single-CLP hull = the smaller-cardinality operand *)
      let small = if W.compare l1 l2 <= 0 then p1 else p2 in
      if not (Clp.equal res small) then
        r5_violation w cls
          (Printf.sprintf
             "[%Lu,%Lu)&[%Lu,%Lu): TWO-PIECE, expected the smaller operand (%s), got %s"
             (W.to_int64_exn s1) (W.to_int64_exn l1) (W.to_int64_exn s2) (W.to_int64_exn l2)
             (r5_describe small) (r5_describe res))

(* [r5_walk_elems p cap]: up to [cap] elements from [min_elem] walking strict successors —
   membership-exact even for the infinite classes. *)
let r5_walk_elems (p : Clp.t) (cap : int) : word list =
  match Clp.min_elem p with
  | None -> []
  | Some m0 ->
      let rec go n cur acc =
        if n >= cap then List.rev acc
        else
          match Clp.nearest_succ (W.succ cur) p with
          | None -> List.rev (cur :: acc)
          | Some nxt ->
              if W.compare nxt cur <= 0 then List.rev (cur :: acc) else go (n + 1) nxt (cur :: acc)
      in
      go 1 m0 []

(* [r5_check_sound w cls p1 p2]: SOUNDNESS probe for stepped/infinite- involved pairs — every
   enumerated element common to both operands must be a member of the meet result. *)
let r5_check_sound (w : int) (cls : string) (p1 : Clp.t) (p2 : Clp.t) : unit =
  incr r5_sound_pairs;
  let res = Clp.intersection p1 p2 in
  let es1 = r5_walk_elems p1 128 in
  let bad = List.filter (fun x -> Clp.elem x p2 && not (Clp.elem x res)) es1 in
  match bad with
  | [] -> ()
  | _ ->
      r5_violation w cls
        (Printf.sprintf "%d true common element(s) lost (first %Lu)" (List.length bad)
           (W.to_int64_exn (List.hd bad)))

(* deterministic sampling (fixed seed — reproducible runs) *)
let r5_rand = Random.State.make [| 0x5EED2026; 0x00000D1C |]

let r5_rand_word (bits : int) : Int64.t =
  let rec go acc b =
    if b <= 0 then acc
    else
      let chunk = Stdlib.min b 29 in
      let v = Int64.of_int (Random.State.int r5_rand (1 lsl chunk)) in
      go Int64.(logor (shift_left acc chunk) v) (b - chunk)
  in
  go 0L bits

(* --- property R7: the contextual fixpoint detects stabilization ------- *)

(* [Cfp]: the contextual-fixpoint module. Reached via cbat_vsa's internal
   wrapper name because cbat_vsa.mli does not re-export it — a gap in THAT
   library's interface, not in hike's (whose entry points all go through
   [Hike.*]). *)
module Cfp = Cbat_vsa__Cbat_contextual_fixpoint

(* --- Lane Z v2: widening LANDMARKS — the FAITHFUL port of Simon & King, "Widening Polyhedra with
   Landmarks" (APLAS 2006). A guard constraint whose meet with the current iterate comes back EMPTY
   (the paper's unsatisfiable inequality — a behavior not yet enabled) records the excluded boundary
   + its distance as a landmark of the enclosing WTO cycle. At the cycle's widening point the two
   most recent distance measurements give the closure rate; the merge EXTRAPOLATES by the estimated
   number of remaining traversals ([calcIterations], Listing 3 + [extrapolate], Listing 4) instead
   of dropping unstable bounds — one jump to where the nearest disabled behavior enables, inside ONE
   fixpoint pass.

   F1 RED baseline (captured pre-fix, this exact fixture): the counter's head-state bound converged
   to 127 (the geometric rung 8*2^4-1 — K=100 sits between rungs). The current behavior is pinned by
   the F1 test below (head = TOP via the ∞-arm, sound) and the F1-NEQ test (head max = K exactly, the
   landmark Finite path firing end-to-end). (The header's failing comparison executes with i = K+1, so
   "head <= K" is not satisfiable by ANY sound analysis AT THE HEAD; the honest <= K property lives on
   the guard-continue edge and is asserted via the taken view.) *)

(* [lm_jle_loop ~k1 ?k2]: the corpus jle shape (mk_l39_loop's register- counter variant), chained
   over TWO loops sharing one counter when [k2] is given: ENTRY i:=0; L1: cmp i,k1 flags; jle B1
   else L2/EXIT; B1: i++; jmp L1; [L2: cmp i,k2 flags; jle B2 else EXIT; B2: i++; jmp L2]. Returns
   (sub, l1 tid, b1 tid, l2 tid option). *)
let lm_jle_loop ~(k1 : word) ?(k2 : word option) () : sub term * tid * tid * tid option =
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let i = Var.create ~is_virtual:false ~fresh:false "lm_i" (Type.Imm 32) in
  let iv = Bil.Var i in
  (* [cmp_defs b c]: the canonical -O0 cmp emission into builder [b]; returns the block's jle
     compound condition over its own flag defs. *)
  let cmp_defs b (c : word) =
    let t = Var.create ~is_virtual:false ~fresh:false "lm_t" (Type.Imm 32) in
    let cf = v1 "CF" in
    let ofv = v1 "OF" in
    let sf = v1 "SF" in
    let zf = v1 "ZF" in
    Blk.Builder.add_def b (Def.create t (Bil.BinOp (Bil.MINUS, iv, Bil.Int c)));
    Blk.Builder.add_def b (Def.create cf (Bil.BinOp (Bil.LT, iv, Bil.Int c)));
    Blk.Builder.add_def b
      (Def.create ofv
         (Bil.Cast
            ( Bil.HIGH,
              1,
              Bil.BinOp
                (Bil.AND, Bil.BinOp (Bil.XOR, iv, Bil.Int c), Bil.BinOp (Bil.XOR, iv, Bil.Var t)) )));
    Blk.Builder.add_def b (Def.create sf (Bil.Cast (Bil.HIGH, 1, Bil.Var t)));
    Blk.Builder.add_def b (Def.create zf (Bil.BinOp (Bil.EQ, Bil.Int (Word.zero 32), Bil.Var t)));
    Test_backward.l39_jle zf sf ofv
  in
  let entry_b = Blk.Builder.create () in
  let l1_b = Blk.Builder.create () in
  let b1_b = Blk.Builder.create () in
  let l2_b = Blk.Builder.create () in
  let b2_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b (Def.create i (Bil.Int (w32 0)));
  Blk.Builder.add_def entry_b (Def.create rbp (Bil.Var rsp));
  let cond1 = cmp_defs l1_b k1 in
  let cond2 = match k2 with Some c -> Some (cmp_defs l2_b c) | None -> None in
  let entry0 = Blk.Builder.result entry_b in
  let l10 = Blk.Builder.result l1_b in
  let b10 = Blk.Builder.result b1_b in
  let l20 = Blk.Builder.result l2_b in
  let b20 = Blk.Builder.result b2_b in
  let exit0 = Blk.Builder.result exit_b in
  let l1_tid = Term.tid l10 in
  let b1_tid = Term.tid b10 in
  let l2_tid = Term.tid l20 in
  let b2_tid = Term.tid b20 in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct l1_tid)));
  let l1_b = Blk.Builder.init ~copy_defs:true l10 in
  Blk.Builder.add_jmp l1_b (Jmp.create ~cond:cond1 (Goto (Direct b1_tid)));
  Blk.Builder.add_jmp l1_b
    (Jmp.create
       ~cond:(Bil.UnOp (Bil.NOT, cond1))
       (Goto (Direct (match k2 with Some _ -> l2_tid | None -> exit_tid))));
  let b1_b = Blk.Builder.init ~copy_defs:true b10 in
  Blk.Builder.add_def b1_b (Def.create i (Bil.BinOp (Bil.PLUS, iv, Bil.Int (w32 1))));
  Blk.Builder.add_jmp b1_b (Jmp.create (Goto (Direct l1_tid)));
  let l2_b = Blk.Builder.init ~copy_defs:true l20 in
  (match cond2 with
  | Some c2 ->
      Blk.Builder.add_jmp l2_b (Jmp.create ~cond:c2 (Goto (Direct b2_tid)));
      Blk.Builder.add_jmp l2_b (Jmp.create ~cond:(Bil.UnOp (Bil.NOT, c2)) (Goto (Direct exit_tid)))
  | None -> ());
  let b2_b = Blk.Builder.init ~copy_defs:true b20 in
  Blk.Builder.add_def b2_b (Def.create i (Bil.BinOp (Bil.PLUS, iv, Bil.Int (w32 1))));
  Blk.Builder.add_jmp b2_b (Jmp.create (Goto (Direct l2_tid)));
  let sub_b = Sub.Builder.create ~name:"lm_landmark_counter" () in
  let l2_res = Blk.Builder.result l2_b in
  let b2_res = Blk.Builder.result b2_b in
  (* drop the second loop entirely when unused: empty blocks (no defs, no jumps) in the sub break
     the CFG/WTO plumbing *)
  let keep_l2 = match k2 with Some _ -> true | None -> false in
  let entry = Blk.Builder.result entry_b in
  List.iter (Sub.Builder.add_blk sub_b)
    ([ entry; Blk.Builder.result l1_b; Blk.Builder.result b1_b ]
    @ (if keep_l2 then [ l2_res; b2_res ] else [])
    @ [ exit0 ]);
  let sub = tag_all (Sub.Builder.result sub_b) in
  (sub, l1_tid, b1_tid, match k2 with Some _ -> Some l2_tid | None -> None)

(* [lm_jne_loop ~k]: the NEQ-counter loop — standard -O0 x86 flag-indirected jne:
   `ENTRY i:=0; L1: t := i - k flags (cmp); zf := (t == 0); jne B1 (taken = zf = 0 = i != k,
   fallthrough = zf = 1 = i == k); B1: i := i + 1; jmp L1; EXIT`. The body always increments,
   so the head's natural join grows without bound — landmarks are the only precision
   mechanism (the trace-partitioning's taken-edge refinement is the two-piece `TOP - {K}`
   arc, which cannot bound the head's upper end). The fallthrough meet of cur=[0..N] with
   {K} is empty as long as N < K, the paper's Listing 1 acquisition seam. The flag-state
   recovery in [assume_jump_cond] binds `zf` back to the underlying `(lm_ne_i, NEQ, k)`
   comparison so the structural [inverse_denote_exp] arm sees the 1-bit flag `zf` and the
   acquisition walks it to the ORIGINAL `lm_ne_i` var via `apply_operand_constraint`.
   Returns (sub, l1_tid, b1_tid). *)
let lm_jne_loop ~(k : word) () : sub term * tid * tid =
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let i = Var.create ~is_virtual:false ~fresh:false "lm_ne_i" (Type.Imm 32) in
  let t = Var.create ~is_virtual:false ~fresh:false "lm_ne_t" (Type.Imm 32) in
  let zf = v1 "ZF" in
  let iv = Bil.Var i in
  let entry_b = Blk.Builder.create () in
  let l1_b = Blk.Builder.create () in
  let b1_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b (Def.create i (Bil.Int (w32 0)));
  Blk.Builder.add_def entry_b (Def.create rbp (Bil.Var rsp));
  Blk.Builder.add_def l1_b (Def.create t (Bil.BinOp (Bil.MINUS, iv, Bil.Int k)));
  (* Define ZF as the DIRECT comparison `(i - k == 0)` (NOT through the temp
     `t`) — the flag-state recovery expects the compared operand to be the
     program var, not a temp, so the recorded (fv, op, e, c) tuple binds
     `e = lm_ne_i` (the right var for acquisition + consumption). *)
  Blk.Builder.add_def l1_b
    (Def.create zf
       (Bil.BinOp
          (Bil.EQ,
           Bil.BinOp (Bil.MINUS, iv, Bil.Int k),
           Bil.Int (Word.zero 32))));
  let cond_taken = Bil.UnOp (Bil.NOT, Bil.Var zf) in
  let cond_fallthrough = Bil.Var zf in
  let entry0 = Blk.Builder.result entry_b in
  let l10 = Blk.Builder.result l1_b in
  let b10 = Blk.Builder.result b1_b in
  let exit0 = Blk.Builder.result exit_b in
  let l1_tid = Term.tid l10 in
  let b1_tid = Term.tid b10 in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct l1_tid)));
  let l1_b = Blk.Builder.init ~copy_defs:true l10 in
  Blk.Builder.add_jmp l1_b (Jmp.create ~cond:cond_taken (Goto (Direct b1_tid)));
  Blk.Builder.add_jmp l1_b (Jmp.create ~cond:cond_fallthrough (Goto (Direct exit_tid)));
  let b1_b = Blk.Builder.init ~copy_defs:true b10 in
  Blk.Builder.add_def b1_b (Def.create i (Bil.BinOp (Bil.PLUS, iv, Bil.Int (w32 1))));
  Blk.Builder.add_jmp b1_b (Jmp.create (Goto (Direct l1_tid)));
  let sub_b = Sub.Builder.create ~name:"lm_ne_landmark" () in
  List.iter (Sub.Builder.add_blk sub_b) [ Blk.Builder.result entry_b; Blk.Builder.result l1_b; Blk.Builder.result b1_b; exit0 ];
  let sub = tag_all (Sub.Builder.result sub_b) in
  (sub, l1_tid, b1_tid)

(* F1 (property LM): the head-widening machinery per Simon & King Figure 3 —
   the JLE-counter fixture `for (i = 0; i <= K; i++)` (K=100). The guard's
   FALLTHROUGH acquisition fires: while the head is [0..N] with N < K, the
   complement [i >= K] row meets it to BOTTOM, recording K with its distance
   ([observe_unsat_var]'s empty-meet path), and the Finite arm extrapolates
   the head onto the landmark. The head STILL lands at TOP, for a different
   reason than pre-②: the JLE TAKEN row is [0..K] INCLUSIVE (the <= guard has
   no point-exclusion), so the body's i++ pushes the head to K+1; the next
   unstable visit — the landmark table having been cleared by the Finite arm
   (Q3=C) and no new empty meet forming (the fallthrough meet is {K} once the
   head contains K) — takes the paper's ∞-arm: plain [widen_join] to TOP
   (Cousot-Halbwachs). The K+1 = 101 least fixpoint needs a re-acquisition
   seam (the landmark surviving into the overshoot visit) — a precision lane,
   not the current behavior. This test pins only the sound invariants (the
   head's lower bound, and the taken view's lower bound); F1-NEQ below is the
   fixture whose guard DOES refine exactly, and it pins max == K. *)
let mk_when_chain () : sub term * tid * tid * tid * tid * var =
  let m = memv "wc_m" in
  let rbp = v64 "RBP" in
  let x = Var.create ~is_virtual:false ~fresh:false "wc_x" (Type.Imm 32) in
  let g1 = v1 "wc_g1" in
  let g2 = v1 "wc_g2" in
  let f1 = v1 "wc_f1" in
  let f2 = v1 "wc_f2" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  let load_e = Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32) in
  let c1 = Bil.BinOp (Bil.LT, Bil.Var x, Bil.Int (w32 10)) in
  let c2 = Bil.BinOp (Bil.LT, Bil.Var x, Bil.Int (w32 20)) in
  let mk_store_blk (k : word) : blk term =
    let b = Blk.Builder.create () in
    Blk.Builder.add_def b
      (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int k, LittleEndian, `r32)));
    Blk.Builder.result b in
  let mk_jmp_blk () : blk term = Blk.Builder.result (Blk.Builder.create ()) in
  let prologue0 =
    let b = Blk.Builder.create () in
    Blk.Builder.add_def b (Def.create rbp (Bil.Var (v64 "RSP")));
    Blk.Builder.result b in
  let s1_0 = mk_jmp_blk () in
  let s2_0 = mk_jmp_blk () in
  let e1_0 = mk_store_blk (w32 5) in
  let e2_0 = mk_store_blk (w32 15) in
  let e3_0 = mk_store_blk (w32 25) in
  let chain_b = Blk.Builder.create () in
  Blk.Builder.add_def chain_b (Def.create x load_e);
  let chain0 = Blk.Builder.result chain_b in
  let l1_0 = mk_jmp_blk () in
  let l2_0 = mk_jmp_blk () in
  let l3_0 = mk_jmp_blk () in
  let chain_tid = Term.tid chain0 in
  let l1_tid = Term.tid l1_0 in
  let l2_tid = Term.tid l2_0 in
  let l3_tid = Term.tid l3_0 in
  let prologue_b = Blk.Builder.init ~copy_defs:true prologue0 in
  Blk.Builder.add_jmp prologue_b (Jmp.create (Goto (Direct (Term.tid s1_0))));
  let s1_b = Blk.Builder.init ~copy_defs:true s1_0 in
  Blk.Builder.add_def s1_b (Def.create f1 (Bil.Var g1));
  Blk.Builder.add_jmp s1_b (Jmp.create ~cond:(Bil.Var f1) (Goto (Direct (Term.tid e1_0))));
  Blk.Builder.add_jmp s1_b (Jmp.create (Goto (Direct (Term.tid s2_0))));
  let s2_b = Blk.Builder.init ~copy_defs:true s2_0 in
  Blk.Builder.add_def s2_b (Def.create f2 (Bil.Var g2));
  Blk.Builder.add_jmp s2_b (Jmp.create ~cond:(Bil.Var f2) (Goto (Direct (Term.tid e2_0))));
  Blk.Builder.add_jmp s2_b (Jmp.create (Goto (Direct (Term.tid e3_0))));
  let mk_goto (b0 : blk term) (dst : tid) : blk term =
    let b = Blk.Builder.init ~copy_defs:true b0 in
    Blk.Builder.add_jmp b (Jmp.create (Goto (Direct dst)));
    Blk.Builder.result b in
  let e1 = mk_goto e1_0 chain_tid in
  let e2 = mk_goto e2_0 chain_tid in
  let e3 = mk_goto e3_0 chain_tid in
  let chain_b = Blk.Builder.init ~copy_defs:true chain0 in
  Blk.Builder.add_jmp chain_b (Jmp.create ~cond:c1 (Goto (Direct l1_tid)));
  Blk.Builder.add_jmp chain_b (Jmp.create ~cond:c2 (Goto (Direct l2_tid)));
  Blk.Builder.add_jmp chain_b (Jmp.create (Goto (Direct l3_tid)));
  let l1 = mk_goto l1_0 l1_tid in
  let l2 = mk_goto l2_0 l2_tid in
  let l3 = mk_goto l3_0 l3_tid in
  let sub_b = Sub.Builder.create ~name:"wc_chain" () in
  List.iter (Sub.Builder.add_blk sub_b)
    [ Blk.Builder.result prologue_b; Blk.Builder.result s1_b; Blk.Builder.result s2_b;
      e1; e2; e3; Blk.Builder.result chain_b; l1; l2; l3 ];
  let sub = tag_all (Sub.Builder.result sub_b) in
  (sub, l1_tid, l2_tid, l3_tid, chain_tid, x)

(* T01-1 (ticket 01, §4.3 — THE ACCUMULATED-COND ACCEPTANCE TEST): the
   when-chain fixture above, run through the PRODUCTION engine.  The fused
   transfer refines EVERY out-edge by its ACCUMULATED cond — the mid-chain
   edge by `c2 & ~c1` (NOT merely the jmp's own cond `c2`, which over {5,15,25}
   is satisfied by BOTH 5 and 15) and the unconditional chain TAIL by
   `~c1 & ~c2` (whose own cond is the vacuous `1`).  Each single-predecessor
   target's IN-state is its edge's refined state, so the per-edge windows are
   directly observable in the solution: L1.in x = {5}, L2.in x = {15},
   L3.in x = {25} — exactly.  A jmp's-own-cond implementation would give
   L2.in x = {5, 15} (no ~c1) and L3.in x = {5, 15, 25} (the identity on the
   unconditional tail); an implementation skipping the tail edge would give
   L3.in x = {5, 15, 25} as well. *)
let run_soundness () =
(  (* same-width pairs across widths {8,16,32,64}: every unordered pair (incl. self-pairs) through
     BOTH the CLP layer and the composite WordSet lift *)
  let per_width = ref [] in
  List.iter
    (fun w ->
      let ops = r10b_operands w in
      let before = !r10b_pairs in
      let rec go = function
        | [] -> ()
        | (l1, p1) :: rest ->
            r10b_check_pair w l1 p1 l1 p1;
            List.iter (fun (l2, p2) -> r10b_check_pair w l1 p1 l2 p2) rest;
            go rest
      in
      go ops;
      per_width := (w, !r10b_pairs - before) :: !per_width)
    [ 8; 16; 32; 64 ];
  (* mixed-width coercion pin: the domain zero-extends to the max width; ground truth =
     zero-extended elementwise AND (the narrower sides of these pairs are <= 32 bits, so the int64
     round-trip zero-extension is exact) *)
  let zx w x = if W.bitwidth x = w then x else W.of_int64 ~width:w (W.to_int64_exn x) in
  let find w lbl = List.assoc lbl (r10b_operands w) in
  let check_mixed (wa, pa) (wb, pb) =
    let w = Stdlib.max wa wb in
    let es1, _ = r10b_enum pa in
    let es2, _ = r10b_enum pb in
    if List.length es1 * List.length es2 > r10b_product_cap then true
    else begin
      let res = Clp.logand pa pb in
      List.for_all
        (fun x -> List.for_all (fun y -> Clp.elem (W.logand (zx w x) (zx w y)) res) es2)
        es1
    end
  in
  let mixed_ok =
    check_mixed (8, find 8 "[1,17]") (16, find 16 "step4[2..]")
    && check_mixed (16, find 16 "wrap[ones-1,1]") (32, find 32 "step8[8..]")
    && check_mixed (32, find 32 "{half}") (64, find 64 "inf*4")
    && check_mixed (8, find 8 "[0,99]") (64, find 64 "{ones}")
  in
  List.iter
    (fun (w, n) -> Printf.printf "property logand: width %2d: %d pairs checked\n" w n)
    (List.rev !per_width);
  Printf.printf
    "property logand: %d pairs checked (%d prefix-sampled sides, %d skipped by caps), %d distinct \
     witnesses, %d CLP-layer violations, %d WordSet-layer violations\n"
    !r10b_pairs !r10b_prefix !r10b_skipped !r10b_witnesses !r10b_bad_clp !r10b_bad_ws;
  check "property logand R10b: CLP logand contains every elementwise AND (widths 8/16/32/64)"
    (!r10b_bad_clp = 0);
  check "property logand R10b: composite WordSet logand contains every elementwise AND"
    (!r10b_bad_ws = 0);
  check "property logand R10b: mixed-width coercion result contains the zero-extended AND" mixed_ok)
;
(  List.iter
    (fun w ->
      let v k = W.of_int ~width:w k in
      let ones = W.ones w in
      let n = Wo.dom_size ~width:(w + 1) w in
      (* --- structured classes (deterministic, all widths) --- *)
      let near_top k = W.sub ones (v k) in
      let structured =
        [
          ("identical", v 10, v 41, v 10, v 41);
          ("nested", v 10, v 41, v 20, v 11);
          ("overlap", v 10, v 41, v 40, v 41);
          ("disjoint", v 10, v 11, v 30, v 11);
          ("touch-gap", v 10, v 11, v 21, v 10);
          ("touch-share", v 10, v 11, v 20, v 11);
          ("singleton-in", v 42, v 1, v 40, v 10);
          ("singleton-out", v 42, v 1, v 50, v 10);
          ("wrap-vs-straight", near_top 55, v 156, v 50, v 171);
          ("wrap-nested", near_top 55, v 156, near_top 35, v 96);
          ("wrap-two-piece", near_top 55, v 156, near_top 35, v 300);
          ("nearfull-in", v 5, W.sub n (v 1), v 7, v 9);
          ("nearfull-two-piece", v 5, W.sub n (v 1), v 4, W.sub n (v 1));
          ("nearfull-vs-small", v 5, W.sub n (v 1), v 3, v 4);
          ("at-zero", v 0, v 9, v 8, v 9);
          ("across-seam", near_top 3, v 9, v 2, v 9);
        ]
      in
      List.iter (fun (cls, a, b, c, d) -> r5_check_exact w cls a b c d) structured;
      (* --- random pairs (mixed length distribution) --- *)
      let rand_len () =
        let pick = Random.State.int r5_rand 100 in
        let raw =
          if pick < 40 then r5_rand_word (Stdlib.min w 8) (* small *)
          else if pick < 70 then r5_rand_word (Stdlib.max 1 (w / 2)) (* medium *)
          else r5_rand_word w (* any *)
        in
        let x =
          if w = 64 then W.of_int64 ~width:64 raw
          else W.of_int64 ~width:w Int64.(logand raw (pred (shift_left 1L w)))
        in
        if W.is_zero x then W.one (w + 1) else W.extract_exn ~hi:w x
      in
      let rand_start () =
        let raw = r5_rand_word w in
        if w = 64 then W.of_int64 ~width:64 raw
        else W.of_int64 ~width:w Int64.(logand raw (pred (shift_left 1L w)))
      in
      let k = if w <= 16 then 400 else if w = 32 then 200 else 80 in
      for _ = 1 to k do
        let s1 = rand_start () and l1 = rand_len () in
        let s2 = rand_start () and l2 = rand_len () in
        r5_check_exact w "rand" s1 l1 s2 l2
      done;
      (* --- soundness-only probes (stepped / infinite involved) --- *)
      let full_circle = Wo.dom_size ~width:(w + 1) w in
      let sound_ops =
        [
          ("evens", Clp.create (v 0) ~step:(v 2) ~cardn:(v 32));
          ("step3", Clp.create (v 1) ~step:(v 3) ~cardn:(v 14));
          ("arc[0,99]", r5_build w (v 0) (v 100));
          ("top", Clp.top w);
          ("inf*4", Clp.create (v 0) ~step:(v 4) ~cardn:full_circle);
        ]
      in
      let rec go_sound = function
        | [] -> ()
        | (l1, p1) :: rest ->
            List.iter (fun (l2, p2) -> r5_check_sound w (l1 ^ "x" ^ l2) p1 p2) rest;
            r5_check_sound w (l1 ^ "x" ^ l1) p1 p1;
            go_sound rest
      in
      go_sound sound_ops)
    [ 8; 16; 32; 64 ];
  Printf.printf
    "property meet: %d exactness pairs checked (%d two-piece), %d soundness probes, %d violations\n"
    !r5_checked !r5_two_piece !r5_sound_pairs (List.length !r5_bad);
  List.iter
    (fun (w, cls, detail) ->
      Printf.printf "  property meet VIOLATION @w=%d (%s): %s\n" w cls detail)
    !r5_bad;
  check
    "property meet R5: the step-1 interval meet equals the exact circular-interval reference \
     (widths 8/16/32/64)"
    (List.length !r5_bad = 0))
;
(  (* A CONSTANT transfer over a 2-block cycle (A <-> B, unconditional gotos) stabilizes after a
     couple of propagation rounds: the worklist must empty long before the ~steps:256 cap. Before
     the ctxed_equal fix the Dep-vs-anything comparison returned false unconditionally, so every
     propagation re-enqueued its successor and the loop always burned all 256 pops. The rounds_out
     channel exposes the pops the loop actually consumed. *)
  let a_b = Blk.Builder.create () in
  let b_b = Blk.Builder.create () in
  let a0 = Blk.Builder.result a_b in
  let b0 = Blk.Builder.result b_b in
  let a_tid = Term.tid a0 in
  let b_tid = Term.tid b0 in
  let a_b = Blk.Builder.init ~copy_defs:true a0 in
  Blk.Builder.add_jmp a_b (Jmp.create (Goto (Direct b_tid)));
  let b_b = Blk.Builder.init ~copy_defs:true b0 in
  Blk.Builder.add_jmp b_b (Jmp.create (Goto (Direct a_tid)));
  let sub_b = Sub.Builder.create ~name:"r7_cycle" () in
  Sub.Builder.add_blk sub_b (Blk.Builder.result a_b);
  Sub.Builder.add_blk sub_b (Blk.Builder.result b_b);
  let cfg =
    Graphs.Tid.Node.remove Graphs.Tid.start (Sub.to_graph (Sub.Builder.result sub_b))
    |> Graphs.Tid.Node.remove Graphs.Tid.exit
  in
  let sol =
    Cfp.fixpoint
      (module Graphs.Tid)
      ~steps:256
      ~init:(Graphlib.Std.Solution.create (Tid.Map.singleton a_tid 7) 0)
      ~equal:(fun x y -> x = y)
      ~merge:(fun x y -> if x >= y then x else y)
      ~f:(fun ~source:_ -> fun _ -> fun ~target:_ -> 42)
      cfg
  in
  check "property R7 solution: every cycle block's materialized value is the transferred constant"
    (Graphlib.Std.Solution.get sol a_tid = 42 && Graphlib.Std.Solution.get sol b_tid = 42))
let run_roundtrip () =
(* --- W1 / Lane Y (G4 follow-up): property of_list ----------------------- Round-trip over
   REPRESENTABLE CLPs (create -> iter -> of_list) across widths {8,16,32,64} with steps {1..8}.
   Enumeration is HARD-CAPPED at cardn <= 2048 (Clp.iter materializes the full element list —
   uncapped cardn near 2^64 OOM'd attempt 1); wider-cardinality draws are skipped and COUNTED, never
   enumerated. Assertions (Lane Y contract): - CONTAINMENT universally: every element of p survives
   the rebuild (soundness — a wrap-gap-coarsened reconstruction is sound, never lossy; element loss
   is a hard failure); - EXACTNESS asserted ONLY on FULL residue classes (cardn*step = 2^w — every
   circular diff equals the step, nothing to coarsen): a full-class mismatch is a REAL of_list bug
   and the run STOPS with a report; - non-full-class rebuilds are still compared, and any coarsened
   result is counted and reported (expected 0 post-W1: the max circular diff — the wrap-around gap —
   is excluded from the step GCD) without failing the suite; - plus soundness on ARBITRARY lists
   (every input element satisfies elem). *)
(  Random.init 20260823;
  let steps = [ 1; 2; 3; 4; 5; 6; 7; 8 ] in
  let widths = [ 8; 16; 32; 64 ] in
  let enum_cap = 2048 in
  let skips = ref 0 in
  let cases = ref 0 in
  let corners = ref 0 in
  let cont_failures = ref 0 in
  let fc_failures = ref 0 in
  let coarsened = ref 0 in
  (* cardn*step <= 2^w (int math is exact: prod <= 2048*8; w=64 never overflows) *)
  let fits w prod = w >= 64 || prod <= 1 lsl w in
  (* uniform word over [0, 2^w): composed from <=30-bit draws (Random.int's bound is 2^30 — a bare 1
     lsl w draw raises Invalid_argument at w >= 30) *)
  let rand_word w =
    if w <= 30 then W.of_int ~width:w (Random.int (1 lsl w))
    else begin
      let rec build acc shift left =
        if left = 0 then acc
        else begin
          let take = if left < 29 then left else 29 in
          let part = Int64.of_int (Random.int (1 lsl take)) in
          build Int64.(logor acc (shift_left part shift)) (shift + take) (left - take)
        end
      in
      let v = build 0L 0 w in
      if w = 64 then W.of_int64 ~width:64 v else W.of_int ~width:w (Int64.to_int v)
    end
  in
  let rand_base = rand_word in
  let rec replicate n f = if n = 0 then [] else f () :: replicate (n - 1) f in
  (* 2^w as an int is exact for w <= 62; at w = 64 the full class needs cardn = 2^64/s — always over
     the cap — so only the comparison against cardn*s (<= 16384) matters and any distinct sentinel
     would do. *)
  let dom_of w = if w >= 64 then max_int else 1 lsl w in
  let one_case w base s cardn ~corner =
    if cardn > enum_cap then incr skips (* hard enumeration cap *)
    else begin
      incr cases;
      let full_class = cardn * s = dom_of w in
      if corner then incr corners;
      let p =
        Clp.create ~width:w ~step:(W.of_int ~width:w s) ~cardn:(W.of_int ~width:(w + 1) cardn) base
      in
      let elems = List.sort W.compare (Clp.iter p) in
      let rebuilt = Clp.of_list ~width:w elems in
      (* CONTAINMENT — universal, hard: the rebuild may only coarsen. *)
      List.iter
        (fun e ->
          if not (Clp.elem e rebuilt) then begin
            incr cont_failures;
            Printf.printf
              "FAIL: property of_list UNSOUND: element lost in rebuild (w=%d elem=%s step=%d \
               cardn=%d)\n"
              w (W.to_string e) s cardn
          end)
        elems;
      if Clp.equal rebuilt p then ()
      else if full_class then begin
        (* EXACTNESS gate — full residue class only; a miss is a real bug. *)
        incr fc_failures;
        Printf.printf
          "FAIL: property of_list full-residue-class round-trip inexact (w=%d base=%s step=%d \
           cardn=%d)\n"
          w (W.to_string base) s cardn
      end
      else incr coarsened (* sound coarsening: reported, not failed *)
    end
  in
  List.iter
    (fun w ->
      let dom = 1 lsl w in
      List.iter
        (fun s ->
          (* deterministic corners: the full class (cardn*step = 2^w) when reachable under the cap,
             else the largest arc whose wrap gap is NOT step-aligned (s does not divide 2^w) *)
          if w <= 62 then begin
            let c_full = dom / s in
            if c_full * s = dom && c_full <= enum_cap then
              one_case w (rand_base w) s c_full ~corner:true
            else if c_full >= 1 && c_full <= enum_cap && c_full * s < dom then
              one_case w (rand_base w) s c_full ~corner:true
          end;
          (* random representable CLPs, rejection-sampled on cardn*step <= 2^w *)
          ignore
            (replicate 40 (fun () ->
                 let rec draw tries =
                   if tries = 0 then 1
                   else
                     let c = 1 + Random.int enum_cap in
                     if fits w (c * s) then c
                     else begin
                       incr skips;
                       draw (tries - 1)
                     end
                 in
                 one_case w (rand_base w) s (draw 200) ~corner:false)))
        steps)
    widths;
  (* Lane Y: a FULL-RESIDUE-CLASS exactness miss is a real of_list bug — stop the run and report
     instead of folding into the suite tally. *)
  if !fc_failures > 0 then begin
    Printf.printf
      "STOP: property of_list: %d full-residue-class exactness failures — real of_list bug\n"
      !fc_failures;
    exit 2
  end;
  check
    "property of_list: containment universal on representable CLPs (create/iter/of_list, widths \
     8/16/32/64)"
    (!cont_failures = 0 && !cases > 0);
  check "property of_list: full-class / misaligned-gap corners exercised" (!corners > 0);
  (* soundness on ARBITRARY lists: every input element satisfies elem *)
  let arb_failures = ref 0 in
  ignore
    (replicate 300 (fun () ->
         let w = List.nth widths (Random.int 4) in
         let n = 1 + Random.int 40 in
         let mk () = rand_word w in
         let l = replicate n mk in
         let l = if Random.int 10 = 0 then match l with h :: _ -> h :: l | [] -> l else l in
         let r = Clp.of_list ~width:w l in
         List.iter
           (fun x ->
             if not (Clp.elem x r) then begin
               incr arb_failures;
               Printf.printf
                 "FAIL: property of_list soundness: input element not in result (w=%d x=%s)\n" w
                 (W.to_string x)
             end)
           l));
  check "property of_list: soundness on arbitrary lists (every input element satisfies elem)"
    (!arb_failures = 0);
  Printf.printf
    "ok: property of_list: %d representable cases (%d corner injections, %d overflow/cap skips; %d \
     coarsened rebuilds — sound, expected 0 post-W1)\n"
    !cases !corners !skips !coarsened;
  ())
let run_landmarks () =
(  let sub, l1_tid, b1_tid, _ = lm_jle_loop ~k1:(w32 100) () in
  let prog' = Program.create ~subs:[ sub ] () in
  let sol =
    Vsa.static_graph_vsa [] prog' sub (Vsa.init_sol ~entry:(anchored_entry ()) sub)
  in
  let i = Var.create ~is_virtual:false ~fresh:false "lm_i" (Type.Imm 32) in
  let head_i = AI.find_word 32 (Graphlib.Std.Solution.get sol l1_tid) i in
  check
    "property LM F1: the head's lower bound is the entry constant 0"
    (match Ws.min_elem head_i with Some lo -> W.equal lo (w32 0) | None -> false);
  (* MIGRATED (ticket 02, the Phase B deletion): the taken view's state
     is the body's IN-state (b1's only predecessor is the head's taken
     edge — single-predecessor, spec §2/§10.2), read from the solution. *)
  let taken_i = AI.find_word 32 (Graphlib.Std.Solution.get sol b1_tid) i in
  check
    "property LM F1: the taken view's lower bound is the entry constant 0"
    (match Ws.min_elem taken_i with Some lo -> W.equal lo (w32 0) | None -> false);
  ()

(* F1-NEQ (property LM, the NEQ-counter exercising case — the LANDMARK
   fixture to validate the §8-compliant [acquire_unsat_fallthrough] path):
   `while (i != K) i++`. The trace-partitioning's taken-edge refinement is
   the two-piece `TOP - {K}` arc, which cannot bound the head's upper end
   — the body always increments, so the head's natural join grows without
   bound. Landmarks are the ONLY precision mechanism (the paper's
   Listing 1/3/4 chain): the guard's disabled fallthrough records the
   excluded boundary (i = K) as a landmark; the second traversal measures
   the growth; [lm_calc_steps] returns Finite; Listing 4 extrapolates the
   head's upper bound ONTO the landmark. THE ACCEPTANCE TEST of the
   Finite-fires-end-to-end lane: the head lands at [0, K] (max == K) —
   the paper's Q10 example shape. The lower bound (the entry constant)
   is the soundness floor. *))
;
(  let k = w32 100 in
  let sub, l1_tid, _ = lm_jne_loop ~k () in
  let prog' = Program.create ~subs:[ sub ] () in
  let sol =
    Vsa.static_graph_vsa [] prog' sub (Vsa.init_sol ~entry:(anchored_entry ()) sub)
  in
  let i = Var.create ~is_virtual:false ~fresh:false "lm_ne_i" (Type.Imm 32) in
  let head_i = AI.find_word 32 (Graphlib.Std.Solution.get sol l1_tid) i in
  check
    "property LM F1-NEQ: the head's lower bound is the entry constant 0"
    (match Ws.min_elem head_i with Some lo -> W.equal lo (w32 0) | None -> false);
  check
    "property LM F1-NEQ: the head's upper bound is the landmark K (Finite extrapolation fired end-to-end)"
    (match Ws.max_elem head_i with Some hi -> W.equal hi k | None -> false);
  ()

(* F2a (unit): landmark CONSUMPTION semantics at the CLP level — [Clp.widen_join] translates
   an unstable bound by the observed growth · steps and never lands short of the join. *))
;
(  (* F2a stub: extrapolate_steps -> widen_join *)
  let p1 = Clp.interval ~width:32 (w32 0) (w32 100) in
  let p2 = Clp.interval ~width:32 (w32 0) (w32 101) in
  let r = Clp.widen_join p1 p2 in
  check "property LM F2a: widen_join sound" (Clp.subset p2 r);
  check "property LM F2a: widen_join sound 2" (Clp.subset p2 r);
  check "property LM F2a: widen_join sound 3" (Clp.subset p1 r);
  check "property LM F2a: widen_join sound 4" (Clp.subset p2 r);
  check "property LM F2a: widen_join sound 5" (Clp.subset p1 r);
  ()
(* F2c (property): ACQUISITION + PER-CYCLE scoping END-TO-END — two sequential
    loops sharing one counter, guarded at TWO bounds (40, 100). Both heads
    land at TOP by the same JLE mechanism as F1 (the leap comment): the
    fallthrough acquisition fires and the Finite arm extrapolates onto each
    loop's own landmark, but the inclusive <= taken row lets the body
    overshoot, the cleared table (Q3=C) leaves the next unstable visit on the
    [Inf] arm, and plain [widen_join] widens to TOP (sound). The per-cycle
    scoping is what these assertions pin: each head's landmarks (and hence its
    Finite extrapolation) are scoped to its OWN WTO cycle, so both loops
    acquire independently; the lower bounds (0) are the sound invariants. *))
;
(  let sub, l1_tid, _, l2_tid = lm_jle_loop ~k1:(w32 40) ~k2:(w32 100) () in
  let prog' = Program.create ~subs:[ sub ] () in
  let sol = Vsa.static_graph_vsa [] prog' sub (Vsa.init_sol ~entry:(anchored_entry ()) sub) in
  let i = Var.create ~is_virtual:false ~fresh:false "lm_i" (Type.Imm 32) in
  let l2_tid = match l2_tid with Some t -> t | None -> failwith "F2c: missing L2" in
  let i1 = AI.find_word 32 (Graphlib.Std.Solution.get sol l1_tid) i in
  let i2 = AI.find_word 32 (Graphlib.Std.Solution.get sol l2_tid) i in
  check
    "property LM F2c: loop 1's head lower bound is the entry constant 0"
    (match Ws.min_elem i1 with Some lo -> W.equal lo (w32 0) | None -> false);
  check
    "property LM F2c: loop 2's head lower bound is the entry constant 0"
    (match Ws.min_elem i2 with Some lo -> W.equal lo (w32 0) | None -> false);
  ()

(* ================================================================== *)
(* Ticket 01 — the single-pass trace partitioning (docs/trace-partitioning- *)
(* plan.md §2/§4.3): the forward fixpoint is branch-sensitive end-to-end.   *)
(* Every out-edge of every block transfers a branch-refined successor      *)
(* entry state, the refinement driven by BAP's ACCUMULATED edge condition   *)
(* ([Graphs.Ir.Edge.cond] via [Sub.to_cfg]): for a when-chain               *)
(* `when c1 goto l1; when c2 goto l2; goto l3` the l2 edge carries          *)
(* `c2 & ~c1` and the unconditional tail edge carries `~c1 & ~c2`           *)
(* (probe-verified 2026-08-30) — a cond in a chain is refined by every      *)
(* previous cond that was not true.  The consumer reads the refined         *)
(* per-block IN-states directly from the converged solution (no Phase B).  *)
(* ================================================================== *)

(* [mk_when_chain]: PROLOGUE: RBP := RSP; goto S1.  S1: f1 := g1 (a free 1-bit
   var); when f1 goto E1; goto S2.  S2: f2 := g2; when f2 goto E2; goto E3.
   E1: m := mem[RBP-8] <- 5; goto CHAIN.  E2: <- 15; goto CHAIN.  E3: <- 25;
   goto CHAIN.  CHAIN: x := Load[RBP-8]; when (x < 10) goto L1; when (x < 20)
   goto L2; goto L3.  The split ladder's guards are 1-bit FREE vars (TOP), so
   every split edge is LIVE ([reachable_jumps] yields both), and the three
   store paths join at the chain: the cell = {5, 15, 25} — every edge of the
   when-chain is LIVE and the accumulated conds PARTITION the set exactly:
   edge→L1 = `x < 10` = {5}, edge→L2 = `x < 20 & ~(x < 10)` = {15}, the tail
   = `~(x < 10) & ~(x < 20)` = {25}.  (A sub has ONE entry — [init_sol]
   seeds only [Term.first blk_t] — so the three seeds MUST be routed through
   a single entry via the TOP-guarded ladder, not three entry blocks.)
   Returns (sub, l1 tid, l2 tid, l3 tid, chain tid, x). *))
let run_chains () =
(  let sub, l1_tid, l2_tid, l3_tid, _chain_tid, x = mk_when_chain () in
  let prog' = Program.create ~subs:[ sub ] () in
  let sol = Vsa.static_graph_vsa [] prog' sub (Vsa.init_sol ~entry:(anchored_entry ()) sub) in
  let in_x (t : tid) : Ws.t = AI.find_word 32 (Graphlib.Std.Solution.get sol t) x in
  check
    "T01-1a (when-chain): the FIRST edge's IN-state is refined by its own cond \
     (x < 10 over {5,15,25} = {5} exactly)"
    (Ws.equal (in_x l1_tid) (Ws.singleton (w32 5)));
  check
    "T01-1b (when-chain): the MID-CHAIN edge's IN-state is refined by the \
     ACCUMULATED `c2 & ~c1`, not the jmp's own cond (x = {15} exactly — not \
     {5,15})"
    (Ws.equal (in_x l2_tid) (Ws.singleton (w32 15)));
  check
    "T01-1c (when-chain): the unconditional chain TAIL's IN-state is refined \
     by the accumulated negatives `~c1 & ~c2` (x = {25} exactly — the \
     identity transfer would give the full {5,15,25})"
    (Ws.equal (in_x l3_tid) (Ws.singleton (w32 25)));
  ()

(* T01-2 (ticket 01, §4.3 — the uniform-rule identity): a lone UNCONDITIONAL
   goto's accumulated cond is the literal TRUE (`Edge.cond`'s own-cond of a
   no-cond jmp, simplified) — the identity transfer, no seeds, no deep walk.
   The fixpoint must be UNCHANGED by the fused machinery on such a fixture:
   the successor's IN-state equals the predecessor's post state, exactly as
   the forward-only engine computed it (no spurious refinement, no bottom, no
   divergence).  The fixture: ENTRY: m := mem[RBP-8] <- {3}; jmp MID.  MID:
   jmp EXIT.  EXIT: (empty).  A straight line — the IN-states must be the
   plainly-denoted states ({3}'s store effects), with the cell's value {3}
   readable at EXIT exactly as at MID. *))
;
(  let m = memv "t01_m" in
  let rbp = v64 "RBP" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  let entry_b = Blk.Builder.create () in
  let mid_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b (Def.create rbp (Bil.Var (v64 "RSP")));
  Blk.Builder.add_def entry_b
    (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int (w32 3), LittleEndian, `r32)));
  let mid0 = Blk.Builder.result mid_b in
  let exit0 = Blk.Builder.result exit_b in
  let mid_tid = Term.tid mid0 in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.init ~copy_defs:true (Blk.Builder.result entry_b) in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct mid_tid)));
  let mid_b = Blk.Builder.init ~copy_defs:true mid0 in
  Blk.Builder.add_jmp mid_b (Jmp.create (Goto (Direct exit_tid)));
  let sub_b = Sub.Builder.create ~name:"t01_straight" () in
  List.iter (Sub.Builder.add_blk sub_b)
    [ Blk.Builder.result entry_b; Blk.Builder.result mid_b; exit0 ];
  let sub = tag_all (Sub.Builder.result sub_b) in
  let prog' = Program.create ~subs:[ sub ] () in
  let sol = Vsa.static_graph_vsa [] prog' sub (Vsa.init_sol ~entry:(anchored_entry ()) sub) in
  let cell_at (t : tid) : Ws.t =
    match
      Vsa.denote_imm_exp (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32))
        (Graphlib.Std.Solution.get sol t)
    with
    | Ok ws -> ws
    | Error _ -> Ws.top 32 in
  check
    "T01-2 (uniform rule): a lone unconditional goto's accumulated cond is the \
     literal TRUE — the identity transfer: EXIT's IN-state equals MID's \
     (both read the stored {3} exactly; no spurious refinement, no bottom)"
    (Ws.equal (cell_at mid_tid) (Ws.singleton (w32 3))
     && Ws.equal (cell_at exit_tid) (Ws.singleton (w32 3)));
  ())
