(* Soundness properties, round-trips, landmark loops, when-chain pins. *)
open Bap.Std
open Bap_core_theory
open Test_common
open Test_fixtures
module W = Cbat_word

(* R10b: logand soundness over a sampled operand corpus. *)

(* Every elementwise AND of enumerated operands must land in the logand result. *)

let r10b_enum_cap = 1024 (* enum cap per side *)
let r10b_product_cap = 131072 (* product cap per pair *)
let r10b_pairs = ref 0 (* pairs checked *)
let r10b_skipped = ref 0 (* pairs skipped by caps *)
let r10b_prefix = ref 0 (* prefix-sampled sides *)
let r10b_witnesses = ref 0 (* ANDs checked *)
let r10b_bad_clp = ref 0 (* CLP violations *)
let r10b_bad_ws = ref 0 (* composite violations *)

(* [c] > [cap] without the width trap. *)
let r10b_cardn_gt (cap : int) (c : W.t) : bool =
  if Cbat_word.bitwidth c >= 11 then Wo.gt_int c cap (* 1024 fits: unsigned cmp ok *)
  else Cbat_word.to_int_exn c > cap

(* All elements when small; else a bounded prefix walk. Reports prefix use. *)
let r10b_enum (p : Clp.t) : W.t list * bool =
  if r10b_cardn_gt r10b_enum_cap (Clp.cardinality p) then
    match Clp.min_elem p with
    | None -> ([], true)
    | Some m0 ->
        let mx = Clp.max_elem p in
        let rec go n cur acc =
          if n >= r10b_enum_cap then (List.rev acc, true)
          else
            match Clp.nearest_succ (Cbat_word.succ cur) p with
            | None -> (List.rev (cur :: acc), true)
            | Some nxt ->
                if
                  Cbat_word.equal nxt cur
                  || W.compare nxt cur <= 0
                  || match mx with Some mx -> W.compare nxt mx > 0 | None -> false
                then (List.rev (cur :: acc), true)
                else go (n + 1) nxt (cur :: acc)
        in
        go 0 m0 []
  else (Clp.iter p, false)

(* Containment assertion for one unordered pair. *)
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
            let k = Cbat_word.to_int64_exn z in
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
                Printf.printf "    x=%Ld y=%Ld -> x&y=%Ld not in result\n" (Cbat_word.to_int64_exn x)
                  (Cbat_word.to_int64_exn y) (Cbat_word.to_int64_exn z))
            (List.rev bad)
    in
    report "CLP" !bad_c;
    report "WordSet" !bad_ws
  end

(* Sampled operand corpus at width [w]. *)
let r10b_operands (w : int) : (string * Clp.t) list =
  let v n = Cbat_word.of_int ~width:w n in
  let ones = Cbat_word.ones w in
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
    ("[half-3,half+3]", Clp.interval ~width:w (Cbat_word.sub half (v 3)) (Cbat_word.add half (v 3)));
    ("[ones-8,ones]", Clp.interval ~width:w (Cbat_word.sub ones (v 8)) ones);
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
    ("wrapstep{ones-4+8k}", Clp.create (Cbat_word.sub ones (v 4)) ~step:(v 8) ~cardn:(v 4));
    (* Cardn-2 antipodal pairs (half circle apart). *)
    ("anti{0,half}", Clp.create (v 0) ~step:half ~cardn:(v 2));
    ("anti{1,1+half}", Clp.create (v 1) ~step:half ~cardn:(v 2));
    (* infinite / top classes *)
    ("top", Clp.top w);
    ("inf*4", Clp.create (v 0) ~step:(v 4) ~cardn:full_circle);
    ("inf*6@6", Clp.create (v 6) ~step:(v 6) ~cardn:full_circle);
  ]
  (* w=8 full-wrap classes (enumerable full-circle traversal). *)
  @
  if w = 8 then
    [
      ("fullwrap[200,100]", Clp.interval ~width:w (v 200) (v 100));
      ("fullwrap step11[3+11k]", Clp.create (v 3) ~step:(v 11) ~cardn:(v 24));
    ]
  else []

(* R5: step-1 interval meet is exact. *)

(* Reference meet computed independently by modular arithmetic at width w+1. *)

let r5_checked = ref 0 (* exactness pairs checked *)
let r5_two_piece = ref 0 (* two-piece meets *)
let r5_sound_pairs = ref 0 (* soundness probes *)
let r5_bad = ref [] (* violations *)
let r5_violation w cls detail = r5_bad := (w, cls, detail) :: !r5_bad

(* Reference circular-interval meet. *)
let r5_ref_meet (w : int) (s1 : W.t) (l1 : W.t) (s2 : W.t) (l2 : W.t) :
    [ `Empty | `Arc of W.t * W.t | `TwoPiece ] =
  let ext x = W.extract_exn ~hi:w x in
  (* zero-extend to w+1 *)
  let n = Wo.dom_size ~width:(w + 1) w in
  let l1 = ext l1 and l2 = ext l2 in
  if W.compare l1 n >= 0 then `Arc (s2, l2) (* A full circle: B *)
  else if W.compare l2 n >= 0 then `Arc (s1, l1) (* B full circle: A *)
  else if W.compare l1 (Cbat_word.zero (w + 1)) = 0 || W.compare l2 (Cbat_word.zero (w + 1)) = 0 then `Empty
  else
    let d = Cbat_word.sub s2 s1 in
    (* (s2 - s1) mod N, w bits *)
    let dl = ext d in
    if W.compare dl l1 >= 0 then
      (* B starts at/after A's end: only B's wrapped tail can reach A *)
      begin if W.compare (Cbat_word.add dl l2) n < 0 then `Empty
      else begin
        let tail = Cbat_word.sub (Cbat_word.add dl l2) n in
        (* in [0, N) *)
        let m = if W.compare tail l1 <= 0 then tail else l1 in
        if W.compare m (Cbat_word.zero (w + 1)) <= 0 then `Empty else `Arc (s1, m)
      end
      end
    else begin
      (* B starts strictly inside A *)
      let e = Cbat_word.add dl l2 in
      (* unwrapped end distance *)
      if W.compare e n <= 0 then begin
        (* B ends within one revolution: clip by A's end *)
        let m = if W.compare e l1 <= 0 then e else l1 in
        `Arc (Cbat_word.add s1 d, Cbat_word.sub m dl)
      end
      else begin
        (* B wraps: P1 = [d, l1), P2 = [0, min(l1, e-N)), relative to s1 *)
        let en = Cbat_word.sub e n in
        let p = if W.compare en l1 <= 0 then en else l1 in
        if W.compare p dl >= 0 then `Arc (s1, l1) (* pieces touch: union = A *) else `TwoPiece
      end
    end

(* Step-1 CLP for arc [s, s+l). *)
let r5_build (w : int) (s : W.t) (l : W.t) : Clp.t =
  Clp.create ~width:w ~step:(Cbat_word.one w) ~cardn:l s

(* Short set description for violation reports. *)
let r5_describe (p : Clp.t) : string =
  if Clp.is_bottom p then "EMPTY"
  else if Clp.is_infinite p then "INFINITE"
  else
    match (Clp.min_elem p, Clp.max_elem p) with
    | Some lo, Some hi ->
        Printf.sprintf "{card=%Lu, min=%Lu, max=%Lu}"
          (Cbat_word.to_int64_exn (Clp.cardinality p))
          (Cbat_word.to_int64_exn lo) (Cbat_word.to_int64_exn hi)
    | _ -> "?"

(* One exactness pair. *)
let r5_check_exact (w : int) (cls : string) (s1 : W.t) (l1 : W.t) (s2 : W.t) (l2 : W.t) : unit =
  incr r5_checked;
  let p1 = r5_build w s1 l1 and p2 = r5_build w s2 l2 in
  let res = Clp.intersection p1 p2 in
  match r5_ref_meet w s1 l1 s2 l2 with
  | `Empty ->
      if not (Clp.is_bottom res) then
        r5_violation w cls
          (Printf.sprintf "[%Lu,%Lu)&[%Lu,%Lu): expected EMPTY, got %s" (Cbat_word.to_int64_exn s1)
             (Cbat_word.to_int64_exn l1) (Cbat_word.to_int64_exn s2) (Cbat_word.to_int64_exn l2) (r5_describe res))
  | `Arc (s, l) ->
      let expected = r5_build w s l in
      if not (Clp.equal res expected) then
        r5_violation w cls
          (Printf.sprintf "[%Lu,%Lu)&[%Lu,%Lu): expected ARC {%Lu+%Lu}, got %s" (Cbat_word.to_int64_exn s1)
             (Cbat_word.to_int64_exn l1) (Cbat_word.to_int64_exn s2) (Cbat_word.to_int64_exn l2) (Cbat_word.to_int64_exn s)
             (Cbat_word.to_int64_exn l) (r5_describe res))
  | `TwoPiece ->
      incr r5_two_piece;
      (* Optimal single-CLP hull = smaller operand. *)
      let small = if W.compare l1 l2 <= 0 then p1 else p2 in
      if not (Clp.equal res small) then
        r5_violation w cls
          (Printf.sprintf
             "[%Lu,%Lu)&[%Lu,%Lu): TWO-PIECE, expected the smaller operand (%s), got %s"
             (Cbat_word.to_int64_exn s1) (Cbat_word.to_int64_exn l1) (Cbat_word.to_int64_exn s2) (Cbat_word.to_int64_exn l2)
             (r5_describe small) (r5_describe res))

(* Up to [cap] elements from min_elem via strict successors. *)
let r5_walk_elems (p : Clp.t) (cap : int) : W.t list =
  match Clp.min_elem p with
  | None -> []
  | Some m0 ->
      let rec go n cur acc =
        if n >= cap then List.rev acc
        else
          match Clp.nearest_succ (Cbat_word.succ cur) p with
          | None -> List.rev (cur :: acc)
          | Some nxt ->
              if W.compare nxt cur <= 0 then List.rev (cur :: acc) else go (n + 1) nxt (cur :: acc)
      in
      go 1 m0 []

(* Soundness probe for stepped/infinite pairs. *)
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
           (Cbat_word.to_int64_exn (List.hd bad)))

(* Fixed seed — reproducible runs. *)
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

(* VSK-02: acyclic diamond over a ranged counter; the entry state carries the
   range, so the guard edges refine to absolute halves. Returns
   (sub, guard_tid, then_tid, else_tid, x). *)
let vsk_diamond () : sub term * tid * tid * tid * var =
  let x = Var.create ~is_virtual:false ~fresh:false "vsk_x" (Type.Imm 32) in
  let guard_e = Bil.BinOp (Bil.LT, Bil.Var x, Bil.Int (Cbat_word.to_word (w32 10))) in
  (* No defs on the entry->guard lane: the transfer is empty, so the
     unconditional edge pins the early-exit identity exactly. *)
  let sub, tids =
    sub_of "vsk_diamond"
      [ [], [ (1, mk_goto) ];
        [], [ (2, fun t -> mk_jmp_to t guard_e); (3, fun t -> mk_jmp_to t (Bil.UnOp (Bil.NOT, guard_e))) ];
        [], [];
        [], [] ]
  in
  (sub, tids.(1), tids.(2), tids.(3), x)

(* F1: JLE-counter head lands at TOP (inclusive taken row overshoots); pins sound invariants. *)

let run_soundness () =
(  (* Same-width pairs across widths, CLP layer and composite lift. *)
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
  (* Mixed-width pin: domain zero-extends; ground truth = zero-extended AND. *)
  let zx w x = if Cbat_word.bitwidth x = w then x else Cbat_word.of_int64 ~width:w (Cbat_word.to_int64_exn x) in
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
      let v k = Cbat_word.of_int ~width:w k in
      let ones = Cbat_word.ones w in
      let n = Wo.dom_size ~width:(w + 1) w in
      (* --- structured classes (deterministic, all widths) --- *)
      let near_top k = Cbat_word.sub ones (v k) in
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
          ("nearfull-in", v 5, Cbat_word.sub n (v 1), v 7, v 9);
          ("nearfull-two-piece", v 5, Cbat_word.sub n (v 1), v 4, Cbat_word.sub n (v 1));
          ("nearfull-vs-small", v 5, Cbat_word.sub n (v 1), v 3, v 4);
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
          if w = 64 then Cbat_word.of_int64 ~width:64 raw
          else Cbat_word.of_int64 ~width:w Int64.(logand raw (pred (shift_left 1L w)))
        in
        if Cbat_word.is_zero x then Cbat_word.one (w + 1) else W.extract_exn ~hi:w x
      in
      let rand_start () =
        let raw = r5_rand_word w in
        if w = 64 then Cbat_word.of_int64 ~width:64 raw
        else Cbat_word.of_int64 ~width:w Int64.(logand raw (pred (shift_left 1L w)))
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
let run_roundtrip () =
(* W1: of_list round-trip over representable CLPs. *)
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
  (* cardn*step <= 2^w (exact int math). *)
  let fits w prod = w >= 64 || prod <= 1 lsl w in
  (* Uniform word over [0, 2^w) from ≤30-bit draws. *)
  let rand_word w =
    if w <= 30 then Cbat_word.of_int ~width:w (Random.int (1 lsl w))
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
      if w = 64 then Cbat_word.of_int64 ~width:64 v else Cbat_word.of_int ~width:w (Int64.to_int v)
    end
  in
  let rand_base = rand_word in
  let rec replicate n f = if n = 0 then [] else f () :: replicate (n - 1) f in
  (* 2^w exact for w ≤ 62; at 64 only the comparison matters. *)
  let dom_of w = if w >= 64 then max_int else 1 lsl w in
  let one_case w base s cardn ~corner =
    if cardn > enum_cap then incr skips (* hard cap *)
    else begin
      incr cases;
      let full_class = cardn * s = dom_of w in
      if corner then incr corners;
      let p =
        Clp.create ~width:w ~step:(Cbat_word.of_int ~width:w s) ~cardn:(Cbat_word.of_int ~width:(w + 1) cardn) base
      in
      let elems = List.sort W.compare (Clp.iter p) in
      let rebuilt = Clp.of_list ~width:w elems in
      (* Containment — universal, hard: rebuild may only coarsen. *)
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
        (* Exactness gate — full residue class only. *)
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
          (* Deterministic corners: full class or largest non-aligned arc. *)
          if w <= 62 then begin
            let c_full = dom / s in
            if c_full * s = dom && c_full <= enum_cap then
              one_case w (rand_base w) s c_full ~corner:true
            else if c_full >= 1 && c_full <= enum_cap && c_full * s < dom then
              one_case w (rand_base w) s c_full ~corner:true
          end;
          (* Random representable CLPs, rejection-sampled. *)
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
  (* Full-class miss is a real bug — stop and report. *)
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
  (* Soundness on arbitrary lists. *)
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
(  (* VSK-02: empty-seed/mixed-seed oracle — pins the existing early exit and the
   mixed-seed refined values through the library seam. The diamond's entry
   state carries x in [0,20]; the entry->guard edge is the empty-seed shape
   (constant-true acc cond refines to the input state exactly), and the
   guard's taken/fallthrough edges refine to the absolute halves. The identity
   is against the seeded entry state (init_sol frames entry RSP at offset 0). *)
  let sub, guard_tid, then_tid, else_tid, x = vsk_diamond () in
   let range lo hi = Ws.of_clp (Clp.interval ~width:32 (w32 lo) (w32 hi)) in
   let entry = AI.add_word (anchored_entry ()) ~key:x ~data:(range 0 20) in
   check "property LM VSK-EMPTY-SEED: a constant-true guard produces no seeds (the early-exit shape)"
     (AI.equal
        (Vsa.Test_seam.inverse_denote ~env:entry (Bil.Int (W.to_word W.b1))
           (Ws.singleton W.b1))
        entry);
   check "property LM VSK-MIXED-SEED: the taken guard produces the single Var seed x in [0,9]"
     (Ws.equal
        (AI.find_word 32
           (Vsa.Test_seam.inverse_denote ~env:entry
              (Bil.BinOp (Bil.LT, Bil.Var x, Bil.Int (Cbat_word.to_word (w32 10))))
              (Ws.singleton W.b1))
           x)
        (range 0 9));
   let prog' = Program.create ~subs:[ sub ] () in
   let sol = Vsa.static_graph_vsa ~abi:Hike_abi.x86_64_sysv [] prog' sub (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv ~entry sub) in
   let st tid = Graphlib.Std.Solution.get sol tid in
   check
     "property LM VSK-EMPTY: the unconditional edge is the identity transfer (guard IN equals the seeded entry state; the frame relation is gone — the identity is over words and memories)"
     (AI.equal (st guard_tid) entry);
   check "property LM VSK-MIXED-TAKEN: the taken edge refines x to [0,9] exactly"
     (Ws.equal (AI.find_word 32 (st then_tid) x) (range 0 9));
   check "property LM VSK-MIXED-FALL: the fallthrough edge refines x to [10,20] exactly"
     (Ws.equal (AI.find_word 32 (st else_tid) x) (range 10 20));
   ()

(* F2a: landmark consumption at CLP level — never lands short of the join. *))
;
(  (* Widening soundness pins. *)
  let p1 = Clp.interval ~width:32 (w32 0) (w32 100) in
  let p2 = Clp.interval ~width:32 (w32 0) (w32 101) in
  let r = Clp.widen_join p1 p2 in
  check "property LM F2a: widen_join sound" (Clp.subset p2 r);
  check "property LM F2a: widen_join sound 2" (Clp.subset p2 r);
  check "property LM F2a: widen_join sound 3" (Clp.subset p1 r);
  check "property LM F2a: widen_join sound 4" (Clp.subset p2 r);
  check "property LM F2a: widen_join sound 5" (Clp.subset p1 r);
  ()
(* F2c: acquisition + per-cycle scoping — landmarks scoped to their own WTO cycle. *))
;
(  let sub, l1_tid, _, l2_tid = lm_jle_loop ~k1:(w32 40) ~k2:(w32 100) () in
  let sol = run_anchored sub in
  let i = Var.create ~is_virtual:false ~fresh:false "lm_i" (Type.Imm 32) in
  let l2_tid = match l2_tid with Some t -> t | None -> failwith "F2c: missing L2" in
  let i1 = AI.find_word 32 (Graphlib.Std.Solution.get sol l1_tid) i in
  let i2 = AI.find_word 32 (Graphlib.Std.Solution.get sol l2_tid) i in
  check
    "property LM F2c: loop 1's head lower bound is the entry constant 0"
    (match Ws.min_elem i1 with Some lo -> Cbat_word.equal lo (w32 0) | None -> false);
  check
    "property LM F2c: loop 2's head lower bound is loop 1's exact exit value K1+1 (the compiled \
     fallthrough comparison partitions the exit edge)"
    (match Ws.min_elem i2 with Some lo -> Cbat_word.equal lo (Cbat_word.succ (w32 40)) | None -> false);
  ()

(* Single-pass trace partitioning: every out-edge transfers a branch-refined state. *)

(* When-chain fixture: split ladder seeds {5,15,25}; chain edges partition exactly. *))
let run_chains () =
(  let sub, l1_tid, l2_tid, l3_tid, _chain_tid, x = mk_when_chain () in
  let sol = run_anchored sub in
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

(* T01-2: lone unconditional goto is the identity transfer. *))
;
(  let m = memv "t01_m" in
  let rbp = v64 "RBP" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
  let sub, tids =
    sub_of "t01_straight"
      [ [ Def.create rbp (Bil.Var (v64 "RSP"));
          Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int (Cbat_word.to_word (w32 3)), LittleEndian, `r32)) ],
        [ (1, mk_goto) ];
        [], [ (2, mk_goto) ];
        [], [] ]
  in
  let mid_tid = tids.(1) in
  let exit_tid = tids.(2) in
  let sol = run_anchored sub in
  let cell t = cell_at m rbp (Graphlib.Std.Solution.get sol t) in
  check
    "T01-2 (uniform rule): a lone unconditional goto's accumulated cond is the \
     literal TRUE — the identity transfer: EXIT's IN-state equals MID's \
     (both read the stored {3} exactly; no spurious refinement, no bottom)"
    (Ws.equal (cell mid_tid) (Ws.singleton (w32 3))
     && Ws.equal (cell exit_tid) (Ws.singleton (w32 3)));
  ())

(* T5: the SSE-lane def-use mechanisms — positional prefix states in the
   deep walk, the Store row (cell constraints flow into the stored
   data's producers), and cycle-written cell data extrapolating at
   warmed heads. *)

let run_t5 () =
(* T5-1 (prefix states): a store, then a load whose ADDRESS the same
   block defines.  The walk's cell meet keys by the same-iteration
   address and lands {5}; denoted on the block-entry state the address
   is TOP and the meet never lands. *)
(  let mem = memv "t5_m" in
  let rbp = v64 "RBP" in
  let addr = Var.create ~is_virtual:true ~fresh:false "t5_addr" (Type.Imm 64) in
  let t = Var.create ~is_virtual:true ~fresh:false "t5_t" (Type.Imm 32) in
  let addr_e = Bil.Var addr in
  let addr_lit = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
  let sub, tids =
    sub_of "t5_store_load"
      [ [ Def.create rbp (Bil.Var (v64 "RSP"));
          Def.create addr addr_lit;
          Def.create mem
            (Bil.Store (Bil.Var mem, addr_e, Bil.Int (Cbat_word.to_word (w32 5)),
                        LittleEndian, `r32));
          Def.create t (Bil.Load (Bil.Var mem, addr_e, LittleEndian, `r32)) ],
        [ (1, fun tt -> mk_jmp_to tt (Bil.BinOp (Bil.EQ, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 5))))) ];
        [], [ (0, mk_ret) ] ]
  in
  let blk = List.nth (Term.enum blk_t sub |> Seq.to_list) 0 in
  let key = match Mem.Key.of_wordset (Ws.singleton (w64 (-8))) with
    | Some k -> k | None -> failwith "T5-1: bad key" in
  let wide = Ws.of_clp (Clp.interval ~width:32 (w32 0) (w32 200)) in
  let wide_mem =
    Mem.add (Mem.top { Mem.addr_width = 64; Mem.addressable_width = 8 })
      ~key ~data:(Mem.Val.create wide LittleEndian) in
  let entry = AI.add_memory (anchored_entry ()) ~key:mem ~data:wide_mem in
  let sol =
    Vsa.static_graph_vsa ~abi:Hike_abi.x86_64_sysv [] (Program.create ~subs:[ sub ] ())
      sub (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv ~entry sub) in
  let cfg =
    Sub.to_graph sub
    |> Graphs.Tid.Node.remove Graphs.Tid.start
    |> Graphs.Tid.Node.remove Graphs.Tid.exit in
  let rctx = Vsa.Test_seam.mk_rctx ~cfg ~abi:Hike_abi.x86_64_sysv sub in
  let entry = AI.add_word entry ~key:t ~data:(Ws.singleton (w32 5)) in
  let refined =
    Vsa.Test_seam.refine_edge ~sol ~rctx
      ~seeds:[ (t, Ws.singleton (w32 5)) ]
      entry blk in
  (* The cell AT the fixture's key (the same-iteration address's key):
     the load's meet lands there. *)
  let cell =
    let open Cbat_vsa.Mem in
    let mv = AI.find_memory { addr_width = 64; addressable_width = 8 } refined mem in
    Val.data (find (32, LittleEndian) mv key) in
  check
    "T5-1 (prefix states): the deep walk's cell meet keys by the \
     same-iteration address — the load after the store meets the cell \
     down to {5}"
    (     Ws.equal cell (Ws.singleton (w32 5)));
  ())

(* T5-2 (the Store row): a cell constraint flows into the stored data's
   producers — load KA, copy, store KB, load KB; the constraint {6} on
   the KB load reaches the KA load's cell through the store's data. *)
;
(  let mem = memv "t5r_m" in
  let rbp = v64 "RBP" in
  let ta = Var.create ~is_virtual:true ~fresh:false "t5r_a" (Type.Imm 32) in
  let tb = Var.create ~is_virtual:true ~fresh:false "t5r_b" (Type.Imm 32) in
  let t2 = Var.create ~is_virtual:true ~fresh:false "t5r_t" (Type.Imm 32) in
  let ka = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 16))) in
  let kb = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
  let sub, _ =
    sub_of "t5_store_row"
      [ [ Def.create rbp (Bil.Var (v64 "RSP"));
          Def.create ta (Bil.Load (Bil.Var mem, ka, LittleEndian, `r32));
          Def.create tb (Bil.Var ta);
          Def.create mem
            (Bil.Store (Bil.Var mem, kb, Bil.Var tb, LittleEndian, `r32));
          Def.create t2 (Bil.Load (Bil.Var mem, kb, LittleEndian, `r32)) ],
        [ (1, fun tt -> mk_jmp_to tt (Bil.BinOp (Bil.EQ, Bil.Var t2, Bil.Int (Cbat_word.to_word (w32 6))))) ];
        [], [ (0, mk_ret) ] ]
  in
  let blk = List.nth (Term.enum blk_t sub |> Seq.to_list) 0 in
  let key_of w = match Mem.Key.of_wordset (Ws.singleton (w64 w)) with
    | Some k -> k | None -> failwith "T5-2: bad key" in
  let k16 = key_of (-16) and k8 = key_of (-8) in
  let wide = Ws.of_clp (Clp.interval ~width:32 (w32 0) (w32 200)) in
  let wide_mem =
    Mem.add
      (Mem.add (Mem.top { Mem.addr_width = 64; Mem.addressable_width = 8 })
         ~key:k16 ~data:(Mem.Val.create wide LittleEndian))
      ~key:k8 ~data:(Mem.Val.create wide LittleEndian) in
  let entry = AI.add_memory (anchored_entry ()) ~key:mem ~data:wide_mem in
  let sol =
    Vsa.static_graph_vsa ~abi:Hike_abi.x86_64_sysv [] (Program.create ~subs:[ sub ] ())
      sub (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv ~entry sub) in
  let cfg =
    Sub.to_graph sub
    |> Graphs.Tid.Node.remove Graphs.Tid.start
    |> Graphs.Tid.Node.remove Graphs.Tid.exit in
  let rctx = Vsa.Test_seam.mk_rctx ~cfg ~abi:Hike_abi.x86_64_sysv sub in
  let entry = AI.add_word entry ~key:t2 ~data:(Ws.singleton (w32 6)) in
  let refined =
    Vsa.Test_seam.refine_edge ~sol ~rctx
      ~seeds:[ (t2, Ws.singleton (w32 6)) ]
      entry blk in
  let cell_of_key k =
    match Vsa.Test_seam.denote_imm_exp
            (Bil.Load (Bil.Var mem, k, LittleEndian, `r32)) refined with
    | Ok ws -> ws
    | Error _ -> Ws.top 32 in
  check
    "T5-2 (Store row): the constrained cell (the store's key) meets {6}"
    (Ws.equal (cell_of_key kb) (Ws.singleton (w32 6)));
  check
    "T5-2 (Store row): the constraint flows into the stored data's \
     producers — the producing load's cell meets {6}"
    (Ws.equal (cell_of_key ka) (Ws.singleton (w32 6)));
  ())

(* T5-3 (the T12 ruling, pinned): a bounded runtime SP adjustment is
   NOT a VLA — no allocation event; an unbounded size is the event. *)
;
(  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let mk ~(unbounded : bool) (name : string) : sub term =
    let t = Var.create ~is_virtual:true ~fresh:false "t5v_sz" (Type.Imm 64) in
    let mem = memv "t5v_m" in
    let sz_rhs =
      if unbounded then
        Bil.Load (Bil.Var mem, Bil.Var rbp, LittleEndian, `r64)
      else Bil.Int (Cbat_word.to_word (w64 16)) in
    fst
      (sub_of name
         [ [ Def.create t sz_rhs;
             Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Var t)) ],
           [ (1, mk_goto) ];
           [], [ (0, mk_ret) ] ]) in
  let bounded = mk ~unbounded:false "t5v_bounded" in
  let unbounded = mk ~unbounded:true "t5v_unbounded" in
  check
    "T5-3 (T12 ruling): a bounded runtime SP adjustment is NOT a VLA — \
     no allocation event"
    (Core.Set.is_empty (extract_anchored_events bounded));
  check
    "T5-3 (T12 ruling): an unbounded runtime SP size IS the allocation \
     event"
    (not (Core.Set.is_empty (extract_anchored_events unbounded)));
  ())

(* T5-4 (head extrapolation): a cycle-written cell's data advances by
   the steps; landmark translation when the head holds entries; the
   overflow arm is the plain widen. *)
;
(  let mv = memv "t5x_m" in
  let xv = Var.create ~is_virtual:true ~fresh:false "t5x_w" (Type.Imm 32) in
  let key = key_of (Ws.singleton (w32 100)) in
  let midx = { Mem.addr_width = 32; Mem.addressable_width = 8 } in
  let mkstate (d : Ws.t) (wd : Ws.t) : AI.t =
    let m =
      Mem.add (Mem.top midx) ~key ~data:(Mem.Val.create d LittleEndian) in
    AI.add_word (AI.add_memory AI.top ~key:mv ~data:m) ~key:xv ~data:wd in
  let cell_of (st : AI.t) : Ws.t =
    Mem.Val.data
      (Mem.find (32, LittleEndian) (AI.find_memory midx st mv) key) in
  let h = Tid.for_name "t5x_head" in
  let need = Var.Set.singleton (Var.base xv) in
  let d_old = Ws.singleton (w32 1) in
  let d_new = Ws.of_clp (Clp.interval ~width:32 (w32 1) (w32 2)) in
  let w_old = Ws.singleton (w32 0) and w_new = Ws.singleton (w32 1) in
  Cbat_landmarks.clear ();
  let plain = AI.widen_join (mkstate d_old w_old) (mkstate d_new w_new) in
  check
    "T5-4 (contrast): the plain memory widen drives the cell data \
     infinite"
    (Ws.is_infinite (cell_of plain));
  let r =
    AI.selective_widen_extrapolate ~head:(Some h) ~need ~steps:1
      (mkstate d_old w_old) (mkstate d_new w_new) in
  check
    "T5-4 (extrapolation): the cycle-written cell data advances by the \
     steps"
    (Ws.equal (cell_of r) (Ws.extrapolate_steps ~steps:1 d_old d_new));
  check
    "T5-4 (extrapolation): the advanced cell stays bounded (the plain \
     widen does not)"
    (not (Ws.is_infinite (cell_of r)));
  Cbat_landmarks.record_landmark_for_head ~head:h (Var.base xv)
    ~bound:(w32 10) ~is_upper:true ~dist:2;
  (match Cbat_landmarks.entries_for_head h (Var.base xv) with
   | e :: _ -> e.Cbat_landmarks.dist_p <- Some 5
   | [] -> failwith "T5-4: landmark not recorded");
  let rl =
    AI.selective_widen_extrapolate ~head:(Some h) ~need ~steps:1
      (mkstate d_old w_old) (mkstate d_new w_new) in
  check
    "T5-4 (landmarks): the cell data translates toward the head's \
     landmark (growth 3 x 1 step: hi 2 -> 5)"
    (match Ws.max_elem (cell_of rl) with
     | Some hi -> W.equal hi (w32 5)
     | None -> false);
  Cbat_landmarks.clear ();
  let r_ex =
    AI.selective_widen_extrapolate ~head:(Some h) ~need ~steps:1
      (mkstate (Ws.bottom 32) w_old) (mkstate d_new w_new) in
  let r_w =
    AI.widen_join (mkstate (Ws.bottom 32) w_old) (mkstate d_new w_new) in
  check
    "T5-4 (overflow): extrapolation overflow falls back to the plain \
     widen"
    (Ws.equal (cell_of r_ex) (cell_of r_w));
  Cbat_landmarks.clear ();
  ())

(* T5-4b (store loop integration): a counter loop storing i into a cell —
   the cell data follows the loop's bounded range instead of widening to
   the infinite ascending hull. *)
;
(  let mem = memv "t5l_m" in
  let rbp = v64 "RBP" in
  let i = Var.create ~is_virtual:false ~fresh:false "t5l_i" (Type.Imm 32) in
  let t = Var.create ~is_virtual:false ~fresh:false "t5l_t" (Type.Imm 32) in
  let zf = v1 "t5l_zf" in
  let k = w32 100 in
  let kw = Cbat_word.to_word k in
  let iv = Bil.Var i in
  let sub, tids =
    sub_of "t5l_store_loop"
      [ [ Def.create i (Bil.Int (Cbat_word.to_word (w32 0)));
          Def.create rbp (Bil.Var (v64 "RSP")) ],
        [ (1, mk_goto) ];
        [ Def.create t (Bil.BinOp (Bil.MINUS, iv, Bil.Int kw));
          Def.create zf (Bil.BinOp (Bil.EQ, Bil.BinOp (Bil.MINUS, iv, Bil.Int kw), Bil.Int (Word.zero 32))) ],
        [ (2, fun tt -> mk_jmp_to tt (Bil.UnOp (Bil.NOT, Bil.Var zf)));
          (3, fun tt -> mk_jmp_to tt (Bil.Var zf)) ];
        [ Def.create i (Bil.BinOp (Bil.PLUS, iv, Bil.Int (Cbat_word.to_word (w32 1))));
          Def.create mem
            (Bil.Store (Bil.Var mem,
                        Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))),
                        Bil.Var i, LittleEndian, `r32)) ],
        [ (1, mk_goto) ];
        [], [ (0, mk_ret) ] ]
  in
  let exit_tid = tids.(3) in
  let key = match Mem.Key.of_wordset (Ws.singleton (w64 (-8))) with
    | Some k -> k | None -> failwith "T5-4b: bad key" in
  let wide_mem =
    Mem.add (Mem.top { Mem.addr_width = 64; Mem.addressable_width = 8 })
      ~key ~data:(Mem.Val.create (Ws.singleton (w32 0)) LittleEndian) in
  let entry_state = AI.add_memory (anchored_entry ()) ~key:mem ~data:wide_mem in
  let sol =
    Vsa.static_graph_vsa ~abi:Hike_abi.x86_64_sysv [] (Program.create ~subs:[ sub ] ())
      sub (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv ~entry:entry_state sub) in
  let exit_st = Graphlib.Std.Solution.get sol exit_tid in
  let cell =
    match
      Vsa.Test_seam.denote_imm_exp
        (Bil.Load (Bil.Var mem,
                   Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))),
                   LittleEndian, `r32))
        exit_st with
    | Ok ws -> ws
    | Error _ -> Ws.top 32 in
  check
    "T5-4b (store loop): the stored cell data is bounded — it followed \
     the loop's landmark range instead of widening to the infinite hull"
    ((not (Ws.is_infinite cell))
     && (match Ws.max_elem cell with
         | Some hi -> W.compare hi k <= 0
         | None -> false));
  ())
