(* Integration pins: the soundness properties (word-domain and
   backward-walk), the landmark-widening loops, the when-chain trace
   partitioning, and the T5 def-use mechanisms.  One Alcotest group per
   pin; each pin builds its own fixture and keeps its counters local, so
   no state crosses pins. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

(* The word-domain alias the property source uses: the property pins read
   and write Cbat_word values through it. *)
module W = Cbat_word

(* VSK-02 fixture: an acyclic diamond over a ranged counter; the entry
   state carries the range, so the guard edges refine to absolute halves.
   Returns (sub, guard_tid, then_tid, else_tid, x). *)
let vsk_diamond () : sub term * tid * tid * tid * var =
  let x = Var.create ~is_virtual:false ~fresh:false "vsk_x" (Type.Imm 32) in
  let guard_e = Bil.BinOp (Bil.LT, Bil.Var x, Bil.Int (Cbat_word.to_word (w32 10))) in
  let sub, tids =
    sub_of "vsk_diamond"
      [ [], [ (1, mk_goto) ];
        [], [ (2, fun t -> mk_jmp_to t guard_e);
              (3, fun t -> mk_jmp_to t (Bil.UnOp (Bil.NOT, guard_e))) ];
        [], [];
        [], [] ]
  in
  (sub, tids.(1), tids.(2), tids.(3), x)

(* The word key the landmark pins use: each pin builds its own table, so
   one base variable serves them all. *)
let lw_var = v64 "lm_word"
let lw = Cbat_landmarks.Word lw_var

let observe_meet lm ~key ~p ~cstr =
  Cbat_landmarks.observe_unsat lm ~key ~p ~cstr ~m:(Ws.meet p cstr)

let tests : unit Alcotest.test list =
  [
    (* R10b: every elementwise AND of enumerated operands lands in the
       logand result, at both the CLP and the composite WordSet layer. *)
    pin "INT-01"
      "R10b: CLP logand and composite WordSet logand contain every elementwise AND (widths \
       8/16/32/64, mixed-width zero-extended)"
      (fun () ->
        let enum_cap = 1024 in
        let product_cap = 131072 in
        let pairs = ref 0 in
        let skipped = ref 0 in
        let prefix = ref 0 in
        let witnesses = ref 0 in
        let bad_clp = ref 0 in
        let bad_ws = ref 0 in
        let cardn_gt (cap : int) (c : W.t) : bool =
          if Cbat_word.bitwidth c >= 11 then Wo.gt_int c cap
          else Cbat_word.to_int_exn c > cap
        in
        let enum_piece (p : Cbat_clp.t) : W.t list * bool =
          if cardn_gt enum_cap (Cbat_clp.cardinality p) then
            match Cbat_clp.min_elem p with
            | None -> ([], true)
            | Some m0 ->
                let mx = Cbat_clp.max_elem p in
                let rec go n cur acc =
                  if n >= enum_cap then (List.rev acc, true)
                  else
                    match Cbat_clp.nearest_succ (Cbat_word.succ cur) p with
                    | None -> (List.rev (cur :: acc), true)
                    | Some nxt ->
                        if
                          Cbat_word.equal nxt cur
                          || W.compare nxt cur <= 0
                          || Option.is_some
                               (Base.Option.filter mx ~f:(fun mx -> W.compare nxt mx > 0))
                        then (List.rev (cur :: acc), true)
                        else go (n + 1) nxt (cur :: acc)
                in
                go 0 m0 []
          else (Cbat_clp.iter p, false)
        in
        let enum (ps : Clp.t) : W.t list * bool =
          List.fold_left
            (fun (es, pre) p ->
              let e, pr = enum_piece p in
              (es @ e, pre || pr))
            ([], false) (Clp.Pieces.to_list ps)
        in
        let check_pair (w : int) (l1 : string) (p1 : Clp.t) (l2 : string) (p2 : Clp.t) : unit =
          let es1, pre1 = enum p1 in
          let es2, pre2 = enum p2 in
          if pre1 || pre2 then incr prefix;
          if List.length es1 * List.length es2 > product_cap then incr skipped
          else begin
            incr pairs;
            let res_c = Clp.logand p1 p2 in
            let res_ws = Ws.logand (Ws.of_clp p1) (Ws.of_clp p2) in
            let seen : (int64, unit) Hashtbl.t = Hashtbl.create 256 in
            let bad_c = ref [] and bad_ws_local = ref [] in
            List.iter
              (fun x ->
                List.iter
                  (fun y ->
                    let z = W.logand x y in
                    let k = Cbat_word.to_int64_exn z in
                    if not (Hashtbl.mem seen k) then begin
                      Hashtbl.add seen k ();
                      incr witnesses;
                      if not (Clp.elem z res_c) then bad_c := (x, y, z) :: !bad_c;
                      if not (Ws.elem z res_ws) then bad_ws_local := (x, y, z) :: !bad_ws_local
                    end)
                  es2)
              es1;
            let report kind bad =
              match bad with
              | [] -> ()
              | _ ->
                  if kind = "CLP" then incr bad_clp else incr bad_ws;
                  Printf.printf
                    "  property logand VIOLATION (%s) @w=%d: %s & %s: %d excluded value(s)\n" kind
                    w l1 l2 (List.length bad);
                  List.iteri
                    (fun i (x, y, z) ->
                      if i < 3 then
                        Printf.printf "    x=%Ld y=%Ld -> x&y=%Ld not in result\n"
                          (Cbat_word.to_int64_exn x) (Cbat_word.to_int64_exn y)
                          (Cbat_word.to_int64_exn z))
                    (List.rev bad)
            in
            report "CLP" !bad_c;
            report "WordSet" !bad_ws_local
          end
        in
        let operands (w : int) : (string * Clp.t) list =
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
            ( "[half-3,half+3]",
              Clp.interval ~width:w (Cbat_word.sub half (v 3)) (Cbat_word.add half (v 3)) );
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
          @
          if w = 8 then
            [
              ("fullwrap[200,100]", Clp.interval ~width:w (v 200) (v 100));
              ("fullwrap step11[3+11k]", Clp.create (v 3) ~step:(v 11) ~cardn:(v 24));
            ]
          else []
        in
        let per_width = ref [] in
        List.iter
          (fun w ->
            let ops = operands w in
            let before = !pairs in
            let rec go = function
              | [] -> ()
              | (l1, p1) :: rest ->
                  check_pair w l1 p1 l1 p1;
                  List.iter (fun (l2, p2) -> check_pair w l1 p1 l2 p2) rest;
                  go rest
            in
            go ops;
            per_width := (w, !pairs - before) :: !per_width)
          [ 8; 16; 32; 64 ];
        (* Mixed-width pin: the domain zero-extends; ground truth = the
           zero-extended AND. *)
        let zx w x =
          if Cbat_word.bitwidth x = w then x
          else Cbat_word.of_int64 ~width:w (Cbat_word.to_int64_exn x)
        in
        let find w lbl = List.assoc lbl (operands w) in
        let check_mixed (wa, pa) (wb, pb) =
          let w = Stdlib.max wa wb in
          let es1, _ = enum pa in
          let es2, _ = enum pb in
          if List.length es1 * List.length es2 > product_cap then true
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
          "property logand: %d pairs checked (%d prefix-sampled sides, %d skipped by caps), %d \
           distinct witnesses, %d CLP-layer violations, %d WordSet-layer violations\n"
          !pairs !prefix !skipped !witnesses !bad_clp !bad_ws;
        check
          "property logand R10b: CLP logand contains every elementwise AND (widths 8/16/32/64)"
          (!bad_clp = 0);
        check "property logand R10b: composite WordSet logand contains every elementwise AND"
          (!bad_ws = 0);
        check "property logand R10b: mixed-width coercion result contains the zero-extended AND"
          mixed_ok);

    (* R5: the step-1 interval meet equals the exact circular-interval
       reference, computed independently by modular arithmetic at width w+1. *)
    pin "INT-02"
      "R5: the step-1 interval meet equals the exact circular-interval reference (widths \
       8/16/32/64)"
      (fun () ->
        let checked = ref 0 in
        let two_piece = ref 0 in
        let sound_pairs = ref 0 in
        let bad = ref [] in
        let violation w cls detail = bad := (w, cls, detail) :: !bad in
        let ref_meet (w : int) (s1 : W.t) (l1 : W.t) (s2 : W.t) (l2 : W.t) :
            [ `Empty | `Arc of W.t * W.t | `Two of (W.t * W.t) * (W.t * W.t) ] =
          let ext x = W.extract_exn ~hi:w x in
          let n = Wo.dom_size ~width:(w + 1) w in
          let l1 = ext l1 and l2 = ext l2 in
          if W.compare l1 n >= 0 then `Arc (s2, l2)
          else if W.compare l2 n >= 0 then `Arc (s1, l1)
          else if
            W.compare l1 (Cbat_word.zero (w + 1)) = 0
            || W.compare l2 (Cbat_word.zero (w + 1)) = 0
          then `Empty
          else
            let d = Cbat_word.sub s2 s1 in
            let dl = ext d in
            if W.compare dl l1 >= 0 then
              begin
                if W.compare (Cbat_word.add dl l2) n < 0 then `Empty
                else begin
                  let tail = Cbat_word.sub (Cbat_word.add dl l2) n in
                  let m = if W.compare tail l1 <= 0 then tail else l1 in
                  if W.compare m (Cbat_word.zero (w + 1)) <= 0 then `Empty else `Arc (s1, m)
                end
              end
            else begin
              let e = Cbat_word.add dl l2 in
              if W.compare e n <= 0 then begin
                let m = if W.compare e l1 <= 0 then e else l1 in
                `Arc (Cbat_word.add s1 d, Cbat_word.sub m dl)
              end
              else begin
                let en = Cbat_word.sub e n in
                let p = if W.compare en l1 <= 0 then en else l1 in
                if W.compare p dl >= 0 then `Arc (s1, l1)
                else `Two ((s1, p), (Cbat_word.add s1 dl, Cbat_word.sub l1 dl))
              end
            end
        in
        let build (w : int) (s : W.t) (l : W.t) : Clp.t =
          Clp.create ~width:w ~step:(Cbat_word.one w) ~cardn:l s
        in
        let describe (p : Clp.t) : string =
          if Clp.is_bottom p then "EMPTY"
          else if Clp.is_infinite p then "INFINITE"
          else
            match (Clp.min_elem p, Clp.max_elem p) with
            | Some lo, Some hi ->
                Printf.sprintf "{card=%Lu, min=%Lu, max=%Lu}"
                  (Cbat_word.to_int64_exn (Clp.cardinality p))
                  (Cbat_word.to_int64_exn lo) (Cbat_word.to_int64_exn hi)
            | _ -> "?"
        in
        let check_exact (w : int) (cls : string) (s1 : W.t) (l1 : W.t) (s2 : W.t) (l2 : W.t) :
            unit =
          incr checked;
          let p1 = build w s1 l1 and p2 = build w s2 l2 in
          let res = Clp.intersection p1 p2 in
          match ref_meet w s1 l1 s2 l2 with
          | `Empty ->
              if not (Clp.is_bottom res) then
                violation w cls
                  (Printf.sprintf "[%Lu,%Lu)&[%Lu,%Lu): expected EMPTY, got %s"
                     (Cbat_word.to_int64_exn s1) (Cbat_word.to_int64_exn l1)
                     (Cbat_word.to_int64_exn s2) (Cbat_word.to_int64_exn l2)
                     (describe res))
          | `Arc (s, l) ->
              let expected = build w s l in
              if not (Clp.equal res expected) then
                violation w cls
                  (Printf.sprintf "[%Lu,%Lu)&[%Lu,%Lu): expected ARC {%Lu+%Lu}, got %s"
                     (Cbat_word.to_int64_exn s1) (Cbat_word.to_int64_exn l1)
                     (Cbat_word.to_int64_exn s2) (Cbat_word.to_int64_exn l2)
                     (Cbat_word.to_int64_exn s) (Cbat_word.to_int64_exn l) (describe res))
          | `Two ((sa, la), (sb, lb)) ->
              incr two_piece;
              let expected = Clp.union (build w sa la) (build w sb lb) in
              if not (Clp.equal res expected) then
                violation w cls
                  (Printf.sprintf
                     "[%Lu,%Lu)&[%Lu,%Lu): TWO-PIECE, expected both arcs (%s), got %s"
                     (Cbat_word.to_int64_exn s1) (Cbat_word.to_int64_exn l1)
                     (Cbat_word.to_int64_exn s2) (Cbat_word.to_int64_exn l2)
                     (describe expected) (describe res))
        in
        let walk_piece (p : Cbat_clp.t) (cap : int) : W.t list =
          match Cbat_clp.min_elem p with
          | None -> []
          | Some m0 ->
              let rec go n cur acc =
                if n >= cap then List.rev acc
                else
                  match Cbat_clp.nearest_succ (Cbat_word.succ cur) p with
                  | None -> List.rev (cur :: acc)
                  | Some nxt ->
                      if W.compare nxt cur <= 0 then List.rev (cur :: acc) else go (n + 1) nxt (cur :: acc)
              in
              go 1 m0 []
        in
        let walk_elems (ps : Clp.t) (cap : int) : W.t list =
          List.concat_map (fun p -> walk_piece p cap) (Clp.Pieces.to_list ps)
        in
        let check_sound (w : int) (cls : string) (p1 : Clp.t) (p2 : Clp.t) : unit =
          incr sound_pairs;
          let res = Clp.intersection p1 p2 in
          let es1 = walk_elems p1 128 in
          let lost = List.filter (fun x -> Clp.elem x p2 && not (Clp.elem x res)) es1 in
          match lost with
          | [] -> ()
          | _ ->
              violation w cls
                (Printf.sprintf "%d true common element(s) lost (first %Lu)" (List.length lost)
                   (Cbat_word.to_int64_exn (List.hd lost)))
        in
        let rand = Random.State.make [| 0x5EED2026; 0x00000D1C |] in
        let rand_word (bits : int) : Int64.t =
          let rec go acc b =
            if b <= 0 then acc
            else
              let chunk = Stdlib.min b 29 in
              let v = Int64.of_int (Random.State.int rand (1 lsl chunk)) in
              go Int64.(logor (shift_left acc chunk) v) (b - chunk)
          in
          go 0L bits
        in
        List.iter
          (fun w ->
            let v k = Cbat_word.of_int ~width:w k in
            let ones = Cbat_word.ones w in
            let n = Wo.dom_size ~width:(w + 1) w in
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
            List.iter (fun (cls, a, b, c, d) -> check_exact w cls a b c d) structured;
            let rand_len () =
              let pick = Random.State.int rand 100 in
              let raw =
                if pick < 40 then rand_word (Stdlib.min w 8)
                else if pick < 70 then rand_word (Stdlib.max 1 (w / 2))
                else rand_word w
              in
              let x =
                if w = 64 then Cbat_word.of_int64 ~width:64 raw
                else Cbat_word.of_int64 ~width:w Int64.(logand raw (pred (shift_left 1L w)))
              in
              if Cbat_word.is_zero x then Cbat_word.one (w + 1) else W.extract_exn ~hi:w x
            in
            let rand_start () =
              let raw = rand_word w in
              if w = 64 then Cbat_word.of_int64 ~width:64 raw
              else Cbat_word.of_int64 ~width:w Int64.(logand raw (pred (shift_left 1L w)))
            in
            let k = if w <= 16 then 400 else if w = 32 then 200 else 80 in
            for _ = 1 to k do
              let s1 = rand_start () and l1 = rand_len () in
              let s2 = rand_start () and l2 = rand_len () in
              check_exact w "rand" s1 l1 s2 l2
            done;
            let full_circle = Wo.dom_size ~width:(w + 1) w in
            let sound_ops =
              [
                ("evens", Clp.create (v 0) ~step:(v 2) ~cardn:(v 32));
                ("step3", Clp.create (v 1) ~step:(v 3) ~cardn:(v 14));
                ("arc[0,99]", build w (v 0) (v 100));
                ("top", Clp.top w);
                ("inf*4", Clp.create (v 0) ~step:(v 4) ~cardn:full_circle);
              ]
            in
            let rec go_sound = function
              | [] -> ()
              | (l1, p1) :: rest ->
                  List.iter (fun (l2, p2) -> check_sound w (l1 ^ "x" ^ l2) p1 p2) rest;
                  check_sound w (l1 ^ "x" ^ l1) p1 p1;
                  go_sound rest
            in
            go_sound sound_ops)
          [ 8; 16; 32; 64 ];
        Printf.printf
          "property meet: %d exactness pairs checked (%d two-piece), %d soundness probes, %d \
           violations\n"
          !checked !two_piece !sound_pairs (List.length !bad);
        List.iter
          (fun (w, cls, detail) ->
            Printf.printf "  property meet VIOLATION @w=%d (%s): %s\n" w cls detail)
          !bad;
        check
          "property meet R5: the step-1 interval meet equals the exact circular-interval reference \
           (widths 8/16/32/64)"
          (List.length !bad = 0));

    (* W1: of_list round-trip over representable CLPs; containment is
       universal, exactness is gated on the full residue class. *)
    pin "INT-03"
      "property of_list: containment universal on representable CLPs, full-class corners exact, \
       arbitrary-list soundness (widths 8/16/32/64)"
      (fun () ->
        Random.init 20260823;
        let steps = [ 1; 2; 3; 4; 5; 6; 7; 8 ] in
        let widths = [ 8; 16; 32; 64 ] in
        let enum_cap = 2048 in
        let skips = ref 0 in
        let cases = ref 0 in
        let corners = ref 0 in
        let cont_failures = ref 0 in
        let fc_failures = ref 0 in
        let coarsened = ref 0 in
        let fits w prod = w >= 64 || prod <= 1 lsl w in
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
            if w = 64 then Cbat_word.of_int64 ~width:64 v
            else Cbat_word.of_int ~width:w (Int64.to_int v)
          end
        in
        let rand_base = rand_word in
        let rec replicate n f = if n = 0 then [] else f () :: replicate (n - 1) f in
        let dom_of w = if w >= 64 then max_int else 1 lsl w in
        let one_case w base s cardn ~corner =
          if cardn > enum_cap then incr skips
          else begin
            incr cases;
            let full_class = cardn * s = dom_of w in
            if corner then incr corners;
            let p =
              Clp.create ~width:w
                ~step:(Cbat_word.of_int ~width:w s)
                ~cardn:(Cbat_word.of_int ~width:(w + 1) cardn)
                base
            in
            let elems = List.sort W.compare (Clp.iter p) in
            let rebuilt = Clp.of_list ~width:w elems in
            (* Containment — universal, hard: a rebuild may only coarsen. *)
            List.iter
              (fun e ->
                if not (Clp.elem e rebuilt) then begin
                  incr cont_failures;
                  Printf.printf
                    "FAIL: property of_list UNSOUND: element lost in rebuild (w=%d elem=%s \
                     step=%d cardn=%d)\n"
                    w (W.to_string e) s cardn
                end)
              elems;
            if Clp.equal rebuilt p then ()
            else if full_class then begin
              incr fc_failures;
              Printf.printf
                "FAIL: property of_list full-residue-class round-trip inexact (w=%d base=%s \
                 step=%d cardn=%d)\n"
                w (W.to_string base) s cardn
            end
            else incr coarsened
          end
        in
        List.iter
          (fun w ->
            let dom = 1 lsl w in
            List.iter
              (fun s ->
                if w <= 62 then begin
                  let c_full = dom / s in
                  if c_full * s = dom && c_full <= enum_cap then
                    one_case w (rand_base w) s c_full ~corner:true
                  else if c_full >= 1 && c_full <= enum_cap && c_full * s < dom then
                    one_case w (rand_base w) s c_full ~corner:true
                end;
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
        (* A full-class miss is a real bug — stop and report. *)
        if !fc_failures > 0 then
          failwith
            (Printf.sprintf
               "STOP: property of_list: %d full-residue-class exactness failures — real of_list bug"
               !fc_failures);
        check
          "property of_list: containment universal on representable CLPs (create/iter/of_list, \
           widths 8/16/32/64)"
          (!cont_failures = 0 && !cases > 0);
        check "property of_list: full-class / misaligned-gap corners exercised" (!corners > 0);
        let arb_failures = ref 0 in
        ignore
          (replicate 300 (fun () ->
               let w = List.nth widths (Random.int 4) in
               let n = 1 + Random.int 40 in
               let mk () = rand_word w in
               let l = replicate n mk in
               (* The ascending contract: of_list consumes an ordered list. *)
               let l = List.sort (fun a b -> W.compare a b) l in
               let r = Clp.of_list ~width:w l in
               List.iter
                 (fun x ->
                   if not (Clp.elem x r) then begin
                     incr arb_failures;
                     Printf.printf "FAIL: property of_list soundness: input element not in result \
                                    (w=%d x=%s)\n" w (W.to_string x)
                   end)
                 l));
        check "property of_list: soundness on arbitrary lists (every input element satisfies elem)"
          (!arb_failures = 0);
        Printf.printf
          "property of_list: %d representable cases (%d corner injections, %d overflow/cap skips; \
           %d coarsened rebuilds)\n"
          !cases !corners !skips !coarsened);

    (* VSK-02: the diamond's entry state carries x in [0,20]; the
       constant-true identity edge is the empty-seed shape and the guard's
       taken/fallthrough edges refine to the absolute halves. *)
    pin "INT-04"
      "VSK-02 empty-seed/mixed-seed oracle: the constant-true guard seeds nothing and the \
       diamond's edges refine to the absolute halves"
      (fun () ->
        let sub, guard_tid, then_tid, else_tid, x = vsk_diamond () in
        let range lo hi = Ws.of_clp (Clp.interval ~width:32 (w32 lo) (w32 hi)) in
        let entry = AI.add_word (anchored_entry ()) ~key:x ~data:(range 0 20) in
        check
          "property LM VSK-EMPTY-SEED: a constant-true guard produces no seeds (the early-exit \
           shape)"
          (AI.equal
             (Vsa.Test_seam.constrain_operands ~landmarks:(Cbat_landmarks.create ()) ~env:entry (Bil.Int (W.to_word W.b1)) (Ws.singleton W.b1))
             entry);
        check "property LM VSK-MIXED-SEED: the taken guard produces the single Var seed x in [0,9]"
          (Ws.equal
             (AI.find_word 32
                (Vsa.Test_seam.constrain_operands ~landmarks:(Cbat_landmarks.create ()) ~env:entry
                   (Bil.BinOp (Bil.LT, Bil.Var x, Bil.Int (Cbat_word.to_word (w32 10))))
                   (Ws.singleton W.b1))
                x)
             (range 0 9));
        let sol =
          static_graph_vsa ~abi:Hike_abi.x86_64_sysv sub
            (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv ~entry sub)
        in
        let st tid = Graphlib.Std.Solution.get sol tid in
        check
          "property LM VSK-EMPTY: the unconditional edge is the identity transfer (guard IN equals \
           the seeded entry state; the frame relation is gone — the identity is over words and \
           memories)"
          (AI.equal (st guard_tid) entry);
        check "property LM VSK-MIXED-TAKEN: the taken edge refines x to [0,9] exactly"
          (Ws.equal (AI.find_word 32 (st then_tid) x) (range 0 9));
        check "property LM VSK-MIXED-FALL: the fallthrough edge refines x to [10,20] exactly"
          (Ws.equal (AI.find_word 32 (st else_tid) x) (range 10 20)));

    (* F2a: landmark consumption at CLP level — never lands short of the join. *)
    pin "INT-05" "LM F2a: widen_join soundness over the landmark-input pair"
      (fun () ->
        let p1 = Clp.interval ~width:32 (w32 0) (w32 100) in
        let p2 = Clp.interval ~width:32 (w32 0) (w32 101) in
        let r = Clp.widen_join p1 p2 in
        check "property LM F2a: widen_join sound on p2" (Clp.subset p2 r);
        check "property LM F2a: widen_join sound on p1" (Clp.subset p1 r));

    (* F2c: acquisition + per-cycle scoping — landmarks scoped to their own WTO cycle. *)
    pin "INT-06"
      "LM F2c: two sequential landmarks loops refine independently (loop 2's head is loop 1's \
       exact exit value K1+1)"
      (fun () ->
        let sub, l1_tid, _, l2_tid = lm_jle_loop ~k1:(w32 40) ~k2:(w32 100) () in
        let sol = run_anchored sub in
        let i = Var.create ~is_virtual:false ~fresh:false "lm_i" (Type.Imm 32) in
        let l2_tid = match l2_tid with Some t -> t | None -> failwith "F2c: missing L2" in
        let i1 = AI.find_word 32 (Graphlib.Std.Solution.get sol l1_tid) i in
        let i2 = AI.find_word 32 (Graphlib.Std.Solution.get sol l2_tid) i in
        check_bound "property LM F2c: loop 1's head lower bound is the entry constant 0"
          (Ws.min_elem i1) (fun lo -> Cbat_word.equal lo (w32 0));
        check_bound
          "property LM F2c: loop 2's head lower bound is loop 1's exact exit value K1+1 (the \
           compiled fallthrough comparison partitions the exit edge)"
          (Ws.min_elem i2) (fun lo -> Cbat_word.equal lo (Cbat_word.succ (w32 40))));

    (* T01: single-pass trace partitioning — every out-edge transfers a
       branch-refined state; the when-chain splits ladder seeds {5,15,25}. *)
    pin "INT-07"
      "T01: the when-chain's edges partition by their accumulated conditions and a lone \
       unconditional goto is the identity transfer"
      (fun () ->
        let sub, l1_tid, l2_tid, l3_tid, _chain_tid, x = mk_when_chain () in
        let sol = run_anchored sub in
        let in_x (t : tid) : Ws.t = AI.find_word 32 (Graphlib.Std.Solution.get sol t) x in
        check
          "T01-1a (when-chain): the FIRST edge's IN-state is refined by its own cond (x < 10 over \
           {5,15,25} = {5} exactly)"
          (Ws.equal (in_x l1_tid) (Ws.singleton (w32 5)));
        check
          "T01-1b (when-chain): the MID-CHAIN edge's IN-state is refined by the ACCUMULATED `c2 & \
           ~c1`, not the jmp's own cond (x = {15} exactly — not {5,15})"
          (Ws.equal (in_x l2_tid) (Ws.singleton (w32 15)));
        check
          "T01-1c (when-chain): the unconditional chain TAIL's IN-state is refined by the \
           accumulated negatives `~c1 & ~c2` (x = {25} exactly)"
          (Ws.equal (in_x l3_tid) (Ws.singleton (w32 25)));
        let m = memv "t01_m" in
        let rbp = v64 "RBP" in
        let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
        let sub2, tids =
          sub_of "t01_straight"
            [ [ Def.create rbp (Bil.Var (v64 "RSP"));
                Def.create m
                  (Bil.Store
                     ( Bil.Var m, addr_e, Bil.Int (Cbat_word.to_word (w32 3)), LittleEndian, `r32 )) ],
              [ (1, mk_goto) ];
              [], [ (2, mk_goto) ];
              [], [] ]
        in
        let mid_tid = tids.(1) in
        let exit_tid = tids.(2) in
        let sol2 = run_anchored sub2 in
        let cell t = cell_at m rbp (Graphlib.Std.Solution.get sol2 t) in
        check
          "T01-2 (uniform rule): a lone unconditional goto's accumulated cond is the literal TRUE \
           — the identity transfer: EXIT's IN-state equals MID's (both read the stored {3} \
           exactly; no spurious refinement, no bottom)"
          (Ws.equal (cell mid_tid) (Ws.singleton (w32 3))
          && Ws.equal (cell exit_tid) (Ws.singleton (w32 3))));

    (* T5-1 (prefix states): a store, then a load whose ADDRESS the same
       block defines; the walk's cell meet keys by the same-iteration
       address and lands {5}. *)
    pin "INT-08"
      "T5-1 prefix states: the deep walk's cell meet keys by the same-iteration address — the load \
       after the store meets the cell down to {5}"
      (fun () ->
        let mem = memv "t5_m" in
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
                  (Bil.Store
                     ( Bil.Var mem, addr_e, Bil.Int (Cbat_word.to_word (w32 5)), LittleEndian, `r32 ));
                Def.create t (Bil.Load (Bil.Var mem, addr_e, LittleEndian, `r32)) ],
              [ (1, fun tt ->
                    mk_jmp_to tt
                      (Bil.BinOp (Bil.EQ, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 5))))) ];
              [], [ (0, mk_ret) ] ]
        in
        let blk = List.nth (Term.enum blk_t sub |> Seq.to_list) 0 in
        let key =
          match Mem.Key.of_wordset (Ws.stack_word_i64 (-8L)) with
          | [ k ] -> k
  | _ -> failwith "key"
        in
        let wide = Ws.of_clp (Clp.interval ~width:32 (w32 0) (w32 200)) in
        let wide_mem =
          Mem.add
            (Mem.top { Mem.addr_width = 64; Mem.addressable_width = 8 })
            ~key ~data:(Mem.Val.create wide LittleEndian)
        in
        let entry = AI.add_memory (anchored_entry ()) ~key:mem ~data:wide_mem in
        let sol =
          static_graph_vsa ~abi:Hike_abi.x86_64_sysv
            sub
            (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv ~entry sub)
        in
        let rctx = mk_rctx ~abi:Hike_abi.x86_64_sysv sub in
        let entry = AI.add_word entry ~key:t ~data:(Ws.singleton (w32 5)) in
        let refined =
          Vsa.Test_seam.refine_edge ~sol ~rctx
            ~seeds:(Var.Set.singleton t)
            entry blk
        in
        let cell =
          let open Cbat_vsa.Mem in
          let mv = AI.find_memory { addr_width = 64; addressable_width = 8 } refined mem in
          Val.data (find (32, LittleEndian) mv key)
        in
        check
          "T5-1 (prefix states): the deep walk's cell meet keys by the same-iteration address — the \
           load after the store meets the cell down to {5}"
          (Ws.equal cell (Ws.singleton (w32 5))));

    (* T5-2 (the Store row): a cell constraint flows into the stored data's
       producers — load KA, copy, store KB, load KB. *)
    pin "INT-09"
      "T5-2 Store row: the constrained cell meets {6} and the constraint flows into the stored \
       data's producing load"
      (fun () ->
        let mem = memv "t5r_m" in
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
                Def.create mem (Bil.Store (Bil.Var mem, kb, Bil.Var tb, LittleEndian, `r32));
                Def.create t2 (Bil.Load (Bil.Var mem, kb, LittleEndian, `r32)) ],
              [ (1, fun tt ->
                    mk_jmp_to tt
                      (Bil.BinOp (Bil.EQ, Bil.Var t2, Bil.Int (Cbat_word.to_word (w32 6))))) ];
              [], [ (0, mk_ret) ] ]
        in
        let blk = List.nth (Term.enum blk_t sub |> Seq.to_list) 0 in
        let key_of w =
          match Mem.Key.of_wordset (Ws.stack_word_i64 (Stdlib.Int64.of_int w)) with
          | [ k ] -> k
  | _ -> failwith "key"
        in
        let k16 = key_of (-16) and k8 = key_of (-8) in
        let wide = Ws.of_clp (Clp.interval ~width:32 (w32 0) (w32 200)) in
        let wide_mem =
          Mem.add
            (Mem.add
               (Mem.top { Mem.addr_width = 64; Mem.addressable_width = 8 })
               ~key:k16 ~data:(Mem.Val.create wide LittleEndian))
            ~key:k8 ~data:(Mem.Val.create wide LittleEndian)
        in
        let entry = AI.add_memory (anchored_entry ()) ~key:mem ~data:wide_mem in
        let sol =
          static_graph_vsa ~abi:Hike_abi.x86_64_sysv
            sub
            (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv ~entry sub)
        in
        let rctx = mk_rctx ~abi:Hike_abi.x86_64_sysv sub in
        let entry = AI.add_word entry ~key:t2 ~data:(Ws.singleton (w32 6)) in
        let refined =
          Vsa.Test_seam.refine_edge ~sol ~rctx
            ~seeds:(Var.Set.singleton t2)
            entry blk
        in
        let cell_of_key k =
          Result.fold
            (Vsa.Test_seam.denote_imm_exp (Bil.Load (Bil.Var mem, k, LittleEndian, `r32)) refined)
            ~ok:Fun.id ~error:(fun _ -> Ws.top 32)
        in
        check "T5-2 (Store row): the constrained cell (the store's key) meets {6}"
          (Ws.equal (cell_of_key kb) (Ws.singleton (w32 6)));
        check
          "T5-2 (Store row): the constraint flows into the stored data's producers — the \
           producing load's cell meets {6}"
          (Ws.equal (cell_of_key ka) (Ws.singleton (w32 6)));
        (* The hull case: the consuming load's address is a SET whose hull
           contains the store's key without equalling it.  The handshake's
           match is interval intersection, so the store row still delivers —
           sound by the join ruling (a load's value is the join over the
           cells its addresses can read, so the constraint contains every
           contributing cell). *)
        let hull_case ~(store_off : int) :
            AI.t * AI.t * var * var * var * exp * exp =
          let hmem = memv "t5r_hm" in
          let ha = Var.create ~is_virtual:true ~fresh:false "t5r_ha" (Type.Imm 32) in
          let hb = Var.create ~is_virtual:true ~fresh:false "t5r_hb" (Type.Imm 32) in
          let ht = Var.create ~is_virtual:true ~fresh:false "t5r_ht" (Type.Imm 32) in
          let hu = Var.create ~is_virtual:true ~fresh:false "t5r_hu" (Type.Imm 64) in
          let hka =
            Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 16)))
          in
          let hkb =
            Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 store_off)))
          in
          (* hu ∈ [0,8]: the load address rbp - hu is the hull [rbp-8, rbp]. *)
          let hull_addr = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Var hu) in
          let sub_h, _ =
            sub_of "t5_store_row_hull"
              [ [ Def.create rbp (Bil.Var (v64 "RSP"));
                  Def.create ha (Bil.Load (Bil.Var hmem, hka, LittleEndian, `r32));
                  Def.create hb (Bil.Var ha);
                  Def.create hmem (Bil.Store (Bil.Var hmem, hkb, Bil.Var hb, LittleEndian, `r32));
                  Def.create ht (Bil.Load (Bil.Var hmem, hull_addr, LittleEndian, `r32)) ],
                [ (1, fun tt ->
                      mk_jmp_to tt
                        (Bil.BinOp (Bil.EQ, Bil.Var ht, Bil.Int (Cbat_word.to_word (w32 6))))) ];
                [], [ (0, mk_ret) ] ]
          in
          let k16 = key_of (-16) and k8 = key_of (-8) in
          let wide_h = Ws.of_clp (Clp.interval ~width:32 (w32 0) (w32 200)) in
          let wide_mem_h =
            Mem.add
              (Mem.add
                 (Mem.top { Mem.addr_width = 64; Mem.addressable_width = 8 })
                 ~key:k16 ~data:(Mem.Val.create wide_h LittleEndian))
              ~key:k8 ~data:(Mem.Val.create wide_h LittleEndian)
          in
          let entry_h =
            AI.add_memory
              (AI.add_word (anchored_entry ()) ~key:hu
                 ~data:(Ws.of_clp (Clp.interval ~width:64 (w64 0) (w64 8))))
              ~key:hmem ~data:wide_mem_h
          in
          let sol_h =
            static_graph_vsa ~abi:Hike_abi.x86_64_sysv
              sub_h
              (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv ~entry:entry_h sub_h)
          in
          let rctx_h = mk_rctx ~abi:Hike_abi.x86_64_sysv sub_h in
          let blk_h = List.nth (Term.enum blk_t sub_h |> Seq.to_list) 0 in
          let forward = Vsa.Test_seam.denote_defs blk_h entry_h in
          let entry_h = AI.add_word entry_h ~key:ht ~data:(Ws.singleton (w32 6)) in
          let refined =
            Vsa.Test_seam.refine_edge ~sol:sol_h ~rctx:rctx_h
              ~seeds:(Var.Set.singleton ht)
              entry_h blk_h
          in
          (refined, forward, ha, hb, hmem, hka, hkb)
        in
        (* S6: the store at rbp-8 sits inside the hull [rbp-8, rbp], but the
           read's set spans past the store's cell, so the read does not read
           the store on every path — the delivery is the identity. *)
        let refined_p, forward_p, ha_p, hb_p, hmem_p, hka_p, hkb_p = hull_case ~store_off:8 in
        let cell_p addr =
          Result.fold
            (Vsa.Test_seam.denote_imm_exp (Bil.Load (Bil.Var hmem_p, addr, LittleEndian, `r32)) refined_p)
            ~ok:Fun.id ~error:(fun _ -> Ws.top 32)
        in
        check
          "T5-2 (Store row, hull): S6 — a set-valued load address spanning past the store's \
           cell delivers nothing; the store's key cell keeps its wide value"
          (Ws.equal (cell_p hkb_p) (Ws.of_clp (Clp.interval ~width:32 (w32 0) (w32 200))));
        check
          "T5-2 (Store row, hull): S6 — the store's data producers keep their forward values"
          (Ws.equal (AI.find_word 32 refined_p hb_p) (AI.find_word 32 forward_p hb_p)
          && Ws.equal (AI.find_word 32 refined_p ha_p) (AI.find_word 32 forward_p ha_p));
        (* Negative: the store at rbp-16 is outside the hull [rbp-8, rbp]. *)
        let refined_n, forward_n, ha_n, hb_n, hmem_n, _hka_n, hkb_n =
          hull_case ~store_off:16 in
        let cell_n addr =
          Result.fold
            (Vsa.Test_seam.denote_imm_exp (Bil.Load (Bil.Var hmem_n, addr, LittleEndian, `r32)) refined_n)
            ~ok:Fun.id ~error:(fun _ -> Ws.top 32)
        in
        check
          "T5-2 (Store row, hull negative): a store outside the hull is untouched — its key \
           cell stays wide"
          (Ws.equal (cell_n hkb_n) (Ws.of_clp (Clp.interval ~width:32 (w32 0) (w32 200))));
        check
          "T5-2 (Store row, hull negative): a store outside the hull leaves the data \
           producers at their forward values"
          (Ws.equal (AI.find_word 32 refined_n hb_n) (AI.find_word 32 forward_n hb_n)
          && Ws.equal (AI.find_word 32 refined_n ha_n) (AI.find_word 32 forward_n ha_n)));

    (* The cross-block cell carry: the store that wrote the cell is in
       ANOTHER block; the guard block's walk still delivers the load's
       constraint across the boundary — the walked block's entry state
       (and the taken view's IN state after the fixpoint) holds the
       constrained cell. *)
    pin "INT-33"
      "C3: a cell constraint crosses the block boundary — the store is in another block, and        the guard block's walk delivers the constrained cell"
      (fun () ->
        let mem = memv "cb_m" in
        let rbp = v64 "RBP" in
        let ta = Var.create ~is_virtual:true ~fresh:false "cb_a" (Type.Imm 32) in
        let tb = Var.create ~is_virtual:true ~fresh:false "cb_b" (Type.Imm 32) in
        let t2 = Var.create ~is_virtual:true ~fresh:false "cb_t" (Type.Imm 32) in
        let ka = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 16))) in
        let kb = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
        let sub, tids =
          sub_of "cb_carry"
            [ [ Def.create rbp (Bil.Var (v64 "RSP"));
                Def.create ta (Bil.Load (Bil.Var mem, ka, LittleEndian, `r32));
                Def.create tb (Bil.Var ta);
                Def.create mem (Bil.Store (Bil.Var mem, kb, Bil.Var tb, LittleEndian, `r32)) ],
              [ (1, mk_goto) ];
              [ Def.create t2 (Bil.Load (Bil.Var mem, kb, LittleEndian, `r32)) ],
              [ (2, fun tt ->
                    mk_jmp_to tt (Bil.BinOp (Bil.EQ, Bil.Var t2, Bil.Int (Cbat_word.to_word (w32 6)))));
                (3, fun tt ->
                    mk_jmp_to tt
                      (Bil.UnOp (Bil.NOT, Bil.BinOp (Bil.EQ, Bil.Var t2, Bil.Int (Cbat_word.to_word (w32 6)))))) ];
              [], [ (0, mk_ret) ];
              [], [ (0, mk_ret) ] ]
        in
        let guard_tid = tids.(1) and taken_tid = tids.(2) in
        let key_ofw w =
          match Mem.Key.of_wordset (Ws.stack_word_i64 (Stdlib.Int64.of_int w)) with
          | [ k ] -> k
          | _ -> failwith "key"
        in
        let k8 = key_ofw (-8) in
        let wide = Ws.of_clp (Clp.interval ~width:32 (w32 0) (w32 200)) in
        let wide_mem =
          Mem.add
            (Mem.add
               (Mem.top { Mem.addr_width = 64; Mem.addressable_width = 8 })
               ~key:(key_ofw (-16)) ~data:(Mem.Val.create wide LittleEndian))
            ~key:k8 ~data:(Mem.Val.create wide LittleEndian)
        in
        let entry = AI.add_memory (anchored_entry ()) ~key:mem ~data:wide_mem in
        let sol =
          static_graph_vsa ~abi:Hike_abi.x86_64_sysv
            sub
            (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv ~entry sub)
        in
        let cell_of env =
          Result.fold
            (Vsa.Test_seam.denote_imm_exp (Bil.Load (Bil.Var mem, kb, LittleEndian, `r32)) env)
            ~ok:Fun.id ~error:(fun _ -> Ws.top 32)
        in
        (* Walk-level: the guard block's walk returns the block's entry
           state with the constrained cell. *)
        let rctx = mk_rctx ~abi:Hike_abi.x86_64_sysv sub in
        let blk1 =
          Term.enum blk_t sub |> Seq.to_list
          |> List.find (fun b -> Term.tid b = guard_tid)
        in
        let refined =
          Vsa.Test_seam.refine_edge ~sol ~rctx
            ~seeds:(Var.Set.singleton t2)
            (AI.add_word entry ~key:t2 ~data:(Ws.singleton (w32 6))) blk1
        in
        check
          "C3: the constraint crosses the block boundary — the walked block's entry state holds            the constrained cell {6}"
          (Ws.equal (cell_of refined) (Ws.singleton (w32 6)));
        (* Fixpoint-level: the taken view's IN state carries it too. *)
        check
          "C3: the taken view's IN state holds the constrained cell {6} (the store is in            another block)"
          (Ws.equal
             (cell_of (Graphlib.Std.Solution.get sol taken_tid))
             (Ws.singleton (w32 6))));

    (* Pin F: the negative store match — a store that must NOT match
       (mismatched endianness, mismatched width, or a disjoint key)
       delivers nothing: the store's data producers stay unconstrained. *)
    pin "INT-34"
      "F: a store whose shape mismatches the read (endian, width) or whose key is disjoint        delivers nothing — the data producers stay unconstrained"
      (fun () ->
        let mk ~(store_endian : endian) ~(store_sz : Size.t) ~(load_addr : exp)
            ~(load_endian : endian) ~(seed_wide : Mem.Key.t list)
            ~(seed_data : Ws.t) : AI.t * var * var * AI.t =
          let mem = memv "pf_m" in
          let rbp = v64 "RBP" in
          (* The producing chain runs at the store's own width. *)
          let data_w = Size.in_bits store_sz in
          let data_sz = store_sz in
          let ta = Var.create ~is_virtual:true ~fresh:false "pf_a" (Type.Imm data_w) in
          let tb = Var.create ~is_virtual:true ~fresh:false "pf_b" (Type.Imm data_w) in
          let t2 = Var.create ~is_virtual:true ~fresh:false "pf_t" (Type.Imm 32) in
          let ka = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 16))) in
          let kb = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
          let sub, _ =
            sub_of "pf_store_row"
              [ [ Def.create rbp (Bil.Var (v64 "RSP"));
                  Def.create ta (Bil.Load (Bil.Var mem, ka, LittleEndian, data_sz));
                  Def.create tb (Bil.Var ta);
                  Def.create mem
                    (Bil.Store (Bil.Var mem, kb, Bil.Var tb, store_endian, store_sz));
                  Def.create t2 (Bil.Load (Bil.Var mem, load_addr, load_endian, `r32)) ],
                [ (1, fun tt ->
                      mk_jmp_to tt
                        (Bil.BinOp (Bil.EQ, Bil.Var t2, Bil.Int (Cbat_word.to_word (w32 6))))) ];
                [], [ (0, mk_ret) ] ]
          in
          let base =
            Core.List.fold (List.rev seed_wide)
              ~init:(Mem.top { Mem.addr_width = 64; Mem.addressable_width = 8 })
              ~f:(fun m k -> Mem.add m ~key:k ~data:(Mem.Val.create seed_data LittleEndian))
          in
          let entry = AI.add_memory (anchored_entry ()) ~key:mem ~data:base in
          let sol =
            static_graph_vsa ~abi:Hike_abi.x86_64_sysv
              sub
              (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv ~entry sub)
          in
          let rctx = mk_rctx ~abi:Hike_abi.x86_64_sysv sub in
          let blk = List.nth (Term.enum blk_t sub |> Seq.to_list) 0 in
          let forward = Vsa.Test_seam.denote_defs blk entry in
          let entry = AI.add_word entry ~key:t2 ~data:(Ws.singleton (w32 6)) in
          let refined =
            Vsa.Test_seam.refine_edge ~sol ~rctx
              ~seeds:(Var.Set.singleton t2)
              entry blk
          in
          (refined, ta, tb, forward)
        in
        let rbp = v64 "RBP" in
        let kb = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
        let k24 = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 24))) in
        let key_ofw w =
          match Mem.Key.of_wordset (Ws.stack_word_i64 (Stdlib.Int64.of_int w)) with
          | [ k ] -> k
          | _ -> failwith "key"
        in
        (* No delivery: each producer keeps its forward value at the edge. *)
        let unconstrained refined forward ta tb =
          let at v st = AI.find_word (match Var.typ v with Type.Imm w -> w | _ -> 64) st v in
          Ws.equal (at ta refined) (at ta forward) && Ws.equal (at tb refined) (at tb forward)
        in
        (* Endian: the store writes LittleEndian, the read is BigEndian. *)
        let r_e, ta_e, tb_e, f_e =
          mk ~store_endian:LittleEndian ~store_sz:`r32 ~load_addr:kb
            ~load_endian:BigEndian ~seed_wide:[ key_ofw (-16); key_ofw (-8) ]
            ~seed_data:(Ws.top 32) in
        check "F (endian): a foreign-endian store's data producers stay unconstrained"
          (unconstrained r_e f_e ta_e tb_e);
        (* Width: the store writes 8 bytes, the read takes 4. *)
        let r_w, ta_w, tb_w, f_w =
          mk ~store_endian:LittleEndian ~store_sz:`r64 ~load_addr:kb
            ~load_endian:LittleEndian ~seed_wide:[ key_ofw (-16); key_ofw (-8) ]
            ~seed_data:(Ws.of_clp (Clp.interval ~width:32 (w32 0) (w32 200))) in
        check "F (width): a wider store's data producers stay unconstrained"
          (unconstrained r_w f_w ta_w tb_w);
        (* Disjoint key: the read's cell is elsewhere. *)
        let r_d, ta_d, tb_d, f_d =
          mk ~store_endian:LittleEndian ~store_sz:`r32 ~load_addr:k24
            ~load_endian:LittleEndian ~seed_wide:[ key_ofw (-16); key_ofw (-24) ]
            ~seed_data:(Ws.of_clp (Clp.interval ~width:32 (w32 0) (w32 200))) in
        check "F (disjoint): a store outside the read's range leaves the producers unconstrained"
          (unconstrained r_d f_d ta_d tb_d));

    (* Pin A: the empty cell meet is the identity — the cell keeps its
       stored value; the dead-path bottom is never written. *)
    pin "INT-32"
      "A: a cell meet whose intersection is empty leaves the env unchanged (the stored value        stays, no dead-path bottom)"
      (fun () ->
        let m = memv "pina_m" in
        let rbp = v64 "RBP" in
        let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
        let key = key_of (Ws.stack_word_i64 (-8L)) in
        let cell5 =
          Mem.add
            (Mem.top { Mem.addr_width = 64; Mem.addressable_width = 8 })
            ~key ~data:(Mem.Val.create (Ws.singleton (w32 5)) LittleEndian)
        in
        let entry = AI.add_memory (anchored_entry ()) ~key:m ~data:cell5 in
        let refined =
          Vsa.Test_seam.constrain_operands
            ~landmarks:(Cbat_landmarks.create ()) ~env:entry
            (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32))
            (Ws.singleton (w32 6))
        in
        let cell =
          Mem.Val.data
            (Mem.find (32, LittleEndian)
               (AI.find_memory { Mem.addr_width = 64; Mem.addressable_width = 8 } refined m)
               key)
        in
        check
          "A: the cell keeps its stored {5} — the empty meet writes nothing, not the dead-path            bottom"
          (Ws.equal cell (Ws.singleton (w32 5)));
        check "A: the env is unchanged by the empty meet" (AI.equal refined entry));

    (* T5-3 (the T12 ruling): a bounded runtime SP adjustment is NOT a VLA
       — no allocation event; an unbounded size is the event. *)
    pin "INT-10"
      "T5-3 (T12 ruling): a bounded runtime SP adjustment is not the VLA event; an unbounded size \
       is"
      (fun () ->
        let rsp = v64 "RSP" in
        let rbp = v64 "RBP" in
        let mk ~(unbounded : bool) (name : string) : sub term =
          let t = Var.create ~is_virtual:true ~fresh:false "t5v_sz" (Type.Imm 64) in
          let mem = memv "t5v_m" in
          let sz_rhs =
            if unbounded then Bil.Load (Bil.Var mem, Bil.Var rbp, LittleEndian, `r64)
            else Bil.Int (Cbat_word.to_word (w64 16))
          in
          fst
            (sub_of name
               [ [ Def.create t sz_rhs;
                   Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Var t)) ],
                 [ (1, mk_goto) ];
                 [], [ (0, mk_ret) ] ])
        in
        let bounded = mk ~unbounded:false "t5v_bounded" in
        let unbounded = mk ~unbounded:true "t5v_unbounded" in
        let fb, bounded = fixture_facts_sub bounded in
        let fu, unbounded = fixture_facts_sub unbounded in
        check
          "T5-3 (T12 ruling): a bounded runtime SP adjustment is NOT a VLA — no allocation event"
          (Core.Set.is_empty
             (Core.Map.key_set (Hike.Sections.dynamic_allocs_of ~facts:fb bounded)));
        check "T5-3 (T12 ruling): an unbounded runtime SP size IS the allocation event"
          (not
             (Core.Set.is_empty
                (Core.Map.key_set (Hike.Sections.dynamic_allocs_of ~facts:fu unbounded)))));

    (* T5-4 (head extrapolation): a cell widens strictly by its OWN
       entries — no own entries plain-widen; own entries translate by
       their own steps; a bottom old state stays the plain widen.  One
       pin per logical check. *)
    pin "INT-20" "T5-4 contrast: the plain memory widen drives the cell data infinite"
      (fun () ->
        let mv = memv "t5x_m" in
        let xv = Var.create ~is_virtual:true ~fresh:false "t5x_w" (Type.Imm 32) in
        let key = key_of (Ws.singleton (w32 100)) in
        let midx = { Mem.addr_width = 32; Mem.addressable_width = 8 } in
        let mkstate (d : Ws.t) (wd : Ws.t) : AI.t =
          let m = Mem.add (Mem.top midx) ~key ~data:(Mem.Val.create d LittleEndian) in
          AI.add_word (AI.add_memory AI.top ~key:mv ~data:m) ~key:xv ~data:wd
        in
        let cell_of (st : AI.t) : Ws.t =
          Mem.Val.data (Mem.find (32, LittleEndian) (AI.find_memory midx st mv) key)
        in
        let d_old = Ws.singleton (w32 1) in
        let d_new = Ws.of_clp (Clp.interval ~width:32 (w32 1) (w32 2)) in
        let w_old = Ws.singleton (w32 0) and w_new = Ws.singleton (w32 1) in
        let plain = AI.widen_join (mkstate d_old w_old) (mkstate d_new w_new) in
        check "T5-4 (contrast): the plain memory widen drives the cell data infinite"
          (Ws.is_infinite (cell_of plain)));







    (* F1: the jle-counter head's lower bound is the entry constant. *)
    pin "INT-13" "LM F1: the jle-counter head and taken view lower bounds are the entry constant 0"
      (fun () ->
        let sub, l1_tid, b1_tid, _ = lm_jle_loop ~k1:(w32 100) () in
        let sol = run_anchored sub in
        let i = Var.create ~is_virtual:false ~fresh:false "lm_i" (Type.Imm 32) in
        let head_i = AI.find_word 32 (Graphlib.Std.Solution.get sol l1_tid) i in
        check_bound "property LM F1: the head's lower bound is the entry constant 0"
          (Ws.min_elem head_i) (fun lo -> Cbat_word.equal lo (w32 0));
        (* The taken view's state is the body's IN-state. *)
        let taken_i = AI.find_word 32 (Graphlib.Std.Solution.get sol b1_tid) i in
        check_bound "property LM F1: the taken view's lower bound is the entry constant 0"
          (Ws.min_elem taken_i) (fun lo -> Cbat_word.equal lo (w32 0)));

        (* F1-FT: the fallthrough-edge fixture — the head, taken body, and
       fallthrough exit pin the walk's delivered values. *)
    pin "INT-15"
      "LM F1-FT: the head, taken body, and fallthrough exit pin the walk-delivered counter values"
      (fun () ->
        let k, sub, sol, l1_tid, b1_tid = lm_jne_run () in
        let i = Var.create ~is_virtual:false ~fresh:false "lm_ne_i" (Type.Imm 32) in
        let st tid = Graphlib.Std.Solution.get sol tid in
        let head_i = AI.find_word 32 (st l1_tid) i in
        check_bound "property LM F1-FT: the head's lower bound is the entry constant 0 (vertex side \
                     of the pin)"
          (Ws.min_elem head_i) (fun lo -> Cbat_word.equal lo (w32 0));
        check_bound "property LM F1-FT: the head's upper bound is the landmark K (vertex side of the \
                     pin)"
          (Ws.max_elem head_i) (fun hi -> Cbat_word.equal hi k);
        let body_i = AI.find_word 32 (st b1_tid) i in
        check_bound "property LM F1-FT: the taken body's lower bound is the entry constant 0"
          (Ws.min_elem body_i) (fun lo -> Cbat_word.equal lo (w32 0));
        check_bound "property LM F1-FT: the taken body's upper bound is K-1 (the guard excluded the \
                     landmark)"
          (Ws.max_elem body_i) (fun hi -> Cbat_word.equal hi (Cbat_word.pred k));
        let exits = exit_blocks_of sub in
        let exit_i =
          match exits with [ b ] -> AI.find_word 32 (st (Term.tid b)) i | _ -> assert false
        in
        check
          "property LM F1-FT: the fallthrough exit pins the counter to {K} exactly (walk side of \
           the pin)"
          (Ws.equal exit_i (Ws.singleton k)));

                (* F1-B4 (the walk's cell meet): the walk's product is the cell meet
       through a Load-producing def, so the fixture seeds a Var constraint
       on a var whose guard-block def is a Load over a known cell with a
       WIDE stored range. *)
    pin "INT-19"
      "LM F1-B4: the walk's cell meet fires through a Load-producing def, moving the cell off its \
       wide range"
      (fun () ->
        let k = w32 100 in
        let sub0, l1_tid, _b1_tid = lm_jne_loop ~k () in
        let i = Var.create ~is_virtual:false ~fresh:false "lm_ne_i" (Type.Imm 32) in
        let mem = Var.create ~is_virtual:true ~fresh:false "f1b4_m" (Type.Mem (`r64, `r8)) in
        (* Prepend to the guard block: t := Load[mem, RBP-8]; i := t.  The
           seed on i walks backward through i's def to t's Load and meets
           the cell. *)
        let guard_blk =
          Term.enum blk_t sub0 |> Seq.to_list |> List.find (fun b -> Term.tid b = l1_tid)
        in
        let t = Var.create ~is_virtual:true ~fresh:false "f1b4_t" (Type.Imm 32) in
        let rbp = v64 "RBP" in
        let gb =
          with_jmps
            (blk_of_defs
               ([ Def.create t
                    (Bil.Load
                       ( Bil.Var mem,
                         Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))),
                         LittleEndian,
                         `r32 ));
                  Def.create i (Bil.Var t) ]
               @ (Term.enum def_t guard_blk |> Seq.to_list)))
            (Term.enum jmp_t guard_blk |> Seq.to_list)
        in
        let sub_b = Sub.Builder.create ~name:"f1b4_sub" () in
        Term.enum blk_t sub0
        |> Seq.iter ~f:(fun b ->
               if Term.tid b = l1_tid then Sub.Builder.add_blk sub_b gb
               else Sub.Builder.add_blk sub_b b);
        let sub = Sub.Builder.result sub_b in
        (* The entry — and therefore the solution snapshot the walk
           re-denotes against — must carry the memory binding. *)
        let wide = Ws.of_clp (Clp.interval ~width:32 (w32 0) (w32 200)) in
        let key =
          match Mem.Key.of_wordset (Ws.stack_word_i64 (-8L)) with
          | [ k ] -> k
  | _ -> failwith "key"
        in
        let wide_mem =
          Mem.add
            (Mem.top { Mem.addr_width = 64; Mem.addressable_width = 8 })
            ~key ~data:(Mem.Val.create wide LittleEndian)
        in
        let entry = AI.add_memory (anchored_entry ()) ~key:mem ~data:wide_mem in
        let sol =
          static_graph_vsa ~abi:Hike_abi.x86_64_sysv
            sub
            (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv ~entry sub)
        in
        let rctx = mk_rctx ~abi:Hike_abi.x86_64_sysv sub in
        let walk () =
          let entry = AI.add_word entry ~key:i ~data:(Ws.singleton k) in
          Vsa.Test_seam.refine_edge ~sol ~rctx
            ~seeds:(Var.Set.singleton i)
            entry gb
        in
        let cell_of env =
          Result.fold
            (Vsa.Test_seam.denote_imm_exp
               (Bil.Load
                  ( Bil.Var mem,
                    Bil.BinOp
                      (Bil.MINUS, Bil.Var (v64 "RBP"), Bil.Int (Cbat_word.to_word (w64 8))),
                    LittleEndian,
                    `r32 ))
               env)
            ~ok:Fun.id ~error:(fun _ -> Ws.top 32)
        in
        let full_cell = cell_of (walk ()) in
        check
          "property LM F1-B4: the walk meets the cell (the fixture's precondition: the walk moves \
           the cell off its wide range)"
          (Ws.precedes full_cell wide));

    (* The landmark consumption: one reading warms the entry, a second,
       closer one fires the traversal-step estimate. *)
    pin "INT-24"
      "LM steps: a shrinking distance fires Finite (record, advance, re-record)"
      (fun () ->
        let h = Tid.for_name "lm_steps_head" in
        let lm = Cbat_landmarks.create () in
        Cbat_landmarks.record lm ~key:lw ~head:h ~bound:(w32 100)
          ~is_upper:true ~warmed:false ~dist:10;
        check "LM steps: a just-recorded entry waits for a second measurement"
          (match Cbat_landmarks.steps lm h lw with
           | Cbat_landmarks.Zero -> true
           | _ -> false);
        Cbat_landmarks.advance lm h lw;
        Cbat_landmarks.record lm ~key:lw ~head:h ~bound:(w32 100)
          ~is_upper:true ~warmed:false ~dist:6;
        check "LM steps: the closer reading fires the steps ((6) / (10 - 6) = 1)"
          (match Cbat_landmarks.steps lm h lw with
           | Cbat_landmarks.Finite 1 -> true
           | _ -> false));

    (* A landmark the guard stopped disabling leaves no reading behind;
       it must not hold the head in the non-widening arm. *)
    pin "INT-25"
      "LM steps: an entry consumed without a fresh reading never holds the head in Zero"
      (fun () ->
        let h = Tid.for_name "lm_stale_head" in
        let lm = Cbat_landmarks.create () in
        Cbat_landmarks.record lm ~key:lw ~head:h ~bound:(w32 100)
          ~is_upper:true ~warmed:false ~dist:10;
        Cbat_landmarks.advance lm h lw;
        Cbat_landmarks.record lm ~key:lw ~head:h ~bound:(w32 200)
          ~is_upper:true ~warmed:false ~dist:5;
        Cbat_landmarks.advance lm h lw;
        Cbat_landmarks.record lm ~key:lw ~head:h ~bound:(w32 200)
          ~is_upper:true ~warmed:false ~dist:4;
        check "LM steps: the live entry still fires ((4) / (5 - 4) = 4)"
          (match Cbat_landmarks.steps lm h lw with
           | Cbat_landmarks.Finite 4 -> true
           | _ -> false));

    (* The rotation keeps the history an entry holds: a round with no
       reading of its own must not erase the measurement the next
       reading pairs against. *)
    pin "INT-28"
      "LM steps: a round with no reading keeps the entry's history"
      (fun () ->
        let h = Tid.for_name "lm_rotate_head" in
        let lm = Cbat_landmarks.create () in
        Cbat_landmarks.record lm ~key:lw ~head:h ~bound:(w32 100)
          ~is_upper:true ~warmed:false ~dist:10;
        Cbat_landmarks.advance lm h lw;
        Cbat_landmarks.advance lm h lw;
        Cbat_landmarks.record lm ~key:lw ~head:h ~bound:(w32 100)
          ~is_upper:true ~warmed:false ~dist:5;
        check "LM steps: the reading after an empty round still pairs ((5) / (10 - 5) = 1)"
          (match Cbat_landmarks.steps lm h lw with
           | Cbat_landmarks.Finite 1 -> true
           | _ -> false));

    (* The magnitude's own edge: |2^63| overflows int64, so the
       difference must cap, never raise. *)
    pin "INT-29" "LM distance: a 2^63 difference caps (the abs overflow)"
      (fun () ->
        let h = Tid.for_name "lm_dist63_head" in
        let lm = Cbat_landmarks.create () in
        Cbat_landmarks.with_widening_head lm (Some h) (fun () ->
            ignore
              (observe_meet lm ~key:lw
                 ~p:(Ws.singleton (w64 0))
                 ~cstr:(Ws.singleton (Cbat_word.of_int64 Stdlib.Int64.min_int))));
        check "LM distance: the 2^63 difference reads the cap"
          (match Cbat_landmarks.entries lm h lw with
           | e :: _ -> (
               match e.Cbat_landmarks.dist with
               | Some d -> d = 1 lsl 40
               | None -> false)
           | [] -> false));

    (* A stack-symbolic value and a plain word are disjoint by line: the
       empty meet disables no behavior. *)
    pin "INT-26"
      "LM acquisition: an empty meet between different lines records no landmark"
      (fun () ->
        let h = Tid.for_name "lm_line_head" in
        let lm = Cbat_landmarks.create () in
        let p = Ws.stack_word (Clp.interval ~width:64 (w64 0) (w64 16)) in
        Cbat_landmarks.with_widening_head lm (Some h) (fun () ->
            ignore
              (observe_meet lm ~key:lw ~p
                 ~cstr:(Ws.singleton (w64 4))));
        check
          "LM acquisition: a stack-symbolic value against a plain word is no landmark"
          (Cbat_landmarks.entries lm h lw = []));

    (* The distance is the counter's own (signed) walk: a value below
       zero is one step from 0, not 2^64 - 1. *)
    pin "INT-27"
      "LM distance: a counter below zero measures its signed distance"
      (fun () ->
        let h = Tid.for_name "lm_dist_head" in
        let lm = Cbat_landmarks.create () in
        Cbat_landmarks.with_widening_head lm (Some h) (fun () ->
            ignore
              (observe_meet lm ~key:lw
                 ~p:(Ws.singleton (w64 (-99999)))
                 ~cstr:(Ws.singleton (w64 0))));
        check_bound "LM distance: the recorded distance is 99999"
          (match Cbat_landmarks.entries lm h lw with
           | e :: _ -> e.Cbat_landmarks.dist
           | [] -> None)
          (fun d -> d = 99999));

    (* The one module's own rules: the per-key cap and the upsert. *)
    pin "INT-30" "LM table: every distinct boundary is kept, for either key"
      (fun () ->
        let h = Tid.for_name "lm_cap_head" in
        let lm = Cbat_landmarks.create () in
        let cell i =
          Cbat_landmarks.Cell
            { Cbat_landmarks.origin = Hike_origin.Stack;
              lo_width = 64; lo_value = Int64.of_int i;
              hi_width = 64; hi_value = Int64.of_int i; stride = 1 }
        in
        for i = 0 to 99 do
          Cbat_landmarks.record lm ~head:h ~key:(cell i) ~bound:(w64 i)
            ~is_upper:true ~warmed:false ~dist:1
        done;
        let count which =
          List.fold_left
            (fun n k ->
              if which k then n + List.length (Cbat_landmarks.entries lm h k)
              else n)
            0 (Cbat_landmarks.keys_at lm h)
        in
        let cells = count (function Cbat_landmarks.Cell _ -> true | _ -> false) in
        for i = 0 to 99 do
          Cbat_landmarks.record lm ~head:h ~key:lw
            ~bound:(w64 i) ~is_upper:true ~warmed:false ~dist:1
        done;
        let words =
          count (function Cbat_landmarks.Word _ -> true | _ -> false)
        in
        check "LM table (a): a cell head keeps every distinct boundary"
          (cells = 100);
        check "LM table (b): a word row keeps every distinct boundary"
          (words = 100));

    (* The narrowed word arm (reachable since the one leaf rule): a
       narrowed record carries its own reading as the prior, so a
       second, closer narrowing fires the traversal-step estimate. *)
    pin "INT-35"
      "the narrowed word arm: two narrowed records pair (the first is never fresh) and fire        Finite"
      (fun () ->
        let h = Tid.for_name "lm_narrowed_head" in
        let lm = Cbat_landmarks.create () in
        Cbat_landmarks.with_widening_head lm (Some h) (fun () ->
            (* p = [0,100] narrowed to [50,100]: a lower landmark at 49. *)
            ignore
              (observe_meet lm ~key:lw
                 ~p:(Ws.of_clp (Clp.interval ~width:32 (w32 0) (w32 100)))
                 ~cstr:(Ws.of_clp (Clp.interval ~width:32 (w32 50) (w32 100))));
            (* A closer narrowing on the same boundary: [60,100]. *)
            ignore
              (observe_meet lm ~key:lw
                 ~p:(Ws.of_clp (Clp.interval ~width:32 (w32 0) (w32 100)))
                 ~cstr:(Ws.of_clp (Clp.interval ~width:32 (w32 60) (w32 100)))));
        (* The first reading: 10 (0 -> 49 is 49 steps? distance p_min=0 to
           bound=49).  The second: 0 -> 59 is 59 — NOT closer, so pair by
           the recorded rule: dist_p = the entry's prior (10), dist = the
           closer one wins only if smaller.  Use the direct record form
           instead for exactness. *)
        let h2 = Tid.for_name "lm_narrowed_head2" in
        let lm2 = Cbat_landmarks.create () in
        Cbat_landmarks.record lm2 ~key:lw ~head:h2 ~bound:(w32 100)
          ~is_upper:true ~warmed:true ~dist:10;
        check "narrowed arm: a lone warmed record does not answer Zero (it widens until paired)"
          (match Cbat_landmarks.steps lm2 h2 lw with
           | Cbat_landmarks.Zero -> false
           | _ -> true);
        (* dist_p = dist = 10 gives no shrink; a closer second reading fires. *)
        Cbat_landmarks.record lm2 ~key:lw ~head:h2 ~bound:(w32 100)
          ~is_upper:true ~warmed:true ~dist:6;
        check "narrowed arm: the closer narrowed reading fires the steps (6 / (10 - 6) = 1)"
          (match Cbat_landmarks.steps lm2 h2 lw with
           | Cbat_landmarks.Finite 1 -> true
           | _ -> false);
        (* And the warmed entry never holds the head in Zero (the INT-15
           property at record time). *)
        let h3 = Tid.for_name "lm_narrowed_head3" in
        let lm3 = Cbat_landmarks.create () in
        Cbat_landmarks.record lm3 ~key:lw ~head:h3 ~bound:(w32 7)
          ~is_upper:false ~warmed:true ~dist:3;
        check "narrowed arm: a lone warmed record does not answer Zero (it widens until paired)"
          (match Cbat_landmarks.steps lm3 h3 lw with
           | Cbat_landmarks.Zero -> false
           | _ -> true));

    (* Pin B (re-pinned): the cell's own Zero arm advances and WIDENS.
       The join form this pin once asserted is the corpus-refuted
       candidate — a loop-carried cell never stabilizes under a plain
       join (out_section_sweep/out_rodata_strings ground to the 6000-
       visit backstop), so the widening IS the cell's tuned Zero
       action; the word's Zero joins. *)
    pin "INT-36"
      "B (re-pinned): a cell whose entry is Zero advances its own row and widens — the        loop-stabilizing form"
      (fun () ->
        let mv = memv "pib_m" in
        let key = key_of (Ws.singleton (w32 100)) in
        let midx = { Mem.addr_width = 32; Mem.addressable_width = 8 } in
        let mkstate (d : Ws.t) : AI.t =
          let m = Mem.add (Mem.top midx) ~key ~data:(Mem.Val.create d LittleEndian) in
          AI.add_memory AI.top ~key:mv ~data:m
        in
        let cell_of (st : AI.t) : Ws.t =
          Mem.Val.data (Mem.find (32, LittleEndian) (AI.find_memory midx st mv) key)
        in
        let h = Tid.for_name "pib_head" in
        let lm = Cbat_landmarks.create () in
        let cl = Cbat_landmarks.Cell (Mem.Key.cell_key key) in
        (* One fresh cell reading: its own arm is Zero.  The head's arm
           is Inf, so the cell reads its own row. *)
        Cbat_landmarks.record lm ~head:h ~key:cl ~bound:(w32 8)
          ~is_upper:true ~warmed:false ~dist:2;
        let d_old = Ws.singleton (w32 1) in
        let d_new = Ws.of_clp (Clp.interval ~width:32 (w32 1) (w32 3)) in
        let joined =
          AI.widen_with_landmarks ~head:h ~landmarks:lm
            ~need:(Core.Int.Set.singleton (Cbat_var_id.intern mv))
            (mkstate d_old) (mkstate d_new)
        in
        let c = cell_of joined in
        check "B: the cell's Zero arm widens — the loop-stabilizing form (the join variant                grinds the corpus fixpoint to the visit budget)"
          (Ws.is_infinite c);
        (* The advance rotated the cell's own row. *)
        check "B: the advance committed the cell's own reading"
          (match Cbat_landmarks.entries lm h cl with
           | [ e ] -> (match e.Cbat_landmarks.dist_p, e.Cbat_landmarks.dist with
                       | Some 2, None -> true
                       | _ -> false)
           | _ -> false);
        (* The contrast at the same shape without the entry: plain widen. *)
        let lm2 = Cbat_landmarks.create () in
        let widened =
          AI.widen_with_landmarks ~head:h ~landmarks:lm2
            ~need:(Core.Int.Set.singleton (Cbat_var_id.intern mv))
            (mkstate d_old) (mkstate d_new)
        in
        check "B (contrast): without own entries the cell widens (INT-20's baseline)"
          (Ws.is_infinite (cell_of widened)));

    (* Pin C: per-key consumption — a word-driven arm does not rotate a
       cell's entries, and the clear spends only what was consumed. *)
    pin "INT-37"
      "C: the head's arm spends only the key it consumed — a word advance leaves the cell's        entries, and a word extrapolation clears its own row only"
      (fun () ->
        let h = Tid.for_name "pic_head" in
        let mv = memv "pic_m" in
        let key = key_of (Ws.singleton (w32 100)) in
        let midx = { Mem.addr_width = 32; Mem.addressable_width = 8 } in
        let cl = Cbat_landmarks.Cell (Mem.Key.cell_key key) in
        let mkstate (d : Ws.t) (wd : Ws.t) : AI.t =
          let m = Mem.add (Mem.top midx) ~key ~data:(Mem.Val.create d LittleEndian) in
          AI.add_word (AI.add_memory AI.top ~key:mv ~data:m) ~key:lw_var ~data:wd
        in
        (* The Zero half: the head's word arm advances the word's own
           row; the cell — no own entries, no own Zero — is not
           advanced, and no cell row appears. *)
        let lm = Cbat_landmarks.create () in
        Cbat_landmarks.record lm ~head:h ~key:lw ~bound:(w32 50)
          ~is_upper:true ~warmed:false ~dist:4;
        let j =
          AI.advance_join_landmarks ~head:h ~landmarks:lm
            ~need:(Core.Int.Set.singleton (Cbat_var_id.intern lw_var))
            (mkstate (Ws.singleton (w32 1)) (Ws.singleton (w32 0)))
            (mkstate (Ws.singleton (w32 2)) (Ws.singleton (w32 1)))
        in
        ignore j;
        check "C (Zero): the word-driven advance rotated the word row"
          (match Cbat_landmarks.entries lm h lw with
           | [ e ] -> (match e.Cbat_landmarks.dist_p, e.Cbat_landmarks.dist with
                       | Some 4, None -> true | _ -> false)
           | _ -> false);
        check "C (Zero): the word-driven advance left no cell row behind"
          (Cbat_landmarks.entries lm h cl = []);
        (* The Finite half: a word extrapolation clears its own row; the
           cell row survives. *)
        let lm2 = Cbat_landmarks.create () in
        Cbat_landmarks.record lm2 ~head:h ~key:lw ~bound:(w32 50)
          ~is_upper:true ~warmed:false ~dist:10;
        Cbat_landmarks.advance lm2 h lw;
        Cbat_landmarks.record lm2 ~head:h ~key:lw ~bound:(w32 50)
          ~is_upper:true ~warmed:false ~dist:6;
        Cbat_landmarks.record lm2 ~head:h ~key:cl ~bound:(w32 8)
          ~is_upper:true ~warmed:false ~dist:2;
        let w =
          AI.selective_widen_extrapolate ~head:h ~landmarks:lm2
            ~need:(Core.Int.Set.singleton (Cbat_var_id.intern lw_var))
            ~steps:1
            (mkstate (Ws.singleton (w32 0)) (Ws.singleton (w32 40)))
            (mkstate (Ws.singleton (w32 1)) (Ws.singleton (w32 41)))
        in
        ignore w;
        check "C (Finite): the word extrapolation spent its own row (cleared)"
          (Cbat_landmarks.entries lm2 h lw = []);
        check
          "C (Finite): the cell's row survives the word's clear, and its rotation came from            its OWN Zero arm"
          (match Cbat_landmarks.entries lm2 h cl with
           | [ e ] -> (match e.Cbat_landmarks.dist_p, e.Cbat_landmarks.dist with
                       | Some 2, None -> true | _ -> false)
           | _ -> false));

    pin "INT-31" "LM table: a smaller distance replaces and keeps the history"
      (fun () ->
        let h = Tid.for_name "lm_upsert_head" in
        let lm = Cbat_landmarks.create () in
        Cbat_landmarks.record lm ~head:h ~key:lw ~bound:(w64 7)
          ~is_upper:true ~warmed:false ~dist:10;
        Cbat_landmarks.advance lm h lw;
        Cbat_landmarks.record lm ~head:h ~key:lw ~bound:(w64 7)
          ~is_upper:true ~warmed:false ~dist:6;
        check "LM table: one entry per (bound, upper); 6 wins and 10 is the history"
          (match Cbat_landmarks.entries lm h lw with
           | [ e ] -> (
               match e.Cbat_landmarks.dist_p, e.Cbat_landmarks.dist with
               | Some 10, Some 6 -> true
               | _ -> false)
           | _ -> false));
  ]

let () = run "integration" tests
