(* Hike_origin pins: the origin ADT, its facts table, and the one-origin
   accessor on the WordSet algebra. *)

open! Core
open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common

module Origin = Hike_origin

(* ORI-01: the facts table — every origin's base sits on the segment
   line and carries the certified entry nibble. *)
let ori_01 () =
  let st = Origin.facts Origin.Stack in
  let vl = Origin.facts Origin.Vla in
  let wn = Origin.facts Origin.Window in
  check "stack base is the segment base"
    (Stdlib.Int64.equal st.Origin.base Origin.segment_base);
  check "entry nibble certified" (st.Origin.certified = 4);
  check "stack span is 8 MiB each way"
    (Stdlib.Int64.equal (Stdlib.Int64.sub st.Origin.hi st.Origin.lo)
       (Stdlib.Int64.mul 2L (Int64.shift_left 1L 23)));
  check "vla band sits below its anchor"
    (Stdlib.Int64.compare vl.Origin.lo vl.Origin.hi < 0
    && Stdlib.Int64.compare vl.Origin.hi Origin.vla_anchor < 0
    && Stdlib.Int64.compare vl.Origin.lo Origin.vla_floor >= 0);
  check "window is the positive side" (Stdlib.Int64.compare wn.Origin.lo 0L > 0);
  check "vla band is disjoint from the window side"
    (Stdlib.Int64.compare Origin.vla_floor Origin.window_floor > 0)

(* ORI-02: the ADT is total and names every origin. *)
let ori_02 () =
  let all = [ Origin.Abs; Origin.Stack; Origin.Vla; Origin.Window; Origin.Rip ] in
  List.iter all ~f:(fun o ->
      let n = Origin.name o in
      check (sprintf "name %s nonempty" n) (String.length n > 0));
  check "five origins" (List.length all = 5)

(* The accessor's name answer, for the pin asserts. *)
let origin_name (o : Origin.t option) : string option =
  Option.map ~f:Origin.name o

(* ORI-03: the one-origin accessor — a stack value reads Stack, plain
   values read None, a mixed union reads None. *)
let ori_03 () =
  let stk = Ws.stack_word_i64 (-8L) in
  check "stack value reads Stack" (Option.equal String.equal (origin_name (Ws.origin stk)) (Some "stack"));
  let plain = Ws.singleton (i2w 5L) in
  check "plain value reads None" (Option.is_none (Ws.origin plain));
  let mixed = Ws.union stk plain in
  check "mixed union reads None" (Option.is_none (Ws.origin mixed));
  let clpv = Ws.of_clp (Clp.interval ~width:64 (i2w 0L) (i2w 16L)) in
  check "absolute clp reads None" (Option.is_none (Ws.origin clpv))

(* ORI-04: same-origin unions keep the origin. *)
let ori_04 () =
  let a = Ws.stack_word_i64 (-8L) in
  let b = Ws.stack_word_i64 (-16L) in
  check "stack union reads Stack"
    (Option.equal String.equal (origin_name (Ws.origin (Ws.union a b))) (Some "stack"));
  check "stack meet reads Stack"
    (Option.equal String.equal (origin_name (Ws.origin (Ws.intersection a b))) (Some "stack"))

let () =
  run "hike_origin"
    [ pin "ORI-01" "the facts table" ori_01;
      pin "ORI-02" "the ADT is total" ori_02;
      pin "ORI-03" "the one-origin accessor" ori_03;
      pin "ORI-04" "same-origin ops keep the origin" ori_04 ]
