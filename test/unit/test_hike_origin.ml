(* Hike_origin pins: the origin ADT, its facts table, and the one-origin
   accessor on the WordSet algebra. *)

open! Core
open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

module Origin = Hike_origin

let abi = Hike_abi.x86_64_sysv

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

(* ORI-05: the solve-boundary band refinement — window-side values
   name the caller's frame, VLA-band values the rebased SP, and a
   value spanning the bands keeps the entry-SP origin. *)
let ori_05 () =
  let window_side = Ws.stack_word_i64 16L in
  let refined = Ws.refine_origin ~word:8 window_side in
  check "window-side value refines to Window"
    (Option.equal Origin.equal (Ws.origin refined) (Some Origin.Window));
  let frame = Ws.stack_word_i64 (-8L) in
  check "below-entry value keeps Stack"
    (Option.equal Origin.equal (Ws.origin (Ws.refine_origin ~word:8 frame)) (Some Origin.Stack));
  let vla = Ws.refine_origin ~word:8 (Ws.stack_word_i64 Origin.vla_floor) in
  check "vla-band value refines to Vla" (Option.equal Origin.equal (Ws.origin vla) (Some Origin.Vla));
  let crossing =
    Ws.union (Ws.stack_word_i64 0L) (Ws.stack_word_i64 16L)
  in
  check "value spanning the entry line keeps Stack"
    (Option.equal Origin.equal (Ws.origin (Ws.refine_origin ~word:8 crossing)) (Some Origin.Stack));
  let plain = Ws.singleton (i2w 5L) in
  check "plain values pass through unchanged"
    (Option.is_none (Ws.origin (Ws.refine_origin ~word:8 plain)))

(* ORI-06: the per-def origin slot, stamped at the solve boundary — a
   window-side address def reads Window through the seam. *)
let ori_06 () =
  let rsp = Var.create ~is_virtual:false ~fresh:false "RSP" (Type.Imm 64) in
  let p = Var.create ~is_virtual:false ~fresh:false "ori_p" (Type.Imm 64) in
  let defs =
    [ Def.create p
        (Bil.BinOp (Bil.PLUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (i2w 16L)))) ]
  in
  let sub = straight_sub "ori_stamp" defs in
  let entry = anchored_entry () in
  let sol =
    Vsa.static_graph_vsa ~abi (Program.create ~subs:[ sub ] ()) sub
      (Vsa.init_sol ~abi ~entry sub)
  in
  let _, stamped = Vsa.stamp_envs_of_sol ~sol sub in
  let blk = Term.enum blk_t stamped |> Seq.to_list |> List.hd_exn in
  let d = Term.enum def_t blk |> Seq.to_list |> List.hd_exn in
  check "window-side def stamps Window"
    (Option.equal Origin.equal (Vsa.Def_origin.def_origin d) (Some Origin.Window))


(* The store-to-load round-trip: a relative value stored to a cell
   reads back with its origin.  [offs] is the pointer's offset (the
   cell address too): negative = the sub's frame (Stack), positive =
   the caller's window (Window). *)
let round_trip (offs : int64) : Origin.t option =
  let m = memv "rt_m" in
  let rsp = Var.create ~is_virtual:false ~fresh:false "RSP" (Type.Imm 64) in
  let x = Var.create ~is_virtual:false ~fresh:false "rt_x" (Type.Imm 64) in
  let ptr = Bil.BinOp (Bil.PLUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (i2w offs))) in
  let store =
    Def.create m
      (Bil.Store (Bil.Var m, ptr, ptr, LittleEndian, `r64))
  in
  let load = Def.create x (Bil.Load (Bil.Var m, ptr, LittleEndian, `r64)) in
  let sub = straight_sub "rt" [ store; load ] in
  let entry = anchored_entry () in
  let sol =
    Vsa.static_graph_vsa ~abi (Program.create ~subs:[ sub ] ()) sub
      (Vsa.init_sol ~abi ~entry sub)
  in
  let _, stamped = Vsa.stamp_envs_of_sol ~sol sub in
  let blk = Term.enum blk_t stamped |> Seq.to_list |> List.hd_exn in
  let defs = Term.enum def_t blk |> Seq.to_list in
  match List.rev defs with
  | load_def :: _ -> Vsa.Def_origin.def_origin load_def
  | _ -> None

(* ORI-07: a frame pointer stored to a cell reads back Stack. *)
let ori_07 () =
  check "stored frame pointer reads back Stack"
    (Option.equal Origin.equal (round_trip (-8L)) (Some Origin.Stack))

(* ORI-08: a caller-window pointer stored to a cell reads back Window. *)
let ori_08 () =
  check "stored window pointer reads back Window"
    (Option.equal Origin.equal (round_trip 16L) (Some Origin.Window))

let () =
  run "hike_origin"
    [ pin "ORI-01" "the facts table" ori_01;
      pin "ORI-02" "the ADT is total" ori_02;
      pin "ORI-03" "the one-origin accessor" ori_03;
      pin "ORI-04" "same-origin ops keep the origin" ori_04;
      pin "ORI-05" "the band refinement" ori_05;
      pin "ORI-06" "the per-def origin stamp" ori_06;
      pin "ORI-07" "store-to-load round-trip (frame)" ori_07;
      pin "ORI-08" "store-to-load round-trip (window)" ori_08 ]
