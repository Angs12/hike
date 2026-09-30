(* Precision-probe classification pins: the shape rule and the shape
   counters' additivity. *)

open Bap.Std
open Hike_test.Harness
open Hike_test.Common

module Rows = Precision_probe_rows

let tests : unit Alcotest.test list =
  [
    pin "PROBE-01"
      "classify_shape names the symbolic arm by its origin and the plain \
       in-segment value as lost"
      (fun () ->
        let kept = Ws.stack_word_i64 0L in
        let lost = Ws.singleton (Cbat_word.of_int64 ~width:64 Ws.stack_base) in
        let base = Ws.stack_word_i64 0L in
        let tid = Tid.create () in
        check "PROBE-01 (both land in the segment)"
          (Ws.in_stack_segment kept && Ws.in_stack_segment lost);
        check "PROBE-01 (the symbolic arm keeps its origin)"
          (Rows.classify_shape kept = `Stack);
        check "PROBE-01 (the plain in-segment value lost it)"
          (Rows.classify_shape lost = `Lost);
        check "PROBE-01 (window)"
          (Rows.classify_shape (Ws.set_origin Ws.Origin.Window base) = `Window);
        check "PROBE-01 (vla)"
          (Rows.classify_shape (Ws.vla_frame tid) = `Vla);
        check "PROBE-01 (rip -> other)"
          (Rows.classify_shape (Ws.set_origin Ws.Origin.Rip base) = `Other));

    pin "PROBE-02"
      "the five access shape counters sum to the stack-flagged access \
       population"
      (fun () ->
        let s = Rows.Sub_stats.create "add" in
        let shapes : Rows.shape list =
          [ `Stack; `Vla; `Window; `Other; `Lost ]
        in
        List.iter
          (fun sh -> Rows.Sub_stats.add_ld s ~stack:true ~shape:sh `Bounded)
          shapes;
        (* A non-stack access counts no shape. *)
        Rows.Sub_stats.add_ld s ~stack:false ~shape:`Lost `Exact;
        let sum =
          s.Rows.Sub_stats.ldstk_sh_stack + s.Rows.Sub_stats.ldstk_sh_vla
          + s.Rows.Sub_stats.ldstk_sh_window + s.Rows.Sub_stats.ldstk_sh_other
          + s.Rows.Sub_stats.ldstk_sh_lost
        in
        let pop =
          s.Rows.Sub_stats.ldstk_exact + s.Rows.Sub_stats.ldstk_bounded
          + s.Rows.Sub_stats.ldstk_top + s.Rows.Sub_stats.ldstk_bottom_live
          + s.Rows.Sub_stats.ldstk_bottom_dead
        in
        check "PROBE-02" (sum = 5 && pop = 5 && sum = pop));

    pin "PROBE-03"
      "the five def shape counters sum to the stack-flagged def population"
      (fun () ->
        let s = Rows.Sub_stats.create "add" in
        let shapes : Rows.shape list =
          [ `Stack; `Vla; `Window; `Other; `Lost ]
        in
        List.iter
          (fun sh -> Rows.Sub_stats.add_def s ~stack:true ~shape:sh `Exact)
          shapes;
        (* A non-stack def counts no shape. *)
        Rows.Sub_stats.add_def s ~stack:false ~shape:`Stack `Top;
        let sum =
          s.Rows.Sub_stats.defstk_sh_stack + s.Rows.Sub_stats.defstk_sh_vla
          + s.Rows.Sub_stats.defstk_sh_window + s.Rows.Sub_stats.defstk_sh_other
          + s.Rows.Sub_stats.defstk_sh_lost
        in
        check "PROBE-03" (sum = 5));
  ]

let () = run "probe" tests
