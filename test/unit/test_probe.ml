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
        check "PROBE-01 (only the carried origin names stack)"
          (Ws.in_stack_segment kept && not (Ws.in_stack_segment lost));
        check "PROBE-01 (the symbolic arm keeps its origin)"
          (Rows.classify_shape kept = `Stack);
        check "PROBE-01 (the plain in-segment value lost it)"
          (Rows.classify_shape lost = `Lost);
        check "PROBE-01 (window)"
          (Rows.classify_shape (Ws.stack_word_i64 8L) = `Window);
        check "PROBE-01 (rip -> other)"
          (Rows.classify_shape (Ws.set_origin (Ws.Origin.Rip Hike_section.Rodata) base) = `Other));

    pin "PROBE-02"
      "the four access shape counters sum to the non-bottom stack-flagged \
       access population"
      (fun () ->
        let s = Rows.Sub_stats.create "add" in
        let shapes : Rows.shape list =
          [ `Stack; `Window; `Other; `Lost ]
        in
        List.iter
          (fun sh ->
             Rows.Sub_stats.add_ld s ~stack:true ~shape:(Some sh) `Bounded)
          shapes;
        (* Both bottom buckets sit in the population but count no shape. *)
        Rows.Sub_stats.add_ld s ~stack:true ~shape:None `Bottom_dead;
        Rows.Sub_stats.add_ld s ~stack:true ~shape:None `Bottom_live;
        (* A non-stack access counts no shape. *)
        Rows.Sub_stats.add_ld s ~stack:false ~shape:(Some `Lost) `Exact;
        let sum =
          s.Rows.Sub_stats.ldstk_sh_stack
          + s.Rows.Sub_stats.ldstk_sh_window + s.Rows.Sub_stats.ldstk_sh_other
          + s.Rows.Sub_stats.ldstk_sh_lost
        in
        let pop =
          s.Rows.Sub_stats.ldstk_exact + s.Rows.Sub_stats.ldstk_bounded
          + s.Rows.Sub_stats.ldstk_top + s.Rows.Sub_stats.ldstk_bottom_live
          + s.Rows.Sub_stats.ldstk_bottom_dead
        in
        let non_bottom =
          pop - s.Rows.Sub_stats.ldstk_bottom_dead
          - s.Rows.Sub_stats.ldstk_bottom_live
        in
        check "PROBE-02"
          (sum = 4 && pop = 6 && non_bottom = 4 && sum = non_bottom));

    pin "PROBE-03"
      "the four def shape counters sum to the shape-carrying stack-flagged \
       def population"
      (fun () ->
        let s = Rows.Sub_stats.create "add" in
        let shapes : Rows.shape list =
          [ `Stack; `Window; `Other; `Lost ]
        in
        List.iter
          (fun sh ->
             Rows.Sub_stats.add_def s ~stack:true ~shape:(Some sh) `Exact)
          shapes;
        let sum () =
          s.Rows.Sub_stats.defstk_sh_stack
          + s.Rows.Sub_stats.defstk_sh_window + s.Rows.Sub_stats.defstk_sh_other
          + s.Rows.Sub_stats.defstk_sh_lost
        in
        let before = sum () in
        (* A non-stack def and both bottom buckets count no shape. *)
        Rows.Sub_stats.add_def s ~stack:false ~shape:(Some `Stack) `Top;
        Rows.Sub_stats.add_def s ~stack:true ~shape:None `Bottom_dead;
        Rows.Sub_stats.add_def s ~stack:true ~shape:None `Bottom_live;
        check "PROBE-03"
          (before = 4 && sum () = 4 && s.Rows.Sub_stats.def_bottom_dead = 1
           && s.Rows.Sub_stats.def_bottom_live = 1));

    pin "PROBE-04"
      "the probe follows stack-family origins, not numeric bands: a magic, a band-reaching \
       integer, a sign-crossing hull and a frame-band literal are not stack; the symbolic arm is"
      (fun () ->
        let magic =
          Ws.singleton (Cbat_word.of_int64 ~width:64 0x4EC4EC4EC4EC4EC5L) in
        let entry =
          Ws.singleton (Cbat_word.of_int64 ~width:64 Ws.stack_base) in
        let below =
          Ws.singleton
            (Cbat_word.of_int64 ~width:64 (Int64.sub Ws.stack_base 64L)) in
        (* A pointer difference: min 2^63 - 8192, max 2^64 - 1. *)
        let base = Cbat_word.of_int64 ~width:64 0x7FFFFFFFFFFFE000L in
        let cardn = Cbat_word.of_int64 ~width:64 0x8000000000002000L in
        let crossed =
          Ws.of_clp
            (Clp.create ~width:64 ~step:(Cbat_word.one 64) ~cardn base) in
        let literal =
          Ws.singleton (Cbat_word.of_int64 ~width:64 0x3FFFFFFFFFFFFFFFL) in
        check "PROBE-04 (the domain rejects numeric coincidence)"
          (not (Ws.in_stack_segment magic));
        check "PROBE-04 (the probe rejects the band-reaching integer)"
          (not (Rows.is_stack_value magic));
        check "PROBE-04 (the sign-crossing hull is not stack)"
          (not (Rows.is_stack_value crossed));
        check "PROBE-04 (the frame-band literal is not stack, a lost shape)"
          (not (Rows.is_stack_value literal) && Rows.shape_of literal = Some `Lost);
        check "PROBE-04 (the symbolic arm is stack)"
          (Rows.is_stack_value (Ws.stack_word_i64 0L));
        check "PROBE-04 (plain frame-shaped integers are not stack)"
          (not (Rows.is_stack_value entry) && not (Rows.is_stack_value below));
        check "PROBE-04 (the dead-path bottom is stack for the buckets)"
          (Rows.is_stack_value (Ws.bottom 64));
        check "PROBE-04 (the dead-path bottom carries no shape)"
          (Rows.shape_of (Ws.bottom 64) = None));
  ]

let () = run "probe" tests
