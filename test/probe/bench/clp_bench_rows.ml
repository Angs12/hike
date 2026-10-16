(* Per-op wall time and minor-heap allocation bill for the CLP composite's
   hot core.  Reporting probe: prints a table and asserts nothing; the
   allocation tripwire is a separate (test).

   Corpus-shaped operands: 64-bit flag/mask patterns, stack-offset strides,
   small ints, signed values, and 128-bit Big words.  The measured bill is
   the exact minor-word counter [Gc.minor_words] — [Gc.quick_stat]'s
   [minor_words] on OCaml 5.3 advances only at minor GCs, so it cannot
   answer a per-op count.  The bill is independent of the GC configuration;
   two consecutive loops must agree on it.

   [lift_binop]/[lift_unop] and [mkzw] are mli-internal, so their rows run
   the public entries that reach them: the composite ops and [of_word]/
   [of_int64]/[of_int].  [create] is [Cbat_clp_core]'s, re-exported by the
   [Cbat_clp] seam the production call sites use.  The bit-op rows run the
   progression-level [Cbat_clp_arith] rules the pieces call.

   Usage: rows shared by clp_bench.exe (the report) and clp_tripwire
   (the allocation tripwire test). *)

open Bap.Std
open Probe_common

module CW = Cbat_word
module Clp = Cbat_clp
module A = Cbat_clp_arith
module Comp = Cbat_clp_set_composite

type row = Probe_common.bench_row

(* Two consecutive loops, each preceded by a warmup; [w_a]/[w_b] are the
   minor-word deltas divided by the iteration count. *)
let measure = Probe_common.bench_measure

(* Keeps an op result alive without measuring the projection. *)
let sink = ref 0
let keep (i : int) : unit = sink := !sink lxor i

let print_table = Probe_common.bench_print_table

(* ---- Cbat_word ----------------------------------------------------- *)

let word_bench () : row list =
  let w = 64 in
  let mask = CW.of_int ~width:w 0xff in
  let addr = CW.of_int ~width:w 0x7fff_ffff_0000 in
  let small = CW.of_int ~width:w 5 in
  let signed = CW.signed (CW.of_int ~width:w 0xffff_ffff) in
  let big = CW.of_int64 ~width:w Int64.min_int in
  let w128 =
    CW.of_word (Word.of_string "340282366920938463463374607431768211455:128")
  in
  let w128b =
    CW.of_word (Word.of_string "123456789012345678901234567890:128")
  in
  let bap64 = Word.of_int64 ~width:w (-1L) in
  let bap128 = Word.of_int64 ~width:128 (-1L) in
  [ measure ~name:"word.logand(mask,addr)" ~n:200_000 (fun () ->
        keep (CW.bitwidth (CW.logand mask addr)));
    measure ~name:"word.logand(big,big)" ~n:200_000 (fun () ->
        keep (CW.bitwidth (CW.logand big big)));
    measure ~name:"word.logand(128,128)" ~n:200_000 (fun () ->
        keep (CW.bitwidth (CW.logand w128 w128b)));
    measure ~name:"word.logor(addr,mask)" ~n:200_000 (fun () ->
        keep (CW.bitwidth (CW.logor addr mask)));
    measure ~name:"word.logxor(small,small)" ~n:200_000 (fun () ->
        keep (CW.bitwidth (CW.logxor small small)));
    measure ~name:"word.logxor(signed,big)" ~n:200_000 (fun () ->
        keep (CW.bitwidth (CW.logxor signed big)));
    measure ~name:"word.lnot(mask)" ~n:200_000 (fun () ->
        keep (CW.bitwidth (CW.lnot mask)));
    measure ~name:"word.lnot(big)" ~n:200_000 (fun () ->
        keep (CW.bitwidth (CW.lnot big)));
    measure ~name:"word.extract_exn(hi=31,addr)" ~n:200_000 (fun () ->
        keep (CW.bitwidth (CW.extract_exn ~hi:31 addr)));
    measure ~name:"word.extract_exn(hi=7,big)" ~n:200_000 (fun () ->
        keep (CW.bitwidth (CW.extract_exn ~hi:7 big)));
    measure ~name:"word.extract_exn(hi=63,128)" ~n:100_000 (fun () ->
        keep (CW.bitwidth (CW.extract_exn ~hi:63 w128)));
    measure ~name:"word.factor_2s(big)" ~n:100_000 (fun () ->
        keep (snd (CW.factor_2s big)));
    measure ~name:"word.factor_2s(mask)" ~n:100_000 (fun () ->
        keep (snd (CW.factor_2s mask)));
    measure ~name:"word.factor_2s(128)" ~n:50_000 (fun () ->
        keep (snd (CW.factor_2s w128)));
    measure ~name:"word.lead_1_bit(mask)" ~n:100_000 (fun () ->
        keep (Option.value (CW.lead_1_bit mask) ~default:(-1)));
    measure ~name:"word.lead_1_bit(big)" ~n:100_000 (fun () ->
        keep (Option.value (CW.lead_1_bit big) ~default:(-1)));
    measure ~name:"word.lead_1_bit(zero)" ~n:200_000 (fun () ->
        keep (Option.value (CW.lead_1_bit (CW.zero w)) ~default:(-1)));
    measure ~name:"word.mkzw(via of_word 64)" ~n:200_000 (fun () ->
        keep (CW.bitwidth (CW.of_word bap64)));
    measure ~name:"word.mkzw(via of_word 128)" ~n:100_000 (fun () ->
        keep (CW.bitwidth (CW.of_word bap128)));
    measure ~name:"word.mkzw(via of_int64 -1)" ~n:200_000 (fun () ->
        keep (CW.bitwidth (CW.of_int64 ~width:w (-1L))));
    measure ~name:"word.mkzw(via of_int 64 -1)" ~n:200_000 (fun () ->
        keep (CW.bitwidth (CW.of_int ~width:w (-1)))) ]

(* ---- Cbat_clp_arith / Clp.create ----------------------------------- *)

(* The step-1 progression [lo, hi]. *)
let interval_of ~(width : int) (lo : int) (hi : int) : Clp.t =
  Clp.create ~width ~step:(CW.one width)
    ~cardn:(CW.of_int ~width:(width + 1) (hi - lo + 1))
    (CW.of_int ~width lo)

let clp_bench () : row list =
  let w = 64 in
  let step8 = CW.of_int ~width:w 8 in
  let asc8 = Clp.create_ascending ~width:w ~base:step8 ~step:step8 in
  let asc8b =
    Clp.create_ascending ~width:w ~base:(CW.of_int ~width:w 16) ~step:step8
  in
  let interval = interval_of ~width:w 0x1000 0x2000 in
  let singleton = Clp.create ~width:w step8 in
  let cardn_two = CW.of_int ~width:(w + 1) 2 in
  let cardn_finite = CW.of_int ~width:(w + 1) 0x100000 in
  let cardn_wrap = CW.dom_size ~width:(w + 1) 63 in
  let w128 = 128 in
  let asc8_128 = Clp.create_ascending ~width:w128 ~base:step8 ~step:step8 in
  let interval_128 = interval_of ~width:w128 0x1000 0x2000 in
  [ measure ~name:"clp.logand(asc8,asc8b)" ~n:20_000 (fun () ->
        keep (List.length (A.logand asc8 asc8b)));
    measure ~name:"clp.logand(interval,interval)" ~n:20_000 (fun () ->
        keep (List.length (A.logand interval interval)));
    measure ~name:"clp.logand(interval,singleton)" ~n:20_000 (fun () ->
        keep (List.length (A.logand interval singleton)));
    measure ~name:"clp.logand(128,128)" ~n:10_000 (fun () ->
        keep (List.length (A.logand asc8_128 interval_128)));
    measure ~name:"clp.logor(asc8,asc8b)" ~n:20_000 (fun () ->
        keep (List.length (A.logor asc8 asc8b)));
    measure ~name:"clp.logor(interval,singleton)" ~n:20_000 (fun () ->
        keep (List.length (A.logor interval singleton)));
    measure ~name:"clp.logxor(singleton,singleton)" ~n:20_000 (fun () ->
        keep (List.length (A.logxor singleton singleton)));
    measure ~name:"clp.logxor(asc8,asc8b)" ~n:20_000 (fun () ->
        keep (List.length (A.logxor asc8 asc8b)));
    measure ~name:"clp.logxor(interval,interval)" ~n:20_000 (fun () ->
        keep (List.length (A.logxor interval interval)));
    measure ~name:"clp.logxor(128,128)" ~n:10_000 (fun () ->
        keep (List.length (A.logxor asc8_128 interval_128)));
    measure ~name:"clp.create(singleton)" ~n:200_000 (fun () ->
        keep (Clp.bitwidth (Clp.create ~width:w step8)));
    measure ~name:"clp.create(two,step8)" ~n:100_000 (fun () ->
        keep (Clp.bitwidth (Clp.create ~width:w ~step:step8 ~cardn:cardn_two step8)));
    measure ~name:"clp.create(finite,step8,2^20)" ~n:50_000 (fun () ->
        keep
          (Clp.bitwidth
             (Clp.create ~width:w ~step:step8 ~cardn:cardn_finite step8)));
    measure ~name:"clp.create(wrap,step8,2^63)" ~n:50_000 (fun () ->
        keep
          (Clp.bitwidth
             (Clp.create ~width:w ~step:step8 ~cardn:cardn_wrap step8)));
    measure ~name:"clp.create(128,singleton)" ~n:100_000 (fun () ->
        keep (Clp.bitwidth (Clp.create ~width:w128 (CW.of_int ~width:w128 7))))
  ]

(* ---- Cbat_clp_set_composite ---------------------------------------- *)

let comp_bench () : row list =
  let w = 64 in
  let step8 = CW.of_int ~width:w 8 in
  let asc8 = Clp.create_ascending ~width:w ~base:step8 ~step:step8 in
  let interval =
    Clp.interval ~width:w (CW.of_int ~width:w 0x1000)
      (CW.of_int ~width:w 0x2000)
  in
  let fin_mask = Comp.singleton (CW.of_int ~width:w 0xff) in
  let fin_nib = Comp.singleton (CW.of_int ~width:w 0xf) in
  let fin_addr = Comp.singleton (CW.of_int ~width:w 0x7fff_ffff_0000) in
  let fin10 =
    Comp.of_list ~width:w (List.init 10 (fun i -> CW.of_int ~width:w (i * 8)))
  in
  let clp_big = Comp.of_clp interval in
  let clp_asc = Comp.of_clp (Clp.Pieces.of_progression asc8) in
  let stack1 = Comp.stack_word_i64 8L in
  let stack_r =
    Comp.stack_word
      (Clp.interval ~width:w (CW.of_int ~width:w 0) (CW.of_int ~width:w 0x100))
  in
  [ measure ~name:"composite.logand(clp,clp)" ~n:20_000 (fun () ->
        keep (Comp.bitwidth (Comp.logand clp_big clp_asc)));
    measure ~name:"composite.logand(fin,fin)" ~n:50_000 (fun () ->
        keep (Comp.bitwidth (Comp.logand fin10 fin10)));
    measure ~name:"composite.logand(clp,fin)" ~n:50_000 (fun () ->
        keep (Comp.bitwidth (Comp.logand clp_big fin10)));
    measure ~name:"composite.logand(stack,nib)" ~n:50_000 (fun () ->
        keep (Comp.bitwidth (Comp.logand stack1 fin_nib)));
    measure ~name:"composite.logand(stack,mask)" ~n:50_000 (fun () ->
        keep (Comp.bitwidth (Comp.logand stack1 fin_mask)));
    measure ~name:"composite.logand(stack,stack)" ~n:50_000 (fun () ->
        keep (Comp.bitwidth (Comp.logand stack_r stack_r)));
    measure ~name:"composite.logor(clp,clp)" ~n:20_000 (fun () ->
        keep (Comp.bitwidth (Comp.logor clp_big clp_asc)));
    measure ~name:"composite.logor(fin,fin)" ~n:50_000 (fun () ->
        keep (Comp.bitwidth (Comp.logor fin_addr fin_mask)));
    measure ~name:"composite.logxor(clp,clp)" ~n:20_000 (fun () ->
        keep (Comp.bitwidth (Comp.logxor clp_big clp_asc)));
    measure ~name:"composite.logxor(fin,fin)" ~n:50_000 (fun () ->
        keep (Comp.bitwidth (Comp.logxor fin_addr fin_mask)));
    measure ~name:"composite.logxor(stack,fin)" ~n:50_000 (fun () ->
        keep (Comp.bitwidth (Comp.logxor stack1 fin_mask)));
    measure ~name:"composite.lnot(clp)" ~n:20_000 (fun () ->
        keep (Comp.bitwidth (Comp.lnot clp_big)));
    measure ~name:"composite.lnot(fin)" ~n:50_000 (fun () ->
        keep (Comp.bitwidth (Comp.lnot fin10)));
    measure ~name:"composite.lnot(stack)" ~n:50_000 (fun () ->
        keep (Comp.bitwidth (Comp.lnot stack1))) ]

let rows () : row list = word_bench () @ clp_bench () @ comp_bench ()
