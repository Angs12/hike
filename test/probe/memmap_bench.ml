(* memmap_bench: per-op wall + minor-word bill for ticket 06's sites —
   find' (the per-query Seq.to_list), op_at (the per-byte cell op on a
   join), try_assemble_cells (the sort/map/reduce of an interior read),
   and the FinSet Cartesian fold.  Same counter as clp_bench:
   [Gc.minor_words] is exact and two consecutive loops must agree.

   Usage: memmap_bench.exe *)

open Bap.Std
open Probe_common

module Ws = Cbat_clp_set_composite
module Clp = Cbat_clp
module Mem = Cbat_vsa.Mem
module Fs = Cbat_fin_set
module CW = Cbat_word

let now = Unix.gettimeofday

let sink = ref 0
let keep (i : int) : unit = sink := !sink lxor i

type row = Probe_common.bench_row

let measure = Probe_common.bench_measure

let print_table = Probe_common.bench_print_table

let w32 = CW.of_int ~width:32

let () =
  init ();
  Printf.printf
    "memmap_bench — ticket 06 sites, wall + minor words, two consecutive loops\n%!";
  let idx = { Mem.addr_width = 32; Mem.addressable_width = 8 } in
  let key_range lo hi =
    match Mem.Key.of_wordset (Ws.of_clp (Clp.interval ~width:32 (w32 lo) (w32 hi))) with
    | Some k -> k
    | None -> failwith "key_range"
  in
  let point c =
    match Mem.Key.of_wordset (Ws.singleton (w32 c)) with
    | Some k -> k
    | None -> failwith "point"
  in
  let cell v = Mem.Val.create (Ws.singleton (w32 v)) LittleEndian in
  let data_at m c =
    Ws.bitwidth (Mem.Val.data (Mem.find (32, LittleEndian) m (point c)))
  in
  let base_m =
    Mem.meet_add (Mem.top idx) ~key:(key_range 0x1000 0x1100) ~data:(cell 7)
  in
  let s1 = Fs.of_list ~width:32 (List.init 10 (fun i -> w32 (i * 3))) in
  let s2 = Fs.of_list ~width:32 (List.init 10 (fun i -> w32 (i * 7 + 1))) in
  let rows =
    [
      (* find' + the interior read (the try_assemble_cells path). *)
      measure ~name:"memmap.find interior (assemble)" ~n:100_000 (fun () ->
          keep (data_at base_m 0x1080));
      (* the aligned read (the stride-aware fast path). *)
      measure ~name:"memmap.find aligned" ~n:100_000 (fun () ->
          keep (data_at base_m 0x1000));
      (* an absent key (the empty-intersection path). *)
      measure ~name:"memmap.find absent" ~n:100_000 (fun () ->
          keep (data_at base_m 0x50));
      (* a join over an existing cell: the per-byte cell op (op_at). *)
      measure ~name:"memmap.join_add overlap" ~n:50_000 (fun () ->
          keep
            (data_at
               (Mem.join_add base_m ~key:(key_range 0x1080 0x1200)
                  ~data:(cell 9))
               0x1090));
      (* a meet into the same key (the gaps path). *)
      measure ~name:"memmap.meet_add ranged" ~n:50_000 (fun () ->
          keep
            (data_at
               (Mem.meet_add base_m ~key:(key_range 0x1040 0x10c0)
                  ~data:(cell 3))
               0x1050));
      (* the FinSet Cartesian fold: two 10-element sets, 100 WSet.adds. *)
      measure ~name:"finset.logand(10,10) cartesian" ~n:50_000 (fun () ->
          keep (CW.bitwidth (Fs.cardinality (Fs.logand s1 s2))));
      measure ~name:"finset.logxor(10,10) cartesian" ~n:50_000 (fun () ->
          keep (CW.bitwidth (Fs.cardinality (Fs.logxor s1 s2))));
    ]
  in
  print_table rows;
  Printf.printf "\nsink=%d\n%!" !sink
