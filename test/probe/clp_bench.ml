(* Prints the CLP composite hot core's per-op wall + allocation bill;
   the rows themselves live in Clp_bench_rows. *)
open Probe_common

let () =
  init ();
  Printf.printf
    "clp_bench — per-op wall + minor-word bill, two consecutive loops\n%!";
  let rows = Clp_bench_rows.rows () in
  Clp_bench_rows.print_table rows;
  Printf.printf "\nsink=%d\n%!" !Clp_bench_rows.sink
