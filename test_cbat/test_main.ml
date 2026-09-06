(* Test entry point: theme modules in file order, then the battery oracle line. *)
open Test_common

let () =
  Test_domains.run_base ();
  Test_seed.run ();
  Test_domains.run_policy ();
  Test_vsa.run ();
  Test_backward.run ();
  Test_domains.run_agreement ();
  Test_regression.run_creg ();
  Test_regression.run_remediation ();
  Test_properties.run_soundness ();
  Test_regression.run_regions ();
  Test_properties.run_roundtrip ();
  Test_properties.run_landmarks ();
  Test_properties.run_chains ();
  Test_dce.run ();
  Test_bil2llvm.run ();
  print_endline
    (if !failures = 0 then "ALL CBAT TESTS PASSED" else Printf.sprintf "%d FAILURES" !failures);
  exit (if !failures = 0 then 0 else 1)

