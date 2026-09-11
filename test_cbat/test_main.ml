(* Test entry point: theme modules in file order, then the battery oracle line. *)
open Test_common

let () =
  (* Targets are registered only by Bap_main: without it Theory.Target has
     no declarations and every target-derived ABI fact is the unknown
     fallback (fixtures needing a real x86_64 target depend on this). *)
  ignore (Bap_main.init ~argv:[| Sys.executable_name |] () : (unit, _) result);
  Test_domains.run_base ();
  Test_seed.run ();
  Test_domains.run_policy ();
  Test_vsa.run ();
  Test_domains.run_shifts ();
  Test_backward.run ();
  Test_domains.run_agreement ();
  Test_regression.run_creg ();
  Test_regression.run_remediation ();
  Test_properties.run_soundness ();
  Test_regression.run_regions ();
  Test_domains.run_overlap ();
  Test_regression.run_t4_resolution ();
  Test_regression.run_copy_reloc ();
  Test_regression.run_fp_gpr ();
  Test_model.run ();
  Test_properties.run_roundtrip ();
  Test_properties.run_landmarks ();
  Test_properties.run_chains ();
  Test_dce.run ();
  Test_jump.run ();
  Test_bil2llvm.run ();
  print_endline
    (if !failures = 0 then "ALL CBAT TESTS PASSED" else Printf.sprintf "%d FAILURES" !failures);
  exit (if !failures = 0 then 0 else 1)

