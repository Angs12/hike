(* The SSA property verifier runs only in the vsa-debug profile. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

let target = x86_target ()
let synth = Hike.Synth.empty

let verify what sub = Hike_test.Verify_ssa.sub ~synth ~target ~what sub

let tests : unit Alcotest.test list =
  [
    pin "VER-01"
      "the post-promotion split is an admissible SSA sub"
      (fun () ->
        let callee, _ = raw_sub_of "ver_callee" [ [], [ (0, mk_ret) ] ] in
        let caller, _ = raw_sub_of "ver_caller"
            [ [], [ (1, fun t -> mk_call_jmp t (Term.tid callee)) ];
              [ Def.create (v64 "ver_use") (Bil.Var (int_ret 0)) ],
              [ (0, mk_ret) ] ]
        in
        let prog =
          Program.create ~subs:[ callee; caller ] ()
          |> Hike.Ssa.ssa_program ~synth ~target
          |> Hike.Split_blocks.normalize ~synth ~target
        in
        Term.enum sub_t prog |> Seq.iter ~f:(verify "VER-01"));

    pin "VER-02"
      "a structural arming result is rejected until the SSA commit"
      (fun () ->
        let callee, _ = raw_sub_of "ver2_callee" [ [], [ (0, mk_ret) ] ] in
        let caller, tids = raw_sub_of "ver2_caller"
            [ [], [ (1, mk_goto) ];
              [ Def.create (v64 "ver2_use") (Bil.Var (int_ret 0)) ],
              [ (0, mk_ret) ] ]
        in
        let ssa =
          Program.create ~subs:[ callee; caller ] ()
          |> Hike.Ssa.ssa_program ~synth ~target
          |> Term.enum sub_t
          |> Seq.find ~f:(fun s -> Tid.equal (Term.tid s) (Term.tid caller))
          |> Base.Option.value_exn
        in
        let call =
          Jmp.create ~cond:(Bil.Int (Word.one 1))
            (Call
               (Call.create ~return:(Direct tids.(1))
                  ~target:(Direct (Term.tid callee)) ()))
        in
        let edit =
          Hike.Ssa.Edit.start ~synth ~target
            ~callee:(fun t ->
              Base.Option.some_if (Tid.equal t (Term.tid callee)) callee)
            ssa
        in
        let bare =
          Hike.Ssa.Edit.view
            (Hike.Ssa.Edit.append_jmp edit tids.(0) call)
        in
        let rejected =
          try
            verify "VER-02" bare;
            false
          with Failure _ -> true
        in
        check "VER-02" rejected);
  ]

let () = run "ssa_verify" tests
