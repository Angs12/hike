(* Pins for the noreturn fact: the base runtime contract, the lifted-sub
   fixpoint, and the completion's consumption (a call to a noreturn sub
   carries no return continuation).  One Alcotest group per pin. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Fixtures

let extern_sub (name : string) : sub term =
  Sub.Builder.result (Sub.Builder.create ~name ())

(* One block whose only jump is a call to [callee] with a return to
   itself (the continuation label is irrelevant to classification). *)
let call_once (name : string) (callee : tid) : sub term * tid array =
  sub_of name
    [ [],
      [ (0,
         fun t ->
           Jmp.create
             (Call
                (Call.create ~target:(Direct callee) ~return:(Direct t) ())))
      ] ]

let first_call (sub : sub term) : Call.t =
  Term.enum blk_t sub
  |> Seq.concat_map ~f:(Term.enum jmp_t)
  |> Seq.find_map ~f:(fun j -> match Jmp.kind j with Call c -> Some c | _ -> None)
  |> Base.Option.value_exn

let tests : unit Alcotest.test list =
  [
    pin "NR-01"
      "the base fact is the runtime contract's names: longjmp is noreturn, puts is not"
      (fun () ->
        let lj = extern_sub "longjmp" in
        let puts = extern_sub "puts" in
        let prog = Program.create ~subs:[ lj; puts ] () in
        let nr = Hike_noreturn.classify ~target:Theory.Target.unknown prog in
        check "NR-01"
          (Core.Set.mem nr (Term.tid lj)
          && not (Core.Set.mem nr (Term.tid puts))));

    pin "NR-02"
      "the lifted-sub fixpoint: an only-exit call to a noreturn callee classifies; a return does not"
      (fun () ->
        let lj = extern_sub "longjmp" in
        let wrapper, _ = call_once "wrapper" (Term.tid lj) in
        let ret, _ = sub_of "returns" [ [], [ (0, mk_ret) ] ] in
        let prog = Program.create ~subs:[ lj; wrapper; ret ] () in
        let nr = Hike_noreturn.classify ~target:Theory.Target.unknown prog in
        check "NR-02"
          (Core.Set.mem nr (Term.tid wrapper)
          && not (Core.Set.mem nr (Term.tid ret))));

    pin "NR-03"
      "the completion's consumption drops the return continuation of a call to a noreturn sub"
      (fun () ->
        let lj = extern_sub "longjmp" in
        let wrapper, _ = call_once "wrapper" (Term.tid lj) in
        let nr = Core.Set.singleton (module Tid) (Term.tid lj) in
        let wrapper' =
          Hike.Cfg_complete.clear_noreturn_returns ~noreturn:nr wrapper
        in
        let c = first_call wrapper' in
        check "NR-03"
          (Base.Option.is_none (Call.return c)
          && Option.is_some (Call.return (first_call wrapper))));
  ]

let () = run "noreturn" tests
