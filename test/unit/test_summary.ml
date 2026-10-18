(* Summary pins: what a solved sub publishes to its callers.  One
   Alcotest group per pin; each pin solves its own fixture through the
   production fixpoint. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

module S = Hike.Summary

let abi = Hike_abi.x86_64_sysv
let rax = int_ret 0
let rcx = int_param 3
let rsp = sp

(* The [ret] instruction's pop, which precedes the canonical return. *)
let pop () = Def.create rsp Bil.(var rsp + int (Word.of_int64 ~width:64 8L))

let id (v : var) : int = Core.Set.min_elt_exn (Cbat_var_id.intern_set (Var.Set.singleton v))

let tail_to (callee : tid) : tid -> jmp term =
 fun _ -> Jmp.create (Call (Call.create ~target:(Label.direct callee) ()))

let summarize ?(callee = fun _ -> None) (sub : sub term) : S.t =
  let envs, sub', block_addrs =
    produce ~synth:Hike.Synth.empty (x86_target ()) (Program.create ~subs:[ sub ] ()) sub in
  S.of_solved ~abi ~synth:Hike.Synth.empty
    ~callee ~slot:(fun _ -> None) ~lookup:(fun _ -> None)
    ~foreign_slots:Core.Int64.Set.empty ~block_addrs ~envs sub'

let writes (s : S.t) (v : var) : bool =
  match s.written with Some w -> Core.Set.mem w (id v) | None -> true

let summary_of ?(written = []) returns : S.t =
  { S.written = Some (Cbat_var_id.intern_set (Var.Set.of_list written)); returns }

let tests : unit Alcotest.test list =
  [
    pin "SUM-01" "a leaf's return comes back and it writes only its own registers"
      (fun () ->
        let sub, _ =
          sub_of "leaf"
            [ ([ Def.create rax (Bil.int (Word.of_int64 ~width:64 1L)) ],
               [ (1, mk_goto) ]);
              ([ pop () ], [ (0, mk_ret) ]) ] in
        let s = summarize sub in
        check "SUM-01.returns" s.returns;
        check "SUM-01.rax" (writes s rax);
        check "SUM-01.rcx" (not (writes s rcx)));

    pin "SUM-02" "a tail call comes back iff the callee does" (fun () ->
        let callee = Tid.create () in
        let sub, _ = sub_of "tail" [ ([], [ (0, tail_to callee) ]) ] in
        check "SUM-02.returning"
          (summarize ~callee:(fun _ -> Some (summary_of true)) sub).returns;
        check "SUM-02.noreturn"
          (not (summarize ~callee:(fun _ -> Some (summary_of false)) sub).returns));

    pin "SUM-03" "a call joins the callee's writes; an unknown callee writes anything"
      (fun () ->
        let callee = Tid.create () in
        let sub, _ =
          sub_of "caller"
            [ ([], [ (1, fun t -> mk_call_jmp t callee) ]);
              ([ pop () ], [ (0, mk_ret) ]) ] in
        let known =
          summarize ~callee:(fun _ -> Some (summary_of ~written:[ rcx ] true)) sub in
        check "SUM-03.joined" (known.written <> None && writes known rcx);
        check "SUM-03.unknown" ((summarize sub).written = None));

    pin "SUM-04" "an unresolved indirect jump is unknown" (fun () ->
        let sub, _ =
          sub_of "dispatch"
            [ ([], [ (0, fun _ -> Jmp.create (Goto (Indirect (Bil.var rax)))) ]) ] in
        let s = summarize sub in
        check "SUM-04" (s.written = None && s.returns));

    pin "SUM-05" "a trap writes anything and is not an exit" (fun () ->
        let callee = Tid.create () in
        let sub, _ =
          sub_of "trap"
            [ ([], [ (1, fun t -> Jmp.create (Int (0x80, t))) ]);
              ([], [ (0, tail_to callee) ]) ] in
        let s = summarize ~callee:(fun _ -> Some (summary_of false)) sub in
        check "SUM-05" (s.written = None && not s.returns));

    pin "SUM-06" "an exit the solve proved unreachable does not count" (fun () ->
        let callee = Tid.create () in
        let sub, _ =
          sub_of "dead"
            [ ([ Def.create rax (Bil.int (Word.of_int64 ~width:64 0L)) ],
               [ (1, fun t -> mk_jmp_to t Bil.(var rax = int (Word.of_int64 ~width:64 1L)));
                 (2, mk_goto) ]);
              ([], [ (0, fun _ -> Jmp.create (Goto (Indirect (Bil.var rcx)))) ]);
              ([], [ (0, tail_to callee) ]) ] in
        let s = summarize ~callee:(fun _ -> Some (summary_of false)) sub in
        check "SUM-06" (s.written <> None && not s.returns));

    pin "SUM-07" "a return whose RSP is not entry + word draws the diagnostic"
      (fun () ->
        let restored, _ = sub_of "restored" [ ([ pop () ], [ (0, mk_ret) ]) ] in
        let moved, _ = sub_of "moved" [ ([], [ (0, mk_ret) ]) ] in
        let message = "RSP at a return is not entry + word" in
        check "SUM-07.quiet"
          (not (contains_substring
                  (capture_stderr (fun () -> ignore (summarize restored))) message));
        check "SUM-07.diag"
          (contains_substring
             (capture_stderr (fun () -> ignore (summarize moved))) message));
  ]

let () = run "summary" tests
