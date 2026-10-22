(* In-solve indirect-call materialization pins: the worklist enumerates a
   normal call's target set from the source post-state, validates every
   word atomically, reuses/solves the callee summaries, and VSA installs
   one guarded direct call per target.  The caller continuation is the
   original return label; a complete unconditional set ends in a trap.

   CALL-6 is synthetic: the x86 decoder never produces a conditional
   call, so the fixture drives the VSA install seam directly. *)

open Bap.Std
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

module D = Cbat_vsa.Dispatch

let raw_addr a = Bil.Int (Word.of_int64 ~width:64 a)

let w (n : int64) : Cbat_word.t = Cbat_word.of_int64 ~width:64 n
let wexp (n : int64) : exp = Bil.Int (Cbat_word.to_word (w n))
let and_ (a : exp) (b : exp) : exp = Bil.BinOp (Bil.AND, a, b)

(* lea rax,[rip+3]; call rax; ret; mov eax,42; ret *)
let singleton_code =
  "\x48\x8d\x05\x03\x00\x00\x00\xff\xd0\xc3\xb8\x2a\x00\x00\x00\xc3"

(* test edi,edi; select table index; lea rdx,table; movsxd rax,[rdx+rcx*4];
   add rax,rdx; call rax; mov eax,1; ret; callee1; callee2 *)
let table_code =
  "\x85\xff\x74\x04\x31\xc9\xeb\x05\xb9\x01\x00\x00\x00\x48\x8d\x15\x74\
   \x0f\x00\x00\x48\x63\x04\x8a\x48\x01\xd0\xff\xd0\xb8\x01\x00\x00\x00\
   \xc3\xb8\x02\x00\x00\x00\xc3\xb8\x03\x00\x00\x00\xc3"

(* Deltas from the 0x401000 table to 0x40009b and 0x4000a1. *)
let table_data = "\x9b\xf0\xff\xff\xa1\xf0\xff\xff"

(* One already-known code target, one non-code word: the whole set must
   be rejected and the valid word must not become an arm. *)
let atomic_data = "\x78\xf0\xff\xff\x00\xf0\x0f\x00"

(* call f; lea rax,[rip+3]; call rax; ret; f: mov eax,2; ret *)
let final_code =
  "\xe8\x0a\x00\x00\x00\x48\x8d\x05\x03\x00\x00\x00\xff\xd0\xc3\xb8\x02\
   \x00\x00\x00\xc3"

let at (prog : program term) (a : int64) : sub term option =
  Term.enum sub_t prog
  |> Seq.find ~f:(fun s ->
      Base.Option.equal Addr.equal (Term.get_attr s address)
        (Some (Addr.of_int64 a)))

let subs_at (prog : program term) (a : int64) : sub term list =
  Term.enum sub_t prog
  |> Seq.filter ~f:(fun s ->
      Base.Option.equal Addr.equal (Term.get_attr s address)
        (Some (Addr.of_int64 a)))
  |> Seq.to_list

let blk_at (sub : sub term) (a : int64) : blk term option =
  Term.enum blk_t sub
  |> Seq.find ~f:(fun b ->
      Base.Option.equal Addr.equal (Term.get_attr b address)
        (Some (Addr.of_int64 a)))

let blk_tid sub a = Term.tid (Base.Option.value_exn (blk_at sub a))
let sub_tid prog a = Term.tid (Base.Option.value_exn (at prog a))

let jmps (b : blk term) : jmp term list = Term.enum jmp_t b |> Seq.to_list

let calls (b : blk term) : Call.t list =
  jmps b
  |> Base.List.filter_map ~f:(fun j ->
      match Jmp.kind j with Call c -> Some c | _ -> None)

let goto_tid (j : jmp term) : tid option =
  match Jmp.kind j with
  | Goto (Direct t) -> Some t
  | _ -> None

let call_target (c : Call.t) : tid option =
  match Call.target c with Direct t -> Some t | Indirect _ -> None

let call_return (c : Call.t) : tid option =
  match Call.return c with
  | Some (Direct t) -> Some t
  | Some (Indirect _) | None -> None

let is_indirect_call (j : jmp term) : bool =
  match Jmp.kind j with
  | Call c -> (match Call.target c with Indirect _ -> true | Direct _ -> false)
  | _ -> false

(* A trap is a normal block whose one jmp is [Int]. *)
let trap_tid (sub : sub term) (j : jmp term) : tid option =
  match goto_tid j with
  | None -> None
  | Some t -> (
    match Term.find blk_t sub t with
    | Some b -> (
      match jmps b with
      | [ i ] -> (match Jmp.kind i with Int _ -> Some t | _ -> None)
      | _ -> None)
    | None -> None)

let env_live (result : Hike.Drive.result) (b : blk term) : bool =
  match Core.Map.find result.Hike.Drive.facts.Hike.Kb.envs (Term.tid b) with
  | Some (pre, _) -> not (Cbat_vsa.AI.equal pre Cbat_vsa.AI.bottom)
  | None -> false

let drive ?data code = with_binary ?data code (fun p -> Hike.Drive.run p)

(* The synthetic VSA seam for CALL-6. *)
let solve_sub ?materialize_transfer (sub : sub term) =
  Vsa.static_graph_vsa ~abi:sysv
    ~synth:(ref Hike.Synth.empty)
    ~def_reads:(fun d -> Sm.reads (`Def d))
    ~def_writes:(fun d -> Sm.writes (`Def d))
    ~phi_reads:(fun p -> Sm.reads (`Phi p))
    ~phi_writes:(fun p -> Sm.writes (`Phi p))
    ~jmp_reads:(fun j ->
      Core.Set.union (Sm.reads (`Jmp j)) (Sm.writes (`Jmp j)))
    ?materialize_transfer sub
    (Vsa.init_sol ~abi:sysv ~entry:(anchored_entry ()) sub)

let tests : unit Alcotest.test list =
  [
    (* The singleton call becomes one direct arm returning to the original
       continuation; the complete set adds the no-match trap. *)
    pin "CALL-1" "a singleton indirect call becomes one direct call arm"
      (fun () ->
        let result = drive singleton_code in
        let sub = Base.Option.value_exn (at result.program 0x400078L) in
        let src = Base.Option.value_exn (blk_at sub 0x400078L) in
        let target = sub_tid result.program 0x400082L in
        let cont = blk_tid sub 0x400081L in
        let cs =
          calls src
          |> Base.List.filter ~f:(fun c -> Option.is_some (call_target c))
        in
        check "CALL-1 one call arm" (List.length cs = 1);
        check "CALL-1 direct target"
          (match cs with
           | [ c ] -> Option.equal Tid.equal (call_target c) (Some target)
           | _ -> false);
        check "CALL-1 original continuation"
          (match cs with
           | [ c ] -> Option.equal Tid.equal (call_return c) (Some cont)
           | _ -> false);
        check "CALL-1 indirect fallback retained"
          (List.exists is_indirect_call (jmps src)));

    (* Ordered guarded arms, every arm returning to the same continuation,
       with the explicit no-match trap after them. *)
    pin "CALL-2" "a multi-target call becomes ordered guarded direct arms"
      (fun () ->
        let result = drive ~data:table_data table_code in
        let sub = Base.Option.value_exn (at result.program 0x400078L) in
        let src = Base.Option.value_exn (blk_at sub 0x400085L) in
        let t1 = sub_tid result.program 0x40009BL in
        let t2 = sub_tid result.program 0x4000A1L in
        let cont = blk_tid sub 0x400095L in
        let cs =
          calls src
          |> Base.List.filter ~f:(fun c -> Option.is_some (call_target c))
        in
        check "CALL-2 two arms"
          (Base.List.equal Tid.equal
             (Base.List.filter_map cs ~f:call_target) [ t1; t2 ]);
        check "CALL-2 same continuation"
          (Base.List.for_all cs ~f:(fun c ->
               Option.equal Tid.equal (call_return c) (Some cont)));
        let js = jmps src in
        check "CALL-2 indirect fallback after the arms"
          (match List.rev js with
           | last :: _ -> is_indirect_call last
           | [] -> false);
        check "CALL-2 both targets solved"
          (match (at result.program 0x40009BL, at result.program 0x4000A1L) with
           | Some s1, Some s2 ->
             env_live result (Base.Option.value_exn (blk_at s1 0x40009BL))
             && env_live result (Base.Option.value_exn (blk_at s2 0x4000A1L))
           | _ -> false));

    (* A callee already published by the direct call is read again, not
       revisited: its address occurs once in the program. *)
    pin "CALL-3" "an already-Final callee is reused, not re-solved"
      (fun () ->
        let result = drive final_code in
        let target = 0x400087L in
        check "CALL-3 one solved function"
          (List.length (subs_at result.program target) = 1);
        let sub = Base.Option.value_exn (at result.program 0x400078L) in
        let src = Base.Option.value_exn (blk_at sub 0x40007DL) in
        let target_tid = sub_tid result.program target in
        check "CALL-3 the direct call arm names the final callee"
          (Base.List.exists (calls src) ~f:(fun c ->
               Option.equal Tid.equal (call_target c) (Some target_tid))));

    (* A code address with no entry yet is discovered, added as a root and
       solved at the call site. *)
    pin "CALL-4" "a new concrete code callee is discovered and solved at the call"
      (fun () ->
        let result = drive singleton_code in
        check "CALL-4 target function"
          (Base.Option.is_some (at result.program 0x400082L));
        let target = Base.Option.value_exn (at result.program 0x400082L) in
        check "CALL-4 target block solved"
          (env_live result (Base.Option.value_exn (blk_at target 0x400082L))));

    (* One non-code word rejects the whole set: the valid word gets no arm
       and the call stays indirect. *)
    pin "CALL-5" "a non-code target fails the whole set atomically"
      (fun () ->
        let result = drive ~data:atomic_data table_code in
        let sub = Base.Option.value_exn (at result.program 0x400078L) in
        let src = Base.Option.value_exn (blk_at sub 0x400085L) in
        check "CALL-5 no new callee sub"
          (Base.Option.is_none (at result.program 0x40009BL)
          && List.length (subs_at result.program 0x400078L) = 1);
        check "CALL-5 the call stays indirect"
          (List.exists is_indirect_call (jmps src));
        check "CALL-5 no call arm to the valid word"
          (not
             (List.exists (fun c ->
                  match call_target c with
                  | Some t -> Tid.equal t (blk_tid sub 0x400078L)
                  | None -> false)
                (calls src))));

    (* The original condition is conjoined with every target test.  The
       false edge is the source block's term-order follower; a true no-match
       reaches the explicit trap block. *)
    pin "CALL-6" "a conditional call conjoins its condition, keeps false, traps"
      (fun () ->
        let t = v64 "ccall_t" and flag = v1 "ccall_c" in
        let sub, tids =
          raw_sub_of "ccall"
            [ [ Def.create t (Bil.Var (v64 "ccall_in")) ],
              [ (2, fun ret ->
                    Jmp.create ~cond:(Bil.Var flag)
                      (Call
                         (Call.create ~return:(Direct ret)
                            ~target:(Indirect (Bil.Var t)) ()))) ];
              [], [ (3, mk_goto) ];
              [], [ (3, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let t1 = Tid.create () and t2 = Tid.create () in
        let targets = [ (w 0x400010L, t1); (w 0x400020L, t2) ] in
        let mat_transfer ~state ~source:_ ~blk:_ ~jmp:_ ~env:_ =
          Some { D.base = None; targets; sub = Vsa.state_sub state; module_addr = raw_addr }
        in
        let sol, state = solve_sub ~materialize_transfer:mat_transfer sub in
        let sub' = Vsa.state_sub state in
        let src = Term.find_exn blk_t sub' tids.(0) in
        let js = jmps src in
        let cond w = and_ (Bil.Var flag) (Bil.BinOp (Bil.EQ, Bil.Var t, wexp w)) in
        check "CALL-6 two guarded call arms"
          (match js with
           | arm1 :: arm2 :: _ ->
             (match (Jmp.kind arm1, Jmp.kind arm2) with
              | Call c1, Call c2 ->
                Option.equal Tid.equal (call_target c1) (Some t1)
                && Option.equal Tid.equal (call_target c2) (Some t2)
                && Option.equal Tid.equal (call_return c1) (Some tids.(2))
                && Option.equal Tid.equal (call_return c2) (Some tids.(2))
                && Exp.equal (Jmp.cond arm1) (cond 0x400010L)
                && Exp.equal (Jmp.cond arm2) (cond 0x400020L)
              | _ -> false)
           | _ -> false);
        let trap_goto, false_goto =
          match js with
          | _ :: _ :: trap :: false_ :: _ -> (Some trap, Some false_)
          | _ -> (None, None)
        in
        check "CALL-6 trap guard keeps the original condition"
          (match trap_goto with
           | Some j ->
             Exp.equal (Jmp.cond j) (Bil.Var flag)
             && Option.is_some (trap_tid sub' j)
           | None -> false);
        check "CALL-6 false edge is the term-order follower"
          (match false_goto with
           | Some j -> Option.equal Tid.equal (goto_tid j) (Some tids.(1))
           | None -> false);
        check "CALL-6 trap block is installed"
          (match trap_goto with
           | Some j -> (
             match goto_tid j with
             | Some tr -> (
               match Term.find blk_t sub' tr with
               | Some b -> (
                 match jmps b with
                 | [ i ] -> (match Jmp.kind i with Int _ -> true | _ -> false)
                 | _ -> false)
               | None -> false)
             | None -> false)
           | None -> false);
        check "CALL-6 false continuation is bottom"
          (AI.equal (Graphlib.Std.Solution.get sol tids.(1)) AI.bottom);
        check "CALL-6 return continuation delivered"
          (not (AI.equal (Graphlib.Std.Solution.get sol tids.(2)) AI.bottom)));
  ]

let () = run "dispatch_call" tests
