(* In-solve jump materialization pins: the worklist callback enumerates a
   jump table during the solve, validates every target atomically, lifts
   missing case blocks and discovers function entries.  The hand-built
   binaries below place a table in .rodata; the code addresses are the
   harness's fixed 0x400078 base.

   JUMP-3 and JUMP-5 cannot be produced by the x86 decoder: an indirect
   Goto there is never conditional, and WordSet.enumerate is a set.  They
   are pinned at the Cbat_dispatch/VSA install seam the worklist feeds
   (the duplicate arm rule is also DISP-05, condition conjunction is also
   INST-07). *)

open Bap.Std
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

module D = Cbat_vsa.Dispatch

let raw_addr a = Bil.Int (Word.of_int64 ~width:64 a)
module Ws = Cbat_vsa.WordSet

let w (n : int64) : Cbat_word.t = Cbat_word.of_int64 ~width:64 n
let wexp (n : int64) : exp = Bil.Int (Cbat_word.to_word (w n))
let iexp (n : int64) : exp = Bil.Int (Word.of_int64 ~width:64 n)
let eq (a : exp) (b : exp) : exp = Bil.BinOp (Bil.EQ, a, b)
let minus (a : exp) (b : exp) : exp = Bil.BinOp (Bil.MINUS, a, b)
let and_ (a : exp) (b : exp) : exp = Bil.BinOp (Bil.AND, a, b)

(* eax := 7; branch index 0/1; relative table in .rodata; jmp rax. *)
let rel_code =
  "\x85\xff\x74\x04\x31\xc9\xeb\x05\xb9\x01\x00\x00\x00\x48\x8d\x15\x74\
   \x0f\x00\x00\x48\x63\x04\x8a\x48\x01\xd0\xff\xe0\xb8\x01\x00\x00\x00\
   \xc3\xb8\x02\x00\x00\x00\xc3"

(* delta case0 - table, delta case1 - table; table at 0x401000. *)
let rel_data = "\x95\xf0\xff\xff\x9b\xf0\xff\xff"

(* The absolute-pointer table: mov rax,[rdx+rcx*8]; jmp rax. *)
let abs_code =
  "\x85\xff\x74\x04\x31\xc9\xeb\x05\xb9\x01\x00\x00\x00\x48\x8d\x15\x74\
   \x0f\x00\x00\x48\x8b\x04\xca\xff\xe0\xb8\x01\x00\x00\x00\xc3\xb8\x02\
   \x00\x00\x00\xc3"

let abs_data =
  "\x95\x00\x40\x00\x00\x00\x00\x00\x9b\x00\x40\x00\x00\x00\x00\x00"

(* One code target and one non-code word. *)
let atomic_data =
  "\x95\x00\x40\x00\x00\x00\x00\x00\x00\x00\x50\x00\x00\x00\x00\x00"

(* call other_func; index 0/1; relative table naming case0 and other_func. *)
let entry_code =
  "\xe8\x23\x00\x00\x00\x85\xff\x74\x04\x31\xc9\xeb\x05\xb9\x01\x00\x00\
   \x00\x48\x8d\x15\x6f\x0f\x00\x00\x48\x63\x04\x8a\x48\x01\xd0\xff\xe0\
   \xb8\x01\x00\x00\x00\xc3\xb8\x02\x00\x00\x00\xc3"

let entry_data = "\x9a\xf0\xff\xff\xa0\xf0\xff\xff"

(* jmp rax, with rax unconstrained at the entry. *)
let top_code = "\xff\xe0"

let at (prog : program term) (a : int64) : sub term option =
  Term.enum sub_t prog
  |> Seq.find ~f:(fun s ->
      Base.Option.equal Addr.equal (Term.get_attr s address)
        (Some (Addr.of_int64 a)))

let blk_at (sub : sub term) (a : int64) : blk term option =
  Term.enum blk_t sub
  |> Seq.find ~f:(fun b ->
      Base.Option.equal Addr.equal (Term.get_attr b address)
        (Some (Addr.of_int64 a)))

let blk_tid sub a = Term.tid (Base.Option.value_exn (blk_at sub a))
let sub_tid prog a = Term.tid (Base.Option.value_exn (at prog a))

let jmps (b : blk term) : jmp term list = Term.enum jmp_t b |> Seq.to_list

let target_tid (j : jmp term) : tid option =
  match Jmp.kind j with
  | Goto (Direct t) -> Some t
  | Call c -> (match Call.target c with Direct t -> Some t | Indirect _ -> None)
  | Ret _ | Int _ | Goto (Indirect _) -> None

let is_indirect (j : jmp term) : bool =
  match Jmp.kind j with
  | Goto (Indirect _) -> true
  | Call c -> (
    match Call.target c with Indirect _ -> true | Direct _ -> false)
  | _ -> false

let is_trap_target (sub : sub term) (j : jmp term) : bool =
  match target_tid j with
  | None -> false
  | Some t -> (
    match Term.find blk_t sub t with
    | None -> false
    | Some b ->
      Term.enum jmp_t b
      |> Seq.exists ~f:(fun j ->
             match Jmp.kind j with Int _ -> true | _ -> false))

let arms (sub : sub term) (b : blk term) : jmp term list =
  jmps b
  |> Base.List.filter ~f:(fun j ->
         not (is_trap_target sub j) && not (is_indirect j))

(* The table-offset case test: [EQ (MINUS target base) delta]. *)
let offset_delta (j : jmp term) : int64 option =
  match Jmp.cond j with
  | Bil.BinOp (Bil.EQ, Bil.BinOp (Bil.MINUS, _, _), Bil.Int w) ->
    Some (Word.to_int64_exn w)
  | _ -> None

let synth_word (v : var) : int64 option =
  let prefix = "hike_synth_" in
  let name = Var.name v in
  let n = String.length prefix in
  if String.length name > n && String.sub name 0 n = prefix then
    let rest = String.sub name n (String.length name - n) in
    let hex =
      match String.index_opt rest '.' with
      | Some i -> String.sub rest 0 i
      | None -> rest
    in
    Base.Option.try_with (fun () -> Int64.of_string ("0x" ^ hex))
  else None

(* The equality case test: [EQ target word], with the word either a raw
   integer or the synthetic module address that represents it. *)
let equality_word (j : jmp term) : int64 option =
  match Jmp.cond j with
  | Bil.BinOp (Bil.EQ, _, Bil.Int w) -> Some (Word.to_int64_exn w)
  | Bil.BinOp (Bil.EQ, _, Bil.Var v) -> synth_word v
  | _ -> None

let rec has_minus (e : exp) : bool =
  match e with
  | Bil.BinOp (Bil.MINUS, _, _) -> true
  | Bil.BinOp (_, a, b) | Bil.Concat (a, b) | Bil.Let (_, a, b) ->
    has_minus a || has_minus b
  | Bil.UnOp (_, a) | Bil.Cast (_, _, a) | Bil.Extract (_, _, a) ->
    has_minus a
  | Bil.Load (m, a, _, _) -> has_minus m || has_minus a
  | Bil.Store (m, a, v, _, _) -> has_minus m || has_minus a || has_minus v
  | Bil.Ite (c, a, b) -> has_minus c || has_minus a || has_minus b
  | Bil.Var _ | Bil.Int _ | Bil.Unknown _ -> false

let env_live (result : Hike.Drive.result) (b : blk term) : bool =
  match Core.Map.find result.Hike.Drive.facts.Hike.Kb.envs (Term.tid b) with
  | Some (pre, _) -> not (Cbat_vsa.AI.equal pre Cbat_vsa.AI.bottom)
  | None -> false

let drive ?data code = with_binary ?data code (fun p -> Hike.Drive.run ~signatures:Hike.Signatures.empty p)

(* ---- the synthetic install seam (JUMP-3 / JUMP-5) ---- *)

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

let synthetic_sub name =
  let t = v64 (name ^ "_t") and flag = v1 (name ^ "_c") in
  let sub, tids =
    raw_sub_of name
      [ [ Def.create t (Bil.Var (v64 (name ^ "_in"))) ],
        [ (1, fun _ ->
              Jmp.create ~cond:(Bil.Var flag) (Goto (Indirect (Bil.Var t))));
          (3, mk_goto) ];
        [], [ (3, mk_goto) ];
        [], [ (3, mk_goto) ];
        [], [ (0, mk_ret) ] ]
  in
  (sub, tids, t, flag)

let tests : unit Alcotest.test list =
  [
    (* A non-singleton relative table becomes two ordered guarded direct
       jumps whose deltas are [target - table base]. *)
    pin "JUMP-1" "a non-singleton table becomes ordered guarded direct edges"
      (fun () ->
        let result = drive ~data:rel_data rel_code in
        let sub = Base.Option.value_exn (at result.program 0x400078L) in
        let src = Base.Option.value_exn (blk_at sub 0x400085L) in
        let arms = arms sub src in
        let t0 = blk_tid sub 0x400095L and t1 = blk_tid sub 0x40009BL in
        check "JUMP-1 two arms"
          (List.length arms = 2
          && List.for_all (fun j ->
                 match Jmp.kind j with Goto (Direct _) -> true | _ -> false) arms);
        check "JUMP-1 ordered targets"
          (match List.map target_tid arms with
           | [ Some a; Some b ] -> Tid.equal a t0 && Tid.equal b t1
           | _ -> false);
        check "JUMP-1 no indirect transfer"
          (not (List.exists is_indirect arms));
        check "JUMP-1 table-offset deltas"
          (Base.List.equal (Option.equal Int64.equal)
             (List.map offset_delta arms)
             [ Some (Int64.sub 0x400095L 0x401000L);
               Some (Int64.sub 0x40009BL 0x401000L) ]));

    (* The missing case blocks are lifted into the source sub and receive
       a solved state in this same pass. *)
    pin "JUMP-2" "missing case blocks are lifted and solved in the same pass"
      (fun () ->
        let result = drive ~data:rel_data rel_code in
        let sub = Base.Option.value_exn (at result.program 0x400078L) in
        let c0 = Base.Option.value_exn (blk_at sub 0x400095L) in
        let c1 = Base.Option.value_exn (blk_at sub 0x40009BL) in
        check "JUMP-2 both case blocks present" true;
        check "JUMP-2 case 0 solved" (env_live result c0);
        check "JUMP-2 case 1 solved" (env_live result c1);
        check "JUMP-2 intra-function, not entries"
          (Base.Option.is_none (at result.program 0x400095L)
          && Base.Option.is_none (at result.program 0x40009BL)));

    (* The worklist enumerates a set, so it cannot produce duplicate
       words; the one-arm-per-line rule lives in Cbat_dispatch. *)
    pin "JUMP-3" "duplicate words produce one arm per word (Cbat_dispatch)"
      (fun () ->
        let t = v64 "j3_t" in
        let tid = Tid.create () in
        let m : D.materialized =
          { D.base = None;
            targets = [ (w 0x10L, tid); (w 0x10L, tid); (w 0x20L, tid) ];
            sub = Sub.create (); module_addr = raw_addr }
        in
        let _, arms =
          D.materialize m ~kind:D.Jump ~cond:None ~target:(Bil.Var t)
        in
        check "JUMP-3 one arm per word"
          (List.length arms = 3
          && Base.List.equal Tid.equal
               (List.map (fun (a : D.arm) -> a.target) arms)
               [ tid; tid; tid ]
          && Base.List.equal Exp.equal
               (List.map (fun (a : D.arm) -> a.guard) arms)
               [ eq (Bil.Var t) (wexp 0x10L);
                 eq (Bil.Var t) (wexp 0x10L);
                 eq (Bil.Var t) (wexp 0x20L) ]));

    (* Without a module base the case tests are plain equalities, never
       table offset arithmetic. *)
    pin "JUMP-4" "no module base uses equality guards" (fun () ->
        let result = drive ~data:abs_data abs_code in
        let sub = Base.Option.value_exn (at result.program 0x400078L) in
        let src = Base.Option.value_exn (blk_at sub 0x400085L) in
        let arms = arms sub src in
        check "JUMP-4 two arms" (List.length arms = 2);
        check "JUMP-4 equality words"
          (Base.List.equal (Option.equal Int64.equal)
             (List.map equality_word arms)
             [ Some 0x400095L; Some 0x40009BL ]);
        check "JUMP-4 no subtraction"
          (not (List.exists (fun j -> has_minus (Jmp.cond j)) arms)));

    (* The decoded x86 shape has no conditional indirect transfer; the
       worklist passes the original jmp through, and the install
       conjoins its condition with every case test.  Pinned here with a
       base so the conjunction is checked on the table-offset form. *)
    pin "JUMP-5" "the original jump condition is conjoined with every case guard"
      (fun () ->
        let sub, tids, t, flag = synthetic_sub "j5" in
        let base = v64 "j5_base" in
        let targets = [ (w 0x400010L, tids.(1)); (w 0x400020L, tids.(2)) ] in
        let mat_transfer ~state ~source:_ ~blk:_ ~jmp:_ ~env:_ =
          Some
            { D.base = Some { D.summand = Bil.Var base; values = [ 0x400000L ] };
              targets;
              sub = Vsa.state_sub state; module_addr = raw_addr }
        in
        let _, state = solve_sub ~materialize_transfer:mat_transfer sub in
        let src =
          Term.find_exn blk_t (Vsa.state_sub state) tids.(0)
        in
        let arms = Term.enum jmp_t src |> Seq.to_list in
        let case delta =
          eq (minus (Bil.Var t) (Bil.Var base)) (iexp delta)
        in
        check "JUMP-5 conjunction"
          (match arms with
           | [ a1; a2; _ ] ->
             Exp.equal (Jmp.cond a1) (and_ (Bil.Var flag) (case 0x10L))
             && Exp.equal (Jmp.cond a2) (and_ (Bil.Var flag) (case 0x20L))
           | _ -> false));

    (* A function-entry target is solved as its own sub and used by a tail
       call; an intra-function target is a block of this sub, never an
       entry. *)
    pin "JUMP-6" "a function-entry target is a function, an intra target a block"
      (fun () ->
        let result = drive ~data:entry_data entry_code in
        let sub = Base.Option.value_exn (at result.program 0x400078L) in
        let src = Base.Option.value_exn (blk_at sub 0x40008AL) in
        let arms = arms sub src in
        let entry = Base.Option.value_exn (at result.program 0x4000A0L) in
        let entry_blk = Base.Option.value_exn (blk_at entry 0x4000A0L) in
        let case = Base.Option.value_exn (blk_at sub 0x40009AL) in
        check "JUMP-6 intra target is a block, not an entry"
          (Base.Option.is_none (at result.program 0x40009AL));
        check "JUMP-6 entry target solved as a function"
          (env_live result entry_blk);
        let case_arm =
          List.exists (fun j ->
              match Jmp.kind j with
              | Goto (Direct t) -> Tid.equal t (Term.tid case)
              | _ -> false) arms
        in
        let entry_arm =
          List.exists (fun j ->
              match Jmp.kind j with
              | Call c ->
                Option.is_none (Call.return c)
                && Call.target c = Direct (Term.tid entry)
              | _ -> false) arms
        in
        check "JUMP-6 one Goto arm, one tail-call arm"
          (List.length arms = 2 && case_arm && entry_arm));

    (* One non-code word fails the whole set before any mutation. *)
    pin "ATOMIC-1" "a non-code target leaves no blocks, edges or entries"
      (fun () ->
        let result = drive ~data:atomic_data abs_code in
        let sub = Base.Option.value_exn (at result.program 0x400078L) in
        let src = Base.Option.value_exn (blk_at sub 0x400085L) in
        check "ATOMIC-1 no case block" (Base.Option.is_none (blk_at sub 0x400095L));
        check "ATOMIC-1 no entry" (Base.Option.is_none (at result.program 0x400095L));
        check "ATOMIC-1 the source sub has only its original blocks"
          (List.length (Term.enum blk_t sub |> Seq.to_list) = 4);
        check "ATOMIC-1 indirect transfer remains"
          (List.exists is_indirect (jmps src));
        check "ATOMIC-1 no case edge"
          (not
             (List.exists
                (fun j ->
                  match target_tid j with
                  | Some t -> (
                    match blk_at sub 0x400095L with
                    | Some b -> Tid.equal t (Term.tid b)
                    | None -> false)
                  | None -> false)
                (jmps src))));

    (* TOP leaves the indirect transfer alone and the solve continues. *)
    pin "TOP-1" "an unbounded target leaves the indirect jump and keeps solving"
      (fun () ->
        let result = drive top_code in
        let sub = Base.Option.value_exn (at result.program 0x400078L) in
        let src = Base.Option.value_exn (blk_at sub 0x400078L) in
        check "TOP-1 indirect transfer remains"
          (List.exists is_indirect (jmps src));
        check "TOP-1 the solve reached the block" (env_live result src));
  ]

let () = run "dispatch_jump" tests
