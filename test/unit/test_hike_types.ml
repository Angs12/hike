(* Pins for the emission-signature home: [free_vars], the FP-return probe,
   the lane-pointer classification, the signature shapes, and the two
   program-level entries.  One Alcotest group per pin; each pin builds its
   own BIR fixtures, so no state crosses pins. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

module Types = Hike__Hike_types
module Model = Hike_stack_model
module Abi = Hike.Abi

(* The real SysV convention (the module contract's [abi]). *)
let abi = Hike.Abi.x86_64_sysv

(* [Abi.t] is built on demand; target facts need the harness [init]. *)
let x86 () : Theory.Target.t = x86_target ()

(* The lane names are the SSA names; the base name is the variable the
   lane carries. *)
let arg_name (a : Arg.t) : string = Var.name (Var.base (Arg.lhs a))
let arg_names (l : Arg.t list) : string list = Base.List.map l ~f:arg_name
let is_ptr (a : Arg.t) : bool = Model.is_ptr_arg a

(* The observable lane: name, intent, pointer-tag. *)
let lane (a : Arg.t) : string * intent option * bool =
  (arg_name a, Arg.intent a, is_ptr a)

let lanes (l : Arg.t list) : (string * intent option * bool) list =
  Base.List.map l ~f:lane

let for_all_in (l : Arg.t list) : bool =
  Base.List.for_all l ~f:(fun a -> Arg.intent a = Some In && not (is_ptr a))

(* Signing assumes an SSA program: build the SSA sub, then sign it. *)
let ssa_of ~synth (sub : sub term) : sub term =
  let target = x86 () in
  Program.create ~subs:[ sub ] ()
  |> Hike.Ssa.ssa_program ~synth ~target
  |> Term.first sub_t |> Base.Option.value_exn

let sig_of ~synth (sub : sub term) =
  let target = x86 () in
  let sub = ssa_of ~synth sub in
  Types.compute_sub_sig ~synth
    ~free_vars:(Types.free_regs_of_sub ~synth ~target sub) target sub

(* One block, no calls, so the PLT signature rule cannot fire. *)
let plain_sub (name : string) (defs : def term list) : sub term =
  fst (sub_of name [ defs, [] ])

(* The pre-SSA form of [straight_sub]: the sign tests hand the pass the
   SSA the drive builds, so their fixture is the pre-SSA sub. *)
let raw_straight_sub (name : string) (defs : def term list) : sub term =
  fst
    (raw_sub_of name
       [ defs, [ (1, mk_goto) ]; [], [ (0, mk_ret) ] ])

(* The epilogue sub: a value-reg def in the block whose only jump is an
   indirect call with no return (the FP-return probe's shape). *)
let epilogue_sub (ret : var) : sub term =
  fst
    (sub_of (Var.name ret ^ "_epi")
       [ [ Def.create ret (Bil.Var (v64 "t14_src")) ],
         [ (1,
            fun _ ->
              Jmp.create
                (Call
                   (Call.create
                      ~target:
                        (Indirect (Bil.Int (Cbat_word.to_word (w64 0))))
                      ()))) ];
         [], [] ])

(* The production seams on fixtures: sign, SSA, then the kind
   inference.  [retype] is the types pass for [emit_ir ~types]. *)
type use_kinds = {
  is_ptr_def : string -> var -> bool;
  is_ptr_lane : string -> var -> bool;
  defs : string -> def term list;
  retype : program term -> program term;
}

(* The production type pass on signed SSA fixtures. *)
let analyse ~synth (subs : sub term list) =
  let target = x86 () in
  let facts, stamped, _ = fixture_facts ~synth subs in
  let prog =
    Program.create ~subs:stamped ()
    |> Types.sign_program ~synth:facts.Hike.Kb.synth ~target
  in
  let typed =
    Types.type_program ~facts ~mem_typ:(Types.mem_type_of_target target) prog
  in
  (facts, prog, typed)

let facts_equal (a : Types.ptr_facts) (b : Types.ptr_facts) =
  Core.Set.equal a.def_tids b.def_tids
  && Core.Map.equal Stdlib.( = ) a.def_storages b.def_storages
  && Core.Set.equal a.vars b.vars

let ptr_var v = match Var.typ v with Type.Mem _ -> true | _ -> false

let sub_named prog name =
  Term.enum sub_t prog
  |> Seq.find ~f:(fun sub -> String.equal (Sub.name sub) name)
  |> Base.Option.value_exn

let ptr_names prog name =
  let add v acc =
    if ptr_var v then Core.Set.add acc (Var.to_string v) else acc
  in
  (object
     inherit [Core.String.Set.t] Term.visitor as super
     method! visit_var v acc = add v acc
     method! visit_def d acc = super#visit_def d (add (Def.lhs d) acc)
     method! visit_phi p acc = super#visit_phi p (add (Phi.lhs p) acc)
     method! visit_arg a acc = super#visit_arg a (add (Arg.lhs a) acc)
   end)#visit_sub (sub_named prog name) Core.String.Set.empty

let type_snapshot prog =
  Term.enum sub_t prog |> Seq.to_list
  |> Base.List.map ~f:(fun sub -> (Sub.name sub, ptr_names prog (Sub.name sub)))
  |> Base.List.sort ~compare:(fun (a, _) (b, _) -> String.compare a b)

let same_types a b =
  Base.List.equal
    (fun (a, x) (b, y) -> String.equal a b && Core.Set.equal x y)
    (type_snapshot a) (type_snapshot b)

let ptr_defs ?(extra = Var.Set.empty) ?(used = Var.Set.empty) ~facts sub =
  (Types.ptr_solver ~facts sub) ~extra ~used

(* Deterministic multi-sub programs: each sub computes and stores through
   sums of its two parameter lanes, and calls other subs (back edges
   included) with a stack pointer or its own lanes. *)
let gen_program (seed : int) (n : int) : sub term list =
  let rng = Random.State.make [| seed |] in
  let rdi = int_param 0 and rsi = int_param 1 and rax = int_ret 0 in
  let m = memv "gen_m" in
  let k x = Bil.Int (Cbat_word.to_word (w64 x)) in
  let pick l = List.nth l (Random.State.int rng (List.length l)) in
  let name i = "gen" ^ string_of_int i in
  let defs () =
    let value =
      pick
        [ Bil.BinOp (Bil.PLUS, Bil.Var rdi, Bil.Var rsi);
          Bil.BinOp (Bil.PLUS, Bil.Var rdi, k 8);
          Bil.BinOp (Bil.PLUS, Bil.Var sp, k 16);
          Bil.Var sp; Bil.Var rsi; Bil.Var rdi; k 4096 ]
    in
    let dst = pick [ rax; rsi; rdi ] in
    let store =
      if Random.State.bool rng then
        [ Def.create m
            (Bil.Store (Bil.Var m, Bil.Var (pick [ rax; rdi; rsi ]), k 1,
                        LittleEndian, `r64)) ]
      else []
    in
    Def.create dst value :: store
  in
  List.init n (fun i ->
      let calls = Random.State.int rng 3 in
      let call callee t =
        Jmp.create
          (Call
             (Call.create ~return:(Label.direct t)
                ~target:(Label.direct (Tid.for_name (name callee))) ()))
      in
      let nodes =
        List.init (calls + 1) (fun b ->
            if b < calls then
              (defs (), [ (b + 1, call (Random.State.int rng n)) ])
            else (defs (), [ (b + 1, mk_goto) ]))
        @ [ ([], [ (0, mk_ret) ]) ]
      in
      fst (sub_of ~tid:(Tid.for_name (name i)) (name i) nodes))

let use_kinds ~synth (subs : sub term list) : use_kinds =
  let target = x86 () in
  let facts, _, typed = analyse ~synth subs in
  let defs name =
    Term.enum blk_t (sub_named typed name)
    |> Seq.concat_map ~f:(Term.enum def_t)
    |> Seq.to_list
  in
  { defs;
    is_ptr_def =
      (fun name reg ->
        defs name
        |> Base.List.exists ~f:(fun d ->
               Var.same (Var.base (Def.lhs d)) reg && ptr_var (Def.lhs d)));
    is_ptr_lane =
      (fun name reg ->
        Model.sig_args (sub_named typed name)
        |> Base.List.exists ~f:(fun a ->
               Var.same (Arg.lhs a) reg && ptr_var (Arg.lhs a)));
    retype = Types.type_program ~facts ~mem_typ:(Types.mem_type_of_target target) }

(* A real [@main]: [Tid.for_name] prefixes ["@"], so ["main"] names the tid
   [@main] — the name the fixed signature reads. *)
let tests : unit Alcotest.test list =
  [
    pin "TYPES-36" "pointer retyping preserves indirect calls and jumps"
      (fun () ->
        let target = v64 "types36_target" in
        let continuation = Tid.create () in
        let call = Jmp.create_call
            (Call.create ~target:(Indirect (Bil.Var target))
               ~return:(Direct continuation) ()) in
        let jump = Jmp.create_goto (Indirect (Bil.Var target)) in
        Base.List.iter [call; jump] ~f:(fun transfer ->
            let blk = Blk.create ~jmps:[transfer] () in
            let sub = Sub.create ~name:"types36" ~blks:[blk] () in
            let typed = Types.retype_sub
                ~mem_typ:(Types.mem_type_of_target (x86 ()))
                ~ptr_vars:(Var.Set.singleton target)
                ~ptr_rets:Var.Set.empty sub in
            let blk = Term.first blk_t typed |> Base.Option.value_exn in
            let typed_jmp = Term.first jmp_t blk |> Base.Option.value_exn in
            let target_exp = match Jmp.kind transfer, Jmp.kind typed_jmp with
              | Call _, Call c ->
                check "TYPES-36 call continuation survives"
                  (Call.return c = Some (Direct continuation));
                (match Call.target c with Indirect e -> e | _ -> assert false)
              | Goto _, Goto (Indirect e) -> e
              | _ -> failwith "TYPES-36 transfer kind changed" in
            check "TYPES-36 target retains its pointer type"
              (Type.infer target_exp = Ok (Types.mem_type_of_target (x86 ())));
            check "TYPES-36 target retains its SSA identity"
              (match target_exp with
               | Bil.Var v -> Var.same v target
               | _ -> false);
            check "TYPES-36 needs no scalar copies"
              (Seq.is_empty (Term.enum def_t blk))));

    pin "TYPES-05" "tag_lane: a plain [In] register lane is not a pointer"
      (fun () ->
        let rdi = int_param 0 in
        let a' = Types.tag_lane ~synth:Hike.Synth.empty (Arg.create ~intent:In rdi (Bil.Var rdi)) in
        check "TYPES-05"
          (arg_name a' = Var.name rdi && Arg.intent a' = Some In && not (is_ptr a')));

    pin "TYPES-12"
      "compute_sub_sig: SP, the thread pointer, and callee-saved registers are \
       not argument lanes"
      (fun () ->
        let sub =
          plain_sub "t14_filt"
            [ Def.create (v64 "t14_f1") (Bil.Var sp);
              Def.create (v64 "t14_f2") (Bil.Var (callee_saved 0));
              Def.create (v64 "t14_f3") (Bil.Var thread_pointer) ]
        in
        let _, args = sig_of ~synth:Hike.Synth.empty sub in
        check "TYPES-12" (args = []));

    pin "TYPES-13"
      "compute_sub_sig: intrinsic-target and registered promoted variables are not argument \
       lanes"
      (fun () ->
        let slot = v64 "registered_slot" and arg = v64 "registered_arg" in
        let synth = Hike.Synth.add
            (Hike.Synth.add Hike.Synth.empty slot (K_slot 0)) arg (K_argument 2) in
        let sub =
          plain_sub "t14_prom"
            [ Def.create (v64 "t14_p1") (Bil.Var slot);
              Def.create (v64 "t14_p2") (Bil.Var arg);
              Def.create (v64 "t14_p3") (Bil.Var (v64 "intrinsic:foo")) ]
        in
        let _, args = sig_of ~synth sub in
        check "TYPES-13" (args = []));

    pin "TYPES-16"
      "compute_sub_sig: a window-param layout carries the caller window as a \
       pointer [In] lane"
      (fun () ->
        let layout : Sm.sub_layout =
          { regions = []; window_param = true; runtime_residue = false }
        in
        let sub = Sm.set_layout layout (plain_sub "t14_window" []) in
        let synth = Hike.Synth.add_window Hike.Synth.empty ~addr_bits:64 in
        let rets, args = sig_of ~synth sub in
        check "TYPES-16"
          (arg_names rets
           = Base.List.map (Abi.of_target (x86 ())).Abi.return_regs ~f:Var.name
          && match args with
             | [ a ] ->
                 arg_name a = "hike_window"
                 && Arg.intent a = Some In
                 && is_ptr a
             | _ -> false));

    pin "TYPES-17"
      "compute_sub_sig: an emittable intrinsic takes its free vars [In] and \
       its own defs [Out]"
      (fun () ->
        let rdi = int_param 0 in
        let y = v64 "intrinsic:testsig_y" in
        let sub =
          Term.set_attr
            (raw_straight_sub "intrinsic:testsig" [ Def.create y (Bil.Var rdi) ])
            Sub.intrinsic ()
        in
        let rets, args = sig_of ~synth:Hike.Synth.empty sub in
        check "TYPES-17"
          (arg_names args = [ Var.name (int_param 0) ]
          && for_all_in args
          && arg_names rets = [ "intrinsic:testsig_y" ]
          && Base.List.for_all rets ~f:(fun a ->
                 Arg.intent a = Some Out && not (is_ptr a))));

    pin "TYPES-18"
      "compute_sub_sig: an internal sub carries exactly the ABI's return registers as Out lanes, no body scan"
      (fun () ->
        let ymm0 = Base.List.nth_exn abi.Abi.vector_param_regs 0 in
        let rets, _ = sig_of ~synth:Hike.Synth.empty (epilogue_sub ymm0) in
        let target_abi = Abi.of_target (x86 ()) in
        check "TYPES-18 the target ABI's carriers, in its order"
          (Base.List.map rets ~f:Arg.lhs
           |> fun lanes ->
           Base.List.length lanes = Base.List.length target_abi.Abi.return_regs
           && Base.List.for_all2_exn lanes target_abi.Abi.return_regs ~f:Var.same);
        check "TYPES-18 Out lanes, each an ABI return register"
          (Base.List.for_all rets ~f:(fun a ->
               Arg.intent a = Some Out && Abi.is_return_reg target_abi (Arg.lhs a))));

    pin "TYPES-22"
      "a named external call absent from the program keeps the synthetic parameter ABI"
      (fun () ->
        let target = Tid.for_name "external_call" in
        let sub, _ =
          sub_of "t14_external_call"
            [ [],
              [ (0,
                 fun _ ->
                   Jmp.create
                     (Call
                        (Call.create ~target:(Label.direct target) ()))) ] ]
        in
        let prog = Program.create ~subs:[ sub ] () in
        let prog' = Hike.Ssa.ssa_program ~synth:Hike.Synth.empty ~target:(x86 ()) prog
          |> Types.sign_program ~synth:Hike.Synth.empty ~target:(x86 ()) in
        let sub' = Term.first sub_t prog' |> Base.Option.value_exn in
        check "TYPES-22"
          (arg_names (Model.sig_args sub')
           = Base.List.map (Abi.param_regs abi @ [ (int_ret 0) ]) ~f:Var.name));

    pin "TYPES-23"
      "a canonical direct return does not add synthetic call lanes"
      (fun () ->
        let sub, _ =
          sub_of "t14_terminal_return" [ [], [ (0, mk_ret) ] ]
        in
        let prog = Program.create ~subs:[ sub ] () in
        let prog' = Hike.Ssa.ssa_program ~synth:Hike.Synth.empty ~target:(x86 ()) prog
          |> Types.sign_program ~synth:Hike.Synth.empty ~target:(x86 ()) in
        let sub' = Term.first sub_t prog' |> Base.Option.value_exn in
        let target_abi = Abi.of_target (x86 ()) in
        check "TYPES-23"
          (Base.List.for_all (Model.sig_args sub') ~f:(fun a ->
               Abi.is_return_reg target_abi (Arg.lhs a))));
    pin "KIND-01"
      "a def computing a stack address is ptr-kind (its denotation is \
       stack-resident)"
      (fun () ->
        let rbp = frame_ptr and rax = int_ret 0 in
        let sub =
          straight_sub "k01"
            [ Def.create rbp (Bil.Var sp);
              Def.create rax
                (Bil.BinOp
                   ( Bil.PLUS,
                     Bil.Var rbp,
                     Bil.Int (Cbat_word.to_word (w64 8)) )) ]
        in
        let facts, stamped = fixture_facts_sub ~synth:Hike.Synth.empty sub in
        let pf = ptr_defs ~facts stamped in
        let rax_def =
          Term.enum blk_t stamped
          |> Seq.concat_map ~f:(Term.enum def_t)
          |> Seq.find ~f:(fun d -> Var.same (Def.lhs d) rax)
        in
        check "KIND-01"
          (match rax_def with
           | Some d -> Core.Set.mem pf.Types.def_tids (Term.tid d)
           | None -> false));

    pin "KIND-05"
      "an integer SSA version of a pointer register stays an integer" (fun () ->
        let rdi = int_param 0 in
        let rbx = callee_saved 0 and rcx = int_param 3 in
        let eight = Bil.Int (Cbat_word.to_word (w64 8)) in
        let dx = Def.create rcx (Bil.BinOp (Bil.PLUS, Bil.Var rdi, eight)) in
        let di = Def.create rdi (Bil.Int (Cbat_word.to_word (w64 48))) in
        let db = Def.create rbx (Bil.BinOp (Bil.PLUS, Bil.Var rdi, eight)) in
        let sub = straight_sub "k05" [ dx; di; db ] in
        let facts, stamped = fixture_facts_sub ~synth:Hike.Synth.empty sub in
        let version d = Term.enum blk_t stamped
          |> Seq.concat_map ~f:(Term.enum def_t)
          |> Seq.find_exn ~f:(fun x -> Tid.equal (Term.tid x) (Term.tid d))
          |> Def.lhs in
        let rcx1 = version dx and rdi1 = version di and rbx1 = version db in
        let pf =
          ptr_defs ~extra:(Var.Set.singleton rdi) ~facts stamped
        in
        check "KIND-05"
          (Core.Set.mem pf.Types.vars rcx1
           && not (Core.Set.mem pf.Types.vars rdi1)
           && not (Core.Set.mem pf.Types.vars rbx1)));

    pin "KIND-04"
      "an unused callee parameter keeps its integer contract when a caller \
       passes a stack address" (fun () ->
        let rdi = int_param 0 in
        let callee, _ =
          sub_of ~args:[ Arg.create ~intent:In rdi (Bil.Var rdi) ] "k04_callee"
            [ [], [ (0, mk_ret) ] ]
        in
        let caller, _ =
          sub_of "k04_caller"
            [ [ Def.create rdi (Bil.Var sp) ],
              [ (1,
                 fun t ->
                   Jmp.create
                     (Call
                        (Call.create ~return:(Label.direct t)
                           ~target:(Label.direct (Term.tid callee))
                           ()))) ];
              [], [ (0, mk_ret) ] ]
        in
        let facts, stamped, _ = fixture_facts ~synth:Hike.Synth.empty [ caller; callee ] in
        let prog = Program.create ~subs:stamped () in
        let mem_typ = Types.mem_type_of_target facts.Hike.Kb.target in
        let prog = Types.type_program ~facts ~mem_typ prog in
        let callee = sub_named prog "k04_callee" in
        let arg =
          Term.enum arg_t callee
          |> Seq.find ~f:(fun a -> Var.same (Arg.lhs a) rdi)
          |> Base.Option.value_exn
        in
        check "KIND-04" (Var.typ (Arg.lhs arg) <> mem_typ));

    pin "TYPES-25" "return carriers retain entry values on unwritten paths"
      (fun () ->
        let target = x86 () in
        let rax = int_ret 0 and rdx = int_ret 1 and rdi = int_param 0 in
        let sub, tids =
          sub_of "preserve_return"
            [ [ Def.create rax (Bil.Var rdi) ],
              [ (1, fun t -> mk_jmp_to t
                    (Bil.BinOp (Bil.EQ, Bil.Var rdi,
                       Bil.Int (Cbat_word.to_word (w64 0)))));
                (2, mk_goto) ];
              [ Def.create rdx (Bil.Int (Cbat_word.to_word (w64 7))) ],
              [ (2, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let signed =
          Types.sign_sub ~synth:Hike.Synth.empty ~target
            (ssa_of ~synth:Hike.Synth.empty sub)
        in
        let inputs = Base.List.map (Model.sig_args signed) ~f:Arg.lhs in
        let has v = Base.List.exists inputs ~f:(Var.same v) in
        check "TYPES-25 the parameter and the lane unwritten on one path are inputs"
          (has rdi && has rdx);
        check "TYPES-25 a lane written on every path is not an input"
          (not (has rax));
        check "TYPES-25 every input beyond the parameter is an ABI return register"
          (Base.List.for_all inputs ~f:(fun v ->
               Var.same v rdi || Abi.is_return_reg (Abi.of_target target) v));
        let join = Term.find blk_t signed tids.(2) |> Base.Option.value_exn in
        let phi = Term.enum phi_t join
            |> Seq.find ~f:(fun p -> Var.same (Var.base (Phi.lhs p)) rdx)
            |> Base.Option.value_exn in
        check "TYPES-25 preserved incoming"
          (Phi.values phi |> Seq.exists ~f:(fun (src, e) ->
               Tid.equal src tids.(0) && Exp.equal e (Bil.Var rdx)));
        let overwritten = plain_sub "overwrite_return"
            [ Def.create rdx (Bil.Int (Cbat_word.to_word (w64 7))) ]
            |> ssa_of ~synth:Hike.Synth.empty
            |> Types.sign_sub ~synth:Hike.Synth.empty ~target in
        check "TYPES-25 overwritten lane"
          (not (Model.sig_args overwritten |> Base.List.exists ~f:(fun a ->
               Var.same (Arg.lhs a) rdx)));
        let untouched, _ = sub_of "untouched_return" [ [], [ (0, mk_ret) ] ] in
        let caller, _ = sub_of "forward_return"
            [ [], [ (1, fun t -> Jmp.create (Call
                  (Call.create ~return:(Direct t)
                     ~target:(Direct (Term.tid untouched)) ()))) ];
              [], [ (0, mk_ret) ] ] in
        (* The callee signs first: its inputs are what the call reads. *)
        let untouched =
          Types.sign_sub ~synth:Hike.Synth.empty ~target
            (ssa_of ~synth:Hike.Synth.empty untouched)
        in
        let caller =
          Program.create ~subs:[ untouched; caller ] ()
          |> Hike.Ssa.ssa_program ~synth:Hike.Synth.empty ~target
          |> fun prog ->
          Term.enum sub_t prog
          |> Seq.find ~f:(fun s -> String.equal (Sub.name s) "forward_return")
          |> Base.Option.value_exn
          |> Types.sign_sub ~synth:Hike.Synth.empty ~target in
        check "TYPES-25 call chains retain incoming carriers"
          (Model.sig_args caller |> Base.List.exists ~f:(fun a ->
               Var.same (Arg.lhs a) rax)));

    (* The PLT-trampoline stamp: hike-sign computes it from the same
       liveness run as the signature; the emitter reads the stamp. *)
    pin "TYPES-24" "sign stamps the self-call stub that reads no register"
      (fun () ->
        let self_tid = Tid.for_name "trampoline_self" in
        let sub, _ =
          sub_of ~tid:self_tid "trampoline_self"
            [ ([],
               [ (1,
                  fun t ->
                    Jmp.create
                      (Call
                         (Call.create ~return:(Direct t)
                            ~target:(Direct self_tid) ()))) ]);
              ([], [ (0, mk_ret) ]) ]
        in
        let prog = Program.create ~subs:[ sub ] ()
          |> Hike.Ssa.ssa_program ~synth:Hike.Synth.empty ~target:(x86 ())
          |> Types.sign_program ~synth:Hike.Synth.empty ~target:(x86 ()) in
        let stamped = Term.enum sub_t prog |> Seq.hd_exn in
        (* the same self-call shape reading RBX first: not a trampoline *)
        let reader_tid = Tid.for_name "trampoline_reader" in
        let rbx = v64 "trampoline_rbx" in
        let rd = v64 "trampoline_rd" in
        let reader, _ =
          sub_of ~tid:reader_tid "trampoline_reader"
            [ [ Def.create rd (Bil.Var rbx) ],
              [ (1,
                 fun t ->
                   Jmp.create
                     (Call
                        (Call.create ~return:(Direct t)
                           ~target:(Direct reader_tid) ()))) ];
              ([], [ (0, mk_ret) ]) ]
        in
        let prog2 = Program.create ~subs:[ reader ] ()
          |> Hike.Ssa.ssa_program ~synth:Hike.Synth.empty ~target:(x86 ())
          |> Types.sign_program ~synth:Hike.Synth.empty ~target:(x86 ()) in
        let stamped2 = Term.enum sub_t prog2 |> Seq.hd_exn in
        check "TYPES-24"
          (Model.is_plt_trampoline_sub stamped
          && not (Model.is_plt_trampoline_sub stamped2)));

    (* One lane source: a declaration's signature is the machine
       convention, so a call, a declaration and the emitter agree. *)
    pin "TYPES-26" "a bodyless declaration is signed with the machine convention"
      (fun () ->
        let target = x86 () in
        let a = Abi.of_target target in
        let signed = Types.sign_sub ~synth:Hike.Synth.empty ~target (Sub.create ~name:"types26_ext" ()) in
        check "TYPES-26 args are exactly the ABI's parameter registers, In"
          (Base.List.equal Var.same
             (Base.List.map (Model.sig_args signed) ~f:Arg.lhs)
             (Abi.param_regs a)
          && Base.List.for_all (Model.sig_args signed) ~f:(fun l ->
                 Arg.intent l = Some In));
        check "TYPES-26 rets are the return lanes"
          (Base.List.equal Var.same
             (Base.List.map (Model.sig_rets signed) ~f:Arg.lhs)
             (Base.List.map (Types.return_lanes ~target signed) ~f:Arg.lhs)));

    (* A return lane follows the version it returns at an exit; a
       trampoline has none, so a pointer argument stays out of it. *)
    pin "TYPES-27"
      "a pointer argument does not type the same register's return lane"
      (fun () ->
        let target = x86 () in
        let rdx = int_ret 1 in
        let ext = Tid.create () in
        let callee, _ =
          sub_of "types27_tramp"
            [ [], [ (1, mk_goto) ];
              [],
              [ (0,
                 fun _ ->
                   Jmp.create
                     (Call
                        (Call.create ~target:(Label.direct ext) ()))) ] ]
        in
        let caller, _ =
          sub_of "types27_caller"
            [ [ Def.create rdx (Bil.Var sp) ],
              [ (1,
                 fun t ->
                   Jmp.create
                     (Call
                        (Call.create ~return:(Label.direct t)
                           ~target:(Label.direct (Term.tid callee))
                           ()))) ];
              [], [ (0, mk_ret) ] ]
        in
        let facts, stamped, _ = fixture_facts ~synth:Hike.Synth.empty [ caller; callee ] in
        let prog = Program.create ~subs:stamped () in
        let prog = Types.sign_program ~synth:Hike.Synth.empty ~target prog in
        let prog =
          Term.map sub_t prog ~f:(fun sub ->
              if Tid.equal (Term.tid sub) (Term.tid callee) then
                Term.map arg_t sub ~f:(fun a ->
                    if not (Model.is_ret a) && Var.same (Arg.lhs a) rdx then
                      Model.set_ptr_arg a
                    else a)
              else sub)
        in
        let mem_typ = Types.mem_type_of_target target in
        let prog = Types.type_program ~facts ~mem_typ prog in
        let callee = sub_named prog "types27_tramp" in
        let lane_typ ~ret =
          Term.enum arg_t callee
          |> Seq.find ~f:(fun a ->
                 Var.same (Arg.lhs a) rdx && Model.is_ret a = ret)
          |> Base.Option.map ~f:(fun a -> Var.typ (Arg.lhs a))
        in
        check "TYPES-27 the argument lane is a pointer"
          (lane_typ ~ret:false = Some mem_typ);
        check "TYPES-27 the return lane stays an integer"
          (match lane_typ ~ret:true with
           | Some t -> t <> mem_typ
           | None -> false));

    (* Use-based kinds: a version used as a load/store address is a
       pointer, per SSA version. *)
    pin "TYPES-28"
      "a version used as a store or load address is a pointer; the loaded \
       value is not"
      (fun () ->
        let rax = int_ret 0 and rcx = int_param 3 and rdx = int_ret 1 in
        let m = memv "types28_m" in
        let sub =
          straight_sub "types28"
            [ Def.create rax (Bil.Int (Cbat_word.to_word (w64 4096)));
              Def.create rcx (Bil.Int (Cbat_word.to_word (w64 8192)));
              Def.create m
                (Bil.Store (Bil.Var m, Bil.Var rax,
                            Bil.Int (Cbat_word.to_word (w64 1)),
                            LittleEndian, `r64));
              Def.create rdx (Bil.Load (Bil.Var m, Bil.Var rcx, LittleEndian, `r64)) ]
        in
        let kinds = use_kinds ~synth:Hike.Synth.empty [ sub ] in
        check "TYPES-28 the store address is a pointer" (kinds.is_ptr_def "types28" rax);
        check "TYPES-28 the load address is a pointer" (kinds.is_ptr_def "types28" rcx);
        check "TYPES-28 the loaded value is an integer"
          (not (kinds.is_ptr_def "types28" rdx)));

    pin "TYPES-29"
      "an unproven operand of an address def is no base: it stays an \
       integer and the access goes through inttoptr"
      (fun () ->
        let rdi = int_param 0 and rax = int_ret 0 in
        let m = memv "types29_m" in
        let eight = Bil.Int (Cbat_word.to_word (w64 8)) in
        let sub =
          straight_sub "types29"
            [ Def.create rax (Bil.BinOp (Bil.PLUS, Bil.Var rdi, eight));
              Def.create m
                (Bil.Store (Bil.Var m, Bil.Var rax,
                            Bil.Int (Cbat_word.to_word (w64 1)),
                            LittleEndian, `r64)) ]
        in
        let kinds = use_kinds ~synth:Hike.Synth.empty [ sub ] in
        check "TYPES-29 the sum is a pointer" (kinds.is_ptr_def "types29" rax);
        check "TYPES-29 the unproven entry lane stays an integer"
          (not (kinds.is_ptr_lane "types29" rdi));
        let ir = emit_ir ~synth:Hike.Synth.empty ~types:kinds.retype [ sub ] in
        check "TYPES-29 the store is addressed through inttoptr"
          (contains_substring ir "inttoptr"));

    pin "TYPES-30"
      "a callee reached only indirectly takes a pointer lane for a parameter \
       it uses as a store address"
      (fun () ->
        let rdi = int_param 0 in
        let m = memv "types30_m" in
        let callee, _ =
          sub_of ~args:[ Arg.create ~intent:In rdi (Bil.Var rdi) ] "types30_redirect"
            [ [ Def.create m
                  (Bil.Store (Bil.Var m, Bil.Var rdi,
                              Bil.Int (Cbat_word.to_word (w64 2)),
                              LittleEndian, `r64)) ],
              [ (1, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let kinds = use_kinds ~synth:Hike.Synth.empty [ callee ] in
        check "TYPES-30 the parameter lane is a pointer"
          (kinds.is_ptr_lane "types30_redirect" rdi));

    pin "TYPES-31"
      "a sum of two bare vars names no base: both stay integers"
      (fun () ->
        let rdi = int_param 0 and rsi = int_param 1 in
        let rax = int_ret 0 in
        let m = memv "types31_m" in
        let sub =
          straight_sub "types31"
            [ Def.create rax (Bil.BinOp (Bil.PLUS, Bil.Var rdi, Bil.Var rsi));
              Def.create m
                (Bil.Store (Bil.Var m, Bil.Var rax,
                            Bil.Int (Cbat_word.to_word (w64 1)),
                            LittleEndian, `r64)) ]
        in
        let kinds = use_kinds ~synth:Hike.Synth.empty [ sub ] in
        check "TYPES-31 the sum is a pointer (it is the address)"
          (kinds.is_ptr_def "types31" rax);
        check "TYPES-31 neither addend is"
          (not (kinds.is_ptr_lane "types31" rdi)
           && not (kinds.is_ptr_lane "types31" rsi)));

    pin "TYPES-32"
      "use makes a version a pointer, not its register: a narrower version \
       of the same register stays an integer"
      (fun () ->
        let rax = int_ret 0 in
        let eax = Var.create ~is_virtual:false ~fresh:false "types32_eax" (Type.Imm 32) in
        let m = memv "types32_m" in
        let sub =
          straight_sub "types32"
            [ Def.create rax (Bil.Int (Cbat_word.to_word (w64 4096)));
              Def.create m
                (Bil.Store (Bil.Var m, Bil.Var rax,
                            Bil.Int (Cbat_word.to_word (w64 1)),
                            LittleEndian, `r64));
              Def.create rax (Bil.Int (Cbat_word.to_word (w64 7)));
              Def.create eax (Bil.Cast (Bil.LOW, 32, Bil.Var rax)) ]
        in
        let kinds = use_kinds ~synth:Hike.Synth.empty [ sub ] in
        let defs_of reg =
          kinds.defs "types32" |> Base.List.filter ~f:(fun d -> Var.same (Var.base (Def.lhs d)) reg)
        in
        let ptr_of d = ptr_var (Def.lhs d) in
        match defs_of rax with
        | [ first; second ] ->
            check "TYPES-32 the version used as an address is a pointer" (ptr_of first);
            check "TYPES-32 the later version of the register is an integer"
              (not (ptr_of second));
            check "TYPES-32 the 32-bit version is an integer"
              (Base.List.for_all (defs_of eax) ~f:(fun d -> not (ptr_of d)))
        | _ -> check "TYPES-32 two versions of the register" false);

    (* An address's base is chosen by denotation: the stack-based
       operand is the base and the loop index stays an integer. *)
    pin "TYPES-33"
      "RSP + (i - 72 + 104) leaves the loop index an integer: the address \
       is a GEP off the stack base"
      (fun () ->
        let i = int_param 4 and a = int_ret 0 in
        let m = memv "types33_m" in
        let c = Var.create ~is_virtual:false ~fresh:false "types33_c" (Type.Imm 1) in
        let n k = Bil.Int (Cbat_word.to_word (w64 k)) in
        let sub, _ =
          sub_of "types33"
            [ [ Def.create i (n 0) ], [ (1, mk_goto) ];
              [ Def.create a
                  (Bil.BinOp (Bil.PLUS, Bil.Var sp,
                              Bil.BinOp (Bil.PLUS,
                                         Bil.BinOp (Bil.MINUS, Bil.Var i, n 72),
                                         n 104)));
                Def.create m
                  (Bil.Store (Bil.Var m, Bil.Var a, n 1, LittleEndian, `r64));
                Def.create i (Bil.BinOp (Bil.PLUS, Bil.Var i, n 8)) ],
              [ (1, fun t -> mk_jmp_to t (Bil.Var c)); (2, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let sub = rewrite_one ~synth:Hike.Synth.empty sub in
        let kinds = use_kinds ~synth:Hike.Synth.empty [ sub ] in
        check "TYPES-33 the address is a pointer" (kinds.is_ptr_def "types33" a);
        check "TYPES-33 the loop index is an integer"
          (not (kinds.is_ptr_def "types33" i));
        let ir = emit_ir ~synth:Hike.Synth.empty ~types:kinds.retype [ sub ] in
        check "TYPES-33 the store is a GEP off the stack base, no cast"
          (contains_substring ir "phi ptr [ %entry1,"
           && contains_substring ir "getelementptr i8, ptr %"
           && (not (contains_substring ir "= inttoptr"))
           && not (contains_substring ir "ptrtoint")));

    pin "TYPES-34"
      "loaded value + index: no operand has base evidence, so both stay \
       integers and the access goes through inttoptr"
      (fun () ->
        let b = int_ret 1 and k = callee_saved 0 and a = int_ret 0 in
        let src = int_param 1 in
        let m = memv "types34_m" in
        let c = Var.create ~is_virtual:false ~fresh:false "types34_c" (Type.Imm 1) in
        let n x = Bil.Int (Cbat_word.to_word (w64 x)) in
        let sub, _ =
          sub_of "types34"
            [ [ Def.create b (Bil.Load (Bil.Var m, Bil.Var src, LittleEndian, `r64)) ],
              [ (2, fun t -> mk_jmp_to t (Bil.Var c)); (1, mk_goto) ];
              [ Def.create k (n 0) ], [ (3, mk_goto) ];
              [ Def.create k (n 8) ], [ (3, mk_goto) ];
              [ Def.create a (Bil.BinOp (Bil.PLUS, Bil.Var b, Bil.Var k));
                Def.create m
                  (Bil.Store (Bil.Var m, Bil.Var a, n 1, LittleEndian, `r64)) ],
              [ (4, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let kinds = use_kinds ~synth:Hike.Synth.empty [ sub ] in
        check "TYPES-34 the loaded value is an integer"
          (not (kinds.is_ptr_def "types34" b));
        check "TYPES-34 the index is an integer"
          (not (kinds.is_ptr_def "types34" k));
        let ir = emit_ir ~synth:Hike.Synth.empty ~types:kinds.retype [ sub ] in
        check "TYPES-34 the store is addressed through inttoptr"
          (contains_substring ir "inttoptr"));

    pin "TYPES-35"
      "rodata + index: the base is a pointer, the module address is the \
       GEP off its global, and the index stays an integer"
      (fun () ->
        let synth, g = Hike_synth.mint_module_addr ~addr_bits:64 0x4010L Hike_synth.empty in
        let b = int_param 2 and k = callee_saved 0 and a = int_ret 0 in
        let m = memv "types35_m" in
        let c = Var.create ~is_virtual:false ~fresh:false "types35_c" (Type.Imm 1) in
        let n x = Bil.Int (Cbat_word.to_word (w64 x)) in
        let raw, _ =
          raw_sub_of "types35"
            [ [ Def.create b (Bil.Var g) ],
              [ (2, fun t -> mk_jmp_to t (Bil.Var c)); (1, mk_goto) ];
              [ Def.create k (n 0) ], [ (3, mk_goto) ];
              [ Def.create k (n 8) ], [ (3, mk_goto) ];
              [ Def.create a
                  (Bil.Load (Bil.Var m, Bil.BinOp (Bil.PLUS, Bil.Var b, Bil.Var k),
                             LittleEndian, `r64)) ],
              [ (4, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let sub = ssa_of ~synth raw in
        let meta = { B2l.sm_type = Hike.Stack_model.Data; sm_access = Hike_section.Writable;
                     sm_lo = 0x4000L; sm_hi = 0x401fL; sm_words = 4;
                     sm_image = Some (Bytes.make 32 '\000'); sm_copy_relocs = [] } in
        let comp = { Hike.Stack_model.comp_id = 7; sec_lo = 0x4000L;
                     sec_hi = 0x401fL; lo_w = 1; hi_w = 3; typed_w = 8 } in
        let spec = { empty_spec with spec_sections = [ Some meta ];
                                     spec_comps = [ comp ] } in
        Hike_origin.Regions.install [ (Hike_section.Rodata, 0x4000L, 0x401fL) ];
        Fun.protect ~finally:(fun () -> Hike_origin.Regions.install [])
          (fun () ->
        let kinds = use_kinds ~synth [ sub ] in
        check "TYPES-35 the index is an integer"
          (not (kinds.is_ptr_def "types35" k));
        check "TYPES-35 the base is a pointer" (kinds.is_ptr_def "types35" b);
        (* The emission takes the pre-SSA program: the pipeline builds
           the SSA form, and the analysis's stamps ride its defs. *)
        let _, stamped, _ = fixture_facts ~synth [ sub ] in
        let pre = Base.List.map ~f:Hike.Ssa.unssa_sub stamped in
        let ir = emit_ir_spec ~synth ~types:kinds.retype spec pre in
        check "TYPES-35 the module address is the GEP off its global"
          (contains_substring ir "getelementptr inbounds (i8, ptr @sec_comp_7")));

    (* The leaf's pointer argument is consumed by the middle sub, whose
       own pointer argument is then consumed by the top sub. *)
    pin "TYPES-37"
      "a leaf's pointer-argument contract propagates through its callers"
      (fun () ->
        let rdi = int_param 0 in
        let m = memv "types37_m" in
        let n x = Bil.Int (Cbat_word.to_word (w64 x)) in
        let call_to callee t =
          Jmp.create
            (Call
               (Call.create ~return:(Label.direct t)
                  ~target:(Label.direct (Term.tid callee)) ()))
        in
        let leaf, _ =
          sub_of "types37_leaf"
            [ [ Def.create m
                  (Bil.Store (Bil.Var m, Bil.Var rdi, n 1, LittleEndian, `r64)) ],
              [ (1, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let mid, _ =
          sub_of "types37_mid"
            [ [ Def.create rdi (Bil.Var rdi) ],
              [ (1, fun t -> call_to leaf t) ];
              [], [ (0, mk_ret) ] ]
        in
        let top, _ =
          sub_of "types37_top"
            [ [ Def.create rdi (Bil.Var sp) ],
              [ (1, fun t -> call_to mid t) ];
              [], [ (0, mk_ret) ] ]
        in
        let kinds = use_kinds ~synth:Hike.Synth.empty [ top; mid; leaf ] in
        check "TYPES-37 the leaf parameter is a pointer"
          (kinds.is_ptr_lane "types37_leaf" rdi);
        check "TYPES-37 the middle parameter is a pointer"
          (kinds.is_ptr_lane "types37_mid" rdi));

    (* A caller's actual pointer does not change the callee's contract. *)
    pin "TYPES-38"
      "unproven callee operands keep their integer contracts, whatever \
       the calling depth or sub order"
      (fun () ->
        let rdi = int_param 0 and rsi = int_param 1 and rax = int_ret 0 in
        let m = memv "types38_m" in
        let n x = Bil.Int (Cbat_word.to_word (w64 x)) in
        let call_to callee t =
          Jmp.create
            (Call
               (Call.create ~return:(Label.direct t)
                  ~target:(Label.direct (Term.tid callee)) ()))
        in
        let f, _ =
          sub_of "types38_f"
            [ [ Def.create rax (Bil.BinOp (Bil.PLUS, Bil.Var rdi, Bil.Var rsi));
                Def.create m
                  (Bil.Store (Bil.Var m, Bil.Var rax, n 1, LittleEndian, `r64)) ],
              [ (1, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let mid, _ =
          sub_of "types38_mid"
            [ [], [ (1, fun t -> call_to f t) ]; [], [ (0, mk_ret) ] ]
        in
        let top_via callee name =
          fst
            (sub_of name
               [ [ Def.create rsi (Bil.Var sp) ],
                 [ (1, fun t -> call_to callee t) ];
                 [], [ (0, mk_ret) ] ])
        in
        let direct = top_via f "types38_top_f" in
        let chain = top_via mid "types38_top_mid" in
        let observe subs =
          let k = use_kinds ~synth:Hike.Synth.empty subs in
          (k.is_ptr_lane "types38_f" rsi, k.is_ptr_lane "types38_f" rdi)
        in
        let expect = (false, false) in
        check "TYPES-38 direct caller preserves the contract"
          (observe [ direct; f ] = expect);
        check "TYPES-38 indirect caller preserves the contract"
          (observe [ chain; mid; f ] = expect);
        check "TYPES-38 the same with the callee solved first"
          (observe [ f; mid; chain ] = expect));

    (* Program order cannot change a completed contract. *)
    pin "TYPES-39" "callee-first contracts are independent of term order"
      (fun () ->
        for seed = 0 to 29 do
          let subs = gen_program seed (2 + (seed mod 4)) in
          let _, _, base = analyse ~synth:Hike.Synth.empty subs in
          let same_in_order label ordered =
            let _, _, typed = analyse ~synth:Hike.Synth.empty ordered in
            check (Printf.sprintf "TYPES-39 %s order agrees (%d)" label seed)
              (same_types base typed)
          in
          same_in_order "reversed" (List.rev subs);
          same_in_order "rotated"
            (match subs with [] -> [] | h :: t -> t @ [ h ])
        done);

    (* Per-sub solver: growing seeds on one solver agree with fresh ones,
       and a repeated solve is a no-op. *)
    pin "TYPES-40"
      "a local solver resumed over growing seeds equals fresh solvers; \
       repeated program inference preserves the completed contracts"
      (fun () ->
        let rdi = int_param 0 and rsi = int_param 1 in
        for seed = 0 to 29 do
          let subs = gen_program (100 + seed) (2 + (seed mod 4)) in
          let facts, prog, typed = analyse ~synth:Hike.Synth.empty subs in
          Term.enum sub_t prog
          |> Seq.iter ~f:(fun sub ->
                 let seeds =
                   [ Var.Set.empty; Var.Set.singleton rdi;
                     Var.Set.of_list [ rdi; rsi ] ]
                 in
                 let resumed = Types.ptr_solver ~facts sub in
                 let used = Var.Set.empty in
                 Base.List.iter seeds ~f:(fun extra ->
                     let r = resumed ~extra ~used in
                     check "TYPES-40 resumed equals fresh"
                       (facts_equal r
                          (ptr_defs ~extra ~used ~facts sub));
                     check "TYPES-40 re-solving is a no-op"
                       (facts_equal r (resumed ~extra ~used))));
          let again =
            Types.type_program ~facts
              ~mem_typ:(Types.mem_type_of_target (x86 ())) typed
          in
          check "TYPES-40 repeated type inference is stable"
            (same_types typed again)
        done);

    (* Local evidence grows facts; callers preserve callee contracts. *)
    pin "TYPES-41"
      "local evidence grows pointer facts, and callers preserve contracts"
      (fun () ->
        let rdi = int_param 0 and rsi = int_param 1 in
        for seed = 0 to 29 do
          let subs = gen_program (200 + seed) (2 + (seed mod 4)) in
          let facts, prog, _ = analyse ~synth:Hike.Synth.empty subs in
          Term.enum sub_t prog
          |> Seq.iter ~f:(fun sub ->
                 let solve extra = ptr_defs ~extra ~facts sub in
                 let a = solve Var.Set.empty
                 and b = solve (Var.Set.singleton rdi)
                 and c = solve (Var.Set.of_list [ rdi; rsi ]) in
                 check "TYPES-41 seeds grow the vars"
                   (Core.Set.is_subset a.vars ~of_:b.vars
                    && Core.Set.is_subset b.vars ~of_:c.vars);
                 check "TYPES-41 seeds grow the pointer defs"
                   (Core.Set.is_subset a.def_tids ~of_:b.def_tids
                    && Core.Set.is_subset b.def_tids ~of_:c.def_tids));
          (* A caller's actual pointers do not retag its callees. *)
          let caller =
            fst
              (sub_of "gen_caller"
                 [ [ Def.create rdi (Bil.Var sp); Def.create rsi (Bil.Var sp) ],
                   [ (1,
                      fun t ->
                        Jmp.create
                          (Call
                             (Call.create ~return:(Label.direct t)
                                ~target:(Label.direct (Tid.for_name "gen0"))
                                ()))) ];
                   [], [ (0, mk_ret) ] ])
          in
          let _, _, p1 = analyse ~synth:Hike.Synth.empty subs in
          let _, _, p2 = analyse ~synth:Hike.Synth.empty (caller :: subs) in
          Term.enum sub_t p1
          |> Seq.iter ~f:(fun s ->
                 let nm = Sub.name s in
                 check "TYPES-41 a caller preserves every callee contract"
                   (Core.Set.equal
                      (ptr_names p1 nm)
                      (ptr_names p2 nm)))
        done;
        (* a module base against an unproven operand: [x + idx] only gains
           pointers when [x] is a module address *)
        let synth, g = Hike_synth.mint_module_addr ~addr_bits:64 0x4010L Hike_synth.empty in
        let a = int_ret 0 and idx = int_param 3 and p = int_param 4 in
        let m = memv "types41_m" in
        let names x =
          let sub =
            straight_sub "types41"
              [ Def.create a (Bil.BinOp (Bil.PLUS, Bil.Var x, Bil.Var idx));
                Def.create m
                  (Bil.Store (Bil.Var m, Bil.Var a,
                              Bil.Int (Cbat_word.to_word (w64 1)),
                              LittleEndian, `r64)) ]
          in
          let _, _, typed = analyse ~synth [ sub ] in
          ptr_names typed "types41"
        in
        let without = names p and with_base = names g in
        check "TYPES-41 an unproven operand is not a base"
          (not (Core.Set.mem without (Var.to_string p)));
        check "TYPES-41 a module base is a base, and the sum stays a pointer"
          (Core.Set.mem with_base (Var.to_string g)
           && Core.Set.length with_base >= Core.Set.length without));
  ]

let () = run "hike_types" tests
