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

let arg_name (a : Arg.t) : string = Var.name (Arg.lhs a)
let arg_names (l : Arg.t list) : string list = Base.List.map l ~f:arg_name
let is_ptr (a : Arg.t) : bool = Model.is_ptr_arg a

(* The observable lane: name, intent, pointer-tag. *)
let lane (a : Arg.t) : string * intent option * bool =
  (arg_name a, Arg.intent a, is_ptr a)

let lanes (l : Arg.t list) : (string * intent option * bool) list =
  Base.List.map l ~f:lane

let for_all_in (l : Arg.t list) : bool =
  Base.List.for_all l ~f:(fun a -> Arg.intent a = Some In && not (is_ptr a))

(* One block, no calls, so the PLT signature rule cannot fire. *)
let plain_sub (name : string) (defs : def term list) : sub term =
  fst (sub_of name [ defs, [] ])

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

(* A real [@main]: [Tid.for_name] prefixes ["@"], so ["main"] names the tid
   [@main] — the name the fixed signature reads. *)
let tests : unit Alcotest.test list =
  [


    pin "TYPES-05" "tag_lane: a plain [In] register lane is not a pointer"
      (fun () ->
        let rdi = int_param 0 in
        let a' = Types.tag_lane (Arg.create ~intent:In rdi (Bil.Var rdi)) in
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
        let _, args = Types.compute_sub_sig ~free_vars:(Types.free_regs_of_sub ~target:(x86 ()) sub) (x86 ()) sub in
        check "TYPES-12" (args = []));

    pin "TYPES-13"
      "compute_sub_sig: intrinsic-target and promoted names are not argument \
       lanes"
      (fun () ->
        let sub =
          plain_sub "t14_prom"
            [ Def.create (v64 "t14_p1") (Bil.Var (v64 "hike_slot0"));
              Def.create (v64 "t14_p2") (Bil.Var (v64 "hike_arg2"));
              Def.create (v64 "t14_p3") (Bil.Var (v64 "intrinsic:foo")) ]
        in
        let _, args = Types.compute_sub_sig ~free_vars:(Types.free_regs_of_sub ~target:(x86 ()) sub) (x86 ()) sub in
        check "TYPES-13" (args = []));





    pin "TYPES-16"
      "compute_sub_sig: a window-param layout carries the caller window as a \
       pointer [In] lane"
      (fun () ->
        let layout : Sm.sub_layout =
          { regions = []; window_param = true; runtime_residue = false }
        in
        let sub = Sm.set_layout layout (plain_sub "t14_window" []) in
        let rets, args = Types.compute_sub_sig ~free_vars:(Types.free_regs_of_sub ~target:(x86 ()) sub) (x86 ()) sub in
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
            (straight_sub "intrinsic:testsig" [ Def.create y (Bil.Var rdi) ])
            Sub.intrinsic ()
        in
        let rets, args = Types.compute_sub_sig ~free_vars:(Types.free_regs_of_sub ~target:(x86 ()) sub) (x86 ()) sub in
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
        let rets, _ = Types.compute_sub_sig ~free_vars:(Types.free_regs_of_sub ~target:(x86 ()) (epilogue_sub ymm0)) (x86 ()) (epilogue_sub ymm0) in
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
        let prog' = Types.sign_program ~target:(x86 ()) prog in
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
        let prog' = Types.sign_program ~target:(x86 ()) prog in
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
        let facts, stamped = fixture_facts_sub sub in
        let pf = Types.ptr_defs ~facts stamped in
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
        let rdi1 = Var.with_index rdi 1 in
        let rbx1 = Var.with_index (callee_saved 0) 1 in
        let rcx1 = Var.with_index (int_param 3) 1 in
        let eight = Bil.Int (Cbat_word.to_word (w64 8)) in
        let sub =
          straight_sub "k05"
            [ Def.create rcx1 (Bil.BinOp (Bil.PLUS, Bil.Var rdi, eight));
              Def.create rdi1 (Bil.Int (Cbat_word.to_word (w64 48)));
              Def.create rbx1 (Bil.BinOp (Bil.PLUS, Bil.Var rdi1, eight)) ]
        in
        let facts, stamped = fixture_facts_sub sub in
        let pf =
          Types.ptr_defs ~extra:(Var.Set.singleton rdi) ~facts stamped
        in
        check "KIND-05"
          (Core.Set.mem pf.Types.vars rcx1
           && not (Core.Set.mem pf.Types.vars rdi1)
           && not (Core.Set.mem pf.Types.vars rbx1)));

    pin "KIND-04"
      "a callee parameter passed a stack address is ptr-kind" (fun () ->
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
        let facts, stamped, _ = fixture_facts [ caller; callee ] in
        let prog = Program.create ~subs:stamped () in
        let sub_of_m = Types.sub_of_program prog in
        let pks, _ = Types.ptr_kinds ~facts ~sub_of:sub_of_m prog in
        let mem_typ = Types.mem_type_of_target facts.Hike.Kb.target in
        let prog =
          Term.map sub_t prog ~f:(fun sub ->
              let ptr_vars =
                Core.Map.find pks (Term.tid sub)
                |> Base.Option.value ~default:Var.Set.empty
              in
              Types.retype_sub ~mem_typ ~ptr_vars ~ptr_rets:Var.Set.empty sub)
        in
        let callee =
          Core.Map.find (Types.sub_of_program prog) (Term.tid callee)
          |> Base.Option.value_exn
        in
        let arg =
          Term.enum arg_t callee
          |> Seq.find ~f:(fun a -> Var.same (Arg.lhs a) rdi)
          |> Base.Option.value_exn
        in
        check "KIND-04"
          (match Core.Map.find pks (Term.tid callee) with
           | Some s ->
             Core.Set.mem s rdi
             && Var.typ (Arg.lhs arg) = mem_typ
           | None -> false));

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
        let signed = Types.sign_sub ~target sub in
        let inputs = Base.List.map (Model.sig_args signed) ~f:Arg.lhs in
        let has v = Base.List.exists inputs ~f:(Var.same v) in
        check "TYPES-25 the parameter and the lane unwritten on one path are inputs"
          (has rdi && has rdx);
        check "TYPES-25 a lane written on every path is not an input"
          (not (has rax));
        check "TYPES-25 every input beyond the parameter is an ABI return register"
          (Base.List.for_all inputs ~f:(fun v ->
               Var.same v rdi || Abi.is_return_reg (Abi.of_target target) v));
        let prog = Hike.Ssa.ssa_program ~target
            (Program.create ~subs:[ signed ] ()) in
        let ssa = Term.first sub_t prog |> Base.Option.value_exn in
        let join = Term.find blk_t ssa tids.(2) |> Base.Option.value_exn in
        let phi = Term.enum phi_t join
            |> Seq.find ~f:(fun p -> Var.same (Var.base (Phi.lhs p)) rdx)
            |> Base.Option.value_exn in
        check "TYPES-25 preserved incoming"
          (Phi.values phi |> Seq.exists ~f:(fun (src, e) ->
               Tid.equal src tids.(0) && Exp.equal e (Bil.Var rdx)));
        let overwritten = plain_sub "overwrite_return"
            [ Def.create rdx (Bil.Int (Cbat_word.to_word (w64 7))) ]
            |> Types.sign_sub ~target in
        check "TYPES-25 overwritten lane"
          (not (Model.sig_args overwritten |> Base.List.exists ~f:(fun a ->
               Var.same (Arg.lhs a) rdx)));
        let untouched, _ = sub_of "untouched_return" [ [], [ (0, mk_ret) ] ] in
        let caller, _ = sub_of "forward_return"
            [ [], [ (1, fun t -> Jmp.create (Call
                  (Call.create ~return:(Direct t)
                     ~target:(Direct (Term.tid untouched)) ()))) ];
              [], [ (0, mk_ret) ] ] in
        let caller = Types.sign_sub ~target caller in
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
        let prog = Types.sign_program ~target:(x86 ()) (Program.create ~subs:[ sub ] ()) in
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
        let prog2 = Types.sign_program ~target:(x86 ()) (Program.create ~subs:[ reader ] ()) in
        let stamped2 = Term.enum sub_t prog2 |> Seq.hd_exn in
        check "TYPES-24"
          (Model.is_plt_trampoline_sub stamped
          && not (Model.is_plt_trampoline_sub stamped2)));
  ]

let () = run "hike_types" tests
