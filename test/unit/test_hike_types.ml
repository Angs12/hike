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
module Model = Hike__Hike_stack_model
module Abi = Hike.Abi

(* The real SysV convention (the module contract's [abi]). *)
let abi = Hike.Abi.x86_64_sysv

(* [Abi.t] is built on demand; target facts need the harness [init]. *)
let x86 () : Theory.Target.t = Theory.Target.of_string "x86_64-gnu-elf"
let unknown = Theory.Target.unknown

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
let main_sub () : sub term =
  fst (sub_of ~tid:(Tid.for_name "main") "main" [ [], [] ])

(* The program-level entries sign the sub's OWN [arg] terms; read them
   back as lanes. *)
let lanes_of_sub (sub : sub term) : (string * intent option * bool) list =
  Term.enum arg_t sub |> Base.Sequence.to_list |> lanes

let tests : unit Alcotest.test list =
  [
    pin "TYPES-01" "free_vars keeps registers and drops memory vars"
      (fun () ->
        let m = memv "t14_free_m" in
        let sub =
          straight_sub "t14_free"
            [ Def.create (v64 "t14_free_t")
                (Bil.Load
                   ( Bil.Var m,
                     Bil.Var (v64 "RDI"),
                     LittleEndian,
                     `r64 )) ]
        in
        check "TYPES-01"
          (Base.List.map (Hike.Split_blocks.free_regs sub) ~f:Var.name
           = [ "RDI" ]));

    pin "TYPES-02" "is_fp_returning: a YMM def on the epilogue path is an FP return"
      (fun () ->
        let ymm0 = Base.List.nth_exn abi.Abi.vector_param_regs 0 in
        check "TYPES-02" (Types.is_fp_returning ~abi (epilogue_sub ymm0)));

    pin "TYPES-03" "is_fp_returning: an integer return register is not an FP return"
      (fun () ->
        let rax = Base.List.nth_exn abi.Abi.return_regs 0 in
        check "TYPES-03" (not (Types.is_fp_returning ~abi (epilogue_sub rax))));

    pin "TYPES-04"
      "is_fp_returning: a value def off the epilogue path is not a return at all"
      (fun () ->
        let ymm0 = Base.List.nth_exn abi.Abi.vector_param_regs 0 in
        let sub, _ =
          sub_of "t14_noep"
            [ [ Def.create ymm0 (Bil.Var (v64 "t14_src")) ],
              [ (1, mk_goto) ];
              [], [ (2, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        check "TYPES-04" (not (Types.is_fp_returning ~abi sub)));

    pin "TYPES-05" "tag_lane: a plain [In] register lane is not a pointer"
      (fun () ->
        let rdi = v64 "RDI" in
        let a' = Types.tag_lane (Arg.create ~intent:In rdi (Bil.Var rdi)) in
        check "TYPES-05"
          (arg_name a' = "RDI" && Arg.intent a' = Some In && not (is_ptr a')));

    pin "TYPES-06" "tag_lane: a [Both] intent lane is a pointer"
      (fun () ->
        let rdi = v64 "RDI" in
        let a' = Types.tag_lane (Arg.create ~intent:Both rdi (Bil.Var rdi)) in
        check "TYPES-06" (Arg.intent a' = Some Both && is_ptr a'));

    pin "TYPES-07" "tag_lane: a memory-typed lhs lane is a pointer"
      (fun () ->
        let m = memv "t14_tag_m" in
        let a' = Types.tag_lane (Arg.create ~intent:In m (Bil.Var m)) in
        check "TYPES-07" (is_ptr a'));

    pin "TYPES-08" "tag_lane: the caller-window lane is a pointer"
      (fun () ->
        let w = Model.hike_window_var ~word:8 in
        let a' = Types.tag_lane (Arg.create ~intent:In w (Bil.Var w)) in
        check "TYPES-08" (is_ptr a'));

    pin "TYPES-09"
      "compute_sub_sig: x86_64 returns RAX/RDX [Out]; a lane-free sub has no args"
      (fun () ->
        let sub = plain_sub "t14_ret" [] in
        let rets, args = Types.compute_sub_sig (x86 ()) sub in
        check "TYPES-09"
          (arg_names rets = [ "RAX"; "RDX" ]
          && Base.List.for_all rets ~f:(fun a ->
                 Arg.intent a = Some Out && not (is_ptr a))
          && args = []));

    pin "TYPES-10" "compute_sub_sig: an unknown target answers no returns"
      (fun () ->
        let sub = plain_sub "t14_ret" [] in
        let rets, args = Types.compute_sub_sig unknown sub in
        check "TYPES-10" (rets = [] && args = []));

    pin "TYPES-11"
      "compute_sub_sig: free registers become [In] args in parameter order"
      (fun () ->
        let rdi = v64 "RDI" in
        let rsi = v64 "RSI" in
        let sub =
          plain_sub "t14_args"
            [ Def.create (v64 "t14_a") (Bil.Var rsi);
              Def.create (v64 "t14_b") (Bil.Var rdi) ]
        in
        let _, args = Types.compute_sub_sig unknown sub in
        check "TYPES-11" (arg_names args = [ "RDI"; "RSI" ] && for_all_in args));

    pin "TYPES-12"
      "compute_sub_sig: SP, the thread pointer, and callee-saved registers are \
       not argument lanes"
      (fun () ->
        let sub =
          plain_sub "t14_filt"
            [ Def.create (v64 "t14_f1") (Bil.Var (v64 "RSP"));
              Def.create (v64 "t14_f2") (Bil.Var (v64 "RBX"));
              Def.create (v64 "t14_f3") (Bil.Var (v64 "FS_BASE")) ]
        in
        let _, args = Types.compute_sub_sig unknown sub in
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
        let _, args = Types.compute_sub_sig unknown sub in
        check "TYPES-13" (args = []));

    pin "TYPES-14"
      "compute_sub_sig: a call with no argument lanes takes the full \
       parameter-register signature"
      (fun () ->
        let sub, _ =
          sub_of "t14_plt"
            [ [],
              [ (1,
                 fun t ->
                   Jmp.create
                     (Call
                        (Call.create ~return:(Label.direct t)
                           ~target:
                             (Indirect (Bil.Int (Cbat_word.to_word (w64 0))))
                           ()))) ];
              [], [] ]
        in
        let _, args = Types.compute_sub_sig unknown sub in
        check "TYPES-14"
          (arg_names args = Base.List.map (Abi.param_regs abi) ~f:Var.name
          && for_all_in args));

    pin "TYPES-15"
      "compute_sub_sig: [@main] keeps the fixed RDI/RSI signature"
      (fun () ->
        let rets, args = Types.compute_sub_sig unknown (main_sub ()) in
        check "TYPES-15"
          (rets = [] && arg_names args = [ "RDI"; "RSI" ] && for_all_in args));

    pin "TYPES-16"
      "compute_sub_sig: a window-param layout carries the caller window as a \
       pointer [In] lane"
      (fun () ->
        let layout : Sm.sub_layout =
          { regions = []; window_param = true }
        in
        let sub = Sm.set_layout layout (plain_sub "t14_window" []) in
        let rets, args = Types.compute_sub_sig unknown sub in
        check "TYPES-16"
          (rets = []
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
        let rdi = v64 "RDI" in
        let y = v64 "intrinsic:testsig_y" in
        let sub =
          Term.set_attr
            (straight_sub "intrinsic:testsig" [ Def.create y (Bil.Var rdi) ])
            Sub.intrinsic ()
        in
        let rets, args = Types.compute_sub_sig unknown sub in
        check "TYPES-17"
          (arg_names args = [ "RDI" ]
          && for_all_in args
          && arg_names rets = [ "intrinsic:testsig_y" ]
          && Base.List.for_all rets ~f:(fun a ->
                 Arg.intent a = Some Out && not (is_ptr a))));

    pin "TYPES-18"
      "compute_sub_sig: an FP-returning sub appends the YMM0 [Out] lane"
      (fun () ->
        let ymm0 = Base.List.nth_exn abi.Abi.vector_param_regs 0 in
        let rets, _ = Types.compute_sub_sig (x86 ()) (epilogue_sub ymm0) in
        check "TYPES-18" (arg_names rets = [ "RAX"; "RDX"; "YMM0" ]));

    pin "TYPES-19"
      "sign_program: the computed (rets @ args) lanes land on the sub's own \
       arg terms"
      (fun () ->
        let rdi = v64 "RDI" in
        let sub =
          straight_sub "t14_sign" [ Def.create (v64 "t14_su") (Bil.Var rdi) ]
        in
        let rets, args = Types.compute_sub_sig (x86 ()) sub in
        let prog = Program.create ~subs:[ sub ] () in
        let prog' = Types.sign_program ~target:(x86 ()) prog in
        let sub' = Term.first sub_t prog' |> Base.Option.value_exn in
        check "TYPES-19" (lanes_of_sub sub' = lanes (rets @ args)));

    pin "TYPES-20" "sign_run: the project entry signs the project's program"
      (fun () ->
        let rsi = v64 "RSI" in
        let sub =
          straight_sub "t14_run" [ Def.create (v64 "t14_ru") (Bil.Var rsi) ]
        in
        let target = x86 () in
        let prog = Program.create ~subs:[ sub ] () in
        let proj = Project.with_program (Project.empty target) prog in
        let proj' = Types.sign_run proj in
        let sub' =
          Term.first sub_t (Project.program proj') |> Base.Option.value_exn
        in
        let rets, args = Types.compute_sub_sig target sub in
        check "TYPES-20"
          (Theory.Target.matches (Project.target proj') "x86_64-gnu-elf"
          && lanes_of_sub sub' = lanes (rets @ args)));

    pin "TYPES-21"
      "a call preserves the complete native integer-parameter input ABI"
      (fun () ->
        let rsi = v64 "RSI" in
        let sub, _ =
          sub_of "t14_call_args"
            [ [ Def.create (v64 "t14_call_t") (Bil.Var rsi) ],
              [ (1,
                 fun t ->
                   Jmp.create
                     (Call
                        (Call.create ~return:(Label.direct t)
                           ~target:(Label.direct (Tid.for_name "callee")) ()))) ];
              [], [ (0, mk_ret) ] ]
        in
        let _, args = Types.compute_sub_sig unknown sub in
        check "TYPES-21"
          (arg_names args = Base.List.map abi.Abi.int_param_regs ~f:Var.name
          && for_all_in args));

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
        let prog' = Types.sign_program ~target:unknown prog in
        let sub' = Term.first sub_t prog' |> Base.Option.value_exn in
        check "TYPES-22"
          (arg_names (Model.sig_args sub')
           = Base.List.map (Abi.param_regs abi) ~f:Var.name));

    pin "TYPES-23"
      "a canonical direct return does not add synthetic call lanes"
      (fun () ->
        let sub, _ =
          sub_of "t14_terminal_return" [ [], [ (0, mk_ret) ] ]
        in
        let prog = Program.create ~subs:[ sub ] () in
        let prog' = Types.sign_program ~target:unknown prog in
        let sub' = Term.first sub_t prog' |> Base.Option.value_exn in
        check "TYPES-23" (Model.sig_args sub' = []));
    pin "KIND-01"
      "a def computing a stack address is ptr-kind (its denotation is \
       stack-resident)"
      (fun () ->
        let rbp = v64 "RBP" and rax = v64 "RAX" in
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

    pin "KIND-02" "a plain integer def is not ptr-kind" (fun () ->
        let rcx = v64 "RCX" in
        let sub =
          straight_sub "k02"
            [ Def.create rcx (Bil.Int (Cbat_word.to_word (w64 5))) ]
        in
        let facts, stamped = fixture_facts_sub sub in
        let pf = Types.ptr_defs ~facts stamped in
        let def =
          Term.enum blk_t stamped
          |> Seq.concat_map ~f:(Term.enum def_t)
          |> Seq.find ~f:(fun d -> Var.same (Def.lhs d) rcx)
        in
        check "KIND-02"
          (match def with
           | Some d -> not (Core.Set.mem pf.Types.def_tids (Term.tid d))
           | None -> false));

    pin "KIND-03" "stamp_ptr_kinds round-trips through def_ptr_kind"
      (fun () ->
        let rax = v64 "RAX" in
        let sub =
          straight_sub "k03"
            [ Def.create rax (Bil.Int (Cbat_word.to_word (w64 1))) ]
        in
        let d = Term.enum blk_t sub |> Seq.concat_map ~f:(Term.enum def_t) |> Seq.hd_exn in
        let sub' =
          Hike.Def_slots.stamp_ptr_kinds ~ptr_tids:(Tid.Set.singleton (Term.tid d))
            sub
        in
        let d' =
          Term.enum blk_t sub'
          |> Seq.concat_map ~f:(Term.enum def_t)
          |> Seq.hd_exn
        in
        check "KIND-03" (Hike.Def_slots.def_ptr_kind d'));

    pin "KIND-04"
      "a callee parameter passed a stack address is ptr-kind" (fun () ->
        let rdi = v64 "RDI" in
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
        let pks = Types.param_kinds ~facts ~sub_of:sub_of_m prog in
        check "KIND-04"
          (match Core.Map.find pks (Term.tid callee) with
           | Some s -> Core.Set.mem s rdi
           | None -> false));
  ]

let () = run "hike_types" tests
