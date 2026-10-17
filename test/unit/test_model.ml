(* The model/producer surface pins: the composed producer end-to-end, the
   layout from the finalized tree, stack-to-locals fission, the emitter's
   alloca shapes, the printable-run rule, and the Abi/Kb domains.  One
   Alcotest group per pin; each pin builds its own fixture, so no state
   crosses pins. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

module Abi = Hike.Abi

(* A register list names exactly [names]. *)
let names_are (vs : var list) (names : string list) : bool =
  Base.List.map vs ~f:(fun v -> Var.name v) = names

(* 64-bit literal word (native-int [w64] covers 63 bits only). *)

let minus_addr sp (off : int64) : exp =
  Bil.BinOp
    ( Bil.MINUS,
      Bil.Var sp,
      Bil.Int (Cbat_word.to_word (w64 (Int64.to_int off))) )

(* The model's 64-KiB below-entry floor plus the ABI entry word. *)
let tp_offset_equal (a : Hike.Stack_model.tp_offset) (b : Hike.Stack_model.tp_offset) =
  match (a, b) with
  | Tp_absent, Tp_absent -> true
  | Tp_nonlinear, Tp_nonlinear -> true
  | Tp_based x, Tp_based y -> Base.Option.equal Int64.equal x y
  | _ -> false


let tid_set (tids : tid list) : Tid.Set.t =
  List.fold_left (fun s t -> Core.Set.add s t) Tid.Set.empty tids

(* The def with the given tid in the sub. *)
let def_of_tid (sub : sub term) (dtid : tid) : def term option =
  Term.enum blk_t sub
  |> Seq.concat_map ~f:(Term.enum def_t)
  |> Seq.find ~f:(fun d -> Tid.equal (Term.tid d) dtid)

(* The def with the given lhs in the sub. *)
let tree_of (sub : sub term) =
  let ctx = fixture_ctx [ sub ] in
  Base.Option.value_exn
    (Core.Map.find ctx.Hike.Sections.sub_trees (Term.tid sub))

(* The fixture stamp: the dyn-alloc facts and the layout tag onto the
   terms; the def's slim tag is stamped at the fixture site (the emitter
   consumes no record). *)
let pr_c_m = memv "pr_c_m"

let mk_store off data (sz : size) : def term =
  Def.create pr_c_m
    (Bil.Store
       ( Bil.Var pr_c_m,
         minus_addr sp off,
         Bil.Int (Cbat_word.to_word (w64 data)),
         LittleEndian,
         sz ))

(* The [pr_b] layout fixture mem var, frame base, and MINUS/rbp load. *)
let pr_b_m = memv "pr_b_m"
let pr_b_rbp = v64 "RBP"

let pr_b_mk_ld name off : def term =
  Def.create (v64 name)
    (Bil.Load
       ( Bil.Var pr_b_m,
         Bil.BinOp
           ( Bil.MINUS,
             Bil.Var pr_b_rbp,
             Bil.Int (Cbat_word.to_word (q64 off)) ),
         LittleEndian,
         `r64 ))

(* The [pr_c] args fixture frame base and PLUS/rbp load. *)
let pr_c_rbp = v64 "RBP"

let pr_c_args_ld name off (sz : size) : def term =
  Def.create (v64 name)
    (Bil.Load
       ( Bil.Var pr_c_m,
         Bil.BinOp
           ( Bil.PLUS,
             Bil.Var pr_c_rbp,
             Bil.Int (Cbat_word.to_word (w64 off)) ),
         LittleEndian,
         sz ))

(* A SysV register by name. *)
let named n = Var.create ~is_virtual:false ~fresh:false n (Type.Imm 64)

let tests : unit Alcotest.test list =
  [
    (* Lane A: the producer record (the composed producer end-to-end). *)
    (* Lane B: the layout from the finalized tree ([layout_of_tree]). *)




    pin "MOD-10"
      "PR-B3: a plain-TOP identity member forces the residue region and selects the runtime stack"
      (fun () ->
        let abi = Hike.Abi.x86_64_sysv in
        let entry = Sm.segment_base in
        let d_rbp = Def.create pr_b_rbp (Bil.Var sp) in
        let u = v64 "pr_b_u" in
        let top_store =
          Def.create pr_b_m
            (Bil.Store
               ( Bil.Var pr_b_m,
                 Bil.Var u,
                 Bil.Int (Cbat_word.to_word (w64 1)),
                 LittleEndian,
                 `r64 ))
        in
        let sub2 =
          straight_sub "pr_b3" [ d_rbp; pr_b_mk_ld "pr_b3_t" 24L; top_store ]
        in
        let l2 =
          Hike.Sections.layout_of_tree ~word:8 ~entry ~abi ~sub:sub2
            (tree_of sub2)
        in
        check "MOD-10"
          (l2.Sm.runtime_residue
           && Base.List.exists l2.Sm.regions
                ~f:(fun { Sm.r_id = id; _ } -> Int.equal id 0)));



    (* Lane C: stack-to-locals fission. *)










    pin "MOD-17"
      "PR-C3: an Args access converts to the caller's slot pointer (the access's own cell)"
      (fun () ->
        let d_rbp = Def.create pr_c_rbp (Bil.Var sp) in
        let c3_rd = pr_c_args_ld "pr_c3_rd" 8 `r64 in
        let c3_st =
          Def.create pr_c_m
            (Bil.Store
               ( Bil.Var pr_c_m,
                 Bil.BinOp
                   ( Bil.PLUS,
                     Bil.Var pr_c_rbp,
                     Bil.Int (Cbat_word.to_word (w64 8)) ),
                 Bil.Int (Cbat_word.to_word (w64 9)),
                 LittleEndian,
                 `r64 ))
        in
        let c3 = straight_sub "pr_c3_abi" [ d_rbp; c3_rd; c3_st ] in
        let c3' = rewrite_one c3 in
        check_bound "MOD-17" (def_of_tid c3' (Term.tid c3_rd)) (fun d ->
            match Def.rhs d with
            | Bil.Load (_, Bil.Var a, _, _) -> Sm.is_arg_slot a
            | _ -> false));

    pin "MOD-18"
      "PR-N3: the split RMW's hoisted read addresses the caller's slot pointer"
      (fun () ->
        let n3_rbp = v64 "RBP" in
        let n3_d_rbp = Def.create n3_rbp (Bil.Var sp) in
        let n3_addr =
          Bil.BinOp
            ( Bil.PLUS,
              Bil.Var n3_rbp,
              Bil.Int (Cbat_word.to_word (w64 8)) )
        in
        let n3_rmw =
          Def.create (v64 "pr_n3_rmw")
            (Bil.Store
               ( Bil.Var pr_c_m,
                 n3_addr,
                 Bil.BinOp
                   ( Bil.PLUS,
                     Bil.Load (Bil.Var pr_c_m, n3_addr, LittleEndian, `r64),
                     Bil.Int (Cbat_word.to_word (w64 1)) ),
                 LittleEndian,
                 `r64 ))
        in
        let n3 =
          straight_sub "pr_n3_rmw" [ n3_d_rbp; n3_rmw ]
          |> fun sub -> Program.create ~subs:[ sub ] ()
          |> Hike.Split_mem.normalize
          |> Term.first sub_t
          |> Base.Option.value_exn
        in
        let n3' = rewrite_one n3 in
        let n3_defs =
          Term.enum blk_t n3'
          |> Seq.concat_map ~f:(Term.enum def_t)
          |> Seq.to_list
        in
        let is_original d =
          Base.List.exists [ n3_rbp; v64 "pr_n3_rmw" ] ~f:(Var.equal (Def.lhs d))
        in
        let slot_addressed =
          Base.List.exists n3_defs ~f:(fun d ->
              let vis =
                object
                  inherit [ bool ] Exp.visitor

                  method! visit_load ~mem:_ ~addr:addr_v _ _ acc =
                    acc
                    || (match addr_v with
                       | Bil.Var v -> Sm.is_arg_slot v
                       | _ -> false)

                  method! visit_store ~mem:_ ~addr:addr_v ~exp:_ _ _ acc =
                    acc
                    || (match addr_v with
                       | Bil.Var v -> Sm.is_arg_slot v
                       | _ -> false)
                end
              in
              vis#visit_exp (Def.rhs d) false)
        in
        check "MOD-18"
          (Base.List.exists n3_defs ~f:(fun d -> not (is_original d))
          && slot_addressed));

    pin "MOD-19"
      "PR-C4: the compiled guard is a value comparison — no memory node rides a cond"
      (fun () ->
        let c4_st = mk_store 16L 7 `r64 in
        let c4_t = v64 "pr_c4_t" in
        let c4_ld =
          Def.create c4_t
            (Bil.Load (Bil.Var pr_c_m, minus_addr sp 16L, LittleEndian, `r64))
        in
        let c4_zf = v1 "ZF" in
        let c4_flag =
          Def.create c4_zf
            (Bil.BinOp
               ( Bil.EQ,
                 Bil.Var c4_t,
                 Bil.Int (Cbat_word.to_word (w64 0)) ))
        in
        let c4_pre, _ =
          sub_of "pr_c4_cond"
            [ [ c4_st; c4_ld; c4_flag ],
              [ (2, fun t -> mk_jmp_to t (Bil.Var c4_zf)); (1, mk_goto) ];
              [], [ (0, mk_ret) ];
              [], [ (0, mk_ret) ] ]
        in
        let c4 = Hike.Jump.compile_sub jump_target c4_pre in
        let has_load (e : exp) : bool =
          let vis =
            object
              inherit [ bool ] Exp.visitor
              method! visit_load ~mem:_ ~addr:_ _ _ _ = true
            end
          in
          vis#visit_exp e false
        in
        check "MOD-19"
          (Term.enum blk_t c4
          |> Seq.concat_map ~f:(Term.enum jmp_t)
          |> Seq.for_all ~f:(fun j -> not (has_load (Jmp.cond j)))));

    pin "MOD-20" "PR-C4: the load def converts to the region mem and the guard reads its temp"
      (fun () ->
        let c4_st = mk_store 16L 7 `r64 in
        let c4_t = v64 "pr_c4_t" in
        let c4_ld =
          Def.create c4_t
            (Bil.Load (Bil.Var pr_c_m, minus_addr sp 16L, LittleEndian, `r64))
        in
        let c4_zf = v1 "ZF" in
        let c4_flag =
          Def.create c4_zf
            (Bil.BinOp
               ( Bil.EQ,
                 Bil.Var c4_t,
                 Bil.Int (Cbat_word.to_word (w64 0)) ))
        in
        let c4_pre, _ =
          sub_of "pr_c4_cond"
            [ [ c4_st; c4_ld; c4_flag ],
              [ (2, fun t -> mk_jmp_to t (Bil.Var c4_zf)); (1, mk_goto) ];
              [], [ (0, mk_ret) ];
              [], [ (0, mk_ret) ] ]
        in
        let c4 = Hike.Jump.compile_sub jump_target c4_pre in
        let c4' = rewrite_one c4 in
        check_bound "MOD-20" (def_of_tid c4' (Term.tid c4_ld)) (fun d ->
            match Def.rhs d with
            | Bil.Load (Bil.Var mem, _, _, _) ->
                Var.same mem (Sm.region_mem ~addr_bits:64 1)
                && (Term.enum blk_t c4'
                   |> Seq.concat_map ~f:(Term.enum jmp_t)
                   |> Seq.exists ~f:(fun j ->
                          match Jmp.cond j with
                          | Bil.BinOp (Bil.EQ, Bil.Var v, Bil.Int _) ->
                              Var.equal v c4_t
                          | _ -> false))
            | _ -> false));

    (* Lane D: the emitter's alloca shapes — the VLA lane, the SP Slot /
       stack_0 anchoring per storage class, and the frame-request clamp. *)




















    (* Lane E: the register/convention facts (Hike_abi, ADR 0008: SP is the
       only stack-semantics register, fp an ordinary callee-saved GPR) and
       the KB carrier's table semantics. *)
    pin "MOD-33" "PR-E1: the stack pointer is RSP, and only RSP (SP-only, ADR 0008)"
      (fun () ->
        let abi = Hike.Abi.x86_64_sysv in
        check "MOD-33"
          (Var.equal (Var.base abi.Abi.sp) (Var.base (named "RSP"))
          && Abi.is_sp abi (named "RSP")
          && not (Abi.is_sp abi (named "RBP"))));

    pin "MOD-34"
      "PR-E1: RBP is an ordinary callee-saved GPR — no frame-pointer fact exists"
      (fun () ->
        let abi = Hike.Abi.x86_64_sysv in
        check "MOD-34"
          (Abi.is_callee_saved abi (named "RBP")
          && names_are abi.Abi.callee_saved
               [ "RBX"; "RBP"; "R12"; "R13"; "R14"; "R15" ]));





    pin "MOD-37" "PR-E1: an unknown target falls back to the SysV record (total)"
      (fun () ->
        check "MOD-37"
          (Abi.is_sp
             (Hike.Abi.of_target Theory.Target.unknown)
             (named "RSP")
          && Hike.Abi.addr_size_bits Theory.Target.unknown = 0));

    pin "MOD-38" "PR-E1: the x86_64-gnu-elf target reifies RSP as the SP"
      (fun () ->
        let x86 = Theory.Target.of_string "x86_64-gnu-elf" in
        check "MOD-38"
          (Theory.Target.matches x86 "x86_64-gnu-elf"
          && Abi.is_sp (Hike.Abi.of_target x86) (Hike.Abi.sp x86)));

    pin "MOD-39"
      "PR-E1: the word size — SysV carries the x86-64 word; of_target derives bits/8"
      (fun () ->
        let abi = Hike.Abi.x86_64_sysv in
        let x86 = Theory.Target.of_string "x86_64-gnu-elf" in
        check "MOD-39"
          (abi.Abi.word = 8
          && Hike.Abi.((of_target x86).Abi.word) = Theory.Target.bits x86 / 8));

    (* The ONE thread-pointer offset rule: the classification and the
       width semantics.  A bare constant is a summand, never a base;
       casts keep an offset only when they preserve the value. *)
    pin "MOD-43"
      "the one TP offset rule: constants never base, casts preserve or drop"
      (fun () ->
        let open Bil in
        let open Hike.Stack_model in
        let tp = Hike.Abi.x86_64_sysv.Abi.thread_pointer in
        let w x = Cbat_word.to_word (w64 x) in
        let at e = tls_tp_offset ~tp e in
        let int x = Int (w x) in
        check "MOD-43.absent" (tp_offset_equal (at (Int (w 0x4038))) Tp_absent);
        check "MOD-43.self" (tp_offset_equal (at (Var tp)) (Tp_based (Some 0L)));
        check "MOD-43.offset"
          (tp_offset_equal (at (BinOp (MINUS, Var tp, int 8)))
             (Tp_based (Some (-8L))));
        check "MOD-43.identity-cast"
          (tp_offset_equal
             (at (Cast (SIGNED, 64, BinOp (MINUS, Var tp, int 8))))
             (Tp_based (Some (-8L))));
        check "MOD-43.width-cast"
          (tp_offset_equal
             (at (Cast (LOW, 32, BinOp (MINUS, Var tp, int 8))))
             Tp_nonlinear);
        (* (tp+1)-tp cancels to the constant 1: the value no longer
           reads the pointer, so the expression is absent. *)
        check "MOD-43.cancel"
          (tp_offset_equal
             (at (BinOp (Bil.MINUS, BinOp (PLUS, Var tp, int 1), Var tp)))
             Tp_absent);
        check "MOD-43.dynamic"
          (tp_offset_equal
             (at (BinOp (PLUS, Var tp, Var (v64 "RDX"))))
             (Tp_based None));
        check "MOD-43.signed-cast"
          (tp_offset_equal
             (at (BinOp (PLUS, Var tp,
                     Cast (SIGNED, 64, Int (Word.of_int ~width:32 (-8))))))
             (Tp_based (Some (-8L))));
        check "MOD-43.unsigned-cast"
          (tp_offset_equal
             (at (BinOp (PLUS, Var tp,
                     Cast (UNSIGNED, 64, Int (Word.of_int ~width:32 (-8))))))
             (Tp_based (Some 0xfffffff8L)));
        check "MOD-43.high-cast"
          (tp_offset_equal
             (at (BinOp (PLUS, Var tp,
                     Cast (HIGH, 64, Concat (int (-8), int 1)))))
             (Tp_based (Some (-8L))));
        check "MOD-43.low-cast"
          (tp_offset_equal
             (at (BinOp (PLUS, Var tp,
                     Cast (LOW, 64, Concat (int (-8), int 1)))))
             (Tp_based (Some 1L)));
        check "MOD-43.foreign"
          (tp_offset_equal (at (Var (v64 "RAX"))) Tp_absent));

    (* The ONE window denotation: stack-symbolic, ordered, entirely
       at/above the args base.  Both the promotion's window stamp and
       the pointer-kind storage read this rule. *)
    pin "MOD-40" "the caller-window denotation accepts exactly the window class"
      (fun () ->
        let module Ws = Cbat_vsa.WordSet in
        let word = 8 in
        let entry = Hike.Stack_model.segment_base in
        let win k = Ws.stack_word_i64 k in
        let is_win ws =
          Hike.Stack_model.is_window_denotation ~entry ~word ws
        in
        (* a stack-symbolic singleton at/above the args base (entry+word) *)
        check "MOD-40a: at/above the args base is window" (is_win (win 16L));
        (* below the entry line is this sub's own frame, never window *)
        check "MOD-40b: below-entry is not window" (not (is_win (win (-8L))));
        (* the boundary: the args base itself is window *)
        check "MOD-40c: the args base is window" (is_win (win 8L));
        (* a plain foreign constant carries no stack offsets: not window *)
        check "MOD-40d: a plain foreign word is not window"
          (not (is_win (Ws.singleton (Cbat_word.of_int ~width:64 0x400000))));
        (* two above-base offsets join into one window interval *)
        check "MOD-40e: an above-base interval is window"
          (is_win (Ws.union (win 16L) (win 32L)));
        (* the degraded plain arm at a window position is not proof: a
           window address must be stack-symbolic, not a plain word
           that happens to land in the band *)
        check "MOD-40f: a plain in-band word is not window"
          (not (is_win (Ws.singleton (Cbat_word.of_int64 ~width:64
                          (Int64.add entry 16L))))));

    pin "MOD-41"
      "term read sets use BAP terms and include ABI transfer reads"
      (fun () ->
        let module Model = Hike.Stack_model in
        let abi = Hike.Abi.x86_64_sysv in
        let rdi = Var.base (Base.List.hd_exn abi.Abi.int_param_regs) in
        let rax = named "RAX" in
        let rbx = named "RBX" in
        let dst = named "term_phi_dst" in
        let d = Def.create rdi (Bil.Var rax) in
        let p1 = Tid.create () in
        let p2 = Tid.create () in
        let phi =
          Phi.of_list dst [ (p1, Bil.Var rax); (p2, Bil.Var rbx) ]
        in
        let call =
          Jmp.create
            (Call (Call.create ~target:(Direct (Tid.create ())) ()))
        in
        let ret = Hike_return.create () in
        let call_reads =
          Core.Set.of_list
            (module Var)
            (Hike.Abi.param_regs abi @ abi.Abi.return_regs @ [ abi.Abi.sp ])
        in
        let block =
          let b = Blk.Builder.create () in
          Blk.Builder.add_def b d;
          ignore (Blk.Builder.add_jmp b call);
          Blk.Builder.result b
        in
        check "MOD-41 def/phi terms use BAP accessors"
          (Core.Set.equal (Model.reads (`Def d)) (Var.Set.singleton rax)
          && Core.Set.equal (Model.writes (`Def d)) (Var.Set.singleton rdi)
          && Core.Set.equal (Model.reads (`Phi phi))
               (Core.Set.of_list (module Var) [ rax; rbx ])
          && Core.Set.equal (Model.phi_reads_from phi p1)
               (Var.Set.singleton rax)
          && Core.Set.equal (Model.writes (`Phi phi)) (Var.Set.singleton dst));
        check "MOD-41 calls include implicit ABI reads"
          (Core.Set.equal (Model.reads (`Jmp call)) call_reads);
        check "MOD-41 calls write return registers; returns write none"
          (Core.Set.equal (Model.writes (`Jmp call))
                (Var.Set.of_list abi.Abi.return_regs)
           && Core.Set.is_empty (Model.writes (`Jmp ret)));
        check "MOD-41 returns include implicit ABI reads"
          (Core.Set.equal (Model.reads (`Jmp ret))
             (Core.Set.of_list (module Var)
                (abi.Abi.return_regs @ [ abi.Abi.sp ])));
        check "MOD-41 block uses respect local definitions"
          (Core.Set.equal (Blk.free_vars block)
             (Var.Set.singleton rax)));

    (* SP arithmetic is ordinary Stack arithmetic (ADR 0037). *)
    pin "MOD-44"
      "a runtime-sized descent from SP reads as the stack positions it stands for"
      (fun () ->
        let c = v1 "vla44_c" and t = v64 "vla44_t" in
        let k n = Bil.Int (Cbat_word.to_word (w64 n)) in
        let d_t =
          Def.create t (Bil.BinOp (Bil.MINUS, Bil.Var sp, Bil.Ite (Bil.Var c, k 16, k 32)))
        in
        let sub = straight_sub "vla44_redzone" [ d_t ] in
        let facts, sub = fixture_facts_sub sub in
        let blk = Term.first blk_t sub |> Base.Option.value_exn in
        check "MOD-44 the value is its stack positions"
          (match facts.Hike.Kb.denote ~blk (Bil.Var t) with
           | Ok ws ->
             Option.equal Hike_origin.equal (Cbat_vsa.WordSet.origin ws)
               (Some Hike_origin.Stack)
             && not (Cbat_vsa.WordSet.is_top ws)
           | Error _ -> false));

    pin "MOD-45"
      "an unbounded runtime SP decrement selects the runtime stack, and a bounded one keeps allocas"
      (fun () ->
        let rcx = v64 "mod45_rcx" in
        let m = memv "mod45_m" in
        let abi = Hike.Abi.x86_64_sysv in
        let layout name defs =
          let sub = straight_sub name defs in
          Hike.Sections.layout_of_tree ~word:8
            ~entry:Hike.Stack_model.segment_base ~abi ~sub (tree_of sub)
        in
        let store =
          Def.create m
            (Bil.Store
               ( Bil.Var m,
                 Bil.BinOp
                   (Bil.PLUS, Bil.Var sp, Bil.Int (Cbat_word.to_word (w64 8))),
                 Bil.Int (Cbat_word.to_word (Cbat_word.of_int ~width:32 5)),
                 LittleEndian,
                 `r32 ))
        in
        let dec = Def.create sp (Bil.BinOp (Bil.MINUS, Bil.Var sp, Bil.Var rcx)) in
        let masked =
          Def.create rcx
            (Bil.BinOp
               ( Bil.AND, Bil.Var rcx, Bil.Int (Cbat_word.to_word (w64 0xFF)) ))
        in
        check "MOD-45 unbounded"
          (layout "mod45_unb" [ dec; store ]).Sm.runtime_residue;
        check "MOD-45 bounded"
          (not (layout "mod45_bnd" [ masked; dec; store ]).Sm.runtime_residue));
  ]

let () = run "model" tests
