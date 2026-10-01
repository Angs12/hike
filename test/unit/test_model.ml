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
let stack_floor_bytes = Int64.mul 64L 1024L
let residue_index = Int64.add stack_floor_bytes 8L
let unbounded_residue_bytes = Int64.mul 2L residue_index

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
    pin "MOD-01"
      "PR-A5: neither the literal decrement nor the chain-resolved constant is the event"
      (fun () ->
        let a5_rbx = v64 "pr_a5_rbx" in
        let a5_lit =
          Def.create sp
            (Bil.BinOp
               ( Bil.MINUS,
                 Bil.Var sp,
                 Bil.Int (Cbat_word.to_word (w64 0x28)) ))
        in
        let a5_rbx_def =
          Def.create a5_rbx (Bil.Int (Cbat_word.to_word (w64 0x80)))
        in
        let a5_bnd =
          Def.create sp (Bil.BinOp (Bil.MINUS, Bil.Var sp, Bil.Var a5_rbx))
        in
        let a5 = straight_sub "pr_a5_vla" [ a5_lit; a5_rbx_def; a5_bnd ] in
        let facts, a5 = fixture_facts_sub a5 in
        check "MOD-01"
          (Core.Set.is_empty
             (Hike.Sections.dynamic_alloc_tids_of ~facts a5)));

    pin "MOD-02"
      "PR-A5: the runtime-unbounded decrement is the event; the literal decrement is not"
      (fun () ->
        let a5_rcx = v64 "pr_a5_rcx" in
        let a5_vla =
          Def.create sp (Bil.BinOp (Bil.MINUS, Bil.Var sp, Bil.Var a5_rcx))
        in
        let a5u = straight_sub "pr_a5_vla_unb" [ a5_vla ] in
        let facts, a5u = fixture_facts_sub a5u in
        let a5u_events =
          Hike.Sections.dynamic_alloc_tids_of ~facts a5u
        in
        check "MOD-02"
          (Core.Set.equal a5u_events (tid_set [ Term.tid a5_vla ])));

    pin "MOD-03"
      "PR-A5: the dynamic-allocation fact rides the def's value through the stamp"
      (fun () ->
        let a5_rcx = v64 "pr_a5_rcx" in
        let a5_vla =
          Def.create sp (Bil.BinOp (Bil.MINUS, Bil.Var sp, Bil.Var a5_rcx))
        in
        let a5u = straight_sub "pr_a5_vla_unb" [ a5_vla ] in
        let facts, a5u = fixture_facts_sub a5u in
        let a5u_events =
          Hike.Sections.dynamic_alloc_tids_of ~facts a5u
        in
        let a5_stamped =
          Ds.stamp_dyn_allocs ~dynamic_alloc_tids:a5u_events a5u
        in
        check "MOD-03"
          (Ds.def_is_dyn_alloc
             (Base.Option.value_exn
                (def_of_tid a5_stamped (Term.tid a5_vla)))));

    pin "MOD-04"
      "PR-A5c: a VLA spelled through TWO temps is still the event (the chain resolves through the sequential state)"
      (fun () ->
        let a5_rcx = v64 "pr_a5_rcx" in
        let a5c_t1 = v64 "pr_a5c_t1" in
        let a5c_t2 = v64 "pr_a5c_t2" in
        let a5c_d1 =
          Def.create a5c_t1
            (Bil.BinOp (Bil.MINUS, Bil.Var sp, Bil.Var a5_rcx))
        in
        let a5c_d2 = Def.create a5c_t2 (Bil.Var a5c_t1) in
        let a5c_sp = Def.create sp (Bil.Var a5c_t2) in
        let a5c = straight_sub "pr_a5c_chain" [ a5c_d1; a5c_d2; a5c_sp ] in
        let facts, a5c = fixture_facts_sub a5c in
        check "MOD-04"
          (Core.Set.equal
             (Hike.Sections.dynamic_alloc_tids_of ~facts a5c)
             (tid_set [ Term.tid a5c_sp ])));

    pin "MOD-05"
      "PR-A5d: the lea-computed adjustment (a negative size ADDED) is the event"
      (fun () ->
        let a5_rcx = v64 "pr_a5_rcx" in
        let a5d_t = v64 "pr_a5d_t" in
        let a5d_d1 =
          Def.create a5d_t
            (Bil.BinOp
               ( Bil.MINUS,
                 Bil.Int (Cbat_word.to_word (w64 0)),
                 Bil.Var a5_rcx ))
        in
        let a5d_sp =
          Def.create sp (Bil.BinOp (Bil.PLUS, Bil.Var sp, Bil.Var a5d_t))
        in
        let a5d = straight_sub "pr_a5d_plus" [ a5d_d1; a5d_sp ] in
        let facts, a5d = fixture_facts_sub a5d in
        check "MOD-05"
          (Core.Set.equal
             (Hike.Sections.dynamic_alloc_tids_of ~facts a5d)
             (tid_set [ Term.tid a5d_sp ])));

    pin "MOD-06"
      "PR-A5e: a provably-above PLUS adjustment is not the VLA event (the value's direction)"
      (fun () ->
        let a5e_y = v64 "pr_a5e_y" in
        let a5e_r8 = v64 "pr_a5e_r8" in
        let a5e_y_def =
          Def.create a5e_y
            (Bil.BinOp
               ( Bil.AND,
                 Bil.Var a5e_r8,
                 Bil.Int (Cbat_word.to_word (w64 63)) ))
        in
        let a5e_sp =
          Def.create sp (Bil.BinOp (Bil.PLUS, Bil.Var sp, Bil.Var a5e_y))
        in
        let a5e = straight_sub "pr_a5e_plus_above" [ a5e_y_def; a5e_sp ] in
        let fa5e, a5e = fixture_facts_sub a5e in
        check "MOD-06"
          (Core.Set.is_empty
             (Hike.Sections.dynamic_alloc_tids_of ~facts:fa5e a5e)));

    pin "MOD-07"
      "PR-A5b: a VLA in a looping sub is the event — the widened loop does not hide it"
      (fun () ->
        let a5_rcx = v64 "pr_a5_rcx" in
        let a5b_loop =
          Bil.BinOp
            (Bil.LT, Bil.Var a5_rcx, Bil.Int (Cbat_word.to_word (w64 5)))
        in
        let a5b, _ =
          sub_of "pr_a5b_loop_vla"
            [ [ Def.create sp
                  (Bil.BinOp (Bil.MINUS, Bil.Var sp, Bil.Var a5_rcx)) ],
              [ (1, mk_goto) ];
              [],
              [ (2, fun t -> mk_jmp_to t a5b_loop);
                (3, fun t -> mk_jmp_to t (Bil.UnOp (Bil.NOT, a5b_loop))) ];
              [], [ (1, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let a5b_body_sp =
          Term.enum blk_t a5b
          |> Seq.find_map ~f:(fun blk ->
                 Term.enum def_t blk
                 |> Seq.find_map ~f:(fun d ->
                        if Var.same (Def.lhs d) sp then Some (Term.tid d)
                        else None))
          |> Base.Option.value_exn
        in
        let facts, a5b = fixture_facts_sub a5b in
        let a5b_events =
          Hike.Sections.dynamic_alloc_tids_of ~facts a5b
        in
        check "MOD-07"
          (Core.Set.equal a5b_events (tid_set [ a5b_body_sp ])));

    (* Lane B: the layout from the finalized tree ([layout_of_tree]). *)




    pin "MOD-10"
      "PR-B3: a plain-TOP identity member forces the residue region with the 64K unbounded floors"
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
          (Base.List.exists l2.Sm.regions
             ~f:(fun { Sm.r_id = id; r_bytes = b; _ } ->
               Int.equal id 0 && Int64.equal b unbounded_residue_bytes)));



    (* Lane C: stack-to-locals fission. *)










    pin "MOD-17"
      "PR-C3: an Args read in a stored cell converts with the store to the incoming-window memory (write-closed)"
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
            | Bil.Load (Bil.Var mem, _, _, _) -> Var.same mem (Sm.window_mem ~addr_bits:64)
            | _ -> false));

    pin "MOD-18"
      "PR-N3: the split RMW's hoisted read converts with the store to the incoming-window memory (write-closed)"
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
        let all_window =
          Base.List.for_all n3_defs ~f:(fun d ->
              let vis =
                object
                  inherit [ bool ] Exp.visitor

                  method! visit_load ~mem ~addr:_ _ _ acc =
                    acc
                    && (match mem with
                       | Bil.Var v -> Var.same v (Sm.window_mem ~addr_bits:64)
                       | _ -> false)

                  method! visit_store ~mem ~addr:_ ~exp:_ _ _ acc =
                    acc
                    && (match mem with
                       | Bil.Var v -> Var.same v (Sm.window_mem ~addr_bits:64)
                       | _ -> false)
                end
              in
              vis#visit_exp (Def.rhs d) true)
        in
        check "MOD-18"
          (Base.List.exists n3_defs ~f:(fun d -> not (is_original d))
          && all_window));

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
  ]

let () = run "model" tests
