(* DCE pass pins.  One Alcotest group per pin; each pin builds its own
   fixture, so no state crosses pins. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

(* Local word literal (BAP words for Bil.Int); named apart from Common.w64. *)
let bw64 = Word.of_int ~width:64

(* Swept sub's defs, one list per block flattened. *)
let dce_defs (sub : sub term) : def term list =
  Term.enum blk_t sub |> Seq.concat_map ~f:(Term.enum def_t) |> Seq.to_list

(* Swept sub's jmps. *)
let dce_jmps (sub : sub term) : jmp term list =
  Term.enum blk_t sub |> Seq.concat_map ~f:(Term.enum jmp_t) |> Seq.to_list

let tests : unit Alcotest.test list =
  [
    pin "DCE-13" "every written global component survives without an in-sub reader"
      (fun () ->
         let memories = [Hike.Synth.Global 1; Hike.Synth.Global 2;
                         Hike.Synth.Stack 1] in
         let defs = Base.List.map memories ~f:(fun storage ->
             let mem = Hike.Synth.bytes ~addr_bits:64 storage in
             Def.create mem (Bil.Store (Bil.Var mem, Bil.Int (bw64 0),
                                       Bil.Int (bw64 9), LittleEndian, `r64))) in
         let sub = straight_sub "global_writes" defs in
         let sub = Hike.Dce.dce ~target:Theory.Target.unknown
             ~escape_roots:Var.Set.empty sub in
         let lhs = Base.List.map (dce_defs sub) ~f:Def.lhs in
         check "both globals stay and the unused local storage dies"
           (Base.List.length lhs = 2
            && Base.List.for_all lhs ~f:(fun v ->
                match Hike.Synth.storage_of Hike.Synth.empty v with
                | Some (Hike.Synth.Global _) -> true | _ -> false)));
    (* D0: totality + basic sweep — unused def dies, jmp-read def survives. *)


    (* D1: the return-shaped transfer's producing def dies in the sweep — the
       CFG completion owns the epilogue rewrite; DCE honors the var-free target
       the completion left.  Indirect with return and direct calls stay
       untouched. *)
    pin "DCE-02"
      "the return-shaped transfer's var-free target stands and its popped-address def dies"
      (fun () ->
        let t = v64 "d1_t" in
        let t2 = v64 "d1_t2" in
        let m = memv "d1_m" in
        let rsp = v64 "RSP" in
        let exit_tid = Tid.create () in
        let sub, _ =
          sub_of "d1_epilogue"
            [ [ Def.create t (Bil.Load (Bil.Var m, Bil.Var rsp, LittleEndian, `r64));
                Def.create t2 (Bil.Int (bw64 7)) ],
              [ (0,
                 fun _ ->
                   Hike_return.create ());
                (0,
                 fun _ ->
                   Jmp.create
                     (Call
                        (Call.create ~return:(Direct exit_tid)
                           ~target:(Indirect (Bil.Var t2)) ())));
                (0,
                 fun _ ->
                   Jmp.create
                     (Call
                        (Call.create ~return:(Direct exit_tid)
                           ~target:(Direct exit_tid) ()))) ] ]
        in
        let sub' = Hike.Dce.dce ~target:Theory.Target.unknown ~escape_roots:Var.Set.empty sub in
        let jmps = dce_jmps sub' in
        let epilogue_target_stays_varfree =
          match jmps with
          | j1 :: _ -> Hike_return.is_jmp j1
          | [] -> false
        in
        let others_untouched =
          match jmps with
          | _ :: j2 :: j3 :: _ -> (
              match (Jmp.kind j2, Jmp.kind j3) with
              | Call c2, Call c3 -> (
                  match (Call.target c2, Call.target c3) with
                  | Indirect (Bil.Var v2), Direct _ -> Var.equal v2 t2
                  | _ -> false)
              | _ -> false)
          | _ -> false
        in
        let t_gone =
          Base.List.for_all (dce_defs sub') ~f:(fun d -> not (Var.equal (Def.lhs d) t))
        in
        check "DCE-02"
          (List.length jmps = 3 && epilogue_target_stays_varfree && others_untouched
          && t_gone));

    (* D2: always-keeps — return/param regs, memory writes, intrinsic vars
       survive unread. *)
    pin "DCE-03"
      "an ABI register def survives through the jump's boundary reads - a ret        reads the return registers, a call the parameter registers; the call block's memory write is the call's read, and an unread intrinsic temp dies"
      (fun () ->
        let rax = v64 "RAX" in
        let rdi = v64 "RDI" in
        let m = memv "d2_m" in
        let x0 = v64 "intrinsic:dead0" in
        let callee_tid = Tid.for_name "d2_callee" in
        let sub, _ =
          sub_of "d2_keeps"
            [ [ Def.create rax (Bil.Int (bw64 1));
                Def.create rdi (Bil.Int (bw64 2));
                Def.create m
                  (Bil.Store
                     ( Bil.Var m,
                       Bil.Int (bw64 0x1000),
                       Bil.Int (bw64 3),
                       LittleEndian,
                       `r64 ));
                Def.create x0 (Bil.Int (bw64 4)) ],
              [ (0,
                 fun _ ->
                   Jmp.create
                     (Call (Call.create ~target:(Direct callee_tid) ())));
                (0, mk_ret) ] ]
        in
        let sub' =
          Hike.Dce.dce
            ~target:(Theory.Target.of_string "x86_64-gnu-elf")
            ~escape_roots:Var.Set.empty sub
        in
        let lhs_set =
          Base.List.map (dce_defs sub') ~f:(fun d -> Var.name (Var.base (Def.lhs d)))
        in
        check "DCE-03"
          (List.length lhs_set = 3
          && Base.List.mem lhs_set ~equal:String.equal "RAX"
          && Base.List.mem lhs_set ~equal:String.equal "RDI"
          && Base.List.mem lhs_set ~equal:String.equal "d2_m"));

    (* D3: two-tier region-mem rule — a fissioned store chain dies iff no Load
       roots it. *)
    pin "DCE-04" "a fissioned region-mem store chain dies iff no Load roots it (the two-tier rule)"
      (fun () ->
        let sm = Hike.Stack_model.region_mem ~addr_bits:64 0 in
        let base = v64 "d_base" in
        (* (a) never loaded: both store-chain members die *)
        let sub_a, _ =
          sub_of "d3_fission_dead"
            [ [ mk_store_plus sm base 8 42; mk_store_plus sm base 16 43 ], [] ]
        in
        let sub_a' = Hike.Dce.dce ~target:Theory.Target.unknown ~escape_roots:Var.Set.empty sub_a in
        let dead_count = List.length (dce_defs sub_a') in
        (* (b) loaded with result read: the whole chain survives. *)
        let t = v64 "d3_t" in
        let sub_b, _ =
          sub_of "d3_fission_live"
            [ [ mk_store_plus sm base 8 42;
                mk_store_plus sm base 16 43;
                Def.create t
                  (Bil.Load
                     ( Bil.Var sm,
                       Bil.BinOp (Bil.PLUS, Bil.Var base, Bil.Int (bw64 8)),
                       LittleEndian,
                       `r64 )) ],
              [ (0,
                 fun _ ->
                   Jmp.create
                     ~cond:(Bil.BinOp (Bil.EQ, Bil.Var t, Bil.Int (bw64 0)))
                     (Goto (Direct (Tid.create ())))) ] ]
        in
        let sub_b' = Hike.Dce.dce ~target:Theory.Target.unknown ~escape_roots:Var.Set.empty sub_b in
        let live_count = List.length (dce_defs sub_b') in
        check "DCE-04" (dead_count = 0 && live_count = 3));

    (* D4: SP-erasure on the precise path; the control sub keeps everything. *)
    pin "DCE-05"
      "the sp/frame_anchor lane survives iff used (the arg read roots it), the unused sp-value def dies on both paths"
      (fun () ->
        let sp_ = v64 "RSP" in
        let hstk = v64 "frame_anchor" in
        let tmp = v64 "d4_tmp" in
        let arg_read = v64 "d4_arg_read" in
        let m = memv "d4_m" in
        let rsp_def =
          Def.create sp_ (Bil.BinOp (Bil.MINUS, Bil.Var sp_, Bil.Int (bw64 16)))
        in
        let hstk_def = Def.create hstk (Bil.Var sp_) in
        (* Sp-value def: erased on the precise path. *)
        let tmp_def =
          Def.create tmp (Bil.BinOp (Bil.PLUS, Bil.Var sp_, Bil.Int (bw64 8)))
        in
        (* Incoming-arg read at [frame_anchor + 16]: the production shape. *)
        let arg_def =
          Def.create arg_read
            (Bil.Load
               ( Bil.Var m,
                 Bil.BinOp (Bil.PLUS, Bil.Var hstk, Bil.Int (bw64 16)),
                 LittleEndian,
                 `r64 ))
        in
        let precise_sub = mk_cond_sub "d4_precise" [ rsp_def; hstk_def; tmp_def; arg_def ] arg_read in
        let ctl_sub = mk_cond_sub "d4_ctl" [ rsp_def; hstk_def; tmp_def; arg_def ] arg_read in
        let precise' = Hike.Dce.dce ~target:Theory.Target.unknown ~escape_roots:Var.Set.empty precise_sub in
        let ctl' = Hike.Dce.dce ~target:Theory.Target.unknown ~escape_roots:Var.Set.empty ctl_sub in
        let names sub' =
          Base.List.map (dce_defs sub') ~f:(fun d -> Var.name (Var.base (Def.lhs d)))
        in
        let pn = names precise' in
        let cn = names ctl' in
        check "DCE-05"
          (pn = [ "RSP"; "frame_anchor"; "d4_arg_read" ]
          && cn = [ "RSP"; "frame_anchor"; "d4_arg_read" ]));

    (* D5: intrinsic passthrough — [Sub.intrinsic] subs pass through untouched. *)
    pin "DCE-06" "a [Sub.intrinsic] sub passes through dce unchanged (dead defs and all)"
      (fun () ->
        let x = v64 "d5_dead" in
        let sub, _ =
          sub_of "intrinsic:d5_stub"
            [ [ Def.create x (Bil.Int (bw64 9)) ],
              [ (0, fun _ -> Jmp.create (Goto (Direct (Tid.create ())))) ] ]
        in
        let sub = Term.set_attr sub Sub.intrinsic () in
        let sub' = Hike.Dce.dce ~target:Theory.Target.unknown ~escape_roots:Var.Set.empty sub in
        check "DCE-06"
          (List.length (dce_defs sub') = 1
          && Var.equal
               (Def.lhs (match dce_defs sub' with d :: _ -> d | [] -> assert false))
               x));

    (* D6: the reads-only sweep — a never-read region-mem store chain
       dies; no in-sub read and no jump's boundary read names its
       storage.  (An escaping store survives through the call boundary
       reads — the recorded increment on this rule.) *)
    pin "DCE-07"
      "a never-read region-mem store chain is swept (the reads-only rule)"
      (fun () ->
        let sm = Hike.Stack_model.region_mem ~addr_bits:64 0 in
        let base = v64 "d_base" in
        let sub, _ =
          sub_of "d6_escape_root"
            [ [ mk_store_plus sm base 8 42; mk_store_plus sm base 16 43 ], [] ]
        in
        let sub' =
          Hike.Dce.dce ~target:Theory.Target.unknown ~escape_roots:Var.Set.empty sub
        in
        check "DCE-07" (List.length (dce_defs sub') = 0));

    (* D10: the call's argument boundary — a call-bearing block's
       mem-typed defs (the outgoing store's storage, the call-arg address
       temp) and FP operand temps are the call's reads; an unread plain
       def in the same block still dies. *)
    pin "DCE-10"
      "a call-bearing block's argument temps are the call's boundary reads"
      (fun () ->
        let sm = Hike.Stack_model.region_mem ~addr_bits:64 0 in
        let base = v64 "d10_base" in
        let arg0 = Hike.Stack_model.call_arg ~addr_bits:64 0 in
        let x0 = v64 "intrinsic:x0:64" in
        let dead = v64 "d10_dead" in
        let callee = Tid.for_name "d10_callee" in
        let sub, _ =
          sub_of "d10_callmem"
            [ [ mk_store_plus sm base 8 42;
                Def.create arg0 (Bil.Var base);
                Def.create x0 (Bil.Int (bw64 7));
                Def.create dead (Bil.Int (bw64 7)) ],
              [ (0,
                 fun _ ->
                   Jmp.create (Call (Call.create ~target:(Direct callee) ()))) ];
              [], [ (0, mk_ret) ] ]
        in
        let sub' = Hike.Dce.dce ~target:Theory.Target.unknown ~escape_roots:Var.Set.empty sub in
        let lhs = dce_defs sub' |> List.map (fun d -> Var.name (Def.lhs d)) in
        check "DCE-10"
          (List.mem "stack_r0_mem" lhs
           && List.mem "hike_arg0" lhs
           && List.mem "intrinsic:x0:64" lhs
           && not (List.mem "d10_dead" lhs)));

    (* D11: the escape roots - a storage whose bytes leave the sub (an
       incoming stack-address parameter's target) survives with no
       in-sub reader. *)
    pin "DCE-11"
      "a store into an escape-rooted storage survives with no in-sub reader"
      (fun () ->
        let sm = Hike.Stack_model.region_mem ~addr_bits:64 0 in
        let base = v64 "d11_base" in
        let dead = v64 "d11_dead" in
        let sub, _ =
          sub_of "d11_escape"
            [ [ mk_store_plus sm base 8 42; Def.create dead (Bil.Int (bw64 7)) ],
              [ (1, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let sub' =
          Hike.Dce.dce ~target:Theory.Target.unknown
            ~escape_roots:(Var.Set.singleton sm) sub
        in
        let lhs = dce_defs sub' |> List.map (fun d -> Var.name (Def.lhs d)) in
        check "DCE-11"
          (List.mem "stack_r0_mem" lhs && not (List.mem "d11_dead" lhs)));

    (* D12: the un-routed global memory - a store into plain [mem] has
       its reader outside the sub (the sret buffer's caller); it never
       dies in the per-sub sweep. *)
    pin "DCE-12"
      "a store into the global memory state survives with no in-sub reader"
      (fun () ->
        let m = memv "mem" in
        let m = Var.with_index m 2 in
        let dead = v64 "d12_dead" in
        let sub, _ =
          sub_of "d12_global"
            [ [ mk_store_plus m (v64 "d12_base") 8 42;
                Def.create dead (Bil.Int (bw64 7)) ],
              [ (1, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let sub' =
          Hike.Dce.dce ~target:Theory.Target.unknown
            ~escape_roots:Var.Set.empty sub
        in
        let lhs = dce_defs sub' |> List.map (fun d -> Var.name (Def.lhs d)) in
        check "DCE-12" (List.mem "mem.2" lhs && not (List.mem "d12_dead" lhs)));

    (* D7: the phi arm — a phi whose result no survivor reads is swept,
       and its operands' defs cascade with it.  Under SSA a dead phi's
       reads would otherwise pin every operand def forever. *)
    pin "DCE-08" "a def read only by a dead phi is swept with the phi"
      (fun () ->
        let v = v64 "d8_v" in
        let dead = v64 "d8_dead" in
        let j_blk =
          let b = Blk.Builder.create () in
          Blk.Builder.add_def b (Def.create dead (Bil.Var v));
          ignore (Blk.Builder.add_jmp b (Hike_return.create ()));
          Blk.Builder.result b
        in
        let p1 =
          with_jmps
            (blk_of_defs [ Def.create v (Bil.Int (bw64 1)) ])
            [ mk_goto (Term.tid j_blk) ]
        in
        let p2 =
          with_jmps
            (blk_of_defs [ Def.create v (Bil.Int (bw64 2)) ])
            [ mk_goto (Term.tid j_blk) ]
        in
        let e =
          with_jmps (blk_of_defs [])
            [ mk_jmp_to (Term.tid p1) (Bil.Var (v64 "d8_c"));
              mk_goto (Term.tid p2) ]
        in
        let sub =
          let sb = Sub.Builder.create ~name:"d8" () in
          List.iter (Sub.Builder.add_blk sb) [ e; p1; p2; j_blk ];
          Sub.Builder.result sb
        in
        let prog = Program.create ~subs:[ sub ] () in
        let prog = Hike.Types.sign_program ~target:Theory.Target.unknown prog in
        let prog = Hike.Ssa.ssa_program ~target:Theory.Target.unknown prog in
        let sub = Term.enum sub_t prog |> Seq.hd_exn in
        let phi_present =
          Term.enum blk_t sub
          |> Seq.exists ~f:(fun b -> not (Seq.is_empty (Term.enum phi_t b)))
        in
        let sub' = Hike.Dce.dce ~target:Theory.Target.unknown ~escape_roots:Var.Set.empty sub in
        let phi_gone =
          Term.enum blk_t sub'
          |> Base.Sequence.for_all ~f:(fun b -> Seq.is_empty (Term.enum phi_t b))
        in
        let v_gone =
          Base.List.for_all (dce_defs sub') ~f:(fun d ->
              not (Var.same (Var.base (Def.lhs d)) v))
        in
        check "DCE-08" (phi_present && phi_gone && v_gone));

    (* D8: attribution still records escape roots on the facts record. *)
    pin "DCE-09" "an escape root rides the attribution facts record"
      (fun () ->
        let sm = Hike.Stack_model.region_mem ~addr_bits:64 0 in
        let base = v64 "d9_base" in
        let sub, _ =
          sub_of "d9_escape_root"
            [ [ mk_store_plus sm base 8 42; mk_store_plus sm base 16 43 ], [] ]
        in
        let roots = Tid.Map.singleton (Term.tid sub) (Var.Set.singleton sm) in
        let facts =
          Hike.Kb.with_attribution top_facts ~spec:empty_spec
            ~escape_roots:roots
        in
        let carried =
          Core.Map.find facts.Hike.Kb.escape_roots (Term.tid sub)
          |> Option.value ~default:Var.Set.empty
        in
        check "DCE-09"
          (Var.Set.equal carried (Var.Set.singleton sm)));
  ]

let () = run "dce" tests
