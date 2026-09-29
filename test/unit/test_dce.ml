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
                   Hike__Hike_return.create ());
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
        let sub' = Hike.Dce.dce ~target:Theory.Target.unknown sub in
        let jmps = dce_jmps sub' in
        let epilogue_target_stays_varfree =
          match jmps with
          | j1 :: _ -> Hike__Hike_return.is_jmp j1
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
      "ABI register defs, memory writes, and intrinsic interface vars always survive"
      (fun () ->
        let rax = v64 "RAX" in
        let rdi = v64 "RDI" in
        let m = memv "d2_m" in
        let x0 = v64 "intrinsic:x0" in
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
              [] ]
        in
        let sub' = Hike.Dce.dce ~target:Theory.Target.unknown sub in
        let lhs_set =
          Base.List.map (dce_defs sub') ~f:(fun d -> Var.name (Var.base (Def.lhs d)))
        in
        check "DCE-03"
          (List.length lhs_set = 4
          && Base.List.mem lhs_set ~equal:String.equal "RAX"
          && Base.List.mem lhs_set ~equal:String.equal "RDI"
          && Base.List.mem lhs_set ~equal:String.equal "d2_m"
          && Base.List.mem lhs_set ~equal:String.equal "intrinsic:x0"));

    (* D3: two-tier region-mem rule — a fissioned store chain dies iff no Load
       roots it. *)
    pin "DCE-04" "a fissioned region-mem store chain dies iff no Load roots it (the two-tier rule)"
      (fun () ->
        let sm = Hike.Stack_model.region_mem 0 in
        let base = v64 "d_base" in
        (* (a) never loaded: both store-chain members die *)
        let sub_a, _ =
          sub_of "d3_fission_dead"
            [ [ mk_store_plus sm base 8 42; mk_store_plus sm base 16 43 ], [] ]
        in
        let sub_a' = Hike.Dce.dce ~target:Theory.Target.unknown sub_a in
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
        let sub_b' = Hike.Dce.dce ~target:Theory.Target.unknown sub_b in
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
        let precise' = Hike.Dce.dce ~target:Theory.Target.unknown precise_sub in
        let ctl' = Hike.Dce.dce ~target:Theory.Target.unknown ctl_sub in
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
        let sub' = Hike.Dce.dce ~target:Theory.Target.unknown sub in
        check "DCE-06"
          (List.length (dce_defs sub') = 1
          && Var.equal
               (Def.lhs (match dce_defs sub' with d :: _ -> d | [] -> assert false))
               x));

    (* D6: the escape root — a never-loaded region-mem store chain whose storage
       carries escaped bytes survives the sweep; its reader is never a def of
       this sub (another world reads the raw pointer). *)
    pin "DCE-07"
      "a never-loaded region-mem store chain survives when rooted as escape storage"
      (fun () ->
        let sm = Hike.Stack_model.region_mem 0 in
        let base = v64 "d_base" in
        let sub, _ =
          sub_of "d6_escape_root"
            [ [ mk_store_plus sm base 8 42; mk_store_plus sm base 16 43 ], [] ]
        in
        let sub' =
          Hike.Dce.dce ~roots:(Var.Set.singleton sm) ~target:Theory.Target.unknown sub
        in
        check "DCE-07" (List.length (dce_defs sub') = 2));
  ]

let () = run "dce" tests
