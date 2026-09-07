(* DCE pass pins D0-D5 through the Hike.Dce seam. *)
open Bap.Std
open Bap_core_theory
open Test_common

let w64 = Word.of_int ~width:64

(* Fixtures run on [Theory.Target.unknown], pinning the total ABI lane. *)

(* Swept sub's defs, one list per block flattened. *)
let dce_defs (sub : sub term) : def term list =
  Term.enum blk_t sub
  |> Seq.concat_map ~f:(Term.enum def_t)
  |> Seq.to_list

(* Swept sub's jmps. *)
let dce_jmps (sub : sub term) : jmp term list =
  Term.enum blk_t sub
  |> Seq.concat_map ~f:(Term.enum jmp_t)
  |> Seq.to_list

let run () =
(  (* D0: totality + basic sweep — unused def dies, jmp-read def survives. *)
  let a = v64 "d0_a" in
  let b = v64 "d0_b" in
  let dead = v64 "d0_dead" in
  let bb = Blk.Builder.create () in
  Blk.Builder.add_def bb (Def.create a (Bil.Int (w64 1)));
  Blk.Builder.add_def bb (Def.create b (Bil.BinOp (Bil.PLUS, Bil.Var a, Bil.Int (w64 1))));
  Blk.Builder.add_def bb (Def.create dead (Bil.Int (w64 5)));
  Blk.Builder.add_jmp bb
    (Jmp.create ~cond:(Bil.BinOp (Bil.EQ, Bil.Var b, Bil.Int (w64 0)))
       (Goto (Direct (Tid.create ()))));
  let sb = Sub.Builder.create ~name:"d0_sweep" () in
  Sub.Builder.add_blk sb (Blk.Builder.result bb);
  let sub = Sub.Builder.result sb in
  let sub' = Hike.Dce.dce ~target:Theory.Target.unknown sub in
  let defs = dce_defs sub' in
  check "D0: dce is total on Theory.Target.unknown; a jmp-read chain survives, an unused def dies"
    (List.length defs = 2
    && Base.List.exists defs ~f:(fun d -> Var.equal (Def.lhs d) a)
    && Base.List.exists defs ~f:(fun d -> Var.equal (Def.lhs d) b)
    && not (Base.List.exists defs ~f:(fun d -> Var.equal (Def.lhs d) dead)));
  ())
;
(  (* D1: return-epilogue rewrite — indirect noreturn call becomes var-free [Unknown].
     Indirect with return and direct calls stay untouched. *)
  let t = v64 "d1_t" in
  let t2 = v64 "d1_t2" in
  let m = memv "d1_m" in
  let rsp = v64 "RSP" in
  let bb = Blk.Builder.create () in
  Blk.Builder.add_def bb
    (Def.create t (Bil.Load (Bil.Var m, Bil.Var rsp, LittleEndian, `r64)));
  let exit_tid = Tid.create () in
  Blk.Builder.add_jmp bb
    (Jmp.create (Call (Call.create ~target:(Indirect (Bil.Var t)) ())));
  Blk.Builder.add_def bb
    (Def.create t2 (Bil.Int (w64 7)));
  Blk.Builder.add_jmp bb
    (Jmp.create
       (Call (Call.create ~return:(Direct exit_tid) ~target:(Indirect (Bil.Var t2)) ())));
  Blk.Builder.add_jmp bb
    (Jmp.create
       (Call (Call.create ~return:(Direct exit_tid) ~target:(Direct exit_tid) ())));
  let sb = Sub.Builder.create ~name:"d1_epilogue" () in
  Sub.Builder.add_blk sb (Blk.Builder.result bb);
  let sub = Sub.Builder.result sb in
  let sub' = Hike.Dce.dce ~target:Theory.Target.unknown sub in
  let jmps = dce_jmps sub' in
  let epilogue_rewritten =
    match dce_jmps sub' with
    | j1 :: _ -> (
        match Jmp.kind j1 with
        | Call c -> (
            match Call.target c with
            | Indirect (Bil.Unknown ("hike-dce-ret", _)) -> true
            | _ -> false)
        | _ -> false)
    | [] -> false
  in
  let others_untouched =
    match dce_jmps sub' with
    | _ :: j2 :: j3 :: _ -> (
        match (Jmp.kind j2, Jmp.kind j3) with
        | Call c2, Call c3 ->
            (match (Call.target c2, Call.target c3) with
             | Indirect (Bil.Var v2), Direct _ -> Var.equal v2 t2
             | _ -> false)
        | _ -> false)
    | _ -> false
  in
  let t_gone =
    Base.List.for_all (dce_defs sub') ~f:(fun d -> not (Var.equal (Def.lhs d) t))
  in
  check "D1: the indirect noreturn call (the lifted return epilogue) is rewritten var-free and its popped-address def dies"
    (List.length jmps = 3 && epilogue_rewritten && others_untouched && t_gone);
  ())
;
(  (* D2: always-keeps — return/param regs, memory writes, intrinsic vars survive unread. *)
  let rax = v64 "RAX" in
  let rdi = v64 "RDI" in
  let m = memv "d2_m" in
  let x0 = v64 "intrinsic:x0" in
  let bb = Blk.Builder.create () in
  Blk.Builder.add_def bb (Def.create rax (Bil.Int (w64 1)));
  Blk.Builder.add_def bb (Def.create rdi (Bil.Int (w64 2)));
  Blk.Builder.add_def bb
    (Def.create m (Bil.Store (Bil.Var m, Bil.Int (w64 0x1000), Bil.Int (w64 3), LittleEndian, `r64)));
  Blk.Builder.add_def bb (Def.create x0 (Bil.Int (w64 4)));
  let sb = Sub.Builder.create ~name:"d2_keeps" () in
  Sub.Builder.add_blk sb (Blk.Builder.result bb);
  let sub = Sub.Builder.result sb in
  let sub' = Hike.Dce.dce ~target:Theory.Target.unknown sub in
  let lhs_set =
    Base.List.map (dce_defs sub') ~f:(fun d -> Var.name (Var.base (Def.lhs d)))
  in
  check "D2: ABI register defs, memory writes, and intrinsic interface vars always survive"
    (List.length lhs_set = 4
    && Base.List.mem lhs_set ~equal:String.equal "RAX"
    && Base.List.mem lhs_set ~equal:String.equal "RDI"
    && Base.List.mem lhs_set ~equal:String.equal "d2_m"
    && Base.List.mem lhs_set ~equal:String.equal "intrinsic:x0");
  ())
;
(  (* D3: two-tier region-mem rule — a fissioned store chain dies iff no Load roots it. *)
  let sm = Hike.Stack_model.region_mem 0 in
  let base = Hike.Stack_model.region_base 0 in
  let mk_store off dat =
    Def.create sm
      (Bil.Store
         ( Bil.Var sm,
           Bil.BinOp (Bil.PLUS, Bil.Var base, Bil.Int (w64 off)),
           Bil.Int (w64 dat),
           LittleEndian,
           `r64 ))
  in
  (* (a) never loaded: both store-chain members die *)
  let bb_a = Blk.Builder.create () in
  Blk.Builder.add_def bb_a (mk_store 8 42);
  Blk.Builder.add_def bb_a (mk_store 16 43);
  let sb_a = Sub.Builder.create ~name:"d3_fission_dead" () in
  Sub.Builder.add_blk sb_a (Blk.Builder.result bb_a);
  let sub_a = Sub.Builder.result sb_a in
  let sub_a' = Hike.Dce.dce ~target:Theory.Target.unknown sub_a in
  let dead_count = List.length (dce_defs sub_a') in
  (* (b) loaded with result read: the whole chain survives. *)
  let t = v64 "d3_t" in
  let bb_b = Blk.Builder.create () in
  Blk.Builder.add_def bb_b (mk_store 8 42);
  Blk.Builder.add_def bb_b (mk_store 16 43);
  Blk.Builder.add_def bb_b
    (Def.create t
       (Bil.Load
          ( Bil.Var sm,
            Bil.BinOp (Bil.PLUS, Bil.Var base, Bil.Int (w64 8)),
            LittleEndian,
            `r64 )));
  Blk.Builder.add_jmp bb_b
    (Jmp.create ~cond:(Bil.BinOp (Bil.EQ, Bil.Var t, Bil.Int (w64 0)))
       (Goto (Direct (Tid.create ()))));
  let sb_b = Sub.Builder.create ~name:"d3_fission_live" () in
  Sub.Builder.add_blk sb_b (Blk.Builder.result bb_b);
  let sub_b = Sub.Builder.result sb_b in
  let sub_b' = Hike.Dce.dce ~target:Theory.Target.unknown sub_b in
  let live_count = List.length (dce_defs sub_b') in
  check "D3: a fissioned region-mem store chain dies iff no Load roots it (the two-tier rule)"
    (dead_count = 0 && live_count = 3);
  ())
;
(  (* D4: SP-erasure on the precise path; the control sub keeps everything. *)
  let sp_ = v64 "RSP" in
  let hstk = v64 "hike_stack" in
  let tmp = v64 "d4_tmp" in
  let arg_read = v64 "d4_arg_read" in
  let m = memv "d4_m" in
  let rsp_def = Def.create sp_ (Bil.BinOp (Bil.MINUS, Bil.Var sp_, Bil.Int (w64 16))) in
  let hstk_def = Def.create hstk (Bil.Var sp_) in
  (* Sp-value def: erased on the precise path. *)
  let tmp_def = Def.create tmp (Bil.BinOp (Bil.PLUS, Bil.Var sp_, Bil.Int (w64 8))) in
  (* Incoming-arg read at [hike_stack + 16]: the production shape. *)
  let arg_def =
    Def.create arg_read
      (Bil.Load
         ( Bil.Var m,
           Bil.BinOp (Bil.PLUS, Bil.Var hstk, Bil.Int (w64 16)),
           LittleEndian,
           `r64 ))
  in
  let mk_sub nm =
    let bb = Blk.Builder.create () in
    Blk.Builder.add_def bb rsp_def;
    Blk.Builder.add_def bb hstk_def;
    Blk.Builder.add_def bb tmp_def;
    Blk.Builder.add_def bb arg_def;
    Blk.Builder.add_jmp bb
      (Jmp.create ~cond:(Bil.BinOp (Bil.EQ, Bil.Var arg_read, Bil.Int (w64 0)))
         (Goto (Direct (Tid.create ()))));
    let sb = Sub.Builder.create ~name:nm () in
    Sub.Builder.add_blk sb (Blk.Builder.result bb);
    Sub.Builder.result sb
  in
  let precise_sub = mk_sub "d4_precise" in
  let ctl_sub = mk_sub "d4_ctl" in
  (* Split-model plan for the precise sub only; the control stays absent. *)
  let region =
    {
      Hike.Convutils.id = 0;
      span = (-16L, -16L);
      members = [];
      convertible = true;
      max_width = 64;
    }
  in
  let info =
    Hike.Convutils.mk_vsa_info ~offsets:[] ~k_ranges:[]
      ~regions:[ region ] ~stack_plan:[ region ]
      ~degraded:false ~vla_bounds:[] ~vla_alloc_tids:Tid.Set.empty
  in
  Kb.provide (Tid.Map.singleton (Term.tid precise_sub) info);
  let precise' = Hike.Dce.dce ~target:Theory.Target.unknown precise_sub in
  let ctl' = Hike.Dce.dce ~target:Theory.Target.unknown ctl_sub in
  let names sub' =
    Base.List.map (dce_defs sub') ~f:(fun d -> Var.name (Var.base (Def.lhs d)))
  in
  let pn = names precise' in
  let cn = names ctl' in
  (* Precise: SP/hike_stack/sp-value erased; control: the whole lane stays. *)
  check "D4: on the precise path (split stack_plan) SP/hike_stack/sp-value defs are erased; the control keeps them"
    (pn = [ "d4_arg_read" ] && cn = [ "RSP"; "hike_stack"; "d4_arg_read" ]);
  ())
;
(  (* D5: intrinsic passthrough — [Sub.intrinsic] subs pass through untouched. *)
  let x = v64 "d5_dead" in
  let bb = Blk.Builder.create () in
  Blk.Builder.add_def bb (Def.create x (Bil.Int (w64 9)));
  Blk.Builder.add_jmp bb (Jmp.create (Goto (Direct (Tid.create ()))));
  let sb = Sub.Builder.create ~name:"intrinsic:d5_stub" () in
  Sub.Builder.add_blk sb (Blk.Builder.result bb);
  let sub = Sub.Builder.result sb in
  let sub = Term.set_attr sub Sub.intrinsic () in
  let sub' = Hike.Dce.dce ~target:Theory.Target.unknown sub in
  check "D5: a [Sub.intrinsic] sub passes through dce unchanged (dead defs and all)"
    (List.length (dce_defs sub') = 1
    && Var.equal (Def.lhs ((match dce_defs sub' with d :: _ -> d | [] -> assert false))) x);
  ())
