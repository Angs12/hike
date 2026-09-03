(* test_dce: the DCE pass pins D0-D5 through the Hike.Dce seam (extends C1's KB map — runs last). *)
open Bap.Std
open Bap_core_theory
open Test_common

(* --------------------------------------------------------------------- *)
(* Dce — the DCE lane through its own interface ([Hike.Dce.dce], the      *)
(* one-function seam hike_dce.mli installs). All fixtures run on          *)
(* [Theory.Target.unknown], pinning the TOTAL ABI lane (the pre-4 pass    *)
(* raised [Abi.sp: stack pointer not found] on this target — that is why  *)
(* the pass had zero tests).                                              *)
(* --------------------------------------------------------------------- *)

(* [dce_defs sub']: the swept sub's defs, one list per block flattened. *)
let dce_defs (sub : sub term) : def term list =
  Term.enum blk_t sub
  |> Seq.concat_map ~f:(Term.enum def_t)
  |> Seq.to_list

(* [dce_jmps sub']: the swept sub's jmps. *)
let dce_jmps (sub : sub term) : jmp term list =
  Term.enum blk_t sub
  |> Seq.concat_map ~f:(Term.enum jmp_t)
  |> Seq.to_list

let run () =
(  (* D0: totality + the basic sweep — [dce] never raises on
     [Theory.Target.unknown] (the x86_64 SysV-record fallback), and an
     ordinary never-used def dies while a jmp-read def survives. *)
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
(  (* D1: the RETURN-EPILOGUE rewrite ([ret_replacement]) — an INDIRECT
     call with NO return (the lifted `call #t with noreturn` idiom)
     becomes the var-free [Unknown] target, so the popped-address def
     dies with it. The NEGATIVE controls pin the discrimination: an
     indirect call WITH a return (a real computed callee) and a DIRECT
     call are left untouched. *)
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
(  (* D2: the ALWAYS-KEEPS — the return-register def (RAX), a
     param-register def (RDI), a memory write (the lifter's mem), and an
     FP-intrinsic interface var all survive the sweep even when nothing
     in the sub reads them (calls read them IMPLICITLY — the sub-local
     used-set cannot see the callee's reads). *)
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
(  (* D3: the TWO-TIER region-mem rule (mem-fission) — a fissioned
     [stack_rN_mem] var's defs survive iff some LOAD reads the var: (a)
     a never-loaded store chain (the retaddr-push class) dies TOGETHER
     (a Store's mem-operand use is write-position, never a load-root);
     (b) the same chain with ONE load survives.  The vars are built with
     the PUBLIC producers ([Stack_to_locals.region_mem] /
     [region_base]) — the same convention the rewrite mints. *)
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
  (* (b) loaded, and the load's RESULT is read (a jmp cond) — the whole
     chain survives: the load roots the region var, the stores keep *)
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
(  (* D4: SP-ERASURE on the precise path — a sub whose [vsa_info] carries
     a non-empty [stack_plan] (the split model; [is_precise]) has its
     SP defs, its [hike_stack] def, and its sp-VALUE defs erased
     unconditionally (the emitter threads its own SP on that path); the
     CONTROL sub (no KB entry — not precise) keeps them. *)
  let sp_ = v64 "RSP" in
  let hstk = v64 "hike_stack" in
  let tmp = v64 "d4_tmp" in
  let arg_read = v64 "d4_arg_read" in
  let m = memv "d4_m" in
  let rsp_def = Def.create sp_ (Bil.BinOp (Bil.MINUS, Bil.Var sp_, Bil.Int (w64 16))) in
  let hstk_def = Def.create hstk (Bil.Var sp_) in
  (* the sp-VALUE def (a temp computed FROM sp — erased on the precise
     path; kept on the control only if something reads it) *)
  let tmp_def = Def.create tmp (Bil.BinOp (Bil.PLUS, Bil.Var sp_, Bil.Int (w64 8))) in
  (* the callee's incoming-arg read at [hike_stack + 16] — the PRODUCTION
     shape that keeps the hike_stack lane alive on the non-precise path *)
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
  (* provide the split-model plan for the precise sub ONLY (a KB map
     EXTENSION — the join domain; the control sub stays absent) *)
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
      ~degraded:false ~vla_bounds:[]
  in
  Kb.provide (Tid.Map.singleton (Term.tid precise_sub) info);
  let precise' = Hike.Dce.dce ~target:Theory.Target.unknown precise_sub in
  let ctl' = Hike.Dce.dce ~target:Theory.Target.unknown ctl_sub in
  let names sub' =
    Base.List.map (dce_defs sub') ~f:(fun d -> Var.name (Var.base (Def.lhs d)))
  in
  let pn = names precise' in
  let cn = names ctl' in
  (* precise: RSP, hike_stack and the sp-value def are erased
     UNCONDITIONALLY (RSP would otherwise survive self-sustained through
     the hike_stack def's rhs — the unconditional lane is the point);
     the ordinary chain [arg_read <- mem[hike_stack+16] <- jmp cond]
     survives.  control: the whole lane stays. *)
  check "D4: on the precise path (split stack_plan) SP/hike_stack/sp-value defs are erased; the control keeps them"
    (pn = [ "d4_arg_read" ] && cn = [ "RSP"; "hike_stack"; "d4_arg_read" ]);
  ())
;
(  (* D5: the INTRINSIC passthrough — a sub carrying the [Sub.intrinsic]
     attribute (the mapped FP-intrinsic stubs) passes through UNTOUCHED,
     dead defs and all. *)
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
