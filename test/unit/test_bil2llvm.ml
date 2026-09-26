(* Emitter pins (hike-convlir / Bil2llvm): the textual IR the emitter
   produces over hand-built BIR, plus the section-tiling algebra.  One
   Alcotest group per pin; each pin builds its own fixture, so no state
   crosses pins. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

(* The producer's per-def tag stamp + the promotion rewrite: the fixture
   hand-states the tags the attribution would stamp, then promotes. *)
let stamp_tag (d : def term) (t : Ds.sec_tag option) : def term =
  match t with Some t -> Ds.set_sec_tag t d | None -> d

let stamp (tags : (Tid.t * Ds.sec_tag) list) (sub : sub term) : sub term =
  let tags =
    Base.List.fold tags ~init:Tid.Map.empty
      ~f:(fun m (tid, t) -> Core.Map.set m ~key:tid ~data:t)
  in
  let sub =
    Term.map blk_t sub ~f:(fun blk ->
        Term.map def_t blk ~f:(fun d ->
            match Core.Map.find tags (Term.tid d) with
            | Some t -> stamp_tag d (Some t)
            | None -> d))
  in
  Hike.Promote.promote_sub ~abi:Hike.Abi.x86_64_sysv (mk_facts ()) sub

(* Phi lines with exactly two incomings. *)
let count_two_incoming_phis (ir : string) : int =
  String.split_on_char '\n' ir
  |> List.filter (fun l -> contains_substring l " = phi i64 ")
  |> List.filter (fun l ->
      match String.split_on_char '[' l with
      | _ :: rest -> List.length rest = 2
      | [] -> false)
  |> List.length

(* One label per incoming: the token between ', %"' and the next '"'. *)
let phi_preds (line : string) : string list =
  let n = String.length line in
  let rec go i acc =
    if i + 4 > n then List.rev acc
    else if String.sub line i 4 = ", %\"" then begin
      let b = i + 4 in
      let e = String.index_from line b '"' in
      go (e + 1) (String.sub line b (e - b) :: acc)
    end
    else go (i + 1) acc
  in
  go 0 []

(* The section-tiling algebra (Bil2llvm.build_sections): the pins read
   owner ids, spans, typed decisions, and the globals' names; the LLVM
   values are not asserted. *)
let tile_comp sid slo shi lo_w hi_w tw =
  { Sm.comp_id = sid; Sm.sec_lo = slo; Sm.sec_hi = shi;
    Sm.lo_w = lo_w; Sm.hi_w = hi_w; Sm.typed_w = tw }

let tile_bytes ty lo hi ~words ~const img =
  Hike.Bil2llvm.Sec_bytes
    { si_type = ty; si_lo = lo; si_hi = hi;
      si_words = words; si_const = const; si_image = img }

let tile_bss lo hi ~words relocs =
  Hike.Bil2llvm.Sec_bss
    { si_lo = lo; si_hi = hi; si_words = words; si_copy_relocs = relocs }

let tile_build specs comps =
  let ctx = Llvm.create_context () in
  let md = Llvm.create_module ctx "Tiling" in
  let built =
    Hike.Bil2llvm.build_sections ctx md
      { Hike.Bil2llvm.spec_comps = comps; Hike.Bil2llvm.spec_whole = [];
        Hike.Bil2llvm.spec_word = 8;
        Hike.Bil2llvm.spec_sections = specs;
        Hike.Bil2llvm.spec_copy_relocs = [] }
  in
  (ctx, md, built)

let tile_dispose (ctx, md, _) =
  Llvm.dispose_module md;
  Llvm.dispose_context ctx

(* The owner's (id, lo, hi) triple. *)
let tile_own (id : int option) (lo : int64) (hi : int64)
    (o : Hike.Bil2llvm.sec_owner) =
  o.Hike.Bil2llvm.own_id = id && Int64.equal o.Hike.Bil2llvm.own_lo lo
  && Int64.equal o.Hike.Bil2llvm.own_hi hi

let tile_name (o : Hike.Bil2llvm.sec_owner) =
  Llvm.value_name o.Hike.Bil2llvm.base

let tests : unit Alcotest.test list =
  [
    (* SCOPE: undef-read diagnostics stay with the sub that reads the lane. *)
    pin "EMIT-01"
      "undef-read diagnostics stay within their sub"
      (fun () ->
        let r15 = v64 "R15" in
        let undef_sub, _ =
          sub_of "scope_leak_a"
            [ [],
              [ (1,
                 fun t ->
                   mk_jmp_to t
                     (Bil.BinOp
                        (Bil.EQ, Bil.Var r15,
                         Bil.Int (Cbat_word.to_word (w64 0)))));
                (1, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let clean_sub, _ =
          sub_of "scope_leak_b"
            [ [ Def.create (v64 "scope_b_t")
                  (Bil.Int (Cbat_word.to_word (w64 1))) ],
              [ (1, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let err =
          capture_stderr (fun () -> ignore (emit_ir [ undef_sub; clean_sub ]))
        in
        let reports blk =
          String.split_on_char '\n' err
          |> List.filter (fun l ->
                 contains_substring l
                   ("undef-read: blk " ^ Tid.name (Term.tid blk)))
        in
        let undef_blk = Term.first blk_t undef_sub |> Base.Option.value_exn in
        let clean_blk = Term.first blk_t clean_sub |> Base.Option.value_exn in
        check "EMIT-01"
          (List.length (reports undef_blk) >= 1
          && List.length (reports clean_blk) = 0));

    (* POISON: an unbounded-span access warns and emits; a Dead-tagged
       access emits a poison value and warns through Hike_diag. *)
    pin "EMIT-02"
      "a Dead-tagged stack access warns and emits a poison value"
      (fun () ->
        let rsp = v64 "RSP" in
        let m = memv "poison_m" in
        let t = v64 "poison_t" in
        let addr =
          Bil.BinOp
            (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 16)))
        in
        let ld = Def.create t (Bil.Load (Bil.Var m, addr, LittleEndian, `r64)) in
        (* The store consumes the LOAD result: the poison is textually live. *)
        let st =
          Def.create m
            (Bil.Store (Bil.Var m, addr, Bil.Var t, LittleEndian, `r64))
        in
        let dead_sub = mk_lds_sub "poison_dead" [ ld; st ] in
        let dead_sub = stamp [ (Term.tid ld, Sm.Tag.Dead) ] dead_sub in
        let ir_holder = ref "" in
        let err =
          capture_stderr (fun () -> ir_holder := emit_ir [ dead_sub ])
        in
        check "EMIT-02"
          (contains_substring !ir_holder "poison"
          && contains_substring err "hike: guarded: sub"));

    (* UNDEF: reading a never-defined register warns and the value
       becomes a frozen undef. *)
    pin "EMIT-03" "a never-defined register read warns and becomes a frozen undef"
      (fun () ->
        let r15 = v64 "R15" in
        let sub, _ =
          sub_of "undef_read_sub"
            [ [],
              [ (1,
                 fun t ->
                   mk_jmp_to t
                     (Bil.BinOp
                        (Bil.EQ, Bil.Var r15,
                         Bil.Int (Cbat_word.to_word (w64 0)))));
                (1, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let ir_holder = ref "" in
        let err = capture_stderr (fun () -> ir_holder := emit_ir [ sub ]) in
        check "EMIT-03"
          (contains_substring err "hike: undef-read:"
          && contains_substring !ir_holder "freeze i64 undef"));

    (* FRZ: the never-defined register's frozen entry value — two reads
       of the same lane observe the SAME freeze. *)
    pin "EMIT-04"
      "a never-defined register's reads freeze once; the never-read phi is pruned (the phi pruner folds/removes it)"
      (fun () ->
        let ymm =
          Var.create ~is_virtual:false ~fresh:false "YMM9" (Type.Imm 256)
        in
        let lane () =
          Bil.Extract (31, 0, Bil.Extract (127, 0, Bil.Var ymm))
        in
        let t1 = Var.create ~is_virtual:true ~fresh:false "sc_t1" (Type.Imm 32) in
        let t2 = Var.create ~is_virtual:true ~fresh:false "sc_t2" (Type.Imm 32) in
        let eq = Bil.BinOp (Bil.EQ, Bil.Var t1, Bil.Var t2) in
        let leaf = Tid.for_name "selfcmp_leaf" in
        let callee, _ =
          sub_of ~tid:(Tid.for_name "selfcmp_callee") "selfcmp_callee"
            [ [],
              [ (0,
                 fun _ ->
                   Jmp.create
                     (Call
                        (Call.create ~target:(Label.direct leaf) ()))) ] ]
        in
        let callee_tid = Term.tid callee in
        let sub, _ =
          sub_of "selfcmp_sub"
            [ [ Def.create t1 (lane ()); Def.create t2 (lane ()) ],
              [ (2, fun t -> mk_jmp_to t eq);
                (2, fun t -> mk_jmp_to t (Bil.UnOp (Bil.NOT, eq))) ];
              [],
              [ (2,
                 fun t ->
                   Jmp.create
                     (Call
                        (Call.create ~return:(Label.direct t)
                           ~target:(Label.direct callee_tid) ()))) ];
              [], [ (0, mk_ret) ] ]
        in
        let ir = emit_ir [ sub; callee ] in
        check "EMIT-04"
          (contains_substring ir "freeze i256 undef"
          && not (contains_substring ir "[ %hike_undef,")
          && not (contains_substring ir "[ undef,")));

    (* SLOT-CHANNEL: the callee's k-th slot parameter binds the caller's
       [call_arg k] def BY MINTED-VAR IDENTITY, not block def order. *)
    pin "EMIT-05" "the call binds slot args by minted var, not def order"
      (fun () ->
        let slot_arg i =
          Arg.create ~intent:In
            (Sm.arg_slot ~word:8 i)
            (Bil.Var (Sm.arg_slot ~word:8 i))
        in
        let callee =
          fst
            (sub_of "@slotcallee"
               [ [ Def.create (v64 "slot_sum")
                     (Bil.BinOp
                        (Bil.PLUS, Bil.Var (Sm.arg_slot ~word:8 0),
                         Bil.Var (Sm.arg_slot ~word:8 1))) ],
                 [ (0, mk_ret) ] ])
        in
        let callee = Term.append arg_t callee (slot_arg 0) in
        let callee = Term.append arg_t callee (slot_arg 1) in
        (* The site's defs in REVERSE slot order. *)
        let arg_def i v =
          Def.create (Sm.call_arg ~word:8 i)
            (Bil.Int (Cbat_word.to_word (w64 v)))
        in
        let caller, _ =
          sub_of "slot_caller"
            [ [ arg_def 1 6; arg_def 0 5 ],
              [ (1,
                 fun t ->
                   Jmp.create
                     (Call
                        (Call.create ~return:(Direct t)
                           ~target:(Direct (Term.tid callee))
                           ()))) ];
              [], [ (0, mk_ret) ] ]
        in
        let ir = emit_ir [ callee; caller ] in
        check "EMIT-05"
          (contains_substring ir "(i64 5, i64 6)"
          && not (contains_substring ir "(i64 6, i64 5)")));

    (* SP-RESTORE: the direct call rebinds sp to post-push + 8. *)
    pin "EMIT-06" "the named sp_restored = add <pushed>, 8 is materialized; the sp phi folds to it (no phi form survives)"
      (fun () ->
        let rsp = v64 "RSP" in
        let m = memv "sp_m" in
        let callee_tid = Tid.for_name "sp_callee" in
        (* The push: RSP := RSP - 8; mem[RSP] := retaddr. *)
        let caller, _ =
          sub_of "sp_caller"
            [ [ Def.create rsp
                  (Bil.BinOp
                     (Bil.MINUS, Bil.Var rsp,
                      Bil.Int (Cbat_word.to_word (w64 8))));
                Def.create m
                  (Bil.Store
                     ( Bil.Var m,
                       Bil.Var rsp,
                       Bil.Int (Cbat_word.to_word (w64 1234)),
                       LittleEndian, `r64 )) ],
              [ (1,
                 fun t ->
                   Jmp.create
                     (Call
                        (Call.create ~return:(Direct t)
                           ~target:(Direct callee_tid) ()))) ];
              [], [ (0, mk_ret) ] ]
        in
        let callee = fst (sub_of "sp_callee" [ [], [ (0, mk_ret) ] ]) in
        let ir = emit_ir [ caller; callee ] in
        check "EMIT-06"
          (contains_substring ir "%sp_restored = add i64 "
          && not (contains_substring ir "[ %sp_restored,")));

    (* SP-RESTORE: the regioned twin's return edge restores too — the
       store and the reload at [SP+8] hit the same cell. *)
    pin "EMIT-07" "a split-layout sub's return edge restores the sp too (the restore value survives; the phi form folds)"
      (fun () ->
        let rsp2 = v64 "RSP" in
        let m2 = memv "sp_m2" in
        let callee2_tid = Tid.for_name "sp_callee2" in
        let t2 = v64 "sp_t2" in
        let w8 = Bil.Int (Cbat_word.to_word (w64 8)) in
        let caller2, _ =
          sub_of "sp_caller2"
            [ [ Def.create rsp2 (Bil.BinOp (Bil.MINUS, Bil.Var rsp2, w8));
                Def.create m2
                  (Bil.Store
                     ( Bil.Var m2,
                       Bil.BinOp (Bil.PLUS, Bil.Var rsp2, w8),
                       Bil.Int (Cbat_word.to_word (w64 7)),
                       LittleEndian, `r64 )) ],
              [ (1,
                 fun t ->
                   Jmp.create
                     (Call
                        (Call.create ~return:(Direct t)
                           ~target:(Direct callee2_tid) ()))) ];
              [ Def.create t2
                  (Bil.Load
                     ( Bil.Var m2,
                       Bil.BinOp (Bil.PLUS, Bil.Var rsp2, w8),
                       LittleEndian, `r64 )) ],
              [ (0, mk_ret) ] ]
        in
        let caller2 =
          Cu.set_layout
            { Cu.regions = [ (0, (pos (-24L), pos (-16L)), 16L) ];
              Cu.anchor = Some (0, 8192L); Cu.window_param = false }
            caller2
        in
        let callee2 = fst (sub_of "sp_callee2" [ [], [ (0, mk_ret) ] ]) in
        let ir2 = emit_ir [ caller2; callee2 ] in
        check "EMIT-07"
          (contains_substring ir2 "%sp_restored = add i64 "
          && not (contains_substring ir2 "[ %sp_restored,")));

    (* CAST: a tagged stack store whose DATA is a narrower cast keeps the
       zext/trunc at the store. *)
    pin "EMIT-08" "the tagged store reaches memory with its narrowing cast intact"
      (fun () ->
        let rsp = v64 "RSP" in
        let m = memv "cast_m" in
        let src = v64 "cast_src" in
        let addr =
          Bil.BinOp
            (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 16)))
        in
        let d_src =
          Def.create src (Bil.Var (v64 "R15"))
        in
        let d_st =
          Def.create m
            (Bil.Store
               ( Bil.Var m,
                 addr,
                 Bil.Cast (Bil.UNSIGNED, 32, Bil.Var src),
                 LittleEndian, `r64 ))
        in
        let sub, _ =
          sub_of "cast_sub"
            [ [ d_src; d_st ],
              [ (1,
                 fun t ->
                   mk_jmp_to t
                     (Bil.BinOp
                        (Bil.EQ, Bil.Var src,
                         Bil.Int (Cbat_word.to_word (w64 0x7B))))) ];
              [], [ (0, mk_ret) ] ]
        in
        let sub =
          stamp [ (Term.tid d_st, Sm.Tag.Stack (pos (-16L), pos (-16L))) ] sub
        in
        let ir = emit_ir [ sub ] in
        check "EMIT-08"
          (contains_substring ir "store" && contains_substring ir "trunc"));

    (* GOLDEN: the substring-complete golden (one singleton slot + one
       fission region + the anchor residue). *)
    pin "EMIT-09" "the golden sub emits the define, fission alloca, loads/stores, branch, ret, and anchor"
      (fun () ->
        let rsp = v64 "RSP" in
        let m = memv "gold_m" in
        let ld_var = v64 "gold_ld" in
        let st_val = v64 "gold_st" in
        let ld_addr =
          Bil.BinOp
            (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 16)))
        in
        let st_addr =
          Bil.BinOp
            (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 24)))
        in
        let d_ld =
          Def.create ld_var (Bil.Load (Bil.Var m, ld_addr, LittleEndian, `r64))
        in
        let d_st =
          Def.create m
            (Bil.Store (Bil.Var m, st_addr, Bil.Var ld_var, LittleEndian, `r64))
        in
        let d_val =
          Def.create st_val
            (Bil.BinOp
               (Bil.PLUS, Bil.Var ld_var,
                Bil.Int (Cbat_word.to_word (w64 1))))
        in
        let sub, _ =
          sub_of "golden_sub"
            [ [ d_ld; d_st; d_val ],
              [ (1,
                 fun t ->
                   mk_jmp_to t
                     (Bil.BinOp
                        (Bil.EQ, Bil.Var st_val,
                         Bil.Int (Cbat_word.to_word (w64 0)))));
                (1, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let sub =
          stamp
            [ (Term.tid d_ld, Sm.Tag.Stack (pos (-16L), pos (-16L)));
              (Term.tid d_st, Sm.Tag.Stack (pos (-24L), pos (-24L))) ]
            sub
        in
        let sub =
          Cu.set_layout
            { Cu.regions = [ (0, (pos (-24L), pos (-16L)), 16L) ];
              Cu.anchor = Some (0, 8192L); Cu.window_param = false }
            sub
        in
        let ir = emit_ir [ sub ] in
        check_ir "EMIT-09" "define" ir;
        check_ir "EMIT-09" "stack_r0" ir;
        check_ir "EMIT-09" "getelementptr" ir;
        check_ir "EMIT-09" "load" ir;
        check_ir "EMIT-09" "store" ir;
        check_ir "EMIT-09" "icmp" ir;
        check_ir "EMIT-09" "br " ir;
        check_ir "EMIT-09" "ret" ir;
        check_ir "EMIT-09" "i64" ir;
        (* The anchor residue: the SP Slot word ≡ 8 (mod 16), the SysV
           entry residue the lifted word arithmetic reproduces. *)
        check_ir "EMIT-09" "getelementptr i8, ptr %stack_r0, i64 8" ir;
        check_ir "EMIT-09" "%anchor_i64 = ptrtoint ptr %anchor to i64" ir);

    (* ANCHOR-RESIDUE: the anchor is built for arbitrary frame geometry,
       the layout tag set directly. *)
    pin "EMIT-10" "the residue alloca keeps the exact byte count and the anchor follows the fold's index"
      (fun () ->
        let rsp = v64 "RSP" in
        let m = memv "res_m" in
        let addr =
          Bil.BinOp
            (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 16)))
        in
        let d_st =
          Def.create m
            (Bil.Store
               ( Bil.Var m, addr, Bil.Int (Cbat_word.to_word (w64 1)),
                 LittleEndian, `r64 ))
        in
        let sub0, _ =
          sub_of "residue_sub"
            [ [ d_st ], [ (1, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let sub =
          stamp [ (Term.tid d_st, Sm.Tag.Stack (pos (-16L), pos (-16L))) ] sub0
        in
        let sub =
          Cu.set_layout
            Cu.{ regions = [ (0, (pos (-24L), pos (-16L)), 33L) ];
                 Cu.anchor = Some (0, 24L); Cu.window_param = false }
            sub
        in
        let ir = emit_ir [ sub ] in
        check_ir "EMIT-10" "%stack_r0 = alloca [33 x i8]" ir;
        check_ir "EMIT-10" "getelementptr i8, ptr %stack_r0, i64 24" ir;
        (* A full-depth residue: the anchor index rides the fold's name. *)
        let sub =
          Cu.set_layout
            Cu.{ regions = [ (0, (pos (-24L), pos (-16L)), 8208L) ];
                 Cu.anchor = Some (0, 8192L); Cu.window_param = false }
            sub
        in
        let ir = emit_ir [ sub ] in
        check_ir "EMIT-10" "getelementptr i8, ptr %stack_r0, i64 8192" ir);

    (* FP-GPR: the emitter never invents a register value for a
       never-defined RBP read (ADR 0008). *)
    pin "EMIT-11" "a never-defined RBP read warns and no invented fp binding is emitted"
      (fun () ->
        let rbp = v64 "RBP" in
        let rdi = v64 "RDI" in
        let v = v64 "fpg_v" in
        let rsp = v64 "RSP" in
        let mm = memv "fpg_m" in
        let d_st =
          Def.create mm
            (Bil.Store
               ( Bil.Var mm,
                 Bil.BinOp
                   (Bil.MINUS, Bil.Var rsp,
                    Bil.Int (Cbat_word.to_word (w64 16))),
                 Bil.Int (Cbat_word.to_word (w64 1)),
                 LittleEndian, `r64 ))
        in
        let d_v = Def.create v (Bil.Var rbp) in
        let d_arg = Def.create rdi (Bil.Var rbp) in
        let callee_tid = Tid.for_name "fpg_callee" in
        let caller_sub, _ =
          sub_of "fpg_read_rbp"
            [ [ d_st; d_v; d_arg ],
              [ (1,
                 fun t ->
                   Jmp.create
                     (Call
                        (Call.create ~return:(Direct t)
                           ~target:(Direct callee_tid) ()))) ];
              [], [ (0, mk_ret) ] ]
        in
        let callee = fst (sub_of "fpg_callee" [ [], [ (0, mk_ret) ] ]) in
        let caller_sub =
          stamp
            [ (Term.tid d_st, Sm.Tag.Stack (pos (-16L), pos (-16L))) ]
            caller_sub
        in
        let ir_holder = ref "" in
        let err =
          capture_stderr (fun () ->
              ir_holder := emit_ir [ caller_sub; callee ])
        in
        let ir = !ir_holder in
        check "EMIT-11"
          (contains_substring err "hike: undef-read:"
          && not (contains_substring ir "sub i64 %anchor_i64, 8")));

    (* PHI-EDGES: one incoming per RENDERED edge. *)
    pin "EMIT-12" "a duplicated edge's identical incomings and the single edge both fold — no two-incoming i64 phi survives either variant"
      (fun () ->
        let build ~(both_to_t : bool) () : string =
          let x = v64 "edge_mult_x" in
          let flag = v64 "edge_mult_flag" in
          let second_i = if both_to_t then 1 else 2 in
          let s, _ =
            sub_of "edge_mult"
              [ [ Def.create flag (Bil.Int (Cbat_word.to_word (w64 1)));
                  Def.create x
                    (Bil.BinOp
                       (Bil.PLUS, Bil.Var (v64 "RSP"),
                        Bil.Int (Cbat_word.to_word (w64 1)))) ],
                [ (1,
                   fun t ->
                     mk_jmp_to t
                       (Bil.BinOp
                          (Bil.EQ, Bil.Var flag,
                           Bil.Int (Cbat_word.to_word (w64 0)))));
                  (second_i, mk_goto) ];
                [ Def.create (v64 "edge_mult_use") (Bil.Var x) ], [];
                [], [] ]
          in
          emit_ir [ s ]
        in
        let duplicated = count_two_incoming_phis (build ~both_to_t:true ()) in
        let distinct = count_two_incoming_phis (build ~both_to_t:false ()) in
        check "EMIT-12" (duplicated = 0 && distinct = 0));

    (* WFAM: the BIR is width-honest post-coerce (ADR 0018), so a
       width-mismatched read is the frozen-undef identity — no silent
       coercion. *)
    pin "EMIT-13" "a width-mismatched read is a frozen undef (no trunc); the same-width control binds normally"
      (fun () ->
        let wfam = v64 "wfam_val" in
        let wfam32 =
          Var.create ~is_virtual:false ~fresh:false "wfam_val" (Type.Imm 32)
        in
        let out32 =
          Var.create ~is_virtual:false ~fresh:false "wfam_out" (Type.Imm 32)
        in
        let binding () : def term =
          Def.create wfam
            (Bil.BinOp
               (Bil.PLUS, Bil.Var (v64 "RDI"),
                Bil.Int (Cbat_word.to_word (w64 1))))
        in
        let build_mismatched () : string =
          let s, _ =
            sub_of "wfam_mismatch"
              [ [ binding (); Def.create out32 (Bil.Var wfam32) ], [ (0, mk_ret) ] ]
          in
          emit_ir [ s ]
        in
        let build_control () : string =
          let out64 = v64 "wfam_out" in
          let s, _ =
            sub_of "wfam_control"
              [ [ binding (); Def.create out64 (Bil.Var wfam) ], [ (0, mk_ret) ] ]
          in
          emit_ir [ s ]
        in
        let mismatched = build_mismatched () in
        let control = build_control () in
        check "EMIT-13"
          (not (contains_substring mismatched "trunc i64 ")
          && contains_substring mismatched "freeze"
          && not (contains_substring control "trunc i64 ")));

    (* TLS: the stack-protector canary's thread-pointer access renders as
       the thread-local anchor's per-thread address. *)
    pin "EMIT-14" "the TLS access renders the thread_local anchor, its accessor, and drops the base offset"
      (fun () ->
        let tp = Hike.Abi.x86_64_sysv.thread_pointer in
        let m = memv "tls_m" in
        let out = v64 "tls_out" in
        let addr =
          Bil.BinOp
            (Bil.PLUS, Bil.Var tp, Bil.Int (Cbat_word.to_word (w64 0x28)))
        in
        let ld =
          Def.create out (Bil.Load (Bil.Var m, addr, LittleEndian, `r64))
        in
        let sub, _ =
          sub_of "tls_anchor_sub"
            [ [ ld ],
              [ (1,
                 fun t ->
                   mk_jmp_to t
                     (Bil.BinOp
                        (Bil.EQ, Bil.Var out,
                         Bil.Int (Cbat_word.to_word (w64 0))))) ];
              [], [ (0, mk_ret) ] ]
        in
        let ir = emit_ir [ sub ] in
        check "EMIT-14"
          (contains_substring ir "@hike_tls_anchor = thread_local global i64 0"
          && contains_substring ir "ptr @llvm.threadlocal.address(ptr"
          && contains_substring ir
               "call ptr @llvm.threadlocal.address(ptr @hike_tls_anchor)"
          && contains_substring ir "load i64, ptr %tls_anchor"
          && (not (contains_substring ir "getelementptr"))
          && not (contains_substring ir "add i64 40")));

    (* ROWS-COUNT: the resolved dispatch's emitter views — one incoming
       per rendered edge. *)
    pin "EMIT-15" "each guarded goto of the series counts one incoming; the term edge keeps its own"
      (fun () ->
        let sub, tids =
          sub_of "rows_views"
            [ [],
              [ (2, fun t -> mk_jmp_to t (Bil.Var (v64 "rows_g1")));
                (3, fun t -> mk_jmp_to t (Bil.Var (v64 "rows_g2")));
                (4, mk_goto) ];
              [],
              [ (3, fun t -> mk_jmp_to t (Bil.Var (v64 "rows_g3"))) ];
              [], [ (0, mk_ret) ];
              [], [ (0, mk_ret); (5, mk_goto) ];
              [], [ (0, mk_ret) ];
              [], [] ]
        in
        let t_fresh = tids.(2) and t_two = tids.(3) and t_dup = tids.(4) in
        let exit_tid = tids.(5) in
        let edges_into (t : Tid.t) : int =
          Term.enum blk_t sub
          |> Seq.fold ~init:0 ~f:(fun acc b ->
                 acc
                 + (Term.enum jmp_t b
                   |> Seq.count ~f:(fun j ->
                          match Jmp.kind j with
                          | Goto (Direct x) | Ret (Direct x) -> Tid.equal x t
                          | _ -> false)))
        in
        check "EMIT-15"
          (edges_into t_fresh = 1 && edges_into t_two = 2
          && edges_into t_dup = 1
          && edges_into exit_tid >= 1
          && edges_into (Tid.create ()) = 0));

    (* TILE-OWNER/SPAN/COVER/TYPE: the two-component span's tiling. *)
    pin "EMIT-16" "the components are owners in ascending word order and the runs cover the gap bytes"
      (fun () ->
        let span_lo = 0x4000L and span_hi = 0x403FL in
        let comps =
          [ tile_comp 7 span_lo span_hi 1 2 8;
            tile_comp 3 span_lo span_hi 5 6 4 ]
        in
        let img = Bytes.init 64 (fun i -> Char.chr (i mod 251)) in
        let ctx, md, built =
          tile_build
            [ Some
                (tile_bytes Hike.Stack_model.Data span_lo span_hi ~words:8
                   ~const:false img) ]
            comps
        in
        check "EMIT-16"
          (match built with
          | [ s ] -> (
              match s.Hike.Bil2llvm.owners with
              | [ o1; o2; o3; o4; o5 ] ->
                  tile_own None 0x4000L 0x4007L o1
                  && tile_own (Some 7) 0x4008L 0x4017L o2
                  && tile_own None 0x4018L 0x4027L o3
                  && tile_own (Some 3) 0x4028L 0x4037L o4
                  && tile_own None 0x4038L 0x403FL o5
              | _ -> false)
          | _ -> false);
        check "EMIT-16"
          (match built with
          | [ s ] -> (
              match s.Hike.Bil2llvm.owners with
              | [ o1; _; o3; _; o5 ] ->
                  Int64.equal o1.Hike.Bil2llvm.own_lo (Int64.add span_lo 0L)
                  && Int64.equal o1.Hike.Bil2llvm.own_hi (Int64.add span_lo 7L)
                  && Int64.equal o3.Hike.Bil2llvm.own_lo (Int64.add span_lo 24L)
                  && Int64.equal o3.Hike.Bil2llvm.own_hi (Int64.add span_lo 39L)
                  && Int64.equal o5.Hike.Bil2llvm.own_lo (Int64.add span_lo 56L)
                  && Int64.equal o5.Hike.Bil2llvm.own_hi span_hi
              | _ -> false)
          | _ -> false);
        check "EMIT-16"
          (match built with
          | [ s ] -> (
              match s.Hike.Bil2llvm.owners with
              | o :: rest ->
                  let rec adj prev = function
                    | [] -> Int64.equal prev span_hi
                    | n :: tl ->
                        Int64.equal n.Hike.Bil2llvm.own_lo
                          (Int64.add prev 1L)
                        && adj n.Hike.Bil2llvm.own_hi tl
                  in
                  Int64.equal o.Hike.Bil2llvm.own_lo span_lo
                  && adj o.Hike.Bil2llvm.own_hi rest
              | [] -> false)
          | _ -> false);
        check "EMIT-16"
          (match built with
          | [ s ] -> (
              match s.Hike.Bil2llvm.owners with
              | [ o1; o2; o3; o4; o5 ] ->
                  Int.equal o1.Hike.Bil2llvm.typed_w 8
                  && Int.equal o2.Hike.Bil2llvm.typed_w 8
                  && Int.equal o3.Hike.Bil2llvm.typed_w 8
                  && Int.equal o4.Hike.Bil2llvm.typed_w 4
                  && Int.equal o5.Hike.Bil2llvm.typed_w 8
              | _ -> false)
          | _ -> false);
        tile_dispose (ctx, md, built));

    (* T6-TEXT: text is a section row — a constant image-backed section. *)
    pin "EMIT-17" "a text spec entry builds beside the data sections as a constant image-backed row"
      (fun () ->
        let tctx, tmd, tbuilt =
          tile_build
            [ Some
                (tile_bytes Hike.Stack_model.Data 0x4000L 0x403FL ~words:8
                   ~const:false
                   (Bytes.init 64 (fun i -> Char.chr (i mod 251))));
              Some
                (tile_bytes Hike.Stack_model.Text 0x1000L 0x100FL ~words:2
                   ~const:true (Bytes.init 16 (fun i -> Char.chr (i + 1)))) ]
            []
        in
        check "EMIT-17"
          (match tbuilt with
          | [ _data; text ] ->
              Int64.equal (Word.to_int64_exn text.Hike.Bil2llvm.min_addr) 0x1000L
              && Int64.equal
                   (Word.to_int64_exn text.Hike.Bil2llvm.max_addr)
                   0x100FL
              && text.Hike.Bil2llvm.owners = []
              && (match text.Hike.Bil2llvm.bytes with
                 | Some b -> Bytes.length b = 16
                 | None -> false)
          | _ -> false);
        tile_dispose (tctx, tmd, tbuilt));

    (* TILE-RESIDUE: the run counter is module-wide and consumes in the
       fixed tiling order (data before rodata). *)
    pin "EMIT-18" "the run counter is module-wide and consumes in the fixed tiling order"
      (fun () ->
        let d_lo = 0x6000L and d_hi = 0x600FL in
        let r_lo = 0x7000L and r_hi = 0x700FL in
        let comps_two =
          [ tile_comp 0 d_lo d_hi 0 0 8; tile_comp 1 r_lo r_hi 0 0 8 ]
        in
        let ctx, md, built_two =
          tile_build
            [ Some
                (tile_bytes Hike.Stack_model.Data d_lo d_hi ~words:2
                   ~const:false (Bytes.init 16 (fun _ -> '\x00')));
              Some
                (tile_bytes Hike.Stack_model.Rodata r_lo r_hi ~words:2
                   ~const:true (Bytes.init 16 (fun _ -> '\x00'))) ]
            comps_two
        in
        check "EMIT-18"
          (match built_two with
          | [ d; r ] -> (
              match (d.Hike.Bil2llvm.owners, r.Hike.Bil2llvm.owners) with
              | [ do_; dr ], [ ro; rr ] ->
                  tile_own (Some 0) d_lo (Int64.add d_lo 7L) do_
                  && tile_own (Some 1) r_lo (Int64.add r_lo 7L) ro
                  && contains_substring (tile_name dr) "sec_res_2"
                  && contains_substring (tile_name rr) "sec_res_3"
                  && contains_substring (tile_name do_) "sec_comp_0"
                  && contains_substring (tile_name ro) "sec_comp_1"
              | _ -> false)
          | _ -> false);
        tile_dispose (ctx, md, built_two));

    (* TILE-IDENTITY/BSS: the identity shapes keep no owners. *)
    pin "EMIT-19" "a component-free span keeps owners = [] with its image; the bss identity keeps bytes = None"
      (fun () ->
        let ctx, md, built_id =
          tile_build
            [ Some
                (tile_bytes Hike.Stack_model.Data 0x8000L 0x801FL ~words:2
                   ~const:false (Bytes.init 16 (fun _ -> '\x01')));
              Some (tile_bss 0x9000L 0x901FL ~words:2 []) ]
            []
        in
        check "EMIT-19"
          (match built_id with
          | [ s; _ ] ->
              s.Hike.Bil2llvm.owners = []
              && s.Hike.Bil2llvm.bytes
                 = Some (Bytes.init 16 (fun _ -> '\x01'))
          | _ -> false);
        check "EMIT-19"
          (match built_id with
          | [ _; b ] ->
              b.Hike.Bil2llvm.owners = [] && b.Hike.Bil2llvm.bytes = None
          | _ -> false);
        tile_dispose (ctx, md, built_id));

    (* TILE-ORDER: the output follows the spec's order, absent sections
       skipped. *)
    pin "EMIT-20" "the output follows the spec's order, absent sections skipped"
      (fun () ->
        let ctx, md, built_ord =
          tile_build
            [ Some
                (tile_bytes Hike.Stack_model.Data 0x8000L 0x801FL ~words:2
                   ~const:false (Bytes.init 16 (fun _ -> '\x00')));
              None;
              Some (tile_bss 0x9000L 0x901FL ~words:2 []) ]
            []
        in
        check "EMIT-20"
          (match built_ord with
          | [ s; b ] ->
              Int64.equal
                (Word.to_int64_exn s.Hike.Bil2llvm.min_addr)
                0x8000L
              && Int64.equal
                   (Word.to_int64_exn b.Hike.Bil2llvm.min_addr)
                   0x9000L
              && Option.is_some s.Hike.Bil2llvm.bytes
              && Option.is_none b.Hike.Bil2llvm.bytes
          | _ -> false);
        tile_dispose (ctx, md, built_ord));

    (* NB: the materialized dispatch's N-branch chain lowering. *)
    pin "EMIT-21" "the 3-case series renders one cond_br per case, the terminal is the unconditional default, and every join folds (the arms' values are one value)"
      (fun () ->
        let rax = v64 "RAX" in
        let flag = v64 "nb_flag" in
        let g k =
          Bil.BinOp (Bil.EQ, Bil.Var flag, Bil.Int (Cbat_word.to_word (w64 k)))
        in
        let guarded, tids =
          sub_of "nb_series"
            [ [ Def.create flag (Bil.Int (Cbat_word.to_word (w64 0))) ],
              [ (1, fun t -> mk_jmp_to t (g 1));
                (2, fun t -> mk_jmp_to t (g 2));
                (3, fun t -> mk_jmp_to t (g 3)) ];
              [ Def.create (v64 "nb_u1") (Bil.Var rax) ], [];
              [ Def.create (v64 "nb_u2") (Bil.Var rax) ], [];
              [ Def.create (v64 "nb_u3") (Bil.Var rax) ], [] ]
        in
        let ir = emit_ir [ guarded ] in
        let cond_brs =
          String.split_on_char '\n' ir
          |> Base.List.filter ~f:(fun l -> contains_substring l "br i1 ")
          |> Base.List.length
        in
        check "EMIT-21"
          (cond_brs = 3
          && not (contains_substring ir "-dead")
          && not (contains_substring ir "unreachable")
          && Base.List.length
               (String.split_on_char '\n' ir
               |> Base.List.filter ~f:(fun l -> contains_substring l " = phi "))
             = 0);
        (* The terminal guard's false edge is the series block's
           term-order successor (node 1), not a dead end. *)
        check "EMIT-21"
          (contains_substring ir
             ("label %\"" ^ Tid.name tids.(3) ^ "\", label %\""
              ^ Tid.name tids.(1) ^ "\""));
        (* The call-dispatch series: guarded cases plus the literal-true
           terminal (the call's own continuation). *)
        let terminal, _ =
          sub_of "nb_series_cont"
            [ [ Def.create flag (Bil.Int (Cbat_word.to_word (w64 0))) ],
              [ (1, fun t -> mk_jmp_to t (g 1));
                (2, fun t -> mk_jmp_to t (g 2));
                (3, mk_goto) ];
              [ Def.create (v64 "nb_c1") (Bil.Var rax) ], [];
              [ Def.create (v64 "nb_c2") (Bil.Var rax) ], [];
              [ Def.create (v64 "nb_c3") (Bil.Var rax) ], [] ]
        in
        let ir' = emit_ir [ terminal ] in
        check "EMIT-21"
          (not (contains_substring ir' "unreachable")
          && contains_substring ir' "-sw"));

    (* PHI-EDGE: the rendered-edge law — one incoming per rendered
       predecessor, and the module is valid LLVM. *)
    pin "EMIT-22" "the join's identical incomings fold (no phi survives), no phi names the same predecessor twice, and llc accepts the module"
      (fun () ->
        let rax = v64 "RAX" in
        let flag = v64 "dup_flag" in
        let g k =
          Bil.BinOp (Bil.EQ, Bil.Var flag, Bil.Int (Cbat_word.to_word (w64 k)))
        in
        let dup_sub, _ =
          sub_of "phi_dup"
            [ [ Def.create flag (Bil.Int (Cbat_word.to_word (w64 0))) ],
              [ (1, fun t -> mk_jmp_to t (g 1));
                (1, fun t -> mk_jmp_to t (g 2)) ];
              [ Def.create (v64 "dup_u") (Bil.Var rax) ], [] ]
        in
        let ir = emit_ir [ dup_sub ] in
        let phi_lines =
          String.split_on_char '\n' ir
          |> Base.List.filter ~f:(fun l -> contains_substring l " = phi ")
        in
        check "EMIT-22" (List.length phi_lines = 0);
        let dup_preds =
          List.concat_map
            (fun l ->
              let ps = phi_preds l in
              let uniq = List.sort_uniq compare ps in
              if List.length uniq < List.length ps then [ l ] else [])
            phi_lines
        in
        check "EMIT-22" (dup_preds = []);
        (* The strong form: llc accepts the emitted module. *)
        let ll = Filename.temp_file "phi_dup" ".ll" in
        let oc = Stdlib.open_out ll in
        output_string oc ir;
        close_out oc;
        let o = Filename.temp_file "phi_dup" ".o" in
        let ic =
          Unix.open_process_in
            (Printf.sprintf "llc -O0 -filetype=obj %s -o %s 2>&1" ll o)
        in
        let llc_out =
          let buf = Buffer.create 256 in
          (try
             while true do
               Buffer.add_char buf (input_char ic)
             done
           with End_of_file -> ());
          Buffer.contents buf
        in
        let status = Unix.close_process_in ic in
        Sys.remove ll;
        Sys.remove o;
        check "EMIT-22"
          (match status with
          | Unix.WEXITED 0 -> true
          | _ ->
              Printf.printf "llc: %s\n" llc_out;
              false));

    (* PHI-EDGE / call fallthrough: a call whose block does not track SP
       still records its fallthrough edge.  The return block's phi must
       not be empty (llc rejects a phi with predecessors but no
       incomings); this is the coreutils `wc`-class shape. *)
    pin "EMIT-24"
      "a call in a block with no SP def still records its fallthrough edge (the module is llc-valid; the join's identical incomings fold)"
      (fun () ->
        let rax = v64 "RAX" in
        let callee = straight_sub "callee_nosp" [] in
        let callee_tid = Term.tid callee in
        let caller, _ =
          sub_of "caller_nosp"
            [ [ Def.create rax (Bil.Int (Cbat_word.to_word (w64 1))) ],
              [ (1, fun t -> mk_call_jmp t callee_tid) ];
              [ Def.create (v64 "ret_v") (Bil.Var rax) ], [] ]
        in
        let ir = emit_ir [ caller; callee ] in
        let phi_lines =
          String.split_on_char '\n' ir
          |> Base.List.filter ~f:(fun l -> contains_substring l " = phi ")
        in
        check "EMIT-24" (List.length phi_lines = 0);
        let ll = Filename.temp_file "call_nosp" ".ll" in
        let oc = Stdlib.open_out ll in
        output_string oc ir;
        close_out oc;
        let o = Filename.temp_file "call_nosp" ".o" in
        let ic =
          Unix.open_process_in
            (Printf.sprintf "llc -O0 -filetype=obj %s -o %s 2>&1" ll o)
        in
        let llc_out =
          let buf = Buffer.create 256 in
          (try
             while true do
               Buffer.add_char buf (input_char ic)
             done
           with End_of_file -> ());
          Buffer.contents buf
        in
        let status = Unix.close_process_in ic in
        Sys.remove ll;
        Sys.remove o;
        check "EMIT-24"
          (match status with
          | Unix.WEXITED 0 -> true
          | _ ->
              Printf.printf "llc: %s\n" llc_out;
              false));

    (* A divide-by-zero trap lifts as a direct goto to the interrupt
       sub, not a call.  The goto must render as the interrupt handler,
       never a block lookup (there is no such block). *)
    pin "EMIT-25"
      "a goto to an interrupt sub emits the interrupt handler"
      (fun () ->
        let interrupt = Tid.for_name "interrupt:#0" in
        let sub, _ =
          sub_of "div_trap"
            [ [ Def.create (v64 "div_trap_t")
                  (Bil.Int (Cbat_word.to_word (w64 1))) ],
              [ (1, mk_goto) ];
              [], [ (0, fun _ -> mk_goto interrupt) ] ]
        in
        let ir = emit_ir [ sub ] in
        check "EMIT-25" (contains_substring ir "llvm.trap"));

    (* A terminal direct call has a machine-level return path. *)
    pin "EMIT-26"
      "a terminal direct call returns to its caller instead of falling through"
      (fun () ->
        let rbx = v64 "RBX" in
        let callee = straight_sub "tail_callee" [] in
        let callee_tid = Term.tid callee in
        let caller, _ =
          sub_of "tail_caller"
            [ [ Def.create (v64 "tail_t") (Bil.Var rbx) ],
              [ (0, fun _ ->
                  Jmp.create
                    (Call (Call.create ~target:(Label.direct callee_tid) ()))) ] ]
        in
        let ir = emit_ir [ caller; callee ] in
        check "EMIT-26"
          (contains_substring ir "ret void"
           && not (contains_substring ir "unreachable")));

    pin "EMIT-27"
      "a self-targeted external stub with a return lane is not emitted as a body"
      (fun () ->
        let rax = v64 "RAX" in
        let stub_tid = Tid.create () in
        let target_tid = Tid.create () in
        Tid.set_name stub_tid "plt_stub";
        Tid.set_name target_tid "plt_stub";
        let stub, _ =
          sub_of ~tid:stub_tid
            ~args:[ Arg.create ~intent:Out rax (Bil.Var rax) ]
            "plt_stub"
            [ [],
              [ (1,
                 fun t ->
                   Jmp.create
                     (Call
                        (Call.create ~return:(Label.direct t)
                           ~target:(Label.direct target_tid) ()))) ];
              [], [ (0, mk_ret) ] ]
        in
        let ir = emit_ir [ stub ] in
        let defined =
          List.exists
            (fun prefix -> contains_substring ir prefix)
            [ "define void @plt_stub";
              "define i64 @plt_stub";
              "define { i64, i64 } @plt_stub" ]
        in
        check "EMIT-27" (not defined));

    pin "EMIT-28"
      "a no-return indirect tail emits an indirect branch"
      (fun () ->
        let target = v64 "tail_target" in
        let sub, _ =
          sub_of "indirect_tail"
            [ [ Def.create target
                  (Bil.Int (Cbat_word.to_word (w64 0x401000))) ],
              [ (0,
                 fun _ ->
                   Jmp.create
                     (Call
                        (Call.create
                           ~target:(Indirect (Bil.Var target)) ()))) ] ]
        in
        let ir = emit_ir [ sub ] in
        check "EMIT-28"
          (contains_substring ir "indirectbr"
           && not (contains_substring ir "ret void")));

    pin "EMIT-29"
      "the canonical direct return edge emits a return"
      (fun () ->
        let sub, _ =
          sub_of "canonical_return"
            [ [], [ (0, fun _ -> Hike__Hike_return.create ()) ] ]
        in
        let ir = emit_ir [ sub ] in
        check "EMIT-29"
          (contains_substring ir "ret void"
           && not (contains_substring ir "indirectbr")));

    (* LGUARD: the lone guarded goto — the split shape — renders its
       false edge to the term-order successor and records it, so the
       successor's phis carry the incoming. *)
    pin "EMIT-30"
      "a lone guarded goto renders cond_br(cond, target, successor) with the false edge recorded"
      (fun () ->
        let c = v64 "lg_c" in
        let sub, tids =
          sub_of "lone_guard"
            [ [ Def.create c (Bil.Int (Cbat_word.to_word (w64 1))) ],
              [ (2,
                 fun t ->
                   mk_jmp_to t
                     (Bil.BinOp
                        (Bil.EQ, Bil.Var c,
                         Bil.Int (Cbat_word.to_word (w64 0))))) ];
              [ Def.create (v64 "lg_d")
                  (Bil.BinOp
                     (Bil.PLUS, Bil.Var c,
                      Bil.Int (Cbat_word.to_word (w64 1)))) ],
              [ (0, mk_ret) ];
              [ Def.create c (Bil.Int (Cbat_word.to_word (w64 2))) ],
              [ (1, mk_goto) ] ]
        in
        let ir = emit_ir [ sub ] in
        check "EMIT-30"
          (contains_substring ir
             ("label %\"" ^ Tid.name tids.(2) ^ "\", label %\""
              ^ Tid.name tids.(1) ^ "\"")
          && not (contains_substring ir "-dead")
          && not (contains_substring ir "unreachable"));
        let phi_lines =
          String.split_on_char '\n' ir
          |> Base.List.filter ~f:(fun l -> contains_substring l " = phi i64 ")
        in
        check "EMIT-30"
          (Base.List.length
             (Base.List.filter phi_lines ~f:(fun l ->
                  match String.split_on_char '[' l with
                  | _ :: rest -> Base.List.length rest = 2
                  | [] -> false))
          = 1
          && Base.List.exists phi_lines ~f:(fun l ->
                 contains_substring l "1, %"
                 && contains_substring l "2, %")));

    (* ENTRYPIECE: after an entry-block split, the original entry tid
       stays the emitted entry (fresh piece ids sort above it). *)
    pin "EMIT-31"
      "an entry block's piece 1 wins entry_blk_tid after the split"
      (fun () ->
        let flag = v64 "ep_flag" in
        let sub, tids =
          sub_of "entry_split"
            [ [ Def.create flag (Bil.Int (Cbat_word.to_word (w64 0))) ],
              [ (1, fun t -> mk_jmp_to t
                    (Bil.BinOp
                       (Bil.EQ, Bil.Var flag,
                        Bil.Int (Cbat_word.to_word (w64 1)))));
                (2, mk_goto) ];
              [], [ (0, mk_ret) ];
              [], [ (0, mk_ret) ] ]
        in
        let split = Hike.Split_blocks.split_sub sub in
        let ir = emit_ir [ split ] in
        let pieces =
          Term.enum blk_t split |> Seq.to_list
        in
        let p2 = Base.List.nth_exn pieces 1 in
        check "EMIT-31"
          (contains_substring ir ("br label %\"" ^ Tid.name tids.(0) ^ "\"")
          && contains_substring ir
               ("label %\"" ^ Tid.name tids.(1) ^ "\", label %\""
                ^ Tid.name (Term.tid p2) ^ "\"")
          && not (contains_substring ir "-sw")));

    (* BIRPHI: a Phi term renders as its own LLVM phi — one incoming
       per (source block, exp), the value read in the source's
       context; the planner does not duplicate the var. *)
    pin "EMIT-32"
      "a BIR phi renders as the LLVM phi with one incoming per source block"
      (fun () ->
        let v = v64 "bp_v" in
        let p1 = blk_of_defs [ Def.create v (Bil.Int (Cbat_word.to_word (w64 1))) ] in
        let p2 = blk_of_defs [ Def.create v (Bil.Int (Cbat_word.to_word (w64 2))) ] in
        (* The SSA convention: the phi's lhs is a fresh version of the
           var; the incomings name the defs' versions in their source
           blocks. *)
        let v1 = Var.with_index v 1 in
        let j =
          let b = Blk.Builder.create () in
          Blk.Builder.add_phi b
            (Phi.of_list v1
               [ (Term.tid p1, Bil.Var v);
                 (Term.tid p2, Bil.Var v) ]);
          Blk.Builder.add_def b
            (Def.create (v64 "bp_x")
               (Bil.BinOp
                  (Bil.PLUS, Bil.Var v1,
                   Bil.Int (Cbat_word.to_word (w64 1)))));
          ignore (Blk.Builder.add_jmp b (Hike__Hike_return.create ()));
          Blk.Builder.result b
        in
        let e =
          with_jmps (blk_of_defs [])
            [ mk_jmp_to (Term.tid p1)
                (Bil.BinOp
                   (Bil.EQ, Bil.Var (v64 "bp_c"),
                    Bil.Int (Cbat_word.to_word (w64 0))));
              mk_goto (Term.tid p2) ]
        in
        let sub =
          let sb = Sub.Builder.create ~name:"bir_phi" () in
          Sub.Builder.add_blk sb e;
          Sub.Builder.add_blk sb p1;
          Sub.Builder.add_blk sb p2;
          Sub.Builder.add_blk sb j;
          Sub.Builder.result sb
        in
        let ir = emit_ir [ sub ] in
        let phi_lines =
          String.split_on_char '\n' ir
          |> Base.List.filter ~f:(fun l ->
                 contains_substring l " = phi i64 [")
        in
        check "EMIT-32"
          (Base.List.length phi_lines = 1
          && Base.List.exists phi_lines ~f:(fun l ->
                 contains_substring l "1, %"
                 && contains_substring l "2, %")));
  ]

let () = run "bil2llvm" tests
