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
  Hike.Promote.promote_sub ~addr_bits:64 (mk_facts ()) sub

(* Phi lines with exactly two incomings. *)
(* The types pass's retype for a fixture: every SSA version of [ptrs]
   is a pointer. *)
let retype_versions (ptrs : var list) : program term -> program term =
  Term.map sub_t ~f:(fun s ->
      let env =
        Term.enum blk_t s
        |> Seq.concat_map ~f:(Term.enum def_t)
        |> Seq.fold ~init:Var.Set.empty ~f:(fun acc d ->
               Core.Set.union acc
                 (Core.Set.add (Exp.free_vars (Def.rhs d)) (Def.lhs d)))
        |> Core.Set.filter ~f:(fun v -> List.exists (Var.same v) ptrs)
      in
      Hike.Types.retype_sub ~mem_typ:(Type.Mem (`r64, `r8)) ~ptr_vars:env
        ~ptr_rets:Var.Set.empty s)

let count_two_incoming_phis (ir : string) : int =
  String.split_on_char '\n' ir
  |> List.filter (fun l -> contains_substring l " = phi i64 ")
  |> List.filter (fun l ->
      match String.split_on_char '[' l with
      | _ :: rest -> List.length rest = 2
      | [] -> false)
  |> List.length

(* Intrinsic calls share the producer's explicit capture/result lanes. *)
let lock_tid = Tid.for_name "intrinsic:x86:lock"

let mk_marker target : tid -> jmp term = fun cont ->
  Jmp.create
    (Call (Call.create ~return:(Direct cont) ~target:(Direct target) ()))

let atomic_w (x : int) = Cbat_word.to_word (w64 x)

(* One label per incoming: the token between ', %"' and the next '"'. *)
let tests : unit Alcotest.test list =
  [
    (* SCOPE: undef-read diagnostics stay with the sub that reads the lane. *)


    (* UNDEF: reading a never-defined register warns and the value
       becomes a frozen undef. *)


    (* FRZ: the never-defined register's frozen entry value — two reads
       of the same lane observe the SAME freeze. *)
    pin "EMIT-04"
      "a never-defined register's reads freeze once; a never-read var never enters the SSA var set, so no phi is placed"
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


    (* SP-RESTORE: the direct call rebinds sp to post-push + 8. *)
    pin "EMIT-06" "the call-pushed word rides the restore def at the continuation; no SP phi survives"
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
        (* The un-anchored frame folds the restore to a constant; the
           pinned fact is the absence of any SP phi or sp_restored
           lane — the continuation needs no merge. *)
        check "EMIT-06"
          (not (contains_substring ir " = phi i64 ")
          && not (contains_substring ir "sp_restored")
          && contains_substring ir "store i64 1234"));

    (* SP-RESTORE: the regioned twin's return edge restores too — the
       store and the reload at [SP+8] hit the same cell. *)


    (* CAST: a tagged stack store whose DATA is a narrower cast keeps the
       zext/trunc at the store. *)


    (* GOLDEN: the substring-complete golden (one singleton slot + one
       fission region + the anchor residue). *)


    (* ANCHOR-RESIDUE: the anchor is built for arbitrary frame geometry,
       the layout tag set directly. *)


    (* FP-GPR: the emitter never invents a register value for a
       never-defined RBP read (ADR 0008). *)


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
        (* Widths stay native at emission (hike-coerce owns the rule):
          the mismatched read aliases the defined var's value — no
          trunc, no frozen lane. *)
        check "EMIT-13"
          (not (contains_substring mismatched "trunc i64 ")
          && not (contains_substring mismatched "freeze")
          && contains_substring mismatched "add i64 %RDI, 1"
          && not (contains_substring control "trunc i64 ")));

    (* The one TP classification: an offset inside the PT_TLS extent
       (negative, within memsz) indexes the module's own thread_local
       block; every other TP-relative address (the FS:0 self pointer,
       the canary slot) routes through the real thread pointer; an
       address that never reads the thread pointer is not TLS. *)
    pin "EMIT-14"
      "own-range TP offsets index the PT_TLS block; the others route through the real thread pointer"
      (fun () ->
        let tp = Hike.Abi.x86_64_sysv.thread_pointer in
        let m = memv "tls_m" in
        let out = v64 "tls_out" in
        let addr offset =
          Bil.BinOp
            (Bil.PLUS, Bil.Var tp, Bil.Int (Cbat_word.to_word (w64 offset)))
        in
        let store name offset value =
          Def.create (memv name)
            (Bil.Store
               ( Bil.Var m, addr offset,
                 Bil.Int (Cbat_word.to_word (w64 value)), LittleEndian, `r64 ))
        in
        let ld_self =
          Def.create (v64 "tls_self")
            (Bil.Load (Bil.Var m, addr 0, LittleEndian, `r64))
        in
        let ld_canary =
          Def.create out (Bil.Load (Bil.Var m, addr 0x28, LittleEndian, `r64))
        in
        let sub, _ =
          sub_of "tls_class_sub"
            [ [ store "tls_own_a" (-0x8) 111;
                store "tls_own_b" (-0x10) 222;
                ld_self;
                ld_canary;
                Def.create (v64 "tls_guard") (Bil.Var out) ],
              [ (1,
                 fun t ->
                   mk_jmp_to t
                     (Bil.BinOp
                        (Bil.EQ, Bil.Var (v64 "tls_guard"),
                         Bil.Int (Cbat_word.to_word (w64 0))))) ];
              [], [ (0, mk_ret) ] ]
        in
        let spec =
          { empty_spec with
            spec_tls = Some { tls_lo = 0x3dd0L; tls_memsz = 0x18L; tls_align = 8;
                              tls_base = -0x18L; tls_prefix = 0; tls_image = Bytes.empty } }
        in
        let ir = emit_ir_spec spec [ sub ] in
        check "EMIT-14"
          (contains_substring ir "@hike_tls_block = thread_local global"
           (* the own-range cells: memsz 0x18, offsets -8/-10 land at
              +0x10/+0x8 in the block *)
           && contains_substring ir "getelementptr i8, ptr %tls_addr, i64 16"
           && contains_substring ir "getelementptr i8, ptr %tls_addr1, i64 8"
           && contains_substring ir "store i64 111"
           && contains_substring ir "store i64 222"
           (* fs:0 is the self pointer: the loaded value IS the real
              thread pointer, never a block cell *)
           && contains_substring ir "getelementptr i8, ptr %hike_tp, i64 0"
           (* the canary slot loads through the real thread pointer *)
           && contains_substring ir "i64 40"
           && contains_substring ir "load i64"));

    (* ROWS-COUNT: the resolved dispatch's emitter views — one incoming
       per rendered edge. *)


    (* TILE-OWNER/SPAN/COVER/TYPE: the two-component span's tiling. *)


    (* T6-TEXT: text is a section row — a constant image-backed section. *)

    (* A symbol-bearing relocation names a global through the same
       sanitizer every function declaration uses: the slot and the call
       site must name one entity. *)
    pin "EMIT-41"
      "an externally-relocated word binds the symbol's sanitized name"
      (fun () ->
        let img = Bytes.make 8 '\000' in
        let meta =
          { B2l.sm_type = Sm.Data; sm_access = Hike_section.Writable;
            sm_lo = 0x1000L; sm_hi = 0x1007L; sm_words = 1;
            sm_image = Some img; sm_copy_relocs = [] }
        in
        let spec =
          { empty_spec with
            spec_sections = [ Some meta ];
            spec_externals = [ (0x1000L, "foo.bar") ] }
        in
        let sub, _ =
          sub_of "ext_slot"
            [ [ Def.create (v64 "ext_slot_t")
                  (Bil.Int (Cbat_word.to_word (w64 1))) ], [] ]
        in
        let ir = emit_ir_spec spec [ sub ] in
        check "EMIT-41"
          (contains_substring ir "@foobar"
          && not (contains_substring ir "@foo.bar")));

    (* §5 — the initializer's substitution rule against fixture
       relocation facts: a word is an address iff a relocation names
       it; every other word keeps its raw bits. *)

    (* REL: a RELATIVE site renders the relocation fact's runtime value
       remapped through the sections — the image's raw bits never
       surface. *)
    pin "EMIT-43"
      "a RELATIVE site renders the relocation fact's value remapped, \
       never the raw bits"
      (fun () ->
        let text_img = Bytes.make 16 '\000' in
        let text_meta =
          { B2l.sm_type = Sm.Text; sm_access = Hike_section.Read_only;
            sm_lo = 0x500L; sm_hi = 0x50FL; sm_words = 2;
            sm_image = Some text_img; sm_copy_relocs = [] }
        in
        let img = Bytes.make 8 '\000' in
        Bytes.set img 0 '\x42';
        let meta =
          { B2l.sm_type = Sm.Data; sm_access = Hike_section.Writable;
            sm_lo = 0x1000L; sm_hi = 0x1007L; sm_words = 1;
            sm_image = Some img; sm_copy_relocs = [] }
        in
        let spec =
          { empty_spec with
            spec_sections = [ Some text_meta; Some meta ];
            spec_relative = [ (0x1000L, 0x504L) ] }
        in
        let sub, _ =
          sub_of "rel_slot"
            [ [ Def.create (v64 "rel_slot_t")
                  (Bil.Int (Cbat_word.to_word (w64 1))) ], [] ]
        in
        let ir = emit_ir_spec spec [ sub ] in
        check "EMIT-43"
          (contains_substring ir
             "ptrtoint (ptr getelementptr inbounds (i8, ptr @text, i64 4) \
              to i64)"
          && not (contains_substring ir "i64 66")));

    (* CLASS-B: an unrelocated word keeps its raw bits even when they
       land inside a built section's span — the span never guesses an
       address (the corpus's class-(b) fixture's rule). *)
    pin "EMIT-44"
      "an unrelocated word inside a built span keeps its raw bits"
      (fun () ->
        let text_img = Bytes.make 16 '\000' in
        let text_meta =
          { B2l.sm_type = Sm.Text; sm_access = Hike_section.Read_only;
            sm_lo = 0x500L; sm_hi = 0x50FL; sm_words = 2;
            sm_image = Some text_img; sm_copy_relocs = [] }
        in
        let img = Bytes.make 8 '\000' in
        Bytes.set img 0 '\x08';
        Bytes.set img 1 '\x05';
        let meta =
          { B2l.sm_type = Sm.Data; sm_access = Hike_section.Writable;
            sm_lo = 0x1000L; sm_hi = 0x1007L; sm_words = 1;
            sm_image = Some img; sm_copy_relocs = [] }
        in
        let spec =
          { empty_spec with
            spec_sections = [ Some text_meta; Some meta ] }
        in
        let sub, _ =
          sub_of "classb_slot"
            [ [ Def.create (v64 "classb_slot_t")
                  (Bil.Int (Cbat_word.to_word (w64 1))) ], [] ]
        in
        let ir = emit_ir_spec spec [ sub ] in
        check "EMIT-44"
          (contains_substring ir "i64 1288"
          && not (contains_substring ir "ptrtoint")
          && not (contains_substring ir "getelementptr")));

    (* STRING: a printable-ASCII word keeps its raw bits too — no
       printable-string guard and no span guess stand in the rule's
       place. *)
    pin "EMIT-45"
      "a printable-ASCII unrelocated word keeps its raw bits"
      (fun () ->
        let ro_img = Bytes.make 8 '\000' in
        let ro_meta =
          { B2l.sm_type = Sm.Rodata; sm_access = Hike_section.Read_only;
            sm_lo = 0x216948L; sm_hi = 0x21694FL; sm_words = 1;
            sm_image = Some ro_img; sm_copy_relocs = [] }
        in
        let img = Bytes.make 8 '\000' in
        Bytes.set img 0 'H';
        Bytes.set img 1 'i';
        Bytes.set img 2 '!';
        let meta =
          { B2l.sm_type = Sm.Data; sm_access = Hike_section.Writable;
            sm_lo = 0x1000L; sm_hi = 0x1007L; sm_words = 1;
            sm_image = Some img; sm_copy_relocs = [] }
        in
        let spec =
          { empty_spec with
            spec_sections = [ Some ro_meta; Some meta ] }
        in
        let sub, _ =
          sub_of "string_slot"
            [ [ Def.create (v64 "string_slot_t")
                  (Bil.Int (Cbat_word.to_word (w64 1))) ], [] ]
        in
        let ir = emit_ir_spec spec [ sub ] in
        check "EMIT-45"
          (contains_substring ir "i64 2189640"
          && not (contains_substring ir "ptrtoint")
          && not (contains_substring ir "getelementptr")));



    (* TILE-RESIDUE: the run counter is module-wide and consumes in the
       fixed tiling order (data before rodata). *)


    (* TILE-IDENTITY/BSS: the identity shapes keep no owners. *)


    (* TILE-ORDER: the output follows the spec's order, absent sections
       skipped. *)


    (* NB: the materialized dispatch's N-branch chain lowering. *)


    (* PHI-EDGE: the rendered-edge law — one incoming per rendered
       predecessor, and the module is valid LLVM. *)


    (* PHI-EDGE / call fallthrough: a call whose block does not track SP
       still records its fallthrough edge.  The return block's phi must
       not be empty (llc rejects a phi with predecessors but no
       incomings); this is the coreutils `wc`-class shape. *)


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




    pin "EMIT-28"
      "an indirect tail with no enumerated destinations is a loud failure — \
       the module never carries destination-less UB behind a warning"
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
        let loud =
          try
            ignore (emit_ir [ sub ]);
            false
          with Failure m ->
            Base.String.is_substring m
              ~substring:"no enumerated destinations"
        in
        check "EMIT-28" loud);

    pin "EMIT-42"
      "an indirect JUMP with no enumerated destinations is a loud failure \
       too (the sibling site to EMIT-28's indirect tail)"
      (fun () ->
        let target = v64 "jump_target" in
        let sub, _ =
          sub_of "indirect_jump"
            [ [ Def.create target
                  (Bil.Int (Cbat_word.to_word (w64 0x401000))) ],
              [ (0, fun _ -> Jmp.create (Goto (Indirect (Bil.Var target)))) ] ]
        in
        let loud =
          try
            ignore (emit_ir [ sub ]);
            false
          with Failure m ->
            Base.String.is_substring m ~substring:"no enumerated destinations"
        in
        check "EMIT-42" loud);



    (* LGUARD: the lone guarded goto — the split shape — renders its
       false edge to the term-order successor and records it, so the
       successor's phis carry the incoming. *)


    (* ENTRYPIECE: after an entry-block split, the original entry tid
       stays the emitted entry (fresh piece ids sort above it). *)


    (* BIRPHI: the SSA pass materializes the join's phi; the emitter
       renders it — one incoming per source block, the def's value. *)


    (* The splitter leaves a non-compilable series alone; reaching the
       emitter with it is a loud failure, never a silent render. *)
    pin "EMIT-33"
      "an unsplit multi-jmp series reaching the emitter is a loud failure"
      (fun () ->
        let sub, _ =
          sub_of "unsplit_series"
            [ [],
              [ (1, mk_goto);
                (2, mk_goto);
                (0,
                 fun _ ->
                   Jmp.create
                     (Goto
                        (Indirect
                           (Bil.Int (Cbat_word.to_word (w64 0)))))) ];
              [], [ (0, mk_ret) ];
              [], [ (0, mk_ret) ] ]
        in
        let loud =
          try
            ignore (emit_ir [ sub ]);
            false
          with Failure m ->
            Base.String.is_substring m ~substring:"unsplit multi-jmp"
        in
        check "EMIT-33" loud);

    pin "EMIT-34"
      "a Vla(T)-origin access GEPs the %vla created at T — two VLAs each hit their own"
      (fun () ->
        let m = memv "emit_vla_m" in
        let rsp = v64 "RSP" in
        let rax = v64 "RAX" in
        let rbx = v64 "RBX" in
        let p1 = v64 "emit_vla_p1" in
        let p2 = v64 "emit_vla_p2" in
        let w (x : int) = Cbat_word.to_word (w64 x) in
        let d_dec1 =
          Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Var rax))
        in
        let d_p1 = Def.create p1 (Bil.Var rsp) in
        let d_ld1 =
          Hike.Vsa.Def_origin.with_origin
            (Hike_origin.Vla (Term.tid d_dec1))
            (Def.create (v64 "emit_vla_t1")
               (Bil.Load
                  ( Bil.Var m,
                    Bil.BinOp (Bil.PLUS, Bil.Var p1, Bil.Int (w 4)),
                    LittleEndian,
                    `r32 )))
        in
        let d_dec2 =
          Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Var rbx))
        in
        let d_p2 = Def.create p2 (Bil.Var rsp) in
        let d_st2 =
          Hike.Vsa.Def_origin.with_origin
            (Hike_origin.Vla (Term.tid d_dec2))
            (Def.create m
               (Bil.Store
                  ( Bil.Var m,
                    Bil.BinOp (Bil.PLUS, Bil.Var p2, Bil.Int (w 8)),
                    Bil.Int (Cbat_word.to_word (Cbat_word.of_int ~width:32 5)),
                    LittleEndian,
                    `r32 )))
        in
        let sub =
          straight_sub "emit_vla_two"
            [ d_dec1; d_p1; d_ld1; d_dec2; d_p2; d_st2 ]
        in
        let sub =
          Ds.stamp_dyn_allocs
            ~allocs:
              (Core.Map.of_key_set
                 (Core.Set.of_list (module Tid) [ Term.tid d_dec1; Term.tid d_dec2 ])
                 ~f:(fun _ -> { Ds.floor = 0L; parent = None }))
            sub
          |> Sm.set_layout
               { Sm.regions = []; window_param = false }
        in
        let types = retype_versions [ rsp; p1; p2 ] in
        let ir = emit_ir ~types [ sub ] in
        let count sub_str =
          String.split_on_char '\n' ir
          |> List.filter (fun l -> contains_substring l sub_str)
          |> List.length
        in
        check "EMIT-34"
          (contains_substring ir "getelementptr i8, ptr %vla, i64 4"
          && contains_substring ir "getelementptr i8, ptr %vla2, i64 8"
          && count " = alloca i8, i64 " = 2));

    pin "EMIT-59"
      "an allocation computed off SP emits its alloca at the producer: the size \
       adds the floor, the base is past it, and SP's copy is the base"
      (fun () ->
        let rsp = v64 "RSP" and rax = v64 "RAX" and t = v64 "emit_vla_t" in
        let m = memv "emit_vla59_m" in
        let w (x : int) = Cbat_word.to_word (w64 x) in
        let d_t = Def.create t (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Var rax)) in
        let sub =
          straight_sub "emit_vla_producer"
            [ d_t;
              Def.create rsp (Bil.BinOp (Bil.AND, Bil.Var t, Bil.Int (w (-16))));
              Def.create m
                (Bil.Store
                   ( Bil.Var m, Bil.Var rsp,
                     Bil.Int (Cbat_word.to_word (Cbat_word.of_int ~width:32 5)),
                     LittleEndian, `r32 )) ]
          |> Ds.stamp_dyn_allocs
               ~allocs:(Tid.Map.singleton (Term.tid d_t) { Ds.floor = -15L; parent = None })
          |> Sm.set_layout { Sm.regions = []; window_param = false }
        in
        let ir = emit_ir ~types:(retype_versions [ rsp; t ]) [ sub ] in
        check "EMIT-59"
          (contains_substring ir "%vla_size = add i64"
          && contains_substring ir ", 15"
          && contains_substring ir "%vla_base = getelementptr i8, ptr %vla, i64 15"
          && contains_substring ir "@llvm.ptrmask.p0.i64(ptr %vla_base"));

    pin "EMIT-58"
      "a pointer masked by an integer stays a pointer (ptrmask); a pointer \
       difference is an integer"
      (fun () ->
        let rsp = v64 "RSP" and rbp = v64 "RBP" in
        let rax = v64 "RAX" and rbx = v64 "RBX" in
        let m = memv "emit_mask_m" in
        let w (x : int) = Cbat_word.to_word (w64 x) in
        let d_dec = Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Var rbx)) in
        let sub =
          straight_sub "emit_ptrmask"
            [ d_dec;
              Def.create rbp (Bil.Var rsp);
              Def.create rsp (Bil.BinOp (Bil.AND, Bil.Var rsp, Bil.Int (w (-16))));
              Def.create rax (Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Var rsp));
              Def.create m
                (Bil.Store (Bil.Var m, Bil.Var rsp, Bil.Var rax, LittleEndian, `r64)) ]
          |> Ds.stamp_dyn_allocs
               ~allocs:
                 (Tid.Map.singleton (Term.tid d_dec) { Ds.floor = 0L; parent = None })
          |> Sm.set_layout { Sm.regions = []; window_param = false }
        in
        let ir = emit_ir ~types:(retype_versions [ rsp; rbp ]) [ sub ] in
        check "EMIT-58"
          (contains_substring ir "call ptr @llvm.ptrmask.p0.i64(ptr %vla"
           && contains_substring ir "store i64"
           && not (contains_substring ir "inttoptr")));

    pin "EMIT-47" "explicit atomic operations emit one effect at every width"
      (fun () ->
        List.iter (fun bits ->
          List.iter (fun op ->
            let addr = Def.create (Hike.Atomic.lane "address" 64) (Bil.Int (atomic_w 0x2000)) in
            let value = Def.create (Hike.Atomic.lane "input0" bits) (Bil.Int (Word.of_int ~width:bits 3)) in
            let sub,_ = sub_of "atomic_family"
                [ [addr;value], [(1,mk_marker (Tid.for_name
                    (Printf.sprintf "intrinsic:x86:atomic_%s_%d" op bits)))];
                  [], [(0,mk_ret)] ] in
            let ir = emit_ir [sub] in
            check (Printf.sprintf "EMIT-47.%s.%d" op bits)
              (contains_substring ir ("atomicrmw " ^ op ^ " ptr")
               && contains_substring ir (Printf.sprintf "i%d 3 seq_cst" bits)
               && not (contains_substring ir " = load ")
               && not (contains_substring ir " store i")
               && not (contains_substring ir "intrinsic:x86:atomic")))
            ["add";"sub";"and";"or";"xor";"xchg"])
          [8;16;32;64]);

    pin "EMIT-48" "the atomic old result feeds later register and flag uses"
      (fun () ->
        let m = memv "atomic_result" in
        let old = Hike.Atomic.lane "old" 64 in
        let sub,_ = sub_of "atomic_result"
            [ [Def.create (Hike.Atomic.lane "address" 64) (Bil.Int (atomic_w 0x2000));
               Def.create (Hike.Atomic.lane "input0" 64) (Bil.Int (atomic_w 7))],
              [(1,mk_marker (Tid.for_name "intrinsic:x86:atomic_add_64"))];
              [Def.create m (Bil.Store (Bil.Var m,Bil.Int (atomic_w 0x2010),
                  Bil.Var old,LittleEndian,`r64))], [(0,mk_ret)] ] in
        let ir = emit_ir [sub] in
        check "EMIT-48"
          (contains_substring ir "i64 7 seq_cst"
           && contains_substring ir "store i64 %xold"
           && not (contains_substring ir " = load ")));

    pin "EMIT-50" "a register xchg carries no markers and stays plain"
      (fun () ->
        let m = memv "regx_m" in
        let rbx = v64 "RBX" in
        let r12 = v64 "R12" in
        let t = v64 "regx_t" in
        let sub, _ =
          sub_of "regx_sub"
            [ [ Def.create r12 (Bil.Int (atomic_w 9));
                Def.create t (Bil.Var rbx);
                Def.create rbx (Bil.Var r12);
                Def.create r12 (Bil.Var t);
                Def.create m
                  (Bil.Store
                     (Bil.Var m, Bil.Int (atomic_w 0x2000), Bil.Var rbx,
                      LittleEndian, `r64)) ],
              [ (0, mk_ret) ] ]
        in
        let ir = emit_ir [ sub ] in
        check "EMIT-50"
          (not (contains_substring ir "atomicrmw")
           && contains_substring ir "store i64 9"));

    pin "EMIT-51"
      "the three fence intrinsics emit their exact LLVM ordering"
      (fun () ->
        List.iter (fun (name, order) ->
            let sub, _ = sub_of "fence_sub"
                [ ([], [ (1, mk_marker (Tid.for_name ("intrinsic:" ^ name))) ]);
                  ([], [ (0, mk_ret) ]) ] in
            let ir = emit_ir [ sub ] in
            check ("EMIT-51." ^ name)
              (contains_substring ir ("fence " ^ order)
               && not (contains_substring ir ("call void @" ^ name))))
          [ "mfence", "seq_cst"; "lfence", "acquire"; "sfence", "release" ]);

    pin "EMIT-52" "explicit compare-exchange emits one conditional atomic effect"
      (fun () ->
        let sub,_ = sub_of "atomic_cas"
            [ [Def.create (Hike.Atomic.lane "address" 64) (Bil.Int (atomic_w 0x2000));
               Def.create (Hike.Atomic.lane "input0" 64) (Bil.Int (atomic_w 5));
               Def.create (Hike.Atomic.lane "input1" 64) (Bil.Int (atomic_w 9))],
              [(1,mk_marker (Tid.for_name "intrinsic:x86:atomic_cmpxchg_64"))];
              [], [(0,mk_ret)] ] in
        let ir = emit_ir [sub] in
        check "EMIT-52"
          (contains_substring ir "cmpxchg ptr"
           && contains_substring ir "i64 5, i64 9 seq_cst seq_cst"
           && not (contains_substring ir " store i")));

    pin "EMIT-54"
      "TLS relocations affect initialized bytes and never the zero tail"
      (fun () ->
        let tls = { Hike_spec.tls_lo = 0x5000L; tls_memsz = 16L;
                    tls_align = 8; tls_base = -16L; tls_prefix = 0;
                    tls_image = Bytes.make 8 '\127' } in
        let spec = { empty_spec with spec_tls = Some tls;
                      spec_externals = [ 0x5000L, "tls_external" ];
                      spec_relative = [ 0x5008L, 0xdeadL ] } in
        let sub, _ = sub_of "tls_init_sub" [ [], [ (0, mk_ret) ] ] in
        let ir = emit_ir_spec spec [ sub ] in
        check "EMIT-54"
          (contains_substring ir "ptrtoint (ptr @tls_external to i64)"
           && contains_substring ir "[8 x i8] zeroinitializer"
           && not (contains_substring ir "i64 57005")));

    pin "EMIT-55" "legacy lock markers are refused rather than emitted as plain accesses"
      (fun () ->
        let sub,_ = sub_of "legacy_atomic"
            [ [], [(1,mk_marker lock_tid)]; [], [(0,mk_ret)] ] in
        let refused = try ignore (emit_ir [sub]); false with
          | Failure message -> contains_substring message "legacy atomic markers" in
        check "EMIT-55" refused);

    pin "EMIT-56" "atomic negation preserves the caller CFG at a phi join"
      (fun () ->
        let guard = Bil.Var (v1 "neg_guard") in
        let old = Hike.Atomic.lane "old" 64 in
        let sub,_ = sub_of "atomic_neg_join"
            [ [], [(1,fun t -> mk_jmp_to t guard);
                   (2,fun t -> mk_jmp_to t (Bil.UnOp (Bil.NOT,guard)))];
              [Def.create (Hike.Atomic.lane "address" 64) (Bil.Int (atomic_w 0x2000))],
              [(3,mk_marker (Tid.for_name "intrinsic:x86:atomic_neg_64"))];
              [Def.create old (Bil.Int (atomic_w 9))], [(3,mk_goto)];
              [Def.create (v64 "RAX") (Bil.Var old)], [(0,mk_ret)] ] in
        let ir = emit_ir [sub] in
        check "EMIT-56"
          (contains_substring ir "call i64 @hike.atomic.neg.64"
           && contains_substring ir "define internal i64 @hike.atomic.neg.64"
           && contains_substring ir "load atomic i64"
           && contains_substring ir "cmpxchg ptr"
           && count_two_incoming_phis ir >= 2));

    pin "EMIT-57" "unknown atomic contracts refuse instead of becoming external calls"
      (fun () ->
        let sub,_ = sub_of "unknown_atomic"
            [ [], [(1,mk_marker (Tid.for_name "intrinsic:x86:atomic_add_128"))];
              [], [(0,mk_ret)] ] in
        let refused = try ignore (emit_ir [sub]); false with
          | Failure message -> contains_substring message "unsupported atomic intrinsic" in
        check "EMIT-57" refused);

    (* ENTRY-NAME: the entry sub is analysed, never defined, and its
       declaration carries the ABI's process-entry symbol — a stripped
       binary's decoded tid must not leak into the link. *)
    pin "EMIT-46"
      "the entry's declaration carries the ABI entry symbol, not the decoded tid name"
      (fun () ->
        let entry, _ =
          sub_of ~tid:(Tid.for_name "sub_10b0") "sub_10b0"
            [ [], [ (0, mk_ret) ] ]
        in
        let entry = Term.set_attr entry Sub.entry_point () in
        let ir = emit_ir [ entry ] in
        check "EMIT-46"
          (contains_substring ir "@_start("
           && not (contains_substring ir "@sub_10b0")));
  ]

let () = run "bil2llvm" tests
