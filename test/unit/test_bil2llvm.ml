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
let count_two_incoming_phis (ir : string) : int =
  String.split_on_char '\n' ir
  |> List.filter (fun l -> contains_substring l " = phi i64 ")
  |> List.filter (fun l ->
      match String.split_on_char '[' l with
      | _ :: rest -> List.length rest = 2
      | [] -> false)
  |> List.length

(* One label per incoming: the token between ', %"' and the next '"'. *)
let tests : unit Alcotest.test list =
  [
    (* SCOPE: undef-read diagnostics stay with the sub that reads the lane. *)


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

    (* TLS offsets address distinct locations relative to the per-thread
       anchor. *)
    pin "EMIT-14" "TLS accesses preserve their offsets from the thread_local anchor"
      (fun () ->
        let tp = Hike.Abi.x86_64_sysv.thread_pointer in
        let m = memv "tls_m" in
        let out = v64 "tls_out" in
        let addr offset =
          Bil.BinOp
            (Bil.PLUS, Bil.Var tp, Bil.Int (Cbat_word.to_word (w64 offset)))
        in
        let store offset value =
          Def.create (memv (Printf.sprintf "tls_store_%d" offset))
            (Bil.Store
               ( Bil.Var m
               , addr offset
               , Bil.Int (Cbat_word.to_word (w64 value))
               , LittleEndian
               , `r64 ))
        in
        let ld =
          Def.create out
            (Bil.Load (Bil.Var m, addr 0x28, LittleEndian, `r64))
        in
        let sub, _ =
          sub_of "tls_anchor_sub"
            [ [ store 0x28 111; store 0x30 222; ld ],
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
          && contains_substring ir
               "getelementptr i8, ptr %tls_anchor, i64 40"
          && contains_substring ir
               "getelementptr i8, ptr %tls_anchor1, i64 48"
          && contains_substring ir "store i64 111"
          && contains_substring ir "store i64 222"
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
          { B2l.sm_type = Sm.Data; sm_const = false;
            sm_lo = 0x1000L; sm_hi = 0x1007L; sm_words = 1;
            sm_image = Some img; sm_copy_relocs = [] }
        in
        let spec =
          { empty_spec with
            B2l.spec_sections = [ Some meta ];
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
          { B2l.sm_type = Sm.Text; sm_const = true;
            sm_lo = 0x500L; sm_hi = 0x50FL; sm_words = 2;
            sm_image = Some text_img; sm_copy_relocs = [] }
        in
        let img = Bytes.make 8 '\000' in
        Bytes.set img 0 '\x42';
        let meta =
          { B2l.sm_type = Sm.Data; sm_const = false;
            sm_lo = 0x1000L; sm_hi = 0x1007L; sm_words = 1;
            sm_image = Some img; sm_copy_relocs = [] }
        in
        let spec =
          { empty_spec with
            B2l.spec_sections = [ Some text_meta; Some meta ];
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
          { B2l.sm_type = Sm.Text; sm_const = true;
            sm_lo = 0x500L; sm_hi = 0x50FL; sm_words = 2;
            sm_image = Some text_img; sm_copy_relocs = [] }
        in
        let img = Bytes.make 8 '\000' in
        Bytes.set img 0 '\x08';
        Bytes.set img 1 '\x05';
        let meta =
          { B2l.sm_type = Sm.Data; sm_const = false;
            sm_lo = 0x1000L; sm_hi = 0x1007L; sm_words = 1;
            sm_image = Some img; sm_copy_relocs = [] }
        in
        let spec =
          { empty_spec with
            B2l.spec_sections = [ Some text_meta; Some meta ] }
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
          { B2l.sm_type = Sm.Rodata; sm_const = true;
            sm_lo = 0x216948L; sm_hi = 0x21694FL; sm_words = 1;
            sm_image = Some ro_img; sm_copy_relocs = [] }
        in
        let img = Bytes.make 8 '\000' in
        Bytes.set img 0 'H';
        Bytes.set img 1 'i';
        Bytes.set img 2 '!';
        let meta =
          { B2l.sm_type = Sm.Data; sm_const = false;
            sm_lo = 0x1000L; sm_hi = 0x1007L; sm_words = 1;
            sm_image = Some img; sm_copy_relocs = [] }
        in
        let spec =
          { empty_spec with
            B2l.spec_sections = [ Some ro_meta; Some meta ] }
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
            ~dynamic_alloc_tids:
              (Core.Set.of_list (module Tid) [ Term.tid d_dec1; Term.tid d_dec2 ])
            sub
          |> Sm.set_layout
               { Sm.regions = []; window_param = false }
        in
        let ir = emit_ir [ sub ] in
        let count sub_str =
          String.split_on_char '\n' ir
          |> List.filter (fun l -> contains_substring l sub_str)
          |> List.length
        in
        check "EMIT-34"
          (contains_substring ir "getelementptr i8, ptr %vla, i64 4"
          && contains_substring ir "getelementptr i8, ptr %vla2, i64 8"
          && count " = alloca i8, i64 " = 2));
  ]

let () = run "bil2llvm" tests
