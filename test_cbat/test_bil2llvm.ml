(* Emitter tests: the first seam over bil2llvm (emit_program).
   Each fixture builds a BIR sub, emits it via emit_program with
   Theory.Target.unknown + ptrsize:64, and asserts on the textual IR
   (Llvm.print_module) — the same idiom check_allocas.sh uses. *)

open Test_common
open Bap.Std
open Bap_core_theory

module B2l = Hike.Bil2llvm
module Cu = Hike.Convutils

(* Emits a program of subs and returns the textual IR. *)
let emit_ir (subs : sub term list) : string =
  let llvm_ctx = Llvm.create_context () in
  let llvm_module = Llvm.create_module llvm_ctx "Test" in
  let prog = Program.create ~subs () in
  B2l.emit_program llvm_ctx llvm_module
    ~target:Theory.Target.unknown ~ptrsize:64
    ~symtab:None ~text_section:None ~section_remap:[] ~copy_relocs:[]
    [] prog;
  let s = Llvm.string_of_llmodule llvm_module in
  Llvm.dispose_module llvm_module;
  Llvm.dispose_context llvm_ctx;
  s

let check_ir (name : string) (must : string) (ir : string) : unit =
  check name (contains_substring ir must)

let count_substr (s : string) (sub : string) : int =
  let rec go i acc =
    if i + String.length sub > String.length s then acc
    else if String.sub s i (String.length sub) = sub then
      go (i + String.length sub) (acc + 1)
    else go (i + 1) acc
  in
  go 0 0

(* Checks a must-contain and a must-NOT-contain pair. *)
let check_ir_pair (name : string) (must : string) (must_not : string) (ir : string) : unit =
  check name (contains_substring ir must && not (contains_substring ir must_not))

(* ------------------------------------------------------------------ *)
(* Family 1: the FP-intrinsic table — every row emits its native op.  *)
(* ------------------------------------------------------------------ *)

let ivar64 (n : string) : var = Var.create ~is_virtual:false ~fresh:false n (Type.Imm 64)

(* One mapped-intrinsic call site, the production shape:
   [intrinsic:x0 := src; call @<name> with return <cont>; cont: ...]. *)
let mk_fp_call_sub (intr : string) (arg_defs : def term list) : sub term =
  let callee_tid = Tid.for_name intr in
  let caller = Blk.Builder.create () in
  let cont = Blk.Builder.create () in
  let exit = Blk.Builder.create () in
  let cont_tid = Tid.create () in
  (* The builder assigns its own tid; use it as the return target. *)
  let cont = Blk.Builder.init ~copy_defs:true (Blk.Builder.result cont) in
  ignore cont_tid;
  Blk.Builder.add_def cont (Def.create (v64 "fp_wb") (Bil.Var (ivar64 "intrinsic:y0")));
  Blk.Builder.add_jmp cont
    (Jmp.create ~cond:(Bil.BinOp (Bil.EQ, Bil.Var (v64 "fp_wb"), Bil.Int (w64 0)))
       (Ret (Direct (Tid.create ()))));
  let cont_blk = Blk.Builder.result cont in
  let cont_tid = Term.tid cont_blk in
  List.iter (Blk.Builder.add_def caller) arg_defs;
  Blk.Builder.add_jmp caller
    (Jmp.create
       (Call
          (Call.create ~return:(Direct cont_tid) ~target:(Direct callee_tid) ())));
  let sb = Sub.Builder.create ~name:"fp_caller" () in
  Sub.Builder.add_blk sb (Blk.Builder.result caller);
  Sub.Builder.add_blk sb cont_blk;
  Sub.Builder.add_blk sb (Blk.Builder.result exit);
  Sub.Builder.result sb

(* The bodyless mapped-intrinsic stub (the model interface sig). *)
let mk_fp_stub (intr : string) : sub term =
  let sb = Sub.Builder.create ~name:intr () in
  let sub = Sub.Builder.result sb in
  let sub = Term.set_attr sub Sub.intrinsic () in
  sub

let mk_fp_program (intr : string) (arg_defs : def term list) : sub term list =
  [ mk_fp_call_sub intr arg_defs; mk_fp_stub intr ]

(* The native op each table row must emit. *)
let fp_rows : (string * B2l.native_fp) list =
  [
    ("intrinsic:fmul_rne_ieee754_binary_64", FMUL);
    ("intrinsic:fmul_rne_ieee754_binary_32", FMUL);
    ("intrinsic:fadd_rne_ieee754_binary_64", FADD);
    ("intrinsic:fadd_rne_ieee754_binary_32", FADD);
    ("intrinsic:fsub_rne_ieee754_binary_64", FSUB);
    ("intrinsic:fsub_rne_ieee754_binary_32", FSUB);
    ("intrinsic:fdiv_rne_ieee754_binary_64", FDIV);
    ("intrinsic:fdiv_rne_ieee754_binary_32", FDIV);
    ("intrinsic:frem_rne_ieee754_binary_64", FREM);
    ("intrinsic:frem_rne_ieee754_binary_32", FREM);
    ("intrinsic:forder_rne_ieee754_binary_64", FORDER);
    ("intrinsic:forder_rne_ieee754_binary_32", FORDER);
    ("intrinsic:is_nan_rne_ieee754_binary_64", ISNAN);
    ("intrinsic:is_nan_rne_ieee754_binary_32", ISNAN);
    ("intrinsic:is_nan_ieee754_binary", ISNAN);
    ("intrinsic:is_nan_rne_ieee754_binary", ISNAN);
    ("intrinsic:forder_ieee754_binary", FORDER);
    ("intrinsic:forder_rne_ieee754_binary", FORDER);
    ("intrinsic:cast_sfloat_rne_ieee754_binary_64", SFLOAT);
    ("intrinsic:cast_sint_rne_ieee754_binary_64", SINT);
    ("intrinsic:fmul_rne_ieee754_binary", FMUL);
    ("intrinsic:fadd_rne_ieee754_binary", FADD);
    ("intrinsic:fsub_rne_ieee754_binary", FSUB);
    ("intrinsic:fdiv_rne_ieee754_binary", FDIV);
    ("intrinsic:frem_rne_ieee754_binary", FREM);
    ("intrinsic:hlt", FHLT);
  ]

(* The IR opcode each native_fp constructor emits. *)
let op_ir_string = function
  | B2l.FMUL -> "fmul"
  | B2l.FADD -> "fadd"
  | B2l.FSUB -> "fsub"
  | B2l.FDIV -> "fdiv"
  | B2l.FREM -> "frem"
  | B2l.SFLOAT -> "sitofp"
  | B2l.SINT -> "fptosi"
  | B2l.FORDER -> "fcmp olt"
  | B2l.FHLT -> "unreachable"
  | B2l.ISNAN -> "fcmp uno"

let string_of_natfp = function
  | B2l.FMUL -> "FMUL"
  | B2l.FADD -> "FADD"
  | B2l.FSUB -> "FSUB"
  | B2l.FDIV -> "FDIV"
  | B2l.FREM -> "FREM"
  | B2l.SFLOAT -> "SFLOAT"
  | B2l.SINT -> "SINT"
  | B2l.FORDER -> "FORDER"
  | B2l.FHLT -> "FHLT"
  | B2l.ISNAN -> "ISNAN"

let run_fp_table () =
  (* Every row maps. *)
  List.iter
    (fun (name, op) ->
      check ("FP-TABLE " ^ name ^ ": native_fp_op resolves")
        (match B2l.native_fp_op ("@" ^ name) with Some _ -> true | None -> false);
      check ("FP-TABLE " ^ name ^ ": native_fp_op gives " ^ string_of_natfp op)
        (match B2l.native_fp_op ("@" ^ name) with
         | Some op' -> op' = op
         | None -> false))
    fp_rows;
  (* Rows NOT in the table must not map. *)
  check "FP-TABLE: unmapped name returns None"
    (match B2l.native_fp_op "@intrinsic:not_a_real_intrinsic" with
     | None -> true
     | Some _ -> false);
  (* One binop row emission: fadd_64 emits fadd, no soft-float call. *)
  let x0 = ivar64 "intrinsic:x0" in
  let x1 = ivar64 "intrinsic:x1" in
  let d0 = Def.create x0 (Bil.Int (w64 0x4059)) in
  let d1 = Def.create x1 (Bil.Int (w64 0x4008)) in
  let subs = mk_fp_program "intrinsic:fadd_rne_ieee754_binary_64" [ d0; d1 ] in
  let ir = emit_ir subs in
  check_ir "FP-TABLE fadd_64: the native fadd is emitted (not a soft-float call)" "fadd" ir;
  check "FP-TABLE fadd_64: no soft-float call survives"
    (not (contains_substring ir "call") || not (contains_substring ir "@intrinsic:fadd"));
  (* SFLOAT: sitofp emitted. *)
  let ir_sfloat =
    emit_ir (mk_fp_program "intrinsic:cast_sfloat_rne_ieee754_binary_64" [ d0 ])
  in
  check_ir "FP-TABLE sfloat_64: the native sitofp is emitted" "sitofp" ir_sfloat;
  (* SINT: fptosi emitted. *)
  let ir_sint =
    emit_ir (mk_fp_program "intrinsic:cast_sint_rne_ieee754_binary_64" [ d0 ])
  in
  check_ir "FP-TABLE sint_64: the native fptosi is emitted" "fptosi" ir_sint;
  (* FORDER: fcmp olt emitted. *)
  let ir_forder =
    emit_ir
      (mk_fp_program "intrinsic:forder_rne_ieee754_binary_64" [ d0; d1 ])
  in
  check_ir "FP-TABLE forder_64: the native fcmp olt is emitted" "fcmp olt" ir_forder;
  (* ISNAN: fcmp uno emitted. *)
  let ir_isnan =
    emit_ir (mk_fp_program "intrinsic:is_nan_rne_ieee754_binary_64" [ d0 ])
  in
  check_ir "FP-TABLE isnan_64: the native fcmp uno is emitted" "fcmp uno" ir_isnan;
  (* FHLT: unreachable emitted. *)
  let ir_hlt = emit_ir (mk_fp_program "intrinsic:hlt" []) in
  check_ir "FP-TABLE hlt: the trap (unreachable) is emitted" "unreachable" ir_hlt;
  (* A dropped row degrades loudly, the c484e13 class: a caller of an
     unmapped name gets the guarded warning. *)
  let x0b = ivar64 "intrinsic:x0" in
  let db = Def.create x0b (Bil.Int (w64 7)) in
  let ir_un =
    capture_stderr (fun () ->
        ignore (emit_ir (mk_fp_program "intrinsic:not_a_real_intrinsic" [ db ])))
  in
  check "FP-TABLE: an unmapped name emits the guarded warning on stderr"
    (contains_substring ir_un "hike: guarded:")


let run_poison () =
  (* The warned-poison class, pinned: an Unbounded-tagged stack access warns
     through Hike_diag and still emits (create_exp); a Dead-tagged access
     emits a poison value. *)
  let rsp = v64 "RSP" in
  let m = memv "poison_m" in
  let t = v64 "poison_t" in
  let addr = Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 16)) in
  let ld = Def.create t (Bil.Load (Bil.Var m, addr, LittleEndian, `r64)) in
  (* The store consumes the LOAD result: the poison is textually live. *)
  let st =
    Def.create m (Bil.Store (Bil.Var m, addr, Bil.Var t, LittleEndian, `r64))
  in
  let mk_sub nm =
    let caller = Blk.Builder.create () in
    Blk.Builder.add_def caller ld;
    Blk.Builder.add_def caller st;
    Blk.Builder.add_jmp caller (Jmp.create (Ret (Direct (Tid.create ()))));
    let sb = Sub.Builder.create ~name:nm () in
    Sub.Builder.add_blk sb (Blk.Builder.result caller);
    Sub.Builder.result sb
  in
  let unb_sub = mk_sub "poison_unb" in
  let dead_sub = mk_sub "poison_dead" in
  (* Unbounded on the load/store; Dead on the second pair. *)
  let unb_info : Cu.vsa_info =
    Cu.mk_vsa_info
      ~offsets:
        [ (Term.tid ld, Cu.Unbounded); (Term.tid st, Cu.Unbounded) ]
      ~k_ranges:[] ~regions:[] ~stack_plan:[] ~degraded:false ~vla_bounds:[]
  in
  let dead_info : Cu.vsa_info =
    Cu.mk_vsa_info
      ~offsets:[ (Term.tid ld, Cu.Dead) ]
      ~k_ranges:[] ~regions:[] ~stack_plan:[] ~degraded:false ~vla_bounds:[]
  in
  Kb.provide
    (Tid.Map.singleton (Term.tid unb_sub) unb_info);
  Kb.provide (Tid.Map.singleton (Term.tid dead_sub) dead_info);
  let ir_holder = ref "" in
  let err_unb =
    capture_stderr (fun () -> ir_holder := emit_ir [ unb_sub ])
  in
  check "POISON: the Unbounded access warns through the Hike_diag channel"
    (contains_substring err_unb "hike: guarded: sub");
  check "POISON: the Unbounded access still emits (create_exp, no crash)"
    (contains_substring !ir_holder "load");
  let ir_holder2 = ref "" in
  let err_dead =
    capture_stderr (fun () -> ir_holder2 := emit_ir [ dead_sub ])
  in
  check "POISON: the Dead-tagged access emits a poison value"
    (contains_substring !ir_holder2 "poison");
  check "POISON: the Dead-tagged access does NOT warn"
    (not (contains_substring err_dead "hike: guarded:"))

(* Family 3: restore_sp_after_call idempotence (the L-E1e class).     *)
(* ------------------------------------------------------------------ *)

let run_sp_restore () =
  (* A direct call: after it, the sp local rebinds to post-push + 8. *)
  let rsp = v64 "RSP" in
  let m = memv "sp_m" in
  let callee_tid = Tid.for_name "sp_callee" in
  let caller = Blk.Builder.create () in
  let cont0 = Blk.Builder.create () in
  let cont = Blk.Builder.init ~copy_defs:true (Blk.Builder.result cont0) in
  Blk.Builder.add_jmp cont (Jmp.create (Ret (Direct (Tid.create ()))));
  let cont_blk = Blk.Builder.result cont in
  let cont_tid = Term.tid cont_blk in
  (* The push: RSP := RSP - 8; mem[RSP] := retaddr — the lifted call shape. *)
  Blk.Builder.add_def caller (Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 8))));
  Blk.Builder.add_def caller
    (Def.create m (Bil.Store (Bil.Var m, Bil.Var rsp, Bil.Int (w64 1234), LittleEndian, `r64)));
  Blk.Builder.add_jmp caller
    (Jmp.create
       (Call (Call.create ~return:(Direct cont_tid) ~target:(Direct callee_tid) ())));
  let sb = Sub.Builder.create ~name:"sp_caller" () in
  Sub.Builder.add_blk sb (Blk.Builder.result caller);
  Sub.Builder.add_blk sb cont_blk;
  let caller = Sub.Builder.result sb in
  let callee =
    let bb2 = Blk.Builder.create () in
    Blk.Builder.add_jmp bb2 (Jmp.create (Ret (Direct (Tid.create ()))));
    let sb2 = Sub.Builder.create ~name:"sp_callee" () in
    Sub.Builder.add_blk sb2 (Blk.Builder.result bb2);
    Sub.Builder.result sb2
  in
  let ir = emit_ir [ caller; callee ] in
  (* The restore emits an add of 8 after the call. *)
  check "SP-RESTORE: after a call, the sp local rebinds (+8 present)"
    (contains_substring ir "add i64")

(* ------------------------------------------------------------------ *)
(* Family 4: cast preservation at BIL type boundaries.                 *)
(* ------------------------------------------------------------------ *)

let run_casts () =
  (* A tagged (singleton Range) stack store whose DATA is a narrower cast:
     the zext/trunc sits at the store, not dropped or promoted. *)
  let rsp = v64 "RSP" in
  let m = memv "cast_m" in
  let src = v64 "cast_src" in
  let addr = Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 16)) in
  let d_src = Def.create src (Bil.Int (w64 0x7B)) in
  let d_st =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           addr,
           Bil.Cast (Bil.UNSIGNED, 32, Bil.Var src),
           LittleEndian,
           `r64 ))
  in
  let bb = Blk.Builder.create () in
  Blk.Builder.add_def bb d_src;
  Blk.Builder.add_def bb d_st;
  let exit0 = Blk.Builder.create () in
  let exit = Blk.Builder.init ~copy_defs:true (Blk.Builder.result exit0) in
  Blk.Builder.add_jmp exit (Jmp.create (Ret (Direct (Tid.create ()))));
  let exit_blk = Blk.Builder.result exit in
  Blk.Builder.add_jmp bb
    (Jmp.create ~cond:(Bil.BinOp (Bil.EQ, Bil.Var src, Bil.Int (w64 0x7B)))
       (Goto (Direct (Term.tid exit_blk))));
  let sb = Sub.Builder.create ~name:"cast_sub" () in
  Sub.Builder.add_blk sb (Blk.Builder.result bb);
  Sub.Builder.add_blk sb exit_blk;
  let sub = Sub.Builder.result sb in
  (* Singleton Range tag on the store: the converted-cell shape. *)
  let info : Cu.vsa_info =
    Cu.mk_vsa_info
      ~offsets:[ (Term.tid d_st, Cu.Range (-16L, -16L)) ]
      ~k_ranges:[] ~regions:[] ~stack_plan:[] ~degraded:false ~vla_bounds:[]
  in
  Kb.provide (Tid.Map.singleton (Term.tid sub) info);
  let ir = emit_ir [ sub ] in
  check "CAST: the tagged store reaches memory with its narrowing cast intact"
    (contains_substring ir "store" && contains_substring ir "trunc")

(* ------------------------------------------------------------------ *)
(* Family 5: the substring-complete golden (singleton slot + one      *)
(* fission region).                                                   *)
(* ------------------------------------------------------------------ *)

let run_golden () =
  (* The golden sub: an entry, a stack load and store (singleton Range
     tags via Kb.provide, the D4 fixture shape), and a ret. *)
  let rsp = v64 "RSP" in
  let m = memv "gold_m" in
  let ld_var = v64 "gold_ld" in
  let st_val = v64 "gold_st" in
  let ld_addr = Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 16)) in
  let st_addr = Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 24)) in
  let d_ld = Def.create ld_var (Bil.Load (Bil.Var m, ld_addr, LittleEndian, `r64)) in
  let d_st = Def.create m (Bil.Store (Bil.Var m, st_addr, Bil.Var ld_var, LittleEndian, `r64)) in
  let d_val = Def.create st_val (Bil.BinOp (Bil.PLUS, Bil.Var ld_var, Bil.Int (w64 1))) in
  let exit0 = Blk.Builder.create () in
  let exit = Blk.Builder.init ~copy_defs:true (Blk.Builder.result exit0) in
  Blk.Builder.add_jmp exit (Jmp.create (Ret (Direct (Tid.create ()))));
  let exit_blk = Blk.Builder.result exit in
  let exit_tid = Term.tid exit_blk in
  let bb = Blk.Builder.create () in
  Blk.Builder.add_def bb d_ld;
  Blk.Builder.add_def bb d_st;
  Blk.Builder.add_def bb d_val;
  Blk.Builder.add_jmp bb
    (Jmp.create ~cond:(Bil.BinOp (Bil.EQ, Bil.Var st_val, Bil.Int (w64 0)))
       (Goto (Direct exit_tid)));
  Blk.Builder.add_jmp bb (Jmp.create (Goto (Direct exit_tid)));
  let sb = Sub.Builder.create ~name:"golden_sub" () in
  Sub.Builder.add_blk sb (Blk.Builder.result bb);
  Sub.Builder.add_blk sb exit_blk;
  let sub = Sub.Builder.result sb in
  (* The vsa_info: singleton Range tags on both accesses + one
     convertible region, the write-closed fission shape. *)
  let info : Cu.vsa_info =
    let offsets =
      [
        (Term.tid d_ld, Cu.Range (-16L, -16L));
        (Term.tid d_st, Cu.Range (-24L, -24L));
      ]
    in
    let region =
      Cu.
        {
          id = 0;
          span = (-24L, -16L);
          members = [];
          convertible = true;
          max_width = 64;
        }
    in
    Cu.mk_vsa_info ~offsets ~k_ranges:[]
      ~regions:[ region ] ~stack_plan:[ region ]
      ~degraded:false ~vla_bounds:[]
  in
  Kb.provide (Tid.Map.singleton (Term.tid sub) info);
  let ir = emit_ir [ sub ] in
  check_ir "GOLDEN: the golden sub emits a function define" "define" ir;
  check_ir "GOLDEN: entry alloca lane (stack_rN or frame) present" "alloca" ir;
  check_ir "GOLDEN: a load reaches the frame" "load" ir;
  check_ir "GOLDEN: a store reaches the frame" "store" ir;
  check_ir "GOLDEN: the jmp cond comparison emitted" "icmp" ir;
  check_ir "GOLDEN: a branch on the cond" "br " ir;
  check_ir "GOLDEN: a return is emitted" "ret" ir;
  check_ir "GOLDEN: i64 lanes (ptrsize 64)" "i64" ir

(* ------------------------------------------------------------------ *)

let run () =
  run_fp_table ();
  run_poison ();
  run_sp_restore ();
  run_casts ();
  run_golden ()
