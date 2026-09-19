(* Jump-compiler pins: each idiom family compiles to the exact
   simplified comparison (pinned by structural equality), consumed flag
   defs die, reused value vars survive, the CFG is unchanged, and the
   residual cases (cross-block flags, unknown opcode, CF-preserved
   inc/dec, inconsistent facts) pass through untouched. *)

open Bap.Std
open Bap_core_theory
open Test_common
open Test_fixtures

module J = struct
  let compile_sub s = Hike.Jump.compile_sub jump_target s
end

let w0_32 = Bil.Int (Word.zero 32)
let w0_64 = Bil.Int (Word.zero 64)

(* The cmp/test fixture universe. *)
let x = v64 "t13_x"
let y = v64 "t13_y"
let t = v64 "t13_t"
let zf = v1 "ZF"
let cf = v1 "CF"
let sf = v1 "SF"
let ovf = v1 "OF"
let pf = v1 "PF"

let xv = Bil.Var x
let yv = Bil.Var y
let tv = Bil.Var t

let sub_of_defs_and_jmp (name : string) (defs : def term list) (cond : exp) :
    sub term * tid =
  let sub, tids = sub_of name [ defs, [ (1, fun t -> mk_jmp_to t cond) ]; [], [] ] in
  (sub, tids.(1))

(* The entry block of the compiled sub (the first block). *)
let entry_of (s : sub term) : blk term =
  Term.enum blk_t s |> Seq.hd_exn

let jmp_cond_of (s : sub term) : exp =
  let blk = entry_of s in
  let j = Term.enum jmp_t blk |> Seq.hd_exn in
  Jmp.cond j

let defs_of (s : sub term) : def term list =
  Term.enum def_t (entry_of s) |> Seq.to_list

let has_def_for (s : sub term) (v : var) : bool =
  Base.List.exists (defs_of s) ~f:(fun d -> Var.equal (Def.lhs d) v)

(* The full sub/cmp flag-def set (the lifter's shapes over x−y). *)
let cmp_defs ?(zf_rhs = `Tmp) ?(with_all = true) () : def term list =
  let diff = Bil.BinOp (Bil.MINUS, xv, yv) in
  let zf_def =
    match zf_rhs with
    | `Tmp -> Def.create zf (Bil.BinOp (Bil.EQ, w0_32, tv))
    | `Inline -> Def.create zf (Bil.BinOp (Bil.EQ, w0_32, diff))
    | `Of_x_y -> Def.create zf (Bil.BinOp (Bil.EQ, w0_32, Bil.Var x))
    | `None -> Def.create zf (Bil.Int (Word.zero 1))
  in
  if not with_all then [ zf_def; Def.create cf (Bil.BinOp (Bil.LT, xv, yv)) ]
  else
    [
      Def.create t diff;
      zf_def;
      Def.create cf (Bil.BinOp (Bil.LT, xv, yv));
      Def.create sf (Bil.Cast (Bil.HIGH, 1, tv));
      Def.create
        ovf
        (Bil.Cast
           ( Bil.HIGH
           , 1
           , Bil.BinOp
               ( Bil.AND
               , Bil.BinOp (Bil.XOR, xv, yv)
               , Bil.BinOp (Bil.XOR, xv, tv) ) ));
    ]

let v_not = Bil.UnOp (Bil.NOT, Bil.Var zf)
let cf_or_zf = Bil.BinOp (Bil.OR, Bil.Var cf, Bil.Var zf)
let n_cf_or_zf = Bil.UnOp (Bil.NOT, cf_or_zf)
let xor_core =
  Bil.BinOp
    ( Bil.AND
    , Bil.BinOp (Bil.OR, Bil.Var sf, Bil.Var ovf)
    , Bil.UnOp (Bil.NOT, Bil.BinOp (Bil.AND, Bil.Var sf, Bil.Var ovf)) )
let zf_or_core = Bil.BinOp (Bil.OR, Bil.Var zf, xor_core)
let n_zf_or_core = Bil.UnOp (Bil.NOT, zf_or_core)
let n_core = Bil.UnOp (Bil.NOT, xor_core)

let run () : unit =
  Printf.printf "-- jump compiler\n";

  (* jz over cmp, inline diff: (x−y)=0 folds to x=y; ZF def dies. *)
  let s, _ = sub_of_defs_and_jmp "t13_jz" (cmp_defs ~zf_rhs:`Inline ()) (Bil.Var zf) in
  let s' = J.compile_sub s in
  check "t13: jz → x = y"
    (Exp.equal (jmp_cond_of s') (Bil.BinOp (Bil.EQ, xv, yv)));
  check "t13: jz consumed ZF def" (not (has_def_for s' zf));

  (* the counter-loop shape (F1), reuse form: tmp := i−k; ZF := 0 =
     t; jnz → t != 0 — the var REUSED, never re-substituted; the ZF
     def dies, the tmp survives. *)
  let s, _ = sub_of_defs_and_jmp "t13_jne_tmp" (cmp_defs ()) v_not in
  let s' = J.compile_sub s in
  check "t13: jne → t != 0 (reuse)"
    (Exp.equal (jmp_cond_of s') (Bil.BinOp (Bil.NEQ, tv, w0_64)));
  check "t13: jne consumed ZF def" (not (has_def_for s' zf));
  check "t13: reused tmp def survives" (has_def_for s' t);

  (* the unsigned borrow family. *)
  let s, _ = sub_of_defs_and_jmp "t13_jb" (cmp_defs ~with_all:false ()) (Bil.Var cf) in
  let s' = J.compile_sub s in
  check "t13: jb → x <u y" (Exp.equal (jmp_cond_of s') (Bil.BinOp (Bil.LT, xv, yv)));
  check "t13: jb consumed CF def" (not (has_def_for s' cf));

  (* the ADD-carry CF shape: the lifter emits the carry as the
     LT-shaped fact (d <u a) — the comparison IS the carry's
     definition, so jb consumes it shape-honestly (the fact is
     verbatim-faithful for both the sub borrow and the add carry). *)
  let add_defs =
    [
      Def.create t (Bil.BinOp (Bil.PLUS, xv, yv));
      Def.create cf (Bil.BinOp (Bil.LT, tv, xv));
    ] in
  let s, _ = sub_of_defs_and_jmp "t13_jb_add" add_defs (Bil.Var cf) in
  let s' = J.compile_sub s in
  check "t13: jb over add-carry → t <u x (the carry, verbatim)"
    (Exp.equal (jmp_cond_of s') (Bil.BinOp (Bil.LT, tv, xv)));
  check "t13: jb over add consumed CF def" (not (has_def_for s' cf));
  check "t13: add's sum def survives (the cond reuses it)" (has_def_for s' t);

  let s, _ = sub_of_defs_and_jmp "t13_jae" (cmp_defs ~with_all:false ()) (Bil.UnOp (Bil.NOT, Bil.Var cf)) in
  let s' = J.compile_sub s in
  check "t13: jae → y <=u x (complement flips operands, no NOT)"
    (Exp.equal (jmp_cond_of s') (Bil.BinOp (Bil.LE, yv, xv)));

  let s, _ = sub_of_defs_and_jmp "t13_jbe" (cmp_defs ()) cf_or_zf in
  let s' = J.compile_sub s in
  check "t13: jbe → x <=u y" (Exp.equal (jmp_cond_of s') (Bil.BinOp (Bil.LE, xv, yv)));
  check "t13: jbe consumed CF and ZF" (not (has_def_for s' cf) && not (has_def_for s' zf));

  let s, _ = sub_of_defs_and_jmp "t13_ja" (cmp_defs ()) n_cf_or_zf in
  let s' = J.compile_sub s in
  check "t13: ja → y <u x" (Exp.equal (jmp_cond_of s') (Bil.BinOp (Bil.LT, yv, xv)));

  (* the signed family over the sub shapes. *)
  let s, _ = sub_of_defs_and_jmp "t13_jl" (cmp_defs ()) xor_core in
  let s' = J.compile_sub s in
  check "t13: jl → x <s y" (Exp.equal (jmp_cond_of s') (Bil.BinOp (Bil.SLT, xv, yv)));

  let s, _ = sub_of_defs_and_jmp "t13_jle" (cmp_defs ()) zf_or_core in
  let s' = J.compile_sub s in
  check "t13: jle → x <=s y" (Exp.equal (jmp_cond_of s') (Bil.BinOp (Bil.SLE, xv, yv)));

  let s, _ = sub_of_defs_and_jmp "t13_jg" (cmp_defs ()) n_zf_or_core in
  let s' = J.compile_sub s in
  check "t13: jg → y <s x" (Exp.equal (jmp_cond_of s') (Bil.BinOp (Bil.SLT, yv, xv)));

  let s, _ = sub_of_defs_and_jmp "t13_jge" (cmp_defs ()) n_core in
  let s' = J.compile_sub s in
  check "t13: jge → y <=s x" (Exp.equal (jmp_cond_of s') (Bil.BinOp (Bil.SLE, yv, xv)));

  (* test a,b; jz → (x&y) = 0 (the conjunction kept, constant-right). *)
  let and_defs =
    [ Def.create zf (Bil.BinOp (Bil.EQ, w0_32, Bil.BinOp (Bil.AND, xv, yv))) ] in
  let s, _ = sub_of_defs_and_jmp "t13_test" and_defs (Bil.Var zf) in
  let s' = J.compile_sub s in
  check "t13: test jz → (x&y) = 0"
    (Exp.equal
       (jmp_cond_of s')
       (Bil.BinOp (Bil.EQ, Bil.BinOp (Bil.AND, xv, yv), Bil.Int (Word.zero 64))));

  (* THE TEST/AND GROUP (the lifter's memory-operand test shape): the
     flag defs — ZF := (x&y) = 0, SF := high:1[x&y], CF := 0, OF := 0.
     With OF ≡ 0 the signed families run on SF alone. *)
  let test_group_defs ?(with_of = true) () : def term list =
    let a = Bil.BinOp (Bil.AND, xv, yv) in
    let base =
      [
        Def.create zf (Bil.BinOp (Bil.EQ, w0_32, a));
        Def.create sf (Bil.Cast (Bil.HIGH, 1, a));
        Def.create cf (Bil.Int (Word.zero 1));
      ] in
    if with_of then Def.create ovf (Bil.Int (Word.zero 1)) :: base else base in
  let test_core =
    Bil.BinOp
      ( Bil.AND
      , Bil.BinOp (Bil.OR, Bil.Var sf, Bil.Var ovf)
      , Bil.UnOp (Bil.NOT, Bil.BinOp (Bil.AND, Bil.Var sf, Bil.Var ovf)) ) in
  let test_jl_cond = test_core in
  let test_jle_cond = Bil.BinOp (Bil.OR, Bil.Var zf, test_core) in
  let zero64 = Bil.Int (Word.zero 64) in
  let and_e = Bil.BinOp (Bil.AND, xv, yv) in
  let s, _ = sub_of_defs_and_jmp "t13_test_jl" (test_group_defs ()) test_jl_cond in
  let s' = J.compile_sub s in
  check "t13: test jl → (x&y) <s 0 (OF ≡ 0)"
    (Exp.equal (jmp_cond_of s') (Bil.BinOp (Bil.SLT, and_e, zero64)));
  check "t13: test jl consumed SF and OF defs"
    (not (has_def_for s' sf) && not (has_def_for s' ovf));

  let s, _ = sub_of_defs_and_jmp "t13_test_jle" (test_group_defs ()) test_jle_cond in
  let s' = J.compile_sub s in
  check "t13: test jle → (x&y) <=s 0"
    (Exp.equal (jmp_cond_of s') (Bil.BinOp (Bil.SLE, and_e, zero64)));

  let s, _ = sub_of_defs_and_jmp "t13_test_jg"
      (test_group_defs ())
      (Bil.UnOp (Bil.NOT, test_jle_cond)) in
  let s' = J.compile_sub s in
  check "t13: test jg → 0 <s (x&y)"
    (Exp.equal (jmp_cond_of s') (Bil.BinOp (Bil.SLT, zero64, and_e)));

  let s, _ = sub_of_defs_and_jmp "t13_test_jge"
      (test_group_defs ())
      (Bil.UnOp (Bil.NOT, test_jl_cond)) in
  let s' = J.compile_sub s in
  check "t13: test jge → 0 <=s (x&y)"
    (Exp.equal (jmp_cond_of s') (Bil.BinOp (Bil.SLE, zero64, and_e)));

  let s, _ = sub_of_defs_and_jmp "t13_test_je" (test_group_defs ()) (Bil.Var zf) in
  let s' = J.compile_sub s in
  check "t13: test je → (x&y) = 0 (full group)"
    (Exp.equal (jmp_cond_of s') (Bil.BinOp (Bil.EQ, and_e, zero64)));

  let s, _ = sub_of_defs_and_jmp "t13_test_jne" (test_group_defs ()) v_not in
  let s' = J.compile_sub s in
  check "t13: test jne → (x&y) != 0 (full group)"
    (Exp.equal (jmp_cond_of s') (Bil.BinOp (Bil.NEQ, and_e, zero64)));

  (* RESIDUAL: the signed family over a test group whose OF def is
     MISSING (cross-block OF): no OF fact, no OF ≡ 0 fact → the
     identity. *)
  let s, _ =
    sub_of_defs_and_jmp "t13_test_noof" (test_group_defs ~with_of:false ()) test_jl_cond in
  let s' = J.compile_sub s in
  check "t13: test jl without OF stays residual" (Exp.equal (jmp_cond_of s') test_jl_cond);

  (* FOLD: cmp x,0 — (x−0)=0 folds; jnz → x != 0. *)
  let zero = Bil.Int (Word.zero 64) in
  let fold_defs =
    [
      Def.create zf (Bil.BinOp (Bil.EQ, w0_32, Bil.BinOp (Bil.MINUS, xv, zero)));
      Def.create cf (Bil.BinOp (Bil.LT, xv, zero));
    ] in
  let s, _ = sub_of_defs_and_jmp "t13_fold0" fold_defs v_not in
  let s' = J.compile_sub s in
  check "t13: cmp x,0 jnz → x != 0" (Exp.equal (jmp_cond_of s') (Bil.BinOp (Bil.NEQ, xv, zero)));

  (* FOLD: a−a → the constant-true cond. *)
  let aa_defs =
    [ Def.create zf (Bil.BinOp (Bil.EQ, w0_32, Bil.BinOp (Bil.MINUS, xv, xv))) ] in
  let s, _ = sub_of_defs_and_jmp "t13_aa" aa_defs (Bil.Var zf) in
  let s' = J.compile_sub s in
  check "t13: a−a jz → 1" (Exp.equal (jmp_cond_of s') (Bil.Int (Word.one 1)));

  (* WIDTH-MINIMAL: 32-bit operands compare at 32 bits (the zero
     constant rides the operand width). *)
  let x32 = Var.create ~is_virtual:false ~fresh:false "t13_x32" (Type.Imm 32) in
  let y32 = Var.create ~is_virtual:false ~fresh:false "t13_y32" (Type.Imm 32) in
  let x32v = Bil.Var x32 and y32v = Bil.Var y32 in
  let w32_defs =
    [ Def.create zf (Bil.BinOp (Bil.EQ, Bil.Int (Word.zero 32), Bil.BinOp (Bil.MINUS, x32v, y32v))) ] in
  let s, _ = sub_of_defs_and_jmp "t13_w32" w32_defs (Bil.Var zf) in
  let s' = J.compile_sub s in
  check "t13: 32-bit cmp jz → x32 = y32 (at the def's width)"
    (Exp.equal (jmp_cond_of s') (Bil.BinOp (Bil.EQ, x32v, y32v)));

  (* BOTH jmps of a block compile; the CFG is unchanged. *)
  let s, tids =
    sub_of "t13_pair"
      [ cmp_defs (), [ (2, fun t -> mk_jmp_to t (Bil.Var zf)); (1, fun t -> mk_jmp_to t v_not) ];
        [], [ (0, mk_ret) ];
        [], [] ]
  in
  let exit_tid = tids.(1) in
  let body_tid = tids.(2) in
  let n_blks = Seq.length (Term.enum blk_t s) in
  let s' = J.compile_sub s in
  let blk' = entry_of s' in
  let jmps = Term.enum jmp_t blk' |> Seq.to_list in
  check "t13: both jmps compile"
    (Base.List.exists jmps ~f:(fun j -> Exp.equal (Jmp.cond j) (Bil.BinOp (Bil.EQ, tv, w0_64)))
    && Base.List.exists jmps ~f:(fun j -> Exp.equal (Jmp.cond j) (Bil.BinOp (Bil.NEQ, tv, w0_64))));
  check "t13: CFG unchanged (3 blocks, targets intact)"
    (Int.equal n_blks (Seq.length (Term.enum blk_t s'))
    && Base.List.exists jmps ~f:(fun j ->
        match Jmp.kind j with
        | Goto (Direct tid) -> Tid.equal tid exit_tid
        | _ -> false)
    && Base.List.exists jmps ~f:(fun j ->
        match Jmp.kind j with
        | Goto (Direct tid) -> Tid.equal tid body_tid
        | _ -> false));

  (* CROSS-BLOCK: the flag def lives in a predecessor — the unique
     reaching definition at the block entry serves the facts. *)
  let s, tids =
    sub_of "t13_cross"
      [ [ Def.create zf (Bil.BinOp (Bil.EQ, w0_32, Bil.BinOp (Bil.MINUS, xv, yv))) ],
        [ (1, mk_goto) ];
        [], [ (2, fun t -> mk_jmp_to t (Bil.Var zf)) ];
        [], [ (0, mk_ret) ] ]
  in
  let use_tid = tids.(1) in
  let pred_tid = tids.(0) in
  let s' = J.compile_sub s in
  let use_blk =
    Term.enum blk_t s'
    |> Seq.find_exn ~f:(fun b -> Tid.equal (Term.tid b) use_tid) in
  let j' = Term.enum jmp_t use_blk |> Seq.hd_exn in
  check "t13: cross-block flag compiles to the comparison"
    (Exp.equal (Jmp.cond j') (Bil.BinOp (Bil.EQ, xv, yv)));
  let pred_blk' =
    Term.enum blk_t s'
    |> Seq.find_exn ~f:(fun b -> Tid.equal (Term.tid b) pred_tid) in
  check
    "t13: cross-block ZF def dies (var unused sub-wide after the rewrite)"
    (not
       (Term.enum def_t pred_blk'
       |> Seq.exists ~f:(fun d -> Var.equal (Def.lhs d) zf)));

  (* RESIDUAL: an AMBIGUOUS cross-block flag — two predecessors define
     ZF differently, no unique reaching def at the block entry. *)
  let s, tids =
    sub_of "t13_cross_amb"
      [ [], [ (1, mk_goto); (2, mk_goto) ];
        [ Def.create zf (Bil.BinOp (Bil.EQ, w0_32, xv)) ], [ (3, mk_goto) ];
        [ Def.create zf (Bil.BinOp (Bil.EQ, w0_32, yv)) ], [ (3, mk_goto) ];
        [], [ (4, fun t -> mk_jmp_to t (Bil.Var zf)) ];
        [], [ (0, mk_ret) ] ]
  in
  let use2_tid = tids.(3) in
  let s' = J.compile_sub s in
  let use_blk2 =
    Term.enum blk_t s'
    |> Seq.find_exn ~f:(fun b -> Tid.equal (Term.tid b) use2_tid) in
  let j2 = Term.enum jmp_t use_blk2 |> Seq.hd_exn in
  check "t13: ambiguous cross-block flag stays residual"
    (Exp.equal (Jmp.cond j2) (Bil.Var zf));

  (* RESIDUAL: unknown opcode (PF:unknown) — the identity. *)
  let pf_defs = [ Def.create pf (Bil.Unknown ("unknown[bits]", Type.Imm 1)) ] in
  let s, _ = sub_of_defs_and_jmp "t13_pf" pf_defs (Bil.Var pf) in
  let s' = J.compile_sub s in
  check "t13: unknown opcode stays residual" (Exp.equal (jmp_cond_of s') (Bil.Var pf));

  (* RESIDUAL: inconsistent facts — jbe whose ZF is not the same
     subtraction as CF's borrow. *)
  let inc_defs =
    [
      Def.create t (Bil.BinOp (Bil.MINUS, xv, yv));
      Def.create zf (Bil.BinOp (Bil.EQ, w0_32, Bil.Var x));
      (* not (x−y) *)
      Def.create cf (Bil.BinOp (Bil.LT, xv, yv));
    ] in
  let s, _ = sub_of_defs_and_jmp "t13_inc" inc_defs cf_or_zf in
  let s' = J.compile_sub s in
  check "t13: inconsistent jbe stays residual" (Exp.equal (jmp_cond_of s') cf_or_zf);

  (* RESIDUAL: the inc/dec class — CF PRESERVED (no CF def in the
     block's flag group).  A CF-consuming family (jbe) stays the
     identity: a stale CF from a predecessor is invisible to the
     per-block facts. *)
  let incdec_defs =
    [
      Def.create t (Bil.BinOp (Bil.PLUS, xv, Bil.Int (Word.one 64)));
      Def.create zf (Bil.BinOp (Bil.EQ, w0_32, tv));
    ] in
  let s, _ = sub_of_defs_and_jmp "t13_incdec" incdec_defs cf_or_zf in
  let s' = J.compile_sub s in
  check "t13: inc/dec (CF preserved) jbe stays residual"
    (Exp.equal (jmp_cond_of s') cf_or_zf);
  check "t13: inc/dec defs untouched (no drop)" (Int.equal (Base.List.length (defs_of s')) 2);

  (* the single REACHING def: two ZF defs in one block — every cond
     reads the LAST (all defs precede all jmps; the first is a dead
     write).  The cond compiles from the second def; BOTH defs die
     (the var is unused sub-wide after the rewrite). *)
  let amb_defs =
    [
      Def.create zf (Bil.BinOp (Bil.EQ, w0_32, xv));
      Def.create zf (Bil.BinOp (Bil.EQ, w0_32, yv));
    ] in
  let s, _ = sub_of_defs_and_jmp "t13_reaching" amb_defs (Bil.Var zf) in
  let s' = J.compile_sub s in
  check "t13: two ZF defs → the reaching (last) def's comparison"
    (Exp.equal (jmp_cond_of s') (Bil.BinOp (Bil.EQ, yv, w0_64)));
  check "t13: both ZF defs die (var unused)" (not (has_def_for s' zf));

  (* unconditional jumps untouched. *)
  let s, _ = sub_of_defs_and_jmp "t13_uncond" (cmp_defs ()) (Bil.Int (Word.one 1)) in
  let s' = J.compile_sub s in
  check "t13: unconditional untouched" (Exp.equal (jmp_cond_of s') (Bil.Int (Word.one 1)));
  check "t13: unconditional defs untouched" (Int.equal (Base.List.length (defs_of s')) 5)

