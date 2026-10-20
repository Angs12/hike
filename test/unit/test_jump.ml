(* Jump-compiler pins.  One Alcotest group per pin; each pin builds its own
   fixture, so no state crosses pins. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

let compile_sub (s : sub term) : sub term =
  snd (Hike.Jump.compile_sub ~synth:Hike.Synth.empty jump_target s)

let w0_32 = Bil.Int (Word.zero 32)
let w0_64 = Bil.Int (Word.zero 64)

(* The cmp/test fixture universe. *)
let x = v64 "t13_x"
let y = v64 "t13_y"
let t = v64 "t13_t"
let zf = abi_zf
let cf = abi_cf
let sf = abi_sf
let ovf = abi_of
let pf = abi_pf

let xv = Bil.Var x
let yv = Bil.Var y
let tv = Bil.Var t

let sub_of_defs_and_jmp (name : string) (defs : def term list) (cond : exp) : sub term =
  let sub, _tids = raw_sub_of name [ defs, [ (1, fun t -> mk_jmp_to t cond) ]; [], [] ] in
  sub

(* The entry block of the compiled sub (the first block). *)
let entry_of (s : sub term) : blk term = Term.enum blk_t s |> Seq.hd_exn

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
let xor_core =
  Bil.BinOp
    ( Bil.AND
    , Bil.BinOp (Bil.OR, Bil.Var sf, Bil.Var ovf)
    , Bil.UnOp (Bil.NOT, Bil.BinOp (Bil.AND, Bil.Var sf, Bil.Var ovf)) )
let zf_or_core = Bil.BinOp (Bil.OR, Bil.Var zf, xor_core)
let test_group_defs ?(with_of = true) () : def term list =
  let a = Bil.BinOp (Bil.AND, xv, yv) in
  let base =
    [
      Def.create zf (Bil.BinOp (Bil.EQ, w0_32, a));
      Def.create sf (Bil.Cast (Bil.HIGH, 1, a));
      Def.create cf (Bil.Int (Word.zero 1));
    ]
  in
  if with_of then Def.create ovf (Bil.Int (Word.zero 1)) :: base else base

let test_jl_cond = xor_core
let tests : unit Alcotest.test list =
  [
    (* jz over cmp, inline diff: (x−y)=0 folds to x=y. *)




    (* the counter-loop shape (F1), reuse form: tmp := i−k; ZF := 0 =
       t; jnz → t != 0 — the var REUSED, never re-substituted. *)






    (* the unsigned borrow family. *)




    (* the ADD-carry CF shape: the carry as the LT-shaped fact (d <u a). *)














    (* the signed family over the sub shapes. *)








    (* test a,b; jz → (x&y) = 0 (the conjunction kept, constant-right). *)
















    (* RESIDUAL: the signed family over a test group whose OF def is
       MISSING (cross-block OF): no OF fact, no OF ≡ 0 fact → the identity. *)
    pin "JMP-27" "test jl without OF stays residual" (fun () ->
        let s =
          sub_of_defs_and_jmp "t13_test_noof" (test_group_defs ~with_of:false ()) test_jl_cond
        in
        let s' = compile_sub s in
        check "JMP-27" (Exp.equal (jmp_cond_of s') test_jl_cond));

    (* FOLD: cmp x,0 — (x−0)=0 folds; jnz → x != 0. *)


    (* FOLD: a−a → the constant-true cond. *)


    (* WIDTH-MINIMAL: 32-bit operands compare at 32 bits (the zero
       constant rides the operand width). *)
    pin "JMP-30" "32-bit cmp jz folds to x32 = y32 (at the def's width)" (fun () ->
        let x32 = Var.create ~is_virtual:false ~fresh:false "t13_x32" (Type.Imm 32) in
        let y32 = Var.create ~is_virtual:false ~fresh:false "t13_y32" (Type.Imm 32) in
        let x32v = Bil.Var x32 and y32v = Bil.Var y32 in
        let w32_defs =
          [
            Def.create zf
              (Bil.BinOp (Bil.EQ, Bil.Int (Word.zero 32), Bil.BinOp (Bil.MINUS, x32v, y32v)));
          ]
        in
        let s = sub_of_defs_and_jmp "t13_w32" w32_defs (Bil.Var zf) in
        let s' = compile_sub s in
        check "JMP-30" (Exp.equal (jmp_cond_of s') (Bil.BinOp (Bil.EQ, x32v, y32v))));

    (* BOTH jmps of a block compile. *)


    (* the CFG is unchanged. *)
    pin "JMP-32" "CFG unchanged (3 blocks, targets intact)" (fun () ->
        let s, tids =
          raw_sub_of "t13_pair"
            [
              ( cmp_defs (),
                [ (2, fun t -> mk_jmp_to t (Bil.Var zf)); (1, fun t -> mk_jmp_to t v_not) ] );
              [], [ (0, mk_ret) ];
              [], [];
            ]
        in
        let exit_tid = tids.(1) in
        let body_tid = tids.(2) in
        let n_blks = Seq.length (Term.enum blk_t s) in
        let s' = compile_sub s in
        let blk' = entry_of s' in
        let jmps = Term.enum jmp_t blk' |> Seq.to_list in
        check "JMP-32"
          (Int.equal n_blks (Seq.length (Term.enum blk_t s'))
          && Base.List.exists jmps ~f:(fun j ->
                 match Jmp.kind j with
                 | Goto (Direct tid) -> Tid.equal tid exit_tid
                 | _ -> false)
          && Base.List.exists jmps ~f:(fun j ->
                 match Jmp.kind j with
                 | Goto (Direct tid) -> Tid.equal tid body_tid
                 | _ -> false)));

    (* CROSS-BLOCK: the flag def lives in a predecessor — the unique
       reaching definition at the block entry serves the facts. *)




    (* RESIDUAL: an AMBIGUOUS cross-block flag — two predecessors define
       ZF differently, no unique reaching def at the block entry. *)
    pin "JMP-35" "ambiguous cross-block flag stays residual" (fun () ->
        let s, tids =
          raw_sub_of "t13_cross_amb"
            [
              [], [ (1, mk_goto); (2, mk_goto) ];
              [ Def.create zf (Bil.BinOp (Bil.EQ, w0_32, xv)) ], [ (3, mk_goto) ];
              [ Def.create zf (Bil.BinOp (Bil.EQ, w0_32, yv)) ], [ (3, mk_goto) ];
              [], [ (4, fun t -> mk_jmp_to t (Bil.Var zf)) ];
              [], [ (0, mk_ret) ];
            ]
        in
        let use2_tid = tids.(3) in
        let s' = compile_sub s in
        let use_blk2 =
          Term.enum blk_t s'
          |> Seq.find_exn ~f:(fun b -> Tid.equal (Term.tid b) use2_tid)
        in
        let j2 = Term.enum jmp_t use_blk2 |> Seq.hd_exn in
        check "JMP-35" (Exp.equal (Jmp.cond j2) (Bil.Var zf)));

    (* RESIDUAL: unknown opcode (PF:unknown) — the identity. *)
    pin "JMP-36" "unknown opcode stays residual" (fun () ->
        let pf_defs = [ Def.create pf (Bil.Unknown ("unknown[bits]", Type.Imm 1)) ] in
        let s = sub_of_defs_and_jmp "t13_pf" pf_defs (Bil.Var pf) in
        let s' = compile_sub s in
        check "JMP-36" (Exp.equal (jmp_cond_of s') (Bil.Var pf)));

    (* jbe whose ZF is not the same subtraction as CF's borrow: the
       relations range over different pairs, so nothing combines and the
       cond is the substituted disjunction itself. *)
    pin "JMP-37" "inconsistent jbe compiles to the uncombined disjunction" (fun () ->
        let inc_defs =
          [
            Def.create t (Bil.BinOp (Bil.MINUS, xv, yv));
            Def.create zf (Bil.BinOp (Bil.EQ, w0_32, Bil.Var x));
            (* not (x−y) *)
            Def.create cf (Bil.BinOp (Bil.LT, xv, yv));
          ]
        in
        let s = sub_of_defs_and_jmp "t13_inc" inc_defs cf_or_zf in
        let s' = compile_sub s in
        check "JMP-37"
          (Exp.equal (jmp_cond_of s')
             (Bil.BinOp
                ( Bil.OR, Bil.BinOp (Bil.LT, xv, yv)
                , Bil.BinOp (Bil.EQ, xv, w0_64) ))
          && Int.equal (Base.List.length (defs_of s')) 1));

    (* RESIDUAL: the inc/dec class — CF PRESERVED (no CF def in the
       block's flag group).  A CF-consuming family (jbe) stays the
       identity: a stale CF from a predecessor is invisible to the
       per-block facts. *)
    pin "JMP-38" "inc/dec (CF preserved) jbe stays residual" (fun () ->
        let incdec_defs =
          [
            Def.create t (Bil.BinOp (Bil.PLUS, xv, Bil.Int (Word.one 64)));
            Def.create zf (Bil.BinOp (Bil.EQ, w0_32, tv));
          ]
        in
        let s = sub_of_defs_and_jmp "t13_incdec" incdec_defs cf_or_zf in
        let s' = compile_sub s in
        check "JMP-38" (Exp.equal (jmp_cond_of s') cf_or_zf));

    pin "JMP-39" "inc/dec defs untouched (no drop)" (fun () ->
        let incdec_defs =
          [
            Def.create t (Bil.BinOp (Bil.PLUS, xv, Bil.Int (Word.one 64)));
            Def.create zf (Bil.BinOp (Bil.EQ, w0_32, tv));
          ]
        in
        let s = sub_of_defs_and_jmp "t13_incdec" incdec_defs cf_or_zf in
        let s' = compile_sub s in
        check "JMP-39" (Int.equal (Base.List.length (defs_of s')) 2));

    (* the single REACHING def: two ZF defs in one block — every cond
       reads the LAST (all defs precede all jmps; the first is a dead
       write). *)
    pin "JMP-40" "two ZF defs give the reaching (last) def's comparison" (fun () ->
        let amb_defs =
          [
            Def.create zf (Bil.BinOp (Bil.EQ, w0_32, xv));
            Def.create zf (Bil.BinOp (Bil.EQ, w0_32, yv));
          ]
        in
        let s = sub_of_defs_and_jmp "t13_reaching" amb_defs (Bil.Var zf) in
        let s' = compile_sub s in
        check "JMP-40" (Exp.equal (jmp_cond_of s') (Bil.BinOp (Bil.EQ, yv, w0_64))));



    (* unconditional jumps untouched. *)
    pin "JMP-42" "unconditional untouched: the condition and the defs survive" (fun () ->
        let s = sub_of_defs_and_jmp "t13_uncond" (cmp_defs ()) (Bil.Int (Word.one 1)) in
        let s' = compile_sub s in
        check "JMP-42"
          (Exp.equal (jmp_cond_of s') (Bil.Int (Word.one 1))
          && Int.equal (Base.List.length (defs_of s')) 5));

    pin "JMP-44" "jb over CF := 1 compiles to the const-true branch and CF dies" (fun () ->
        let s =
          sub_of_defs_and_jmp "t13_cf1"
            [ Def.create cf (Bil.Int (Word.one 1)) ]
            (Bil.Var cf)
        in
        let s' = compile_sub s in
        check "JMP-44"
          (Exp.equal (jmp_cond_of s') (Bil.Int (Word.one 1))
          && not (has_def_for s' cf)));

    (* cmp x,0: BAP folds x - 0 to x and leaves OF := high:1[x & (x ^ t)]
       with t := x; substituting t makes the OF identically zero, so jle
       compiles to x <=s 0 and the flag defs die. *)
    pin "JMP-45" "cmp x,0's folded OF (x & (x ^ t), t := x) is OF == 0"
      (fun () ->
        let defs =
          [
            Def.create t xv;
            Def.create zf (Bil.BinOp (Bil.EQ, w0_32, tv));
            Def.create sf (Bil.Cast (Bil.HIGH, 1, tv));
            Def.create ovf
              (Bil.Cast
                 ( Bil.HIGH
                 , 1
                 , Bil.BinOp (Bil.AND, xv, Bil.BinOp (Bil.XOR, xv, tv)) ));
          ]
        in
        let s = sub_of_defs_and_jmp "t13_cmpzero" defs zf_or_core in
        let s' = compile_sub s in
        check "JMP-45"
          (Exp.equal (jmp_cond_of s')
             (Bil.BinOp (Bil.SLE, xv, w0_64))
          && Int.equal (Base.List.length (defs_of s')) 1));

    (* The reused register (clang -O0's spilled switch index): x is
       written three times, so the borrow and the zero test read
       different x's.  Substitution makes every read positional: the
       guard is 6 <u x at the def that reads x into t, bound to a fresh
       comparison def there because x is rewritten before the jump. *)
    pin "JMP-46" "jbe over a reused register binds 6 <u x where t := x reads it"
      (fun () ->
        let defs =
          [
            Def.create x (Bil.BinOp (Bil.MINUS, xv, yv));
            Def.create t xv;
            Def.create x (Bil.BinOp (Bil.MINUS, xv, Bil.Int (Word.of_int ~width:64 6)));
            Def.create cf (Bil.BinOp (Bil.LT, tv, Bil.Int (Word.of_int ~width:64 6)));
            Def.create zf (Bil.BinOp (Bil.EQ, w0_64, xv));
          ]
        in
        let s = sub_of_defs_and_jmp "t13_reuse" defs (Bil.UnOp (Bil.NOT, cf_or_zf)) in
        let s' = compile_sub s in
        let ds = defs_of s' in
        check "JMP-46"
          (match jmp_cond_of s', ds with
           | Bil.Var c, [ _; cmp; t_def; _ ] ->
             Var.equal (Def.lhs cmp) c
             && Exp.equal (Def.rhs cmp)
                  (Bil.BinOp (Bil.LT, Bil.Int (Word.of_int ~width:64 6), xv))
             && Var.equal (Def.lhs t_def) t
           | _ -> false));

    (* The signed family over a register rewritten after the compare:
       the earliest equal-size form reads values the jump still holds,
       so it is inlined. *)
    pin "JMP-47" "jle over a reused register compiles to y <=s z inline"
      (fun () ->
        let z = v64 "t13_z" in
        let zv = Bil.Var z in
        let defs =
          [
            Def.create x yv;
            Def.create t (Bil.BinOp (Bil.MINUS, xv, zv));
            Def.create zf (Bil.BinOp (Bil.EQ, w0_64, tv));
            Def.create sf (Bil.Cast (Bil.HIGH, 1, tv));
            Def.create ovf
              (Bil.Cast
                 ( Bil.HIGH, 1
                 , Bil.BinOp
                     (Bil.AND, Bil.BinOp (Bil.XOR, xv, zv), Bil.BinOp (Bil.XOR, xv, tv)) ));
            Def.create x w0_64;
          ]
        in
        let s = sub_of_defs_and_jmp "t13_sreuse" defs zf_or_core in
        let s' = compile_sub s in
        check "JMP-47"
          (Exp.equal (jmp_cond_of s') (Bil.BinOp (Bil.SLE, yv, zv))
          && Int.equal (Base.List.length (defs_of s')) 3));

    (* cmp in one block, jbe in its goto successor: the walk continues
       into the unique predecessor. *)
    pin "JMP-48" "cross-block jbe compiles to x <= y and the flags die" (fun () ->
        let s, tids =
          raw_sub_of "t13_xjbe"
            [
              ( [
                  Def.create t (Bil.BinOp (Bil.MINUS, xv, yv));
                  Def.create zf (Bil.BinOp (Bil.EQ, w0_64, tv));
                  Def.create cf (Bil.BinOp (Bil.LT, xv, yv));
                ],
                [ (1, mk_goto) ] );
              [], [ (2, fun t -> mk_jmp_to t cf_or_zf) ];
              [], [];
            ]
        in
        let s' = compile_sub s in
        let blk i = Term.enum blk_t s' |> Seq.find_exn ~f:(fun b -> Tid.equal (Term.tid b) tids.(i)) in
        let j = Term.enum jmp_t (blk 1) |> Seq.hd_exn in
        check "JMP-48"
          (Exp.equal (Jmp.cond j) (Bil.BinOp (Bil.LE, xv, yv))
          && Int.equal (Seq.length (Term.enum def_t (blk 0))) 1));

    (* ucomisd: the lifter's flags are formulas over the is_nan/forder
       intrinsic results, set in the block before the jump; jp is the
       unordered test itself. *)
    pin "JMP-49" "jp after an FP compare compiles to the unordered test" (fun () ->
        let a = v1 "t13_a" and b = v1 "t13_b" and c = v1 "t13_c" and d = v1 "t13_d" in
        let bv v = Bil.Var v in
        let s, tids =
          raw_sub_of "t13_fjp"
            [
              ( [
                  Def.create pf (Bil.BinOp (Bil.OR, bv a, bv b));
                  Def.create cf (Bil.BinOp (Bil.OR, bv pf, bv c));
                  Def.create zf
                    (Bil.BinOp
                       ( Bil.OR, bv pf
                       , Bil.BinOp (Bil.AND, Bil.UnOp (Bil.NOT, bv c), Bil.UnOp (Bil.NOT, bv d)) ));
                ],
                [ (1, mk_goto) ] );
              [], [ (2, fun t -> mk_jmp_to t (bv pf)) ];
              [], [];
            ]
        in
        let s' = compile_sub s in
        let blk1 = Term.enum blk_t s' |> Seq.find_exn ~f:(fun b -> Tid.equal (Term.tid b) tids.(1)) in
        let j = Term.enum jmp_t blk1 |> Seq.hd_exn in
        check "JMP-49" (Exp.equal (Jmp.cond j) (Bil.BinOp (Bil.OR, bv a, bv b))));

    (* Integer jp: PF is the low byte's parity of the result; the cond
       becomes that expression over the result and the PF def dies. *)
    pin "JMP-50" "integer jp compiles to the parity expression" (fun () ->
        let v0 = Var.create ~is_virtual:true ~fresh:false "$0" (Type.Imm 64) in
        let v1_ = Var.create ~is_virtual:true ~fresh:false "$1" (Type.Imm 64) in
        let sh e k = Bil.BinOp (Bil.RSHIFT, e, Bil.Int (Word.of_int ~width:64 k)) in
        let parity =
          Bil.UnOp
            ( Bil.NOT
            , Bil.Cast
                ( Bil.LOW, 1
                , Bil.Let
                    ( v0, Bil.BinOp (Bil.XOR, sh tv 4, tv)
                    , Bil.Let
                        ( v1_, Bil.BinOp (Bil.XOR, sh (Bil.Var v0) 2, Bil.Var v0)
                        , Bil.BinOp (Bil.XOR, sh (Bil.Var v1_) 1, Bil.Var v1_) ) ) ) )
        in
        let defs = [ Def.create t (Bil.BinOp (Bil.MINUS, xv, yv)); Def.create pf parity ] in
        let s = sub_of_defs_and_jmp "t13_ijp" defs (Bil.Var pf) in
        let s' = compile_sub s in
        check "JMP-50"
          (Exp.equal (jmp_cond_of s') parity
          && Int.equal (Base.List.length (defs_of s')) 1));

    (* A call between the flags and the jump: the callee may write the
       flags, so the walk stops at the call edge and the cond stays. *)
    pin "JMP-51" "flags set before a call stay residual after it" (fun () ->
        let s, tids =
          raw_sub_of "t13_xcall"
            [
              ( [ Def.create zf (Bil.BinOp (Bil.EQ, w0_64, xv)) ],
                [ (1, fun post -> mk_call_jmp post (Tid.create ())) ] );
              [], [ (2, fun t -> mk_jmp_to t (Bil.Var zf)) ];
              [], [];
            ]
        in
        let s' = compile_sub s in
        let blk1 = Term.enum blk_t s' |> Seq.find_exn ~f:(fun b -> Tid.equal (Term.tid b) tids.(1)) in
        let j = Term.enum jmp_t blk1 |> Seq.hd_exn in
        check "JMP-51" (Exp.equal (Jmp.cond j) (Bil.Var zf)));

    pin "JMP-52" "low casts compose with signed and unsigned casts by width"
      (fun () ->
        let src = Bil.Var (Var.create ~is_virtual:true ~fresh:true
            "cast_source" (Type.Imm 8)) in
        (* LOW:width(kind:middle(src)) for an 8-bit source: a narrower
           width is a low cast of the source, the source's own width is
           the source, a wider one keeps the extension kind. *)
        let table kind =
          [ (16, 4), Bil.Cast (Bil.LOW, 4, src);
            (16, 8), src;
            (16, 12), Bil.Cast (kind, 12, src);
            (4, 2), Bil.Cast (Bil.LOW, 2, src) ] in
        Base.List.iter [ Bil.UNSIGNED; Bil.SIGNED ] ~f:(fun kind ->
            Base.List.iter (table kind) ~f:(fun ((middle, width), expected) ->
                let rhs = Bil.Var (Var.create ~is_virtual:true ~fresh:true
                    "cast_other" (Type.Imm width)) in
                let cast = Bil.Cast (Bil.LOW, width, Bil.Cast (kind, middle, src)) in
                let s = sub_of_defs_and_jmp "cast_widths"
                    [ Def.create zf (Bil.BinOp (Bil.EQ, cast, rhs)) ] (Bil.Var zf) in
                check "JMP-52"
                  (Exp.equal (jmp_cond_of (compile_sub s))
                     (Bil.BinOp (Bil.EQ, expected, rhs))))));

    pin "JMP-53" "a casted reused switch index retains its inclusive bound"
      (fun () ->
        let saved = Var.create ~is_virtual:true ~fresh:true
            "saved_index" (Type.Imm 32) in
        let low = Bil.Cast (Bil.LOW, 32, xv) in
        let limit = Bil.Int (Word.of_int ~width:32 23) in
        let defs =
          [ Def.create saved low;
            Def.create x (Bil.Cast (Bil.UNSIGNED, 64,
                Bil.BinOp (Bil.MINUS, low, limit)));
            Def.create cf (Bil.BinOp (Bil.LT, Bil.Var saved, limit));
            Def.create zf (Bil.BinOp (Bil.EQ, Bil.Cast (Bil.LOW, 32, xv), w0_32)) ] in
        let s = compile_sub (sub_of_defs_and_jmp "casted_switch" defs cf_or_zf) in
        check "JMP-53"
          (match jmp_cond_of s, defs_of s with
           | Bil.Var guard, comparison :: _ ->
             Var.equal (Def.lhs comparison) guard
             && Exp.equal (Def.rhs comparison) (Bil.BinOp (Bil.LE, low, limit))
           | _ -> false));
  ]

let () = run "jump" tests
