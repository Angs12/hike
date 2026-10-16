(* Extract-of-concat pins: a field read from a double-width temporary
   that lies inside one concat operand reads that operand, so the
   domain's concat hull never reaches the extract. *)

open Bap.Std
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

let v128 (n : string) : var =
  Var.create ~is_virtual:true ~fresh:true n (Type.Imm 128)

let rhs_of (blk : blk term) (d : def term) : exp =
  match Term.find def_t blk (Term.tid d) with
  | Some d -> Def.rhs d
  | None -> assert false

let block (defs : def term list) : blk term = blk_of_defs defs

let div_shape name =
  let a = v64 (name ^ "_a") and b = v64 (name ^ "_b") in
  let t = v128 (name ^ "_t") in
  let lo = v64 (name ^ "_lo") and hi = v64 (name ^ "_hi") in
  (a, b, t, lo, hi)

let tests : unit Alcotest.test list =
  [
    pin "CC-01"
      "a field covering a whole operand of a concat temporary reads that operand"
      (fun () ->
        let a, b, t, lo, hi = div_shape "cc1" in
        let d_t = Def.create t (Bil.Concat (Bil.Var a, Bil.Var b)) in
        let d_lo = Def.create lo (Bil.Extract (63, 0, Bil.Var t)) in
        let d_hi = Def.create hi (Bil.Extract (127, 64, Bil.Var t)) in
        let blk = Hike.Concat.normalize_block (block [ d_t; d_lo; d_hi ]) in
        check "CC-01"
          (Exp.equal (rhs_of blk d_lo) (Bil.Var b)
           && Exp.equal (rhs_of blk d_hi) (Bil.Var a)));

    pin "CC-02"
      "a field inside one operand extracts from that operand alone"
      (fun () ->
        let a, b, t, lo, _ = div_shape "cc2" in
        let d_t = Def.create t (Bil.Concat (Bil.Var a, Bil.Var b)) in
        let d_lo = Def.create lo (Bil.Extract (31, 8, Bil.Var t)) in
        let blk = Hike.Concat.normalize_block (block [ d_t; d_lo ]) in
        check "CC-02"
          (Exp.equal (rhs_of blk d_lo) (Bil.Extract (31, 8, Bil.Var b))));

    pin "CC-03"
      "a field spanning both operands keeps the concat"
      (fun () ->
        let a, b, t, lo, _ = div_shape "cc3" in
        let d_t = Def.create t (Bil.Concat (Bil.Var a, Bil.Var b)) in
        let d_lo = Def.create lo (Bil.Extract (95, 32, Bil.Var t)) in
        let blk = Hike.Concat.normalize_block (block [ d_t; d_lo ]) in
        check "CC-03" (Exp.equal (rhs_of blk d_lo) (rhs_of (block [ d_t; d_lo ]) d_lo)));

    pin "CC-04"
      "a redefined operand ends the look-through"
      (fun () ->
        let a, b, t, lo, _ = div_shape "cc4" in
        let d_t = Def.create t (Bil.Concat (Bil.Var a, Bil.Var b)) in
        let d_b =
          Def.create b (Bil.BinOp (Bil.PLUS, Bil.Var b, Bil.Int (Cbat_word.to_word (w64 1))))
        in
        let d_lo = Def.create lo (Bil.Extract (63, 0, Bil.Var t)) in
        let blk = Hike.Concat.normalize_block (block [ d_t; d_b; d_lo ]) in
        check "CC-04" (Exp.equal (rhs_of blk d_lo) (Bil.Extract (63, 0, Bil.Var t))));

    pin "CC-05"
      "an operand that reads memory is not duplicated"
      (fun () ->
        let _, b, t, lo, _ = div_shape "cc5" in
        let m = memv "cc5_m" in
        let a = v64 "cc5_a" in
        let load = Bil.Load (Bil.Var m, Bil.Var a, LittleEndian, `r64) in
        let d_t = Def.create t (Bil.Concat (load, Bil.Var b)) in
        let d_lo = Def.create lo (Bil.Extract (127, 64, Bil.Var t)) in
        let blk = Hike.Concat.normalize_block (block [ d_t; d_lo ]) in
        check "CC-05" (Exp.equal (rhs_of blk d_lo) (Bil.Extract (127, 64, Bil.Var t))));

    pin "CC-06"
      "a literal concat reduces in place"
      (fun () ->
        let a, b, _, lo, _ = div_shape "cc6" in
        let d_lo =
          Def.create lo (Bil.Extract (63, 0, Bil.Concat (Bil.Var a, Bil.Var b)))
        in
        let blk = Hike.Concat.normalize_block (block [ d_lo ]) in
        check "CC-06" (Exp.equal (rhs_of blk d_lo) (Bil.Var b)));

    pin "CC-07"
      "x86 div: the extracted quotient keeps its finite range through the solve"
      (fun () ->
        (* q = x >> 4 over 128 bits is finite (< 2^60); the concat with
           the remainder hulls both halves. *)
        let x = v64 "cc7_x" and rem = v64 "cc7_rem" and quot = v128 "cc7_q" in
        let t = v128 "cc7_t" and rax = v64 "cc7_rax" in
        let d_q =
          Def.create quot
            (Bil.BinOp
               ( Bil.RSHIFT,
                 Bil.Cast (Bil.UNSIGNED, 128, Bil.Var x),
                 Bil.Int (Cbat_word.to_word (Cbat_word.of_int ~width:128 4)) ))
        in
        let d_rem =
          Def.create rem
            (Bil.BinOp (Bil.AND, Bil.Var x, Bil.Int (Cbat_word.to_word (w64 15))))
        in
        let d_t =
          Def.create t
            (Bil.Concat
               ( Bil.Cast (Bil.LOW, 64, Bil.Var rem),
                 Bil.Cast (Bil.LOW, 64, Bil.Var quot) ))
        in
        let d_rax = Def.create rax (Bil.Extract (63, 0, Bil.Var t)) in
        let blk = block [ d_q; d_rem; d_t; d_rax ] in
        let solve blk =
          AI.find_word 64 (Vsa.Test_seam.denote_defs blk (anchored_entry ())) rax
        in
        let before = solve blk in
        let after = solve (Hike.Concat.normalize_block blk) in
        let bound =
          Ws.of_clp (Clp.interval ~width:64 (w64 0) (w64 0x0FFFFFFFFFFFFFFF))
        in
        check "CC-07"
          (Ws.is_top before && (not (Ws.is_top after)) && Ws.precedes after bound));
  ]

let () = run "concat" tests
