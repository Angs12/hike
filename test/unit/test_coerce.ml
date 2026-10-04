(* Width-coercion pins: the one binop coercion point.  A width-mismatched
   binop resolves to one width before the VSA and the emitter read it. *)

open Bap.Std
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

let coerce = Hike.Coerce.coerce_exp

let v32 (n : string) : var = Var.create ~is_virtual:false ~fresh:false n (Type.Imm 32)

let int32 (n : int) : exp = Bil.Int (Cbat_word.to_word (w32 n))
let int64 (n : int) : exp = Bil.Int (Cbat_word.to_word (w64 n))
let vcast (c : Bil.cast) (w : int) (v : var) : exp = Bil.Cast (c, w, Bil.Var v)

let tests : unit Alcotest.test list =
  [
    (* CO-01: the common lifted shape — a 32-bit register against a 64-bit
       zero literal retypes the literal down; no cast node. *)


    (* CO-02: a wider literal the narrower width cannot represent keeps the
       reference resolution (the register widens). *)


    (* CO-03: the fit test follows the op's signedness — a sign-extended
       all-ones literal narrows under SLT. *)
    pin "CO-03" "a sign-extended all-ones literal narrows under SLT"
      (fun () ->
        let v = v32 "co3_v" in
        check "CO-03"
          (Exp.equal
             (coerce
                (Bil.BinOp
                   ( Bil.SLT
                   , Bil.Var v
                   , Bil.Int (Word.ones 64) )))
             (Bil.BinOp (Bil.SLT, Bil.Var v, Bil.Int (Word.ones 32)))));

    (* CO-04: the same value does NOT narrow under SLT when it is not the
       signed representation of the 32-bit word (0xffffffff:64 = 2^32−1,
       positive), so the register sign-extends. *)
    pin "CO-04" "an unsigned-valued 0xffffffff:64 does not narrow under SLT"
      (fun () ->
        let v = v32 "co4_v" in
        let imm = Bil.Int (Word.of_int64 ~width:64 0xFFFF_FFFFL) in
        check "CO-04"
          (Exp.equal
             (coerce (Bil.BinOp (Bil.SLT, Bil.Var v, imm)))
             (Bil.BinOp (Bil.SLT, vcast SIGNED 64 v, imm))));

    (* CO-05: a comparison's result is one bit — an AND over two one-bit
       operands (a high-bit extract and a nested comparison) stays put. *)
    pin "CO-05" "a nested comparison is one bit wide (no spurious coercion)"
      (fun () ->
        let x = v64 "co5_x" in
        let y = v64 "co5_y" in
        let e =
          Bil.BinOp
            ( Bil.AND
            , Bil.UnOp (Bil.NOT, Bil.Cast (Bil.HIGH, 1, Bil.Var x))
            , Bil.BinOp (Bil.EQ, Bil.Var y, int64 0) )
        in
        check "CO-05" (Exp.equal (coerce e) e));

    (* CO-06: a non-comparison op's result carries the common operand
       width, so the wider literal cannot narrow — the register widens. *)


    (* CO-07: no literal — the narrower operand casts to the wider. *)


    (* CO-08: a narrower literal retypes in place — zero filler. *)


    (* CO-09: the filler follows the op's signedness — the signed ops
       sign-extend a narrower all-ones literal. *)
    pin "CO-09" "a narrower all-ones literal sign-extends under ARSHIFT"
      (fun () ->
        let v = v64 "co9_v" in
        check "CO-09"
          (Exp.equal
             (coerce
                (Bil.BinOp
                   ( Bil.ARSHIFT
                   , Bil.Var v
                   , Bil.Int (Word.ones 32) )))
             (Bil.BinOp (Bil.ARSHIFT, Bil.Var v, Bil.Int (Word.ones 64)))));

    (* CO-10: the block mapper reaches jmp conditions. *)
    pin "CO-10" "coerce_block coerces a jmp condition" (fun () ->
        let v = v32 "co10_v" in
        let sub, _ =
          sub_of "co10"
            [
              ( [ Def.create (v64 "co10_t") (Bil.BinOp (Bil.PLUS, Bil.Var v, int64 1)) ],
                [ (1, fun t -> mk_jmp_to t (Bil.BinOp (Bil.EQ, Bil.Var v, int64 0))) ] );
              [], [ (0, mk_ret) ];
            ]
        in
        let blk = Term.enum blk_t sub |> Seq.hd_exn in
        let blk' = Hike.Coerce.coerce_block blk in
        let cond = Term.enum jmp_t blk' |> Seq.hd_exn |> Jmp.cond in
        check "CO-10" (Exp.equal cond (Bil.BinOp (Bil.EQ, Bil.Var v, int32 0))));

    (* CO-11: a def's value is born at its lhs's declared width — a
       narrower value zero-extends. *)
    pin "CO-11" "a def rhs zero-extends to the lhs width" (fun () ->
        let lhs = v64 "co11_t" in
        let rhs = v32 "co11_src" in
        let d = Def.create lhs (Bil.Var rhs) in
        let blk = blk_of_defs [ d ] in
        let blk' = Hike.Coerce.coerce_block blk in
        let rhs' = Term.enum def_t blk' |> Seq.hd_exn |> Def.rhs in
        check "CO-11" (Exp.equal rhs' (vcast UNSIGNED 64 rhs)));

    (* CO-12: an exactly-representable wider literal retypes to the lhs
       width (no cast node). *)


    (* CO-13: a wider non-literal truncates to the lhs width (the
       emitter's def-birth rule). *)


    (* CO-14: a store's data is exactly its size. *)
    pin "CO-14" "store data coerces to the store size" (fun () ->
        let mem = memv "co14_mem" in
        let addr = v64 "co14_addr" in
        let data = v64 "co14_data" in
        let e =
          Bil.Store (Bil.Var mem, Bil.Var addr, Bil.Var data, LittleEndian, `r32)
        in
        let e' = Hike.Coerce.coerce_exp e in
        check "CO-14"
          (Exp.equal e'
             (Bil.Store
                ( Bil.Var mem
                , Bil.Var addr
                , vcast UNSIGNED 32 data
                , LittleEndian
                , `r32 ))));

    (* CO-15: Ite branches share one width. *)
    pin "CO-15" "Ite branches widen to the common width" (fun () ->
        let c = v1 "co15_c" in
        let b = v64 "co15_b" in
        let e = Bil.Ite (Bil.Var c, int32 5, Bil.Var b) in
        let e' = Hike.Coerce.coerce_exp e in
        check "CO-15"
          (Exp.equal e' (Bil.Ite (Bil.Var c, int64 5, Bil.Var b))));

    (* CO-16: a phi's values are born at the phi's declared width. *)
    pin "CO-16" "a phi value coerces to the phi lhs width" (fun () ->
        let phi =
          Phi.of_list (v64 "co16_phi") [ (Tid.create (), int32 7) ]
        in
        let bb = Blk.Builder.init ~copy_phis:true (blk_of_defs []) in
        Blk.Builder.add_phi bb phi;
        let blk = Blk.Builder.result bb in
        let blk' = Hike.Coerce.coerce_block blk in
        let p' = Term.enum phi_t blk' |> Seq.hd_exn in
        let value = Phi.values p' |> Seq.hd_exn |> snd in
        check "CO-16" (Exp.equal value (int64 7)));

    (* CO-17: a Let binder's value is born at the binder's declared
       width. *)
    pin "CO-17" "a Let binder value coerces to the binder width" (fun () ->
        let v = v32 "co17_v" in
        let e = Bil.Let (v, int64 9, Bil.Var v) in
        check "CO-17"
          (Exp.equal (Hike.Coerce.coerce_exp e) (Bil.Let (v, int32 9, Bil.Var v))));

    (* CO-18: a zero-width concat operand contributes no bits — the
       concat reduces to the other operand. *)
    pin "CO-18" "a zero-width concat operand drops" (fun () ->
        let x = v64 "co18_x" in
        let y = v64 "co18_y" in
        let e = Bil.Concat (Bil.Cast (Bil.HIGH, 0, Bil.Var x), Bil.Var y) in
        check "CO-18" (Exp.equal (Hike.Coerce.coerce_exp e) (Bil.Var y)));

    (* CO-19: the dropped operand's def is then width-honest — the rhs is
       the surviving operand, coerced to the lhs width. *)

    (* A Let expression's value width is the body's width, independent of
       the temporary binder's width. *)
    pin "CO-20" "a Let rhs is coerced from the body width"
      (fun () ->
        let binder = v64 "co20_binder" in
        let lhs = v64 "co20_lhs" in
        let narrow =
          Bil.Int (Cbat_word.to_word (Cbat_word.of_int ~width:8 7))
        in
        let e = Bil.Let (binder, int64 1, narrow) in
        let rhs =
          Hike.Coerce.coerce_block (blk_of_defs [ Def.create lhs e ])
          |> Term.enum def_t |> Seq.hd_exn |> Def.rhs
        in
        check "CO-20"
          (Exp.equal rhs
             (Bil.Cast
                (UNSIGNED, 64,
                 Bil.Let (binder, int64 1, narrow)))));

  ]

let () = run "coerce" tests
