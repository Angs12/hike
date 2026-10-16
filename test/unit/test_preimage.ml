open Bap.Std
open Hike_test.Harness
module W = Cbat_word
module C = Cbat_clp
module P = C.Pieces
module E = C.Exact
module I = Cbat_preimage
module S = Cbat_clp_set_composite

let w bits x = W.of_int ~width:bits x
let iv bits lo hi = C.interval ~width:bits (w bits lo) (w bits hi)

let tests =
  [
    pin "INV-01" "LOW inverse preserves the two separated switch-index pieces"
      (fun () ->
        let arg = P.union (iv 64 0 118) (iv 64 0xfffffff7 0xffffffff) in
        let result = iv 8 0 23 in
        let got = P.backward1 (I.Cast (Bil.LOW, 8)) ~arg ~result in
        check "INV-01.pieces" (P.equal got (iv 64 0 23));
        let v = Var.create "switch_index" (Type.Imm 64) in
        let env =
          Cbat_vsa.AI.add_word Cbat_vsa.AI.top ~key:v ~data:(S.of_clp arg)
        in
        let env =
          Cbat_vsa.Test_seam.constrain_operands ~env
            ~landmarks:(Cbat_landmarks.create ())
            (Bil.Cast (Bil.LOW, 8, Bil.Var v))
            (S.of_clp result)
        in
        check "INV-01.walk"
          (S.equal (Cbat_vsa.AI.find_word 64 env v) (S.of_clp (iv 64 0 23))));
    pin "INV-02"
      "finite pre-images retain disjoint alternatives and both binary \
       projections" (fun () ->
        let e bits xs = E.of_list ~width:bits (List.map (w bits) xs) in
        let got =
          E.backward1
            (I.Cast (Bil.LOW, 8))
            ~arg:(e 64 [ 1; 2; 257; 258; 1000 ])
            ~result:(e 8 [ 1; 232 ])
        in
        check "INV-02.unary" (E.equal got (e 64 [ 1; 257; 1000 ]));
        let a, b =
          E.backward2 (I.Op Bil.PLUS)
            ~left:(e 8 [ 1; 2; 100 ])
            ~right:(e 8 [ 3; 4; 200 ])
            ~result:(e 8 [ 4; 202 ])
        in
        check "INV-02.binary"
          (E.equal a (e 8 [ 1; 2 ]) && E.equal b (e 8 [ 3; 200 ])));
    pin "INV-03"
      "piece lifting distributes operand and result alternatives without \
       hulling the gap" (fun () ->
        let arg = P.union (iv 32 0 100) (iv 32 1000 1100) in
        let result = P.union (iv 32 5 10) (iv 32 1005 1010) in
        let a, b =
          P.backward2 (I.Op Bil.PLUS) ~left:arg
            ~right:(P.singleton (w 32 5))
            ~result
        in
        let expected = P.union (iv 32 0 5) (iv 32 1000 1005) in
        check "INV-03" (P.equal a expected && P.equal b (P.singleton (w 32 5))));
    pin "INV-04"
      "inverse kernels preserve every satisfying concrete binary pair"
      (fun () ->
        let ops =
          [
            Bil.PLUS;
            MINUS;
            TIMES;
            DIVIDE;
            SDIVIDE;
            MOD;
            SMOD;
            LSHIFT;
            RSHIFT;
            ARSHIFT;
            AND;
            OR;
            XOR;
            EQ;
            NEQ;
            LT;
            LE;
            SLT;
            SLE;
          ]
        in
        let left = P.top 8 in
        let rights =
          [ iv 8 0 255; P.singleton (w 8 2); P.singleton (w 8 255) ]
        in
        List.iter
          (fun op ->
            List.iter
              (fun right ->
                let comparison =
                  match op with
                  | Bil.EQ | NEQ | LT | LE | SLT | SLE -> true
                  | _ -> false
                in
                let results =
                  if comparison then [ iv 1 0 0; iv 1 1 1 ]
                  else [ iv 8 2 13; iv 8 240 250 ]
                in
                List.iter
                  (fun result ->
                    let a, b = P.backward2 (I.Op op) ~left ~right ~result in
                    List.iter
                      (fun x ->
                        List.iter
                          (fun y ->
                            if
                              not
                                ((op = Bil.DIVIDE || op = SDIVIDE || op = MOD
                                || op = SMOD)
                                && W.is_zero y)
                            then
                              let z =
                                Bil.Apply.binop op (W.to_word x) (W.to_word y)
                                |> W.of_word
                              in
                              if
                                P.elem z result && not (P.elem x a && P.elem y b)
                              then
                                Alcotest.failf
                                  "binary pre-image excludes %a op %a = %a" W.pp
                                  x W.pp y W.pp z)
                          (P.elements right))
                      (P.elements left))
                  results)
              rights)
          ops);
    pin "INV-05"
      "cast and extract kernels preserve every satisfying concrete input"
      (fun () ->
        let ops =
          [
            I.Lnot;
            I.Neg;
            I.Cast (Bil.LOW, 4);
            I.Cast (Bil.HIGH, 4);
            I.Cast (Bil.UNSIGNED, 16);
            I.Cast (Bil.SIGNED, 16);
            I.Extract (Some 5, 2);
          ]
        in
        List.iter
          (fun op ->
            let oracle x =
              match op with
              | I.Lnot -> Bil.Apply.unop Bil.NOT x
              | I.Neg -> Bil.Apply.unop Bil.NEG x
              | I.Cast (c, n) -> Bil.Apply.cast c n x
              | I.Extract (hi, lo) -> Word.extract_exn ?hi ~lo x
            in
            let bits = Word.bitwidth (oracle (Word.zero 8)) in
            let results =
              [ iv bits 0 3; iv bits ((1 lsl bits) - 4) ((1 lsl bits) - 1) ]
            in
            List.iter
              (fun result ->
                let arg = P.top 8 in
                let got = P.backward1 op ~arg ~result in
                List.iter
                  (fun x ->
                    if
                      P.elem (W.of_word (oracle (W.to_word x))) result
                      && not (P.elem x got)
                    then Alcotest.failf "unary pre-image excludes %a" W.pp x)
                  (P.elements arg))
              results)
          ops);
    pin "INV-06" "mixed representations preserve origin and empty-result width"
      (fun () ->
        let left = S.stack_word (iv 64 0 100) in
        let right = S.singleton (w 64 3) in
        let result = S.stack_word_i64 7L in
        let a, b = S.backward2 (I.Op Bil.PLUS) ~left ~right ~result in
        check "INV-06.origin"
          (S.equal a (S.stack_word_i64 4L) && S.equal b right);
        let impossible =
          S.backward1
            (I.Cast (Bil.LOW, 8))
            ~arg:(S.of_clp (iv 64 0 100))
            ~result:(S.singleton (w 8 200))
        in
        check "INV-06.empty"
          (S.is_bottom impossible && S.bitwidth impossible = 64));
    pin "INV-07" "excluded inverse boundaries still reach the landmark observer"
      (fun () ->
        let v = Var.create "inverse_counter" (Type.Imm 32) in
        let env =
          Cbat_vsa.AI.add_word Cbat_vsa.AI.top ~key:v
            ~data:(S.of_clp (iv 32 0 10))
        in
        let landmarks = Cbat_landmarks.create () and head = Tid.create () in
        Cbat_landmarks.with_widening_head landmarks (Some head) (fun () ->
            ignore
              (Cbat_vsa.Test_seam.constrain_operands ~env ~landmarks
                 (Bil.BinOp
                    ( Bil.EQ,
                      Bil.BinOp
                        ( Bil.MINUS,
                          Bil.Var v,
                          Bil.Int (Word.of_int ~width:32 100) ),
                      Bil.Int (Word.zero 32) ))
                 (S.singleton W.b1)));
        let entries =
          Cbat_landmarks.entries landmarks head (Cbat_landmarks.Word v)
        in
        check "INV-07"
          (List.exists
             (fun (e : Cbat_landmarks.lm_entry) -> W.equal e.bound (w 32 100))
             entries));
    pin "INV-08"
      "a disabled flag carries its requested polarity through the observer"
      (fun () ->
        let module V = Cbat_vsa in
        let v = Var.create "inverse_counter" (Type.Imm 32) in
        let zf = Var.create "inverse_flag" (Type.Imm 1) in
        let eq =
          Bil.BinOp
            ( Bil.EQ,
              Bil.BinOp
                (Bil.MINUS, Bil.Var v, Bil.Int (Word.of_int ~width:32 100)),
              Bil.Int (Word.zero 32) )
        in
        let blk =
          Blk.create () |> fun b -> Term.append def_t b (Def.create zf eq)
        in
        let sub = Sub.create () |> fun s -> Term.append blk_t s blk in
        let rctx = Hike_test.Common.mk_rctx ~abi:Hike_abi.x86_64_sysv sub in
        let landmarks = V.Test_seam.landmarks_of rctx in
        let entry =
          V.AI.add_word V.AI.top ~key:v ~data:(S.of_clp (iv 32 0 10))
        in
        let env = V.Test_seam.denote_defs blk entry in
        V.Test_seam.with_widening_head rctx
          (Some (Term.tid blk))
          (fun () ->
            V.Test_seam.acquire_unsat ~rctx ~entry env blk (Bil.Var zf));
        let entries =
          Cbat_landmarks.entries landmarks (Term.tid blk)
            (Cbat_landmarks.Word v)
        in
        check "INV-08"
          (List.exists
             (fun (e : Cbat_landmarks.lm_entry) -> W.equal e.bound (w 32 100))
             entries));
    pin "INV-09"
      "periodic LOW constraints retain their stride across arbitrarily many \
       windows" (fun () ->
        let result =
          P.of_progression
            (C.create ~width:8 ~step:(w 8 2) ~cardn:(w 9 128) (w 8 0))
        in
        let got = P.backward1 (I.Cast (Bil.LOW, 8)) ~arg:(P.top 64) ~result in
        List.iter
          (fun x -> check "INV-09.keep" (P.elem (W.of_int64 x) got))
          [ 0L; 2L; 254L; 256L; Int64.minus_one |> Int64.pred ];
        List.iter
          (fun x -> check "INV-09.drop" (not (P.elem (W.of_int64 x) got)))
          [ 1L; 255L; Int64.minus_one ]);
  ]

let () = run "preimage" tests
