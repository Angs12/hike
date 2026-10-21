(* Cbat_dispatch pins: equality and table-offset case tests, the original
   condition conjunction, duplicate/ordered targets, the no-base fallback,
   and the target binding.  No VSA fixture is needed: the module only
   builds BIR expressions. *)

open Bap.Std
open Hike_test.Harness
open Hike_test.Common

module D = Cbat_vsa.Dispatch

let w (n : int64) : Cbat_word.t = Cbat_word.of_int64 ~width:64 n
let wexp (n : int64) : exp = Bil.Int (Cbat_word.to_word (w n))
let iexp (n : int64) : exp = Bil.Int (Word.of_int64 ~width:64 n)

let eq (a : exp) (b : exp) : exp = Bil.BinOp (Bil.EQ, a, b)
let minus (a : exp) (b : exp) : exp = Bil.BinOp (Bil.MINUS, a, b)
let and_ (a : exp) (b : exp) : exp = Bil.BinOp (Bil.AND, a, b)
let or_ (a : exp) (b : exp) : exp = Bil.BinOp (Bil.OR, a, b)

let sub = Sub.create ~name:"dispatch_test" ()

let mat ?base (targets : (Cbat_word.t * Tid.t) list) : D.materialized =
  { D.base; targets; sub }

let guards_of (arms : D.arm list) : exp list =
  Base.List.map arms ~f:(fun a -> a.guard)

let targets_of (arms : D.arm list) : Tid.t list =
  Base.List.map arms ~f:(fun a -> a.target)

let kinds_of (arms : D.arm list) : D.arm_kind list =
  Base.List.map arms ~f:(fun a -> a.kind)

let table ~(summand : var) ~(values : int64 list) : D.base =
  { D.summand = Bil.Var summand; values }

let tests : unit Alcotest.test list =
  [
    (* No base: every arm is exactly (target == word), in target order. *)
    pin "DISP-01" "equality guards without a base" (fun () ->
        let target = v64 "disp1_target" in
        let t1 = Tid.create () and t2 = Tid.create () in
        let targets = [ (w 0x401000L, t1); (w 0x401020L, t2) ] in
        let arms =
          D.arms ~kind:D.Jump ~cond:None ~target:(Bil.Var target) ~base:None
            ~targets
        in
        check "DISP-01"
          (Base.List.equal Exp.equal (guards_of arms)
             [ eq (Bil.Var target) (wexp 0x401000L);
               eq (Bil.Var target) (wexp 0x401020L) ]
          && Base.List.equal Tid.equal (targets_of arms) [ t1; t2 ]
          && Base.List.equal (fun a b -> a = b) (kinds_of arms)
               [ D.Jump; D.Jump ]));

    (* One base value: the relative word, with no summand test. *)
    pin "DISP-02" "table-offset guards with one base value" (fun () ->
        let target = v64 "disp2_target" in
        let summand = v64 "disp2_summand" in
        let t1 = Tid.create () in
        let arms =
          D.arms ~kind:D.Jump ~cond:None ~target:(Bil.Var target)
            ~base:(Some (table ~summand ~values:[ 0x400000L ]))
            ~targets:[ (w 0x400018L, t1) ]
        in
        check "DISP-02"
          (Base.List.equal Exp.equal (guards_of arms)
             [ eq (minus (Bil.Var target) (Bil.Var summand)) (iexp 0x18L) ]));

    (* Several base values: each value also tests the summand itself, and
       the cases are ORed in value order. *)
    pin "DISP-03" "table-offset guards with several base values" (fun () ->
        let target = v64 "disp3_target" in
        let summand = v64 "disp3_summand" in
        let t1 = Tid.create () in
        let delta b =
          eq (minus (Bil.Var target) (Bil.Var summand)) (iexp (Int64.sub 0x500018L b))
        in
        let expected =
          or_
            (and_ (eq (Bil.Var summand) (iexp 0x400000L)) (delta 0x400000L))
            (and_ (eq (Bil.Var summand) (iexp 0x500000L)) (delta 0x500000L))
        in
        let arms =
          D.arms ~kind:D.Jump ~cond:None ~target:(Bil.Var target)
            ~base:(Some (table ~summand ~values:[ 0x400000L; 0x500000L ]))
            ~targets:[ (w 0x500018L, t1) ]
        in
        check "DISP-03" (Base.List.equal Exp.equal (guards_of arms) [ expected ]));

    (* Every arm carries the original condition as the left conjunct; an
       unconditional condition adds nothing.  Checked for equality and
       table-offset guards, and for both arm kinds. *)
    pin "DISP-04" "original condition conjoined with every case test"
      (fun () ->
        let target = v64 "disp4_target" in
        let summand = v64 "disp4_summand" in
        let flag = v1 "disp4_flag" in
        let cond = Bil.Var flag in
        let targets =
          [ (w 0x10L, Tid.create ()); (w 0x20L, Tid.create ());
            (w 0x30L, Tid.create ()) ]
        in
        let same_with_cond ~base ~kind =
          let bare =
            D.arms ~kind ~cond:None ~target:(Bil.Var target) ~base ~targets
          in
          let with_cond =
            D.arms ~kind ~cond:(Some cond) ~target:(Bil.Var target) ~base
              ~targets
          in
          Base.List.for_all2_exn bare with_cond ~f:(fun b c ->
              Tid.equal b.target c.target
              && b.kind = c.kind
              && Exp.equal c.guard (and_ cond b.guard))
        in
        let true_cond_is_unconditional =
          let base = Some (table ~summand ~values:[ 0x400000L ]) in
          let bare =
            D.arms ~kind:D.Jump ~cond:None ~target:(Bil.Var target) ~base
              ~targets
          in
          let with_true =
            D.arms ~kind:D.Jump ~cond:(Some (Bil.Int (Word.one 1)))
              ~target:(Bil.Var target) ~base ~targets
          in
          Base.List.equal Exp.equal (guards_of bare) (guards_of with_true)
        in
        check "DISP-04"
          (same_with_cond ~base:None ~kind:D.Jump
          && same_with_cond
               ~base:(Some (table ~summand ~values:[ 0x400000L; 0x500000L ]))
               ~kind:D.Call
          && true_cond_is_unconditional
          && Base.List.equal (fun a b -> a = b)
               (kinds_of
                  (D.arms ~kind:D.Call ~cond:(Some cond)
                     ~target:(Bil.Var target) ~base:None ~targets))
               [ D.Call; D.Call; D.Call ]));

    (* Duplicate words and duplicate targets each get their own arm, in
       input order. *)
    pin "DISP-05" "duplicate words and targets keep order and one arm each"
      (fun () ->
        let target = v64 "disp5_target" in
        let t1 = Tid.create () and t2 = Tid.create () in
        let targets =
          [ (w 0x10L, t1); (w 0x10L, t1); (w 0x20L, t2); (w 0x10L, t2) ]
        in
        let arms =
          D.arms ~kind:D.Jump ~cond:None ~target:(Bil.Var target) ~base:None
            ~targets
        in
        let expected_guards =
          [ eq (Bil.Var target) (wexp 0x10L);
            eq (Bil.Var target) (wexp 0x10L);
            eq (Bil.Var target) (wexp 0x20L);
            eq (Bil.Var target) (wexp 0x10L) ]
        in
        check "DISP-05"
          (Int.equal (Base.List.length arms) 4
          && Base.List.equal Exp.equal (guards_of arms) expected_guards
          && Base.List.equal Tid.equal (targets_of arms)
               [ t1; t1; t2; t2 ]));

    (* A missing base and a base with no values both fall back to the
       absolute equality test. *)
    pin "DISP-06" "no usable base falls back to equality guards" (fun () ->
        let target = v64 "disp6_target" in
        let summand = v64 "disp6_summand" in
        let targets = [ (w 0x401000L, Tid.create ()) ] in
        let expected = [ eq (Bil.Var target) (wexp 0x401000L) ] in
        let none =
          guards_of
            (D.arms ~kind:D.Jump ~cond:None ~target:(Bil.Var target) ~base:None
               ~targets)
        in
        let empty =
          guards_of
            (D.arms ~kind:D.Jump ~cond:None ~target:(Bil.Var target)
               ~base:(Some (table ~summand ~values:[])) ~targets)
        in
        check "DISP-06"
          (Base.List.equal Exp.equal none expected
          && Base.List.equal Exp.equal empty expected));

    (* A stable variable target is reused: no def, guards read it. *)
    pin "DISP-07" "a stable target is reused without a def" (fun () ->
        let target = v64 "disp7_target" in
        let e = Bil.Var target in
        let bound, binding = D.bind_target e in
        let targets = [ (w 0x10L, Tid.create ()); (w 0x20L, Tid.create ()) ] in
        let m = mat targets in
        let m_binding, arms =
          D.materialize m ~kind:D.Jump ~cond:None ~target:e
        in
        check "DISP-07"
          (Exp.equal bound e
          && Option.is_none binding
          && Option.is_none m_binding
          && Base.List.equal Exp.equal (guards_of arms)
               [ eq e (wexp 0x10L); eq e (wexp 0x20L) ]));

    (* A non-variable target gets one fresh def [t := e]; every guard reads
       the bound variable, and the def's rhs is the original expression. *)
    pin "DISP-08" "a non-stable target gets one fresh binding def"
      (fun () ->
        let target = v64 "disp8_target" in
        let e = Bil.BinOp (Bil.PLUS, Bil.Var target, iexp 8L) in
        let bound, binding = D.bind_target e in
        let targets = [ (w 0x10L, Tid.create ()); (w 0x20L, Tid.create ()) ] in
        let m = mat targets in
        let m_binding, arms =
          D.materialize m ~kind:D.Call ~cond:None ~target:e
        in
        match binding, m_binding, bound with
        | Some (v, d), Some (v', d'), Bil.Var v'' ->
          check "DISP-08"
            (Var.equal v v''
            && Var.is_virtual v
            && Var.is_virtual v'
            && Exp.equal (Def.rhs d) e
            && Exp.equal (Def.rhs d') e
            && Var.equal (Def.lhs d) v
            && Var.equal (Def.lhs d') v'
            && Base.List.equal (fun a b -> a = b) (kinds_of arms)
                 [ D.Call; D.Call ]
            && Base.List.equal Exp.equal (guards_of arms)
                 [ eq (Bil.Var v') (wexp 0x10L);
                   eq (Bil.Var v') (wexp 0x20L) ])
        | _ -> check "DISP-08" false);
  ]

let () = run "dispatch" tests
