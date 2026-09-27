(* The SSA pass's pins: the materialized phi shape, the call-ret
   versioning convention, and the sub's input lanes under SSA. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

let guard v k =
  Bil.BinOp (Bil.EQ, Bil.Var v, Bil.Int (Cbat_word.to_word (w64 k)))


let ret_reg = v64 "RAX"

let tests : unit Alcotest.test list =
  [
    pin "SSA-01" "a call site's ret lanes mint versions stamped on its block"
      (fun () ->
        let callee, _ = sub_of "@retcallee" [ [], [ (0, mk_ret) ] ] in
        let callee =
          Term.append arg_t callee (Arg.create ~intent:Out ret_reg (Var ret_reg))
        in
        let caller, _ =
          sub_of "ret_caller"
            [ [],
              [ (1,
                 fun t ->
                   Jmp.create
                     (Call
                        (Call.create ~return:(Direct t)
                           ~target:(Direct (Term.tid callee))
                           ()))) ];
              [ Def.create (v64 "rc_use")
                  (Bil.BinOp
                     (Bil.PLUS, Bil.Var ret_reg,
                      Bil.Int (Cbat_word.to_word (w64 1)))) ],
              [ (0, mk_ret) ] ]
        in
        let prog = Program.create ~subs:[ callee; caller ] () in
        let prog = B2l.sign_program ~target:Theory.Target.unknown prog in
        let prog = Hike.Ssa.ssa_program ~target:Theory.Target.unknown prog in
        let caller' =
          Term.enum sub_t prog
          |> Seq.find ~f:(fun s -> String.equal (Sub.name s) "ret_caller")
          |> Base.Option.value_exn
        in
        let call_blk = Term.first blk_t caller' |> Base.Option.value_exn in
        let stamp =
          Term.get_attr call_blk Hike.Stack_model.versions_tag
          |> Base.Option.value_exn
        in
        let stamped =
          Base.List.Assoc.find stamp.Hike.Stack_model.Versions.rets ret_reg
            ~equal:Var.same
        in
        check "SSA-01"
          (Hike.Stack_model.is_ssa caller'
          && Base.Option.is_some stamped
          && Base.Option.is_some
               (Base.Option.filter stamped ~f:(fun v ->
                    Var.index v > 0
                    && String.equal (Var.name (Var.base v)) "RAX")));
        (* The continuation reads the stamped version. *)
        let cont =
          Term.enum blk_t caller'
          |> Seq.find ~f:(fun b ->
                 Term.enum def_t b
                 |> Seq.exists ~f:(fun d ->
                        Var.equal (Var.base (Def.lhs d)) (v64 "rc_use")))
          |> Base.Option.value_exn
        in
        let reads_version =
          Term.enum def_t cont
          |> Seq.exists ~f:(fun d ->
                 match Def.rhs d with
                 | Bil.BinOp (Bil.PLUS, Bil.Var v, Bil.Int _) ->
                     Base.Option.equal Var.equal stamped (Some v)
                 | _ -> false)
        in
        check "SSA-01" reads_version);

    pin "SSA-02" "a join's phi is materialized with versioned lhs and per-edge versions"
      (fun () ->
        let v = v64 "sj_v" in
        let j =
          let b = Blk.Builder.create () in
          Blk.Builder.add_def b
            (Def.create (v64 "sj_x")
               (Bil.BinOp
                  (Bil.PLUS, Bil.Var v,
                   Bil.Int (Cbat_word.to_word (w64 1)))));
          ignore (Blk.Builder.add_jmp b (Hike__Hike_return.create ()));
          Blk.Builder.result b
        in
        let p1 =
          with_jmps
            (blk_of_defs [ Def.create v (Bil.Int (Cbat_word.to_word (w64 1))) ])
            [ mk_goto (Term.tid j) ]
        in
        let p2 =
          with_jmps
            (blk_of_defs [ Def.create v (Bil.Int (Cbat_word.to_word (w64 2))) ])
            [ mk_goto (Term.tid j) ]
        in
        let e =
          with_jmps (blk_of_defs [])
            [ mk_jmp_to (Term.tid p1) (guard (v64 "sj_c") 0);
              mk_goto (Term.tid p2) ]
        in
        let sub =
          let sb = Sub.Builder.create ~name:"sj" () in
          Sub.Builder.add_blk sb e;
          Sub.Builder.add_blk sb p1;
          Sub.Builder.add_blk sb p2;
          Sub.Builder.add_blk sb j;
          Sub.Builder.result sb
        in
        let prog = Program.create ~subs:[ sub ] () in
        let prog = B2l.sign_program ~target:Theory.Target.unknown prog in
        let prog = Hike.Ssa.ssa_program ~target:Theory.Target.unknown prog in
        let sub =
          Term.enum sub_t prog |> Seq.hd_exn
        in
        let join =
          Term.enum blk_t sub
          |> Seq.find ~f:(fun b -> not (Seq.is_empty (Term.enum phi_t b)))
          |> Base.Option.value_exn
        in
        let phis = Term.enum phi_t join |> Seq.to_list in
        let sj_phi =
          Base.List.find phis ~f:(fun p ->
              String.equal (Var.name (Var.base (Phi.lhs p))) "sj_v")
          |> Base.Option.value_exn
        in
        let incomings = Phi.values sj_phi |> Seq.to_list in
        Printf.printf "===S2 phi=%s incomings=[%s]\n"
          (Var.name (Phi.lhs sj_phi))
          (String.concat ";"
             (Base.List.map incomings ~f:(fun (_, e) ->
                  match e with
                  | Bil.Var w -> Var.name w ^ "/" ^ string_of_int (Var.index w)
                  | _ -> "exp")));
        check "SSA-02"
          (Var.index (Phi.lhs sj_phi) > 0
          && Base.List.length incomings = 2
          && Base.List.for_all incomings ~f:(fun (_, exp) ->
                 match exp with
                 | Bil.Var w ->
                     String.equal (Var.name (Var.base w)) "sj_v"
                     && Var.index w > 0
                 | _ -> false)));

    pin "SSA-04" "var versions are distinct under Var.equal, equal under Var.same"
      (fun () ->
        let v = v64 "RAX" in
        let v1 = Var.with_index v 1 in
        check "SSA-04"
          (not (Var.equal v1 v)
          && Var.same v1 v
          && String.equal (Var.name v1) "RAX.1"
          && Var.index (Var.base v1) = 0));

    pin "SSA-03" "under SSA the sub's input lanes are its index-0 reads"
      (fun () ->
        let v = v64 "s3_v" in
        let sub =
          let b = Blk.Builder.create () in
          Blk.Builder.add_def b
            (Def.create v (Bil.Var (v64 "RDI")));
          ignore (Blk.Builder.add_jmp b (Hike__Hike_return.create ()));
          Blk.Builder.result b
        in
        let sub =
          let sb = Sub.Builder.create ~name:"s3" () in
          Sub.Builder.add_blk sb sub;
          Sub.Builder.result sb
        in
        let prog = Program.create ~subs:[ sub ] () in
        let prog = B2l.sign_program ~target:Theory.Target.unknown prog in
        let prog = Hike.Ssa.ssa_program ~target:Theory.Target.unknown prog in
        let sub = Term.enum sub_t prog |> Seq.hd_exn in
        check "SSA-03"
          (Hike.Stack_model.is_ssa sub
          && Hike.Ssa.free_regs_ssa sub = [ v64 "RDI" ]));
  ]

let () = run "hike_ssa" tests
