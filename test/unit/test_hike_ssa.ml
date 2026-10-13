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
        let prog = Hike.Types.sign_program ~target:Theory.Target.unknown prog in
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
          ignore (Blk.Builder.add_jmp b (Hike_return.create ()));
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
        let prog = Hike.Types.sign_program ~target:Theory.Target.unknown prog in
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
        check "SSA-02"
          (Var.index (Phi.lhs sj_phi) > 0
          && Base.List.length incomings = 2
          && Base.List.for_all incomings ~f:(fun (_, exp) ->
                 match exp with
                 | Bil.Var w ->
                     String.equal (Var.name (Var.base w)) "sj_v"
                     && Var.index w > 0
                 | _ -> false)));



    pin "SSA-03" "under SSA the sub's input lanes are its index-0 reads"
      (fun () ->
        let v = v64 "s3_v" in
        let sub =
          let b = Blk.Builder.create () in
          Blk.Builder.add_def b
            (Def.create v (Bil.Var (v64 "RDI")));
          ignore (Blk.Builder.add_jmp b (Hike_return.create ()));
          Blk.Builder.result b
        in
        let sub =
          let sb = Sub.Builder.create ~name:"s3" () in
          Sub.Builder.add_blk sb sub;
          Sub.Builder.result sb
        in
        let prog = Program.create ~subs:[ sub ] () in
        let prog = Hike.Types.sign_program ~target:Theory.Target.unknown prog in
        let prog = Hike.Ssa.ssa_program ~target:Theory.Target.unknown prog in
        let sub = Term.enum sub_t prog |> Seq.hd_exn in
        check "SSA-03"
          (Hike.Stack_model.is_ssa sub
          && Hike.Ssa.free_regs_ssa
               ~abi:(Hike.Abi.of_target Theory.Target.unknown) sub
             = [ v64 "RDI" ]));

    pin "SSA-04" "a call return and bypass value meet in a join phi"
      (fun () ->
        let ret_reg = v64 "RAX" in
        let callee, _ = sub_of "ssa4_callee" [ [], [ (0, mk_ret) ] ] in
        let callee =
          Term.append arg_t callee
            (Arg.create ~intent:Out ret_reg (Bil.Var ret_reg))
        in
        let join =
          let b = Blk.Builder.create () in
          Blk.Builder.add_def b
            (Def.create (v64 "ssa4_use") (Bil.Var ret_reg));
          ignore (Blk.Builder.add_jmp b (Hike_return.create ()));
          Blk.Builder.result b
        in
        let call =
          with_jmps (blk_of_defs [])
            [ Jmp.create
                (Call
                   (Call.create ~return:(Direct (Term.tid join))
                      ~target:(Direct (Term.tid callee)) ())) ]
        in
        let bypass = with_jmps (blk_of_defs []) [ mk_goto (Term.tid join) ] in
        let initial = Cbat_word.to_word (w64 5) in
        let entry =
          with_jmps
            (blk_of_defs [ Def.create ret_reg (Bil.Int initial) ])
            [ mk_jmp_to (Term.tid call) (Bil.Var (v1 "ssa4_cond"));
              mk_goto (Term.tid bypass) ]
        in
        let sub =
          let sb = Sub.Builder.create ~name:"ssa4_caller" () in
          Sub.Builder.add_blk sb entry;
          Sub.Builder.add_blk sb call;
          Sub.Builder.add_blk sb bypass;
          Sub.Builder.add_blk sb join;
          Sub.Builder.result sb
        in
        let prog = Program.create ~subs:[ callee; sub ] () in
        let prog = Hike.Ssa.ssa_program ~target:Theory.Target.unknown prog in
        let caller =
          Term.enum sub_t prog
          |> Seq.find ~f:(fun s -> String.equal (Sub.name s) "ssa4_caller")
          |> Base.Option.value_exn
        in
        let call' = Term.find blk_t caller (Term.tid call) |> Base.Option.value_exn in
        let join' = Term.find blk_t caller (Term.tid join) |> Base.Option.value_exn in
        let phi =
          Term.enum phi_t join'
          |> Seq.find ~f:(fun p -> Var.same (Var.base (Phi.lhs p)) ret_reg)
          |> Base.Option.value_exn
        in
        let versions =
          Term.get_attr call' Hike.Stack_model.versions_tag
          |> Base.Option.value_exn
        in
        let call_version =
          Base.List.Assoc.find versions.Hike.Stack_model.Versions.rets ret_reg
            ~equal:Var.same
          |> Base.Option.value_exn
        in
        let incoming = Phi.values phi |> Seq.to_list in
        let call_incoming =
          Base.List.Assoc.find incoming (Term.tid call) ~equal:Tid.equal
        in
        let bypass_incoming =
          Base.List.Assoc.find incoming (Term.tid bypass) ~equal:Tid.equal
        in
        let bypass_has_version =
          match bypass_incoming with
          | None -> false
          | Some exp ->
              let vars = Exp.free_vars exp in
              Core.Set.length vars = 1
              && (let v = Core.Set.choose_exn vars in
                  Exp.equal exp (Bil.Var v)
                  && Var.same (Var.base v) ret_reg
                  && Var.index v > 0)
        in
        check "SSA-04"
          (Var.index (Phi.lhs phi) > 0
          && Option.equal Exp.equal call_incoming (Some (Bil.Var call_version))
          && bypass_has_version));

    pin "SSA-05"
      "a dynamic allocation records the SP version live before it, though \
       it reads no SP and writes another register"
      (fun () ->
        let rsp = v64 "RSP" and rax = v64 "RAX" and rbx = v64 "RBX" in
        let d_adj =
          Def.create rsp
            (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 8))))
        in
        let d_prod = Def.create rax (Bil.BinOp (Bil.MINUS, Bil.Var rax, Bil.Var rbx)) in
        let sub =
          straight_sub "ssa_dyn_alloc"
            [ Def.create rax (Bil.Var rsp);
              d_adj;
              d_prod;
              Def.create rsp (Bil.Var rax) ]
          |> Hike.Def_slots.stamp_dyn_allocs
               ~allocs:
                 (Tid.Map.singleton (Term.tid d_prod)
                    { Hike.Def_slots.floor = 0L; parent = None })
        in
        let prog = Program.create ~subs:[ sub ] () in
        let prog = Hike.Types.sign_program ~target:Theory.Target.unknown prog in
        let prog = Hike.Ssa.ssa_program ~target:Theory.Target.unknown prog in
        let defs =
          Term.enum sub_t prog |> Seq.hd_exn |> Term.enum blk_t
          |> Seq.concat_map ~f:(Term.enum def_t)
        in
        let find tid = Seq.find defs ~f:(fun d -> Tid.equal (Term.tid d) tid) in
        let adj_version = Base.Option.map (find (Term.tid d_adj)) ~f:Def.lhs in
        let stamped =
          Base.Option.bind (find (Term.tid d_prod)) ~f:Hike.Def_slots.def_sp_before
        in
        check "SSA-05"
          (Base.Option.is_some adj_version
          && Option.equal Var.equal stamped adj_version));
  ]

let () = run "hike_ssa" tests
