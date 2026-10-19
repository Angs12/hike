(* The SSA pass's pins: the materialized phi shape, the call-ret
   versioning convention, and the sub's input lanes under SSA. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

let guard v k =
  Bil.BinOp (Bil.EQ, Bil.Var v, Bil.Int (Cbat_word.to_word (w64 k)))


let ret_reg = int_ret 0

let sub_named name blks =
  let sb = Sub.Builder.create ~name () in
  List.iter (Sub.Builder.add_blk sb) blks;
  Sub.Builder.result sb

let ssa_of sub =
  Program.create ~subs:[ sub ] ()
  |> Hike.Ssa.ssa_program ~synth:Hike.Synth.empty ~target:(x86_target ())
  |> Term.enum sub_t |> Seq.hd_exn

(* The SSA of [old_pre], the update to [full] (the new blocks pre-SSA,
   changed blocks replaced), and fresh construction on [full]. *)
let updated ~old_pre ~full =
  let old_ssa = ssa_of old_pre in
  let abi = Hike.Abi.of_target (x86_target ()) in
  let prepared =
    Hike.Stack_model.prepare_effects ~synth:Hike.Synth.empty ~abi
      ~callee:(Fun.const None) full
  in
  let ids sel b = Term.enum sel b |> Seq.map ~f:Term.tid |> Seq.to_list in
  let mixed =
    Term.map blk_t old_ssa ~f:(fun b ->
        match Term.find blk_t prepared (Term.tid b) with
        | Some pb when ids def_t pb <> ids def_t b -> pb
        | Some pb when ids jmp_t pb <> ids jmp_t b ->
            (* The SSA block with its jmps swapped. *)
            Seq.fold (Term.enum jmp_t pb)
              ~init:(Term.filter jmp_t b ~f:(Fun.const false))
              ~f:(fun b j -> Term.append jmp_t b j)
        | _ -> b)
  in
  let mixed =
    Seq.fold (Term.enum blk_t prepared) ~init:mixed ~f:(fun m pb ->
        if Base.Option.is_none (Term.find blk_t m (Term.tid pb)) then
          Term.append blk_t m pb
        else m)
  in
  let upd =
    Hike.Ssa.update_sub ~synth:Hike.Synth.empty ~target:(x86_target ())
      ~old:old_ssa mixed
  in
  (old_ssa, upd, ssa_of full)

let blk_in sub b = Term.find blk_t sub (Term.tid b) |> Base.Option.value_exn

(* A block the update left alone: same terms and same version stamp. *)
let kept old_ssa upd b =
  let o = blk_in old_ssa b and u = blk_in upd b in
  String.equal (Blk.to_string o) (Blk.to_string u)
  && Base.Option.equal
       (fun x y -> Hike.Stack_model.Versions.compare x y = 0)
       (Term.get_attr o Hike.Stack_model.versions_tag)
       (Term.get_attr u Hike.Stack_model.versions_tag)

let phi_arity sub b base =
  Term.enum phi_t (blk_in sub b)
  |> Seq.find ~f:(fun p -> Var.same (Var.base (Phi.lhs p)) base)
  |> Base.Option.map ~f:(fun p -> Seq.length (Phi.values p))

let int_exp k = Bil.Int (Cbat_word.to_word (w64 k))
(* The VSA tolerates SSA input: both forms of the same subs run from the
   anchored entry, and every def of the unversioned sub carries the same
   value in the SSA sub. *)
let c64 k = Bil.Int (Cbat_word.to_word (w64 k))

(* Every imm def's value right after it, by def tid. *)
let def_values sub sol : (Tid.t * Ws.t) list =
  Term.enum blk_t sub
  |> Seq.fold ~init:[] ~f:(fun acc blk ->
         fst
           (Vsa.fold_block_states ~synth:Hike.Synth.empty ~sol blk ~init:acc
              ~f:(fun _ after d acc ->
                match Var.typ (Def.lhs d) with
                | Type.Imm w ->
                    (Term.tid d, AI.find_word w after (Def.lhs d)) :: acc
                | _ -> acc)))

let ssa_matches (subs : sub term list) (name : string) : bool =
  let subs = Base.List.map subs ~f:jump_compiled in
  let plain =
    Base.List.find_exn subs ~f:(fun s -> String.equal (Sub.name s) name) in
  let ssa = ssa_of_subs subs name in
  let want = def_values plain (run_ssa_anchored plain) in
  let got = def_values ssa (run_ssa_anchored ssa) in
  not (Base.List.is_empty want)
  && Base.List.for_all want ~f:(fun (tid, ws) ->
         match Base.List.Assoc.find got tid ~equal:Tid.equal with
         | Some ws' -> Ws.equal ws ws'
         | None -> false)

let guard_lt v k = Bil.BinOp (Bil.LT, Bil.Var v, c64 k)

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
        let prog = Hike.Ssa.ssa_program ~synth:Hike.Synth.empty ~target:(x86_target ()) prog in
        let prog = Hike.Types.sign_program ~synth:Hike.Synth.empty ~target:(x86_target ()) prog in
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
        let call = Term.first jmp_t call_blk |> Base.Option.value_exn in
        check "SSA-01 term writes are the stamped results"
          (Core.Set.equal (Hike.Stack_model.writes (`Jmp call))
             (stamp.Hike.Stack_model.Versions.rets
              |> Base.List.map ~f:snd |> Var.Set.of_list));
        check "SSA-01"
          (Base.Option.is_some stamped
          && Base.Option.is_some
               (Base.Option.filter stamped ~f:(fun v ->
                    Var.index v > 0
                    && Var.same (Var.base v) (int_ret 0))));
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
        let prog = Hike.Ssa.ssa_program ~synth:Hike.Synth.empty ~target:(x86_target ()) prog in
        let prog = Hike.Types.sign_program ~synth:Hike.Synth.empty ~target:(x86_target ()) prog in
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
            (Def.create v (Bil.Var (int_param 0)));
          ignore (Blk.Builder.add_jmp b (Hike_return.create ()));
          Blk.Builder.result b
        in
        let sub =
          let sb = Sub.Builder.create ~name:"s3" () in
          Sub.Builder.add_blk sb sub;
          Sub.Builder.result sb
        in
        let prog = Program.create ~subs:[ sub ] () in
        let prog = Hike.Ssa.ssa_program ~synth:Hike.Synth.empty ~target:(x86_target ()) prog in
        let prog = Hike.Types.sign_program ~synth:Hike.Synth.empty ~target:(x86_target ()) prog in
        let sub = Term.enum sub_t prog |> Seq.hd_exn in
        let abi = Hike.Abi.of_target (x86_target ()) in
        let free = Hike.Ssa.free_regs_ssa ~synth:Hike.Synth.empty ~abi sub in
        check "SSA-03"
          (Base.List.exists free ~f:(Var.same (int_param 0))
          && Base.List.for_all free ~f:(fun v ->
                 Var.same v (int_param 0) || Hike.Abi.is_return_reg abi v)));

    pin "SSA-04" "a call return and bypass value meet in a join phi"
      (fun () ->
        let ret_reg = int_ret 0 in
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
        let prog = Hike.Ssa.ssa_program ~synth:Hike.Synth.empty ~target:(x86_target ()) prog in
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
      "a self-loop phi is placed only for vars live into the header"
      (fun () ->
        let ctr = v64 "ssa5_ctr" in
        let tmp = v64 "ssa5_tmp" in
        let one = Bil.Int (Cbat_word.to_word (w64 1)) in
        let loop_blk =
          blk_of_defs
            [ Def.create tmp (Bil.BinOp (Bil.PLUS, Bil.Var ctr, one));
              Def.create ctr (Bil.Var tmp) ]
        in
        let exit_blk = with_jmps (blk_of_defs []) [ Hike_return.create () ] in
        let loop_blk =
          with_jmps loop_blk
            [ mk_jmp_to (Term.tid loop_blk) (Bil.Var (v1 "ssa5_cond"));
              mk_goto (Term.tid exit_blk) ]
        in
        let entry =
          with_jmps
            (blk_of_defs
               [ Def.create ctr (Bil.Int (Cbat_word.to_word (w64 0))) ])
            [ mk_goto (Term.tid loop_blk) ]
        in
        let sub =
          let sb = Sub.Builder.create ~name:"ssa5" () in
          Sub.Builder.add_blk sb entry;
          Sub.Builder.add_blk sb loop_blk;
          Sub.Builder.add_blk sb exit_blk;
          Sub.Builder.result sb
        in
        let prog = Program.create ~subs:[ sub ] () in
        let prog = Hike.Ssa.ssa_program ~synth:Hike.Synth.empty ~target:(x86_target ()) prog in
        let prog = Hike.Types.sign_program ~synth:Hike.Synth.empty ~target:(x86_target ()) prog in
        let sub = Term.enum sub_t prog |> Seq.hd_exn in
        let header =
          Term.find blk_t sub (Term.tid loop_blk) |> Base.Option.value_exn
        in
        let phi_of v =
          Term.enum phi_t header
          |> Seq.exists ~f:(fun p -> Var.same (Var.base (Phi.lhs p)) v)
        in
        check "SSA-05" (phi_of ctr && not (phi_of tmp)));

    pin "SSA-14" "signing an SSA program builds the call and stack-argument lanes"
      (fun () ->
        let target = x86_target () in
        let slot = v64 "ssa7_arg" in
        let synth = Hike.Synth.add Hike.Synth.empty slot (K_argument 6) in
        let callee, _ = sub_of "ssa7_callee" [ [], [ (0, mk_ret) ] ] in
        let callee =
          Term.append arg_t callee (Arg.create ~intent:Out ret_reg (Var ret_reg))
        in
        let caller =
          let after = Tid.create () in
          let b0 =
            Blk.create
              ~defs:
                [ Def.create (int_param 1) (Bil.Var (v64 "ssa7_in"));
                  Def.create (v64 "ssa7_x") (Bil.Var slot) ]
              ~jmps:
                [ Jmp.create
                    (Call
                       (Call.create ~return:(Direct after)
                          ~target:(Direct (Term.tid callee)) ())) ]
              ()
          in
          let b1 =
            Blk.create ~tid:after
              ~defs:[ Def.create (v64 "ssa7_y") (Bil.Var ret_reg) ]
              ~jmps:[ Hike_return.create () ] ()
          in
          let sb = Sub.Builder.create ~name:"ssa7" () in
          Sub.Builder.add_blk sb b0;
          Sub.Builder.add_blk sb b1;
          Term.append arg_t (Sub.Builder.result sb)
            (Arg.create ~intent:In slot (Bil.Var slot))
        in
        let prog = Program.create ~subs:[ callee; caller ] () in
        let prog = Hike.Ssa.ssa_program ~synth ~target prog in
        let before = Term.find_exn sub_t prog (Term.tid caller) in
        let prog = Hike.Types.sign_program ~synth ~target prog in
        let caller' =
          Term.enum sub_t prog
          |> Seq.find ~f:(fun s -> String.equal (Sub.name s) "ssa7")
          |> Base.Option.value_exn
        in
        let names l = Base.List.map l ~f:(fun a -> Var.name (Arg.lhs a)) in
        let args = names (Hike.Stack_model.sig_args caller') in
        let rets = names (Hike.Stack_model.sig_rets caller') in
        let has l v = Base.List.mem l (Var.name v) ~equal:String.equal in
        let abi = Hike.Abi.of_target target in
        check "SSA-14 a call keeps the parameter registers and the stack argument"
          (Base.List.for_all abi.Hike.Abi.int_param_regs ~f:(has args)
          && has args slot && has args (v64 "ssa7_in"));
        check "SSA-14 a locally defined register is not an extra lane"
          (not (has args (v64 "ssa7_x")));
        check "SSA-14 the return carrier is a return lane" (has rets ret_reg);
        check "SSA-14 narrowing preserves definitions and their fact identities"
          (Seq.for_all (Term.enum blk_t before) ~f:(fun b ->
               let after = Term.find_exn blk_t caller' (Term.tid b) in
               Base.List.equal Def.equal
                 (Term.enum def_t b |> Seq.to_list)
                 (Term.enum def_t after |> Seq.to_list))));

    pin "SSA-06" "a call to a bodyless declaration reads the parameter registers"
      (fun () ->
        let reg = int_param 1 in
        let ext = Sub.create ~name:"ssa6_ext" () in
        let join =
          with_jmps (blk_of_defs [])
            [ Jmp.create
                (Call
                   (Call.create ~return:(Direct (Tid.create ()))
                      ~target:(Direct (Term.tid ext)) ())) ]
        in
        let arm k =
          with_jmps
            (blk_of_defs
               [ Def.create reg (Bil.Int (Cbat_word.to_word (w64 k))) ])
            [ mk_goto (Term.tid join) ]
        in
        let a1 = arm 1 and a2 = arm 2 in
        let entry =
          with_jmps (blk_of_defs [])
            [ mk_jmp_to (Term.tid a1) (Bil.Var (v1 "ssa6_cond"));
              mk_goto (Term.tid a2) ]
        in
        let sub =
          let sb = Sub.Builder.create ~name:"ssa6" () in
          List.iter (Sub.Builder.add_blk sb) [ entry; a1; a2; join ];
          Sub.Builder.result sb
        in
        let prog = Program.create ~subs:[ ext; sub ] () in
        let prog = Hike.Ssa.ssa_program ~synth:Hike.Synth.empty ~target:(x86_target ()) prog in
        let prog = Hike.Types.sign_program ~synth:Hike.Synth.empty ~target:(x86_target ()) prog in
        let sub =
          Term.enum sub_t prog
          |> Seq.find ~f:(fun s -> String.equal (Sub.name s) "ssa6")
          |> Base.Option.value_exn
        in
        let join' = Term.find blk_t sub (Term.tid join) |> Base.Option.value_exn in
        check "SSA-06"
          (Term.enum phi_t join'
          |> Seq.exists ~f:(fun p -> Var.same (Var.base (Phi.lhs p)) reg)));

    pin "SSA-07" "a new predecessor of a merge widens its phi and equals fresh SSA"
      (fun () ->
        let v = v64 "u7_v" and c = v1 "u7_c" in
        let j =
          with_jmps
            (blk_of_defs [ Def.create (v64 "u7_x") (Bil.Var v) ])
            [ Hike_return.create () ]
        in
        let arm k =
          with_jmps (blk_of_defs [ Def.create v (int_exp k) ])
            [ mk_goto (Term.tid j) ]
        in
        let p1 = arm 1 and p2 = arm 2 and p3 = arm 3 in
        let e0 = blk_of_defs [] in
        let e_old =
          with_jmps e0 [ mk_jmp_to (Term.tid p1) (guard c 0); mk_goto (Term.tid p2) ]
        in
        let e_new =
          with_jmps e0
            [ mk_jmp_to (Term.tid p1) (guard c 0);
              mk_jmp_to (Term.tid p3) (guard c 1);
              mk_goto (Term.tid p2) ]
        in
        let old_ssa, upd, fresh =
          updated ~old_pre:(sub_named "u7" [ e_old; p1; p2; j ])
            ~full:(sub_named "u7" [ e_new; p1; p2; j; p3 ])
        in
        check "SSA-07 equals fresh" (Hike.Ssa.equivalent upd fresh);
        check "SSA-07 phi" (phi_arity upd j v = Some 3);
        check "SSA-07 untouched" (kept old_ssa upd p1 && kept old_ssa upd p2));

    pin "SSA-08" "a new definition on a path renames downstream with fresh versions"
      (fun () ->
        let v = v64 "u8_v" in
        let j =
          with_jmps
            (blk_of_defs [ Def.create (v64 "u8_x") (Bil.Var v) ])
            [ Hike_return.create () ]
        in
        let m = with_jmps (blk_of_defs []) [ mk_goto (Term.tid j) ] in
        let e =
          with_jmps (blk_of_defs [ Def.create v (int_exp 1) ])
            [ mk_goto (Term.tid m) ]
        in
        let bump =
          Def.create v (Bil.BinOp (Bil.PLUS, Bil.Var v, int_exp 1))
        in
        let m' = Term.append def_t m bump in
        let old_ssa, upd, fresh =
          updated ~old_pre:(sub_named "u8" [ e; m; j ])
            ~full:(sub_named "u8" [ e; m'; j ])
        in
        let top sub =
          Term.enum def_t (blk_in sub e)
          |> Seq.hd_exn |> Def.lhs |> Var.index
        in
        let bumped =
          Term.enum def_t (blk_in upd m') |> Seq.hd_exn |> Def.lhs |> Var.index
        in
        check "SSA-08 equals fresh" (Hike.Ssa.equivalent upd fresh);
        check "SSA-08 untouched" (kept old_ssa upd e);
        check "SSA-08 fresh version" (bumped > top old_ssa));

    pin "SSA-09" "a new case body joining a loop header equals fresh SSA"
      (fun () ->
        let ctr = v64 "u9_ctr" and cond = v1 "u9_c" in
        let exit_b =
          with_jmps
            (blk_of_defs [ Def.create (v64 "u9_out") (Bil.Var ctr) ])
            [ Hike_return.create () ]
        in
        let body0 =
          blk_of_defs
            [ Def.create ctr (Bil.BinOp (Bil.PLUS, Bil.Var ctr, int_exp 1)) ]
        in
        let h0 = blk_of_defs [] in
        let body = with_jmps body0 [ mk_goto (Term.tid h0) ] in
        let h =
          with_jmps h0
            [ mk_jmp_to (Term.tid body) (Bil.Var cond);
              mk_goto (Term.tid exit_b) ]
        in
        let e0 = blk_of_defs [ Def.create ctr (int_exp 0) ] in
        let e_old = with_jmps e0 [ mk_goto (Term.tid h) ] in
        let case =
          with_jmps (blk_of_defs [ Def.create ctr (int_exp 5) ])
            [ mk_goto (Term.tid h) ]
        in
        let e_new =
          with_jmps e0
            [ mk_jmp_to (Term.tid case) (guard cond 7); mk_goto (Term.tid h) ]
        in
        let old_ssa, upd, fresh =
          updated ~old_pre:(sub_named "u9" [ e_old; h; body; exit_b ])
            ~full:(sub_named "u9" [ e_new; h; body; exit_b; case ])
        in
        check "SSA-09 equals fresh" (Hike.Ssa.equivalent upd fresh);
        check "SSA-09 phi" (phi_arity upd h ctr = Some 3);
        check "SSA-09 entry defs kept"
          (Var.equal
             (Def.lhs (Seq.hd_exn (Term.enum def_t (blk_in old_ssa e_old))))
             (Def.lhs (Seq.hd_exn (Term.enum def_t (blk_in upd e_old))))));
    pin "SSA-15" "removed versions are never reused by later updates"
      (fun () ->
        let v = v64 "history_v" in
        let old = straight_sub "history"
            [ Def.create v (int_exp 1); Def.create v (int_exp 2) ] |> ssa_of in
        let old_top = Term.enum blk_t old |> Seq.concat_map ~f:(Term.enum def_t)
          |> Seq.fold ~init:0 ~f:(fun n d -> max n (Var.index (Def.lhs d))) in
        let update old sub = Hike.Ssa.update_sub ~synth:Hike.Synth.empty
            ~target:(x86_target ()) ~old sub in
        let empty = Term.map blk_t old ~f:(fun b ->
            Term.filter def_t b ~f:(Fun.const false)) |> update old in
        let added = Term.map blk_t empty ~f:(fun b ->
            Term.append def_t b (Def.create v (int_exp 3))) |> update empty in
        let d = Term.first blk_t added |> Base.Option.value_exn
          |> Term.first def_t |> Base.Option.value_exn in
        check "SSA-15 fresh after removal" (Var.index (Def.lhs d) > old_top));

    pin "SSA-16" "a changed read on the same jump tid is renamed and woken"
      (fun () ->
        let a = v64 "same_a" and b = v64 "same_b" in
        let sub, _ = sub_of "same_jump"
            [ [ Def.create a (int_exp 1); Def.create b (int_exp 2) ],
              [ (1, fun t -> mk_jmp_to t (guard a 1)); (2, mk_goto) ];
              [], [ (0, mk_ret) ]; [], [ (0, mk_ret) ] ] in
        let old = ssa_of sub in
        let entry = Term.first blk_t old |> Base.Option.value_exn in
        let jump = Term.first jmp_t entry |> Base.Option.value_exn in
        let changed = Term.update blk_t old
            (Term.update jmp_t entry (Jmp.with_cond jump (guard b 2))) in
        let result, woken = Hike.Ssa.update_sub_woken ~synth:Hike.Synth.empty
            ~target:(x86_target ()) ~old changed in
        let fresh = Hike.Ssa.unssa_sub changed |> ssa_of in
        check "SSA-16 equals fresh" (Hike.Ssa.equivalent result fresh);
        check "SSA-16 wakes changed block" (Core.Set.mem woken (Term.tid entry)));

    pin "SSA-17" "signature lanes reach callers through recursive call groups"
      (fun () ->
        let lane = v64 "signature_lane" in
        let a = Tid.for_name "sig_a" and b = Tid.for_name "sig_b" in
        let call target next = Jmp.create_call
            (Call.create ~target:(Direct target) ~return:(Direct next) ()) in
        let make tid defs target =
          fst (sub_of ~tid (Tid.name tid)
                 [ defs, [ (1, call target) ]; [], [ (0, mk_ret) ] ]) in
        let sa = make a [] b in
        let sb = make b [ Def.create ret_reg (Bil.Var lane) ] a in
        let top = make (Tid.for_name "sig_top") [] a in
        let program = Program.create ~subs:[ top; sa; sb ] ()
          |> Hike.Ssa.ssa_program ~synth:Hike.Synth.empty ~target:(x86_target ())
          |> Hike.Types.sign_program ~synth:Hike.Synth.empty ~target:(x86_target ()) in
        check "SSA-17 all callers consume the final lane"
          (Seq.for_all (Term.enum sub_t program) ~f:(fun sub ->
               Base.List.exists (Hike.Stack_model.sig_args sub)
                 ~f:(fun arg -> Var.same (Arg.lhs arg) lane))));

    pin "SSA-18" "decode preparation preserves untouched SSA blocks"
      (fun () ->
        let module P = Hike__Hike_program_vsa in
        let v = v64 "decode_v" and c = v1 "decode_c" in
        let join = with_jmps (blk_of_defs [ Def.create ret_reg (Bil.Var v) ])
            [ Hike_return.create () ] in
        let arm n = with_jmps (blk_of_defs [ Def.create v (int_exp n) ])
            [ mk_goto (Term.tid join) ] in
        let left = arm 1 and right = arm 2 and added = arm 3 in
        let entry = with_jmps (blk_of_defs [])
            [ mk_jmp_to (Term.tid left) (guard c 0); mk_goto (Term.tid right) ] in
        let before = sub_named "decode" [ entry; left; right; join ] in
        let after = Term.update blk_t before
            (with_jmps (Term.filter jmp_t entry ~f:(Fun.const false))
               [ mk_jmp_to (Term.tid left) (guard c 0);
                 mk_jmp_to (Term.tid added) (guard c 1); mk_goto (Term.tid right) ])
          |> fun s -> Term.append blk_t s added in
        let context : P.context =
          { target = x86_target (); images = []; linker_slots = Core.Int64.Set.empty;
            text_range = None; data_spans = [] } in
        let old, synth = P.prepare_function context ~synth:Hike.Synth.empty
            ~is_entry:(Fun.const false) before in
        let result, synth, _ = P.update_function context ~synth
            ~is_entry:(Fun.const false) ~old after in
        let fresh, _ = P.prepare_function context ~synth
            ~is_entry:(Fun.const false) after in
        check "SSA-18 equals fresh" (Hike.Ssa.equivalent result fresh);
        check "SSA-18 untouched versions" (kept old result left && kept old result right));

    pin "SSA-10" "the VSA gives a diamond's phi the join of its edges' values"
      (fun () ->
        let v = int_ret 0 and out = callee_saved 0 and arg = int_param 0 in
        let sub, _ =
          sub_of "ssa7"
            [ [], [ (1, fun t -> mk_jmp_to t (guard_lt arg 5)); (2, mk_goto) ];
              [ Def.create v (c64 1) ], [ (3, mk_goto) ];
              [ Def.create v (c64 2) ], [ (3, mk_goto) ];
              [ Def.create out (Bil.BinOp (Bil.PLUS, Bil.Var v, c64 1)) ],
              [ (4, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        check "SSA-10" (ssa_matches [ sub ] "ssa7"));

    pin "SSA-11" "the VSA on a loop's versioned counter matches the unversioned run"
      (fun () ->
        let i = callee_saved 1 and out = callee_saved 0 in
        let sub, _ =
          sub_of "ssa8"
            [ [ Def.create i (c64 0) ], [ (1, mk_goto) ];
              [ Def.create i (Bil.BinOp (Bil.PLUS, Bil.Var i, c64 1)) ],
              [ (1, fun t -> mk_jmp_to t (guard_lt i 10)); (2, mk_goto) ];
              [ Def.create out (Bil.Var i) ], [ (3, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        check "SSA-11" (ssa_matches [ sub ] "ssa8"));

    pin "SSA-12" "the VSA across a call keeps the callee-saved register and the restored SP"
      (fun () ->
        let callee, _ = sub_of "ssa9_callee" [ [], [ (0, mk_ret) ] ] in
        let callee =
          Term.append arg_t callee (Arg.create ~intent:Out ret_reg (Var ret_reg))
        in
        let rbx = callee_saved 0 and out = callee_saved 1 and sp_copy = int_param 1 in
        let d_out = Def.create out (Bil.BinOp (Bil.PLUS, Bil.Var rbx, c64 1)) in
        let d_sp = Def.create sp_copy (Bil.Var sp) in
        let caller, _ =
          sub_of "ssa9"
            [ [ Def.create rbx (c64 5);
                Def.create sp (Bil.BinOp (Bil.MINUS, Bil.Var sp, c64 8)) ],
              [ (1, fun t -> mk_call_jmp t (Term.tid callee)) ];
              [ d_out; d_sp ],
              [ (2, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let ssa = ssa_of_subs [ jump_compiled callee; jump_compiled caller ] "ssa9" in
        let values = def_values ssa (run_ssa_anchored ssa) in
        let value d = Base.List.Assoc.find_exn values (Term.tid d) ~equal:Tid.equal in
        check "SSA-12"
          (Ws.equal (value d_out) (Ws.singleton (w64 6))
           && Ws.equal (value d_sp) (Ws.stack_word_i64 0L)));

    pin "SSA-13" "dead register versions leave the VSA state"
      (fun () ->
        let r = int_ret 0 and out = callee_saved 0 in
        let n = 12 in
        let step () = [ Def.create r (Bil.BinOp (Bil.PLUS, Bil.Var r, c64 1)) ] in
        let sub, tids =
          sub_of "ssa10"
            ([ [ Def.create r (c64 0) ], [ (1, mk_goto) ] ]
             @ Base.List.init n ~f:(fun k -> step (), [ (k + 2, mk_goto) ])
             @ [ [ Def.create out (Bil.Var r) ], [ (n + 2, mk_goto) ];
                 [], [ (0, mk_ret) ] ])
        in
        let ssa = ssa_of_subs [ jump_compiled sub ] "ssa10" in
        let sol = run_ssa_anchored ssa in
        let versions =
          Term.enum blk_t ssa
          |> Seq.concat_map ~f:(Term.enum def_t)
          |> Seq.filter_map ~f:(fun d ->
                 let v = Def.lhs d in
                 if Var.same v r then Some v else None)
          |> Seq.to_list
        in
        let last = Graphlib.Std.Solution.get sol tids.(n + 1) in
        let held =
          Base.List.count versions ~f:(fun v ->
              not (Ws.is_top (AI.find_word 64 last v)))
        in
        check "SSA-13" (Base.List.length versions > n && held <= 1));
  ]

let () = run "hike_ssa" tests
