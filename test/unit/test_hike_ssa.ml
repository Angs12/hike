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

let ssa_of sub = ssa_of_subs [ sub ] (Sub.name sub)

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
  let upd, woken =
    Hike.Ssa.update_sub_woken ~synth:Hike.Synth.empty ~target:(x86_target ())
      ~old:old_ssa mixed
  in
  (old_ssa, upd, ssa_of full, woken)

let blk_in sub b = Term.find blk_t sub (Term.tid b) |> Base.Option.value_exn

(* A block the update left alone keeps its terms and SSA marker. *)
let kept old_ssa upd b =
  let o = blk_in old_ssa b and u = blk_in upd b in
  String.equal (Blk.to_string o) (Blk.to_string u)
  && Bool.equal (Term.has_attr o Hike.Stack_model.ssa_tag)
       (Term.has_attr u Hike.Stack_model.ssa_tag)

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

let solve_ssa ?(wake = Tid.Set.empty) sub init =
  let abi = Hike.Abi.of_target (x86_target ()) in
  Vsa.static_graph_vsa ~abi ~synth:(ref Hike.Synth.empty) ~wake
    ~def_reads:(fun d -> Hike.Stack_model.reads (`Def d))
    ~def_writes:(fun d -> Hike.Stack_model.writes (`Def d))
    ~phi_reads:(fun p -> Hike.Stack_model.reads (`Phi p))
    ~phi_writes:(fun p -> Hike.Stack_model.writes (`Phi p))
    ~jmp_reads:(fun j -> Core.Set.union (Hike.Stack_model.reads (`Jmp j))
        (Hike.Stack_model.writes (`Jmp j)))
    sub init

let warm_seed ~abi ~sub ~woken sol =
  let entry = Base.Option.map (Vsa.entry_block_of sub) ~f:Term.tid in
  let initial = Vsa.init_sol ~abi sub in
  let seed = Graphlib.Std.Solution.enum sol
    |> Seq.filter ~f:(fun (b, _) ->
         Option.is_some (Term.find blk_t sub b) && not (Core.Set.mem woken b))
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m (b, v) -> Core.Map.set m ~key:b ~data:v) in
  let seed = match entry with
    | Some b when Core.Set.mem woken b ->
        Core.Map.set seed ~key:b ~data:(Graphlib.Std.Solution.get initial b)
    | _ -> seed in
  let seed = Graphlib.Std.Solution.create seed (Graphlib.Std.Solution.default sol) in
  let g = Sub.to_graph sub in
  let wake = Core.Set.fold woken ~init:woken ~f:(fun acc b ->
      Graphs.Tid.Node.preds b g |> Seq.fold ~init:acc ~f:(fun acc p ->
          if Tid.equal p Graphs.Tid.start || Tid.equal p Graphs.Tid.exit then acc
          else Core.Set.add acc p)) in
  (seed, wake)

let guard_lt v k = Bil.BinOp (Bil.LT, Bil.Var v, c64 k)

let tests : unit Alcotest.test list =
  [
    pin "SSA-01" "a call site's return lanes mint versions on its jump"
      (fun () ->
        let callee, _ = raw_sub_of "@retcallee" [ [], [ (0, mk_ret) ] ] in
        let callee =
          Term.append arg_t callee (Arg.create ~intent:Out ret_reg (Var ret_reg))
        in
        let caller, _ =
          raw_sub_of "ret_caller"
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
        let minted =
          Hike.Stack_model.boundary_write call_blk ret_reg
        in
        let call = Term.first jmp_t call_blk |> Base.Option.value_exn in
        check "SSA-01 term writes include the result"
          (Base.Option.value_map minted ~default:false
             ~f:(fun v -> Core.Set.mem (Hike.Stack_model.writes (`Jmp call)) v));
        check "SSA-01"
          (Base.Option.is_some minted
          && Base.Option.is_some
               (Base.Option.filter minted ~f:(fun v ->
                    Var.index v > 0
                    && Var.same (Var.base v) (int_ret 0))));
        (* The continuation reads its own phi of the call result. *)
        let cont =
          Term.enum blk_t caller'
          |> Seq.find ~f:(fun b ->
                 Term.enum def_t b
                 |> Seq.exists ~f:(fun d ->
                        Var.equal (Var.base (Def.lhs d)) (v64 "rc_use")))
          |> Base.Option.value_exn
        in
        let result_phi = Term.enum phi_t cont
          |> Seq.find ~f:(fun p -> Var.same (Var.base (Phi.lhs p)) ret_reg)
          |> Base.Option.value_exn in
        check "SSA-01 incoming result"
          (Phi.values result_phi |> Seq.exists ~f:(fun (_, e) ->
              match e with
              | Bil.Var v -> Base.Option.equal Var.equal minted (Some v)
              | _ -> false));
        let reads_version =
          Term.enum def_t cont
          |> Seq.exists ~f:(fun d ->
                 match Def.rhs d with
                 | Bil.BinOp (Bil.PLUS, Bil.Var v, Bil.Int _) ->
                     Var.equal (Phi.lhs result_phi) v
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
        let join = blk_in sub j in
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
        let callee, _ = raw_sub_of "ssa4_callee" [ [], [ (0, mk_ret) ] ] in
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
        let call_version =
          Hike.Stack_model.boundary_write call' ret_reg
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
        let callee, _ = raw_sub_of "ssa7_callee" [ [], [ (0, mk_ret) ] ] in
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
        let v = v64 "u7_v" and c = v64 "u7_c" in
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
        let old_ssa, upd, fresh, woken =
          updated ~old_pre:(sub_named "u7" [ e_old; p1; p2; j ])
            ~full:(sub_named "u7" [ e_new; p1; p2; j; p3 ])
        in
        let phi_lhs sub =
          Term.enum phi_t (blk_in sub j)
          |> Seq.find_exn ~f:(fun p -> Var.same (Var.base (Phi.lhs p)) v)
          |> Phi.lhs in
        let local_lhs sub =
          Term.enum def_t (blk_in sub j)
          |> Seq.find_exn ~f:(fun d -> Var.same (Var.base (Def.lhs d)) (v64 "u7_x"))
          |> Def.lhs in
        let merge_phi =
          Term.enum phi_t (blk_in upd j)
          |> Seq.find_exn ~f:(fun p -> Var.same (Var.base (Phi.lhs p)) v) in
        let p3_lhs =
          Term.enum def_t (blk_in upd p3)
          |> Seq.find_exn ~f:(fun d -> Var.same (Var.base (Def.lhs d)) v)
          |> Def.lhs in
        let new_input =
          Base.List.Assoc.find (Phi.values merge_phi |> Seq.to_list) (Term.tid p3)
            ~equal:Tid.equal in
        check "SSA-07 equals fresh" (Hike.Ssa.equivalent upd fresh);
        check "SSA-07 phi" (phi_arity upd j v = Some 3);
        check "SSA-07 new predecessor wired"
          (Option.equal Exp.equal new_input (Some (Bil.Var p3_lhs)));
        check "SSA-07 existing phi identity" (Var.equal (phi_lhs old_ssa) (phi_lhs upd));
        check "SSA-07 existing local identity"
          (Var.equal (local_lhs old_ssa) (local_lhs upd));
        let abi = Hike.Abi.of_target (x86_target ()) in
        let old_sol = solve_ssa old_ssa (Vsa.init_sol ~abi old_ssa) in
        let seed, wake = warm_seed ~abi ~sub:upd ~woken old_sol in
        let warm = solve_ssa ~wake upd seed in
        let cold = solve_ssa fresh (Vsa.init_sol ~abi fresh) in
        let warm_values = def_values upd warm and cold_values = def_values fresh cold in
        check "SSA-07 VSA matches cold solve"
          (Base.List.for_all warm_values ~f:(fun (tid, ws) ->
               match Base.List.Assoc.find cold_values tid ~equal:Tid.equal with
               | Some cold -> Ws.equal ws cold
               | None -> false));
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
        let old_ssa, upd, fresh, _woken =
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
        let old_ssa, upd, fresh, _woken =
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
        let sub, _ = raw_sub_of "same_jump"
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
          fst (raw_sub_of ~tid (Tid.name tid)
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
        let sub, tids =
          raw_sub_of "ssa7"
            [ [], [ (1, fun t -> mk_jmp_to t (guard_lt arg 5)); (2, mk_goto) ];
              [ Def.create v (c64 1) ], [ (3, mk_goto) ];
              [ Def.create v (c64 2) ], [ (3, mk_goto) ];
              [ Def.create out (Bil.BinOp (Bil.PLUS, Bil.Var v, c64 1)) ],
              [ (4, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let ssa = ssa_of_subs [ jump_compiled sub ] "ssa7" in
        let sol = run_ssa_anchored ssa in
        (* The join block receives the two edges' values, and the
           definition on top of it adds one. *)
        let dbg name ws =
          Printf.eprintf "DBG %s min=%s max=%s\n" name
            (match Ws.min_elem ws with Some w -> Cbat_word.to_string w | None -> "-")
            (match Ws.max_elem ws with Some w -> Cbat_word.to_string w | None -> "-") in
        let ssa2 = ssa_form ssa in
        let shape s' =
          String.concat ";" (Seq.to_list (Term.enum blk_t s')
            |> List.map (fun b ->
                Printf.sprintf "[%s]" (String.concat ","
                   (Seq.to_list (Term.enum def_t b) |> List.map (fun d -> Var.name (Def.lhs d)))))) in
        Printf.eprintf "DBG same_tid=%b\n" (Tid.equal (Term.tid ssa) (Term.tid ssa2));
        Printf.eprintf "DBG shape1=%s\n" (shape ssa);
        Printf.eprintf "DBG shape2=%s\n" (shape ssa2);
        dbg "phi" (value_at ssa sol tids.(3) v);
        dbg "out" (value_after ssa sol tids.(3) out);
        check "SSA-10"
          (Ws.equal (value_at ssa sol tids.(3) v)
             (Ws.of_list ~width:64 [ w64 1; w64 2 ])
           && Ws.equal (value_after ssa sol tids.(3) out)
              (Ws.of_list ~width:64 [ w64 2; w64 3 ])));

    pin "SSA-11" "the VSA on a loop's versioned counter matches the unversioned run"
      (fun () ->
        let i = callee_saved 1 and out = callee_saved 0 in
        let sub, tids =
          raw_sub_of "ssa8"
            [ [ Def.create i (c64 0) ], [ (1, mk_goto) ];
              [ Def.create i (Bil.BinOp (Bil.PLUS, Bil.Var i, c64 1)) ],
              [ (1, fun t -> mk_jmp_to t (guard_lt i 10)); (2, mk_goto) ];
              [ Def.create out (Bil.Var i) ], [ (3, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let ssa = ssa_of_subs [ jump_compiled sub ] "ssa8" in
        let sol = run_ssa_anchored ssa in
        (* The counter's value is the version's own: the loop reaches the
           guard's bound and stops there. *)
        let v = value_after ssa sol tids.(1) i in
        check "SSA-11"
          (Ws.elem (w64 10) v && not (Ws.elem (w64 11) v)));

    pin "SSA-12" "the VSA across a call keeps the callee-saved register and the restored SP"
      (fun () ->
        let callee, _ = raw_sub_of "ssa9_callee" [ [], [ (0, mk_ret) ] ] in
        let callee =
          Term.append arg_t callee (Arg.create ~intent:Out ret_reg (Var ret_reg))
        in
        let rbx = callee_saved 0 and out = callee_saved 1 and sp_copy = int_param 1 in
        let d_out = Def.create out (Bil.BinOp (Bil.PLUS, Bil.Var rbx, c64 1)) in
        let d_sp = Def.create sp_copy (Bil.Var sp) in
        let caller, _ =
          raw_sub_of "ssa9"
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

    pin "SSA-13" "SSA definitions keep their values after later versions are defined"
      (fun () ->
        let r = int_ret 0 and out = callee_saved 0 in
        let n = 12 in
        let step () = [ Def.create r (Bil.BinOp (Bil.PLUS, Bil.Var r, c64 1)) ] in
        let sub, tids =
          raw_sub_of "ssa10"
            ([ [ Def.create r (c64 0) ], [ (1, mk_goto) ] ]
             @ Base.List.init n ~f:(fun k -> step (), [ (k + 2, mk_goto) ])
             @ [ [ Def.create out (Bil.Var r) ], [ (n + 2, mk_goto) ];
                 [], [ (0, mk_ret) ] ])
        in
        let ssa = ssa_of_subs [ jump_compiled sub ] "ssa10" in
        let sol = run_ssa_anchored ssa in
        (* Every version keeps its own value, in the block that defines
           it: a later version does not overwrite an earlier one. *)
        let defined =
          Term.enum blk_t ssa
          |> Seq.concat_map ~f:(fun blk ->
                 Term.enum def_t blk |> Seq.filter_map ~f:(fun d ->
                     let v = Def.lhs d in
                     if Var.same v r then Some (blk, v) else None))
          |> Seq.to_list
        in
        check "SSA-13" (Base.List.length defined > n
          && Base.List.for_alli defined ~f:(fun i (blk, v) ->
              let post =
                Vsa.Test_seam.denote_defs ~synth:Hike.Synth.empty blk
                  (Graphlib.Std.Solution.get sol (Term.tid blk)) in
              Ws.equal (AI.find_word 64 post v) (Ws.singleton (w64 i)))));

    pin "SSA-19" "single-predecessor inputs retain edge bounds without narrowing the other branch"
      (fun () ->
        let x = int_param 0 and y = callee_saved 0 and z = callee_saved 1 in
        let sub, tids = raw_sub_of "edge_parameter"
            [ [], [ (1, fun t -> mk_jmp_to t (guard_lt x 5)); (3, mk_goto) ];
              [ Def.create y Bil.(var x + c64 1) ], [ (2, mk_goto) ];
              [], [ (0, mk_ret) ];
              [ Def.create z (Bil.Var x) ], [ (0, mk_ret) ] ] in
        let ssa = ssa_of_subs [ jump_compiled sub ] "edge_parameter" in
        let sol = run_ssa_anchored ssa in
        check "SSA-19 single predecessor phi"
          (phi_arity ssa (Term.find_exn blk_t ssa tids.(1)) x = Some 1
           && phi_arity ssa (Term.find_exn blk_t ssa tids.(3)) x = Some 1);
        (* The taken edge delivers the refined value; the other edge
           keeps the seeded one. *)
        let taken_y = value_after ssa sol tids.(1) y in
        let other_x = value_at ssa sol tids.(3) x in
        check "SSA-19 taken value"
          (Ws.min_elem taken_y = Some (w64 1)
           && Ws.max_elem taken_y = Some (w64 5));
        check "SSA-19 other edge"
          (not (bounded_above other_x (w64 4))));
    pin "SSA-20" "byte refinements follow phi identities across single-predecessor blocks"
      (fun () ->
        let x = int_param 0 and y = callee_saved 0 in
        let low = Bil.Cast (Bil.LOW, 8, Bil.Var x) in
        let bound = Bil.Int (Cbat_word.to_word (Cbat_word.of_int ~width:8 0x25)) in
        let sub, tids = raw_sub_of "phi_slice"
            [ [], [ (4, fun t -> mk_jmp_to t (Bil.BinOp (Bil.LT, bound, low))); (1, mk_goto) ];
              [], [ (2, mk_goto) ];
              [ Def.create y (Bil.Cast (Bil.UNSIGNED, 64, low)) ], [ (3, mk_goto) ];
              [], [ (0, mk_ret) ];
              [], [ (0, mk_ret) ] ] in
        let ssa = ssa_of_subs [ jump_compiled sub ] "phi_slice" in
        let sol = run_ssa_anchored ssa in
        (* The byte bound crosses the edge as the phi value; the whole
           word stays wide. *)
        check "SSA-20 bounded byte"
          (bounded_above (value_after ssa sol tids.(2) y) (w64 0x25));
        check "SSA-20 original word stays wide"
          (not (bounded_above (value_at ssa sol tids.(2) x) (w64 0xff))));
    pin "SSA-21" "a transfer through incoming phis still names its linker slot"
      (fun () ->
        let x = int_ret 0 and mem = memv "phi_slot_mem" in
        let load addr = Def.create x (Bil.Load
            (Bil.Var mem, c64 addr, LittleEndian, `r64)) in
        let sub, _ = raw_sub_of "phi_slot"
            [ [load 0x1000], [(1, mk_goto)];
              [], [(0, fun _ -> Jmp.create (Goto (Indirect (Bil.Var x))))] ] in
        let ssa = ssa_of sub in
        let dest = Term.enum blk_t ssa |> Seq.to_list |> Base.List.last_exn in
        let target = Term.first jmp_t dest |> Base.Option.value_exn
          |> Jmp.kind |> function Goto (Indirect e) -> e | _ -> assert false in
        check "SSA-21 singleton phi"
          (Hike_transfer.slot_of_target ~synth:Hike.Synth.empty ~sub:ssa target = Some 0x1000L);
        let merged addr =
          let sub, tids = raw_sub_of "phi_slots"
              [ [], [(1, fun t -> mk_jmp_to t (guard (int_param 0) 0)); (2, mk_goto)];
                [load 0x1000], [(3, mk_goto)];
                [load addr], [(3, mk_goto)];
                [], [(0, fun _ -> Jmp.create (Goto (Indirect (Bil.Var x))))] ] in
          let ssa = ssa_of sub in
          let blk = Term.find_exn blk_t ssa tids.(3) in
          let phi = Term.enum phi_t blk
            |> Seq.find ~f:(fun p -> Var.same (Phi.lhs p) x)
            |> Base.Option.value_exn in
          Hike_transfer.slot_of_target ~synth:Hike.Synth.empty ~sub:ssa (Bil.Var (Phi.lhs phi)) in
        check "SSA-21 common slot" (merged 0x1000 = Some 0x1000L);
        check "SSA-21 different slots" (merged 0x2000 = None));
    pin "SSA-22" "an entry backedge has separate initial and loop phi operands"
      (fun () ->
        let x = int_param 0 and y = callee_saved 0 in
        let sub, tids = raw_sub_of "entry_loop"
            [ [Def.create x Bil.(var x + c64 1)],
              [(0, fun t -> mk_jmp_to t (guard_lt x 3)); (1, mk_goto)];
              [Def.create y (Bil.Var x)], [(0, mk_ret)] ] in
        let ssa = ssa_of sub in
        let entry = Term.first blk_t ssa |> Base.Option.value_exn in
        check "SSA-22 entry is separate" (not (Tid.equal (Term.tid entry) tids.(0)));
        check "SSA-22 both operands"
          (phi_arity ssa (Term.find_exn blk_t ssa tids.(0)) x = Some 2);
        let initial = AI.add_word (anchored_entry ()) ~key:x ~data:(Ws.singleton (w64 0)) in
        let sol = static_graph_vsa ~synth:Hike.Synth.empty ~abi:Hike_abi.x86_64_sysv ssa
            (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv ~entry:initial ssa) in
        let exit = Term.find_exn blk_t ssa tids.(1) in
        let def_tid = Term.first def_t exit |> Base.Option.value_exn |> Term.tid in
        let value = Base.List.Assoc.find (def_values ssa sol) def_tid ~equal:Tid.equal
          |> Base.Option.value_exn in
        check "SSA-22 initial value reaches the loop" (Ws.equal value (Ws.singleton (w64 3))));
    pin "SSA-23" "an entry backedge update keeps unrelated blocks' versions"
      (fun () ->
        let x = int_param 0 and y = callee_saved 0 and z = callee_saved 1 in
        let sub, tids = raw_sub_of "entry_update"
            [ [ Def.create x Bil.(var x + c64 1) ],
              [ (0, fun t -> mk_jmp_to t (guard_lt x 3)); (1, mk_goto) ];
              [ Def.create y (Bil.Var x) ], [ (0, mk_ret) ] ] in
        let old = ssa_of sub in
        let full = Term.map blk_t sub ~f:(fun b ->
            if Tid.equal (Term.tid b) tids.(1) then
              Term.append def_t b (Def.create z (Bil.Var x))
            else b) in
        let prepared = Hike.Ssa.prepare_sub ~synth:Hike.Synth.empty
            ~target:(x86_target ()) full in
        (* The decode update drops the old synthetic entry and re-adds it;
           the changed exit block alone is the local update. *)
        let old_base = Hike.Ssa.unssa_sub old in
        let mixed =
          Term.filter_map blk_t old ~f:(fun b ->
              if Term.has_attr b Hike.Ssa.entry_tag then None
              else
                match Term.find blk_t prepared (Term.tid b) with
                | Some pb when
                    not (Blk.equal
                           (Term.find_exn blk_t old_base (Term.tid b)) pb) ->
                  Some pb
                | _ -> Some b)
        in
        let upd = Hike.Ssa.update_sub ~synth:Hike.Synth.empty
            ~target:(x86_target ()) ~old mixed in
        check "SSA-23 equals fresh" (Hike.Ssa.equivalent upd (ssa_of full));
        check "SSA-23 unrelated block kept"
          (kept old upd (Term.find_exn blk_t old tids.(0)));
        check "SSA-23 entry marked processed"
          (match Term.first blk_t upd with
           | Some b ->
             Term.has_attr b Hike.Ssa.entry_tag
             && Term.has_attr b Hike.Stack_model.ssa_tag
           | None -> false));
    pin "SSA-24" "relane narrowing drops dead input phis and reads"
      (fun () ->
        let kept = int_param 0 and dropped = int_param 1 and ret = int_ret 0 in
        let abi = Hike.Abi.of_target (x86_target ()) in
        let callee, _ = raw_sub_of "relane_callee" [ [], [ (0, mk_ret) ] ] in
        let callee =
          Base.List.fold
            (Arg.create ~intent:In kept (Bil.Var kept)
             :: Base.List.map abi.Hike.Abi.return_regs ~f:(fun r ->
                    Arg.create ~intent:Out r (Bil.Var r)))
            ~init:callee ~f:(fun s a -> Term.append arg_t s a) in
        let caller, tids = raw_sub_of "relane_caller"
            [ [], [ (1, mk_goto) ];
              [], [ (2, fun t -> mk_call_jmp t (Term.tid callee)) ];
              [ Def.create (v64 "relane_use") (Bil.Var ret) ], [ (0, mk_ret) ] ] in
        let old = ssa_of caller in
        let result = Hike.Ssa.relane_sub ~synth:Hike.Synth.empty
            ~target:(x86_target ())
            ~callee:(fun t ->
              if Tid.equal t (Term.tid callee) then Some callee else None)
            old in
        let has_phi b v =
          Term.enum phi_t b
          |> Seq.exists ~f:(fun p -> Var.same (Var.base (Phi.lhs p)) v) in
        let phi_lhs b v =
          Term.enum phi_t b
          |> Seq.find_map ~f:(fun p ->
                 Base.Option.some_if (Var.same (Var.base (Phi.lhs p)) v)
                   (Phi.lhs p)) in
        let call = Term.find_exn blk_t old tids.(1) in
        let call' = Term.find_exn blk_t result tids.(1) in
        check "SSA-24 fixture" (has_phi call kept && has_phi call dropped);
        check "SSA-24 kept input phi keeps its version"
          (match phi_lhs call kept, phi_lhs call' kept with
           | Some a, Some b -> Var.equal a b
           | _ -> false);
        check "SSA-24 kept input phi" (has_phi call' kept);
        check "SSA-24 dead input phi removed" (not (has_phi call' dropped));
        check "SSA-24 dead input lane removed"
          (Base.Option.is_none (Hike.Stack_model.boundary_read call' dropped)
           && Base.Option.is_none (Hike.Stack_model.local_output call' dropped)));
    pin "SSA-25"
      "a multi-predecessor loop header with a call wires phis from its preds"
      (fun () ->
        let ctr = callee_saved 0 and arg = int_param 0 and out = callee_saved 1 in
        let cond = v1 "ssa25_cond" in
        let callee, _ = raw_sub_of "ssa25_callee" [ [], [ (0, mk_ret) ] ] in
        let callee =
          Term.append arg_t callee
            (Arg.create ~intent:Out ret_reg (Bil.Var ret_reg))
        in
        let e0 = blk_of_defs [ Def.create ctr (int_exp 0) ] in
        let h0 =
          blk_of_defs
            [ Def.create arg
                (Bil.BinOp (Bil.PLUS, Bil.Var ctr, int_exp 1)) ]
        in
        let a0 =
          blk_of_defs
            [ Def.create out
                (Bil.BinOp (Bil.PLUS, Bil.Var ret_reg, Bil.Var ctr)) ]
        in
        let b0 = blk_of_defs [] in
        let exit0 = blk_of_defs [ Def.create out (Bil.Var ctr) ] in
        (* e -> h; h calls and returns to a; a loops through b or exits. *)
        let h =
          with_jmps h0
            [ Jmp.create
                (Call
                   (Call.create ~return:(Direct (Term.tid a0))
                      ~target:(Direct (Term.tid callee)) ())) ]
        in
        let a =
          with_jmps a0
            [ mk_jmp_to (Term.tid b0) (Bil.Var cond);
              mk_goto (Term.tid exit0) ]
        in
        let b = with_jmps b0 [ mk_goto (Term.tid h0) ] in
        let e = with_jmps e0 [ mk_goto (Term.tid h0) ] in
        let exit_b = with_jmps exit0 [ Hike_return.create () ] in
        let sub = sub_named "ssa25" [ e; h; a; b; exit_b ] in
        let phi_of blk v =
          Term.enum phi_t blk
          |> Seq.find ~f:(fun p -> Var.same (Var.base (Phi.lhs p)) v)
          |> Base.Option.value_exn
        in
        let incoming phi src =
          Base.List.Assoc.find (Phi.values phi |> Seq.to_list) src
            ~equal:Tid.equal
        in
        let ssa = ssa_of sub in
        let h' = blk_in ssa h and a' = blk_in ssa a in
        let b' = blk_in ssa b and e' = blk_in ssa e in
        let h_ctr = phi_of h' ctr in
        let entry_ctr =
          Term.first def_t e' |> Base.Option.value_exn |> Def.lhs
        in
        let back_ctr = Phi.lhs (phi_of b' ctr) in
        let h_arg = Term.first def_t h' |> Base.Option.value_exn |> Def.lhs in
        let call = Term.first jmp_t h' |> Base.Option.value_exn in
        let ret_v =
          Hike.Stack_model.boundary_write h' ret_reg
          |> Base.Option.value_exn
        in
        let ret_phi = phi_of a' ret_reg in
        let cont_ctr = phi_of a' ctr in
        check "SSA-25 header phis take both predecessor outputs"
          (Seq.length (Phi.values h_ctr) = 2
          && Option.equal Exp.equal (incoming h_ctr (Term.tid e'))
               (Some (Bil.Var entry_ctr))
          && Option.equal Exp.equal (incoming h_ctr (Term.tid b'))
               (Some (Bil.Var back_ctr)));
        check "SSA-25 local def is fresh and reads the header phi"
          (Var.index h_arg > 0
          && not (Var.equal h_arg (Phi.lhs h_ctr))
          && (match Def.rhs (Term.first def_t h' |> Base.Option.value_exn) with
              | Bil.BinOp (Bil.PLUS, Bil.Var v, Bil.Int _) ->
                  Var.equal v (Phi.lhs h_ctr)
              | _ -> false));
        check "SSA-25 call argument reads the def before the ret mint"
          (Core.Set.mem (Hike.Stack_model.reads (`Jmp call)) h_arg
          && Option.equal Var.equal
               (Hike.Stack_model.boundary_read h' arg) (Some h_arg)
          && not (Var.equal h_arg ret_v));
        check "SSA-25 call result reaches the continuation phi"
          (Option.equal Exp.equal (incoming ret_phi (Term.tid h'))
             (Some (Bil.Var ret_v))
          && Option.equal Exp.equal (incoming cont_ctr (Term.tid h'))
               (Some (Bil.Var (Phi.lhs h_ctr))));
        (* A new back-edge def renames the header and the continuation; the
           incremental body still equals fresh construction. *)
        let full =
          Term.map blk_t sub ~f:(fun blk ->
              if Tid.equal (Term.tid blk) (Term.tid b0) then
                Term.append def_t blk
                  (Def.create ctr
                     (Bil.BinOp (Bil.PLUS, Bil.Var ctr, int_exp 1)))
              else blk)
        in
        let old_ssa, upd, fresh, _woken = updated ~old_pre:sub ~full in
        let h_upd = blk_in upd h and b_upd = blk_in upd b in
        let a_upd = blk_in upd a in
        let b_def =
          Term.enum def_t b_upd |> Seq.to_list |> Base.List.last_exn
          |> Def.lhs
        in
        let h_ctr_upd = phi_of h_upd ctr in
        let ret_upd =
          Hike.Stack_model.boundary_write h_upd ret_reg
          |> Base.Option.value_exn
        in
        check "SSA-25 update equals fresh" (Hike.Ssa.equivalent upd fresh);
        check "SSA-25 update keeps the untouched entry" (kept old_ssa upd e);
        check "SSA-25 existing call result identity is stable"
          (Var.equal ret_v ret_upd);
        check "SSA-25 back edge reads the new local def"
          (Var.index b_def > 0
          && Option.equal Exp.equal (incoming h_ctr_upd (Term.tid b_upd))
               (Some (Bil.Var b_def)));
        check "SSA-25 updated call result reaches the continuation"
          (Option.equal Exp.equal
             (incoming (phi_of a_upd ret_reg) (Term.tid h_upd))
             (Some (Bil.Var ret_upd))));

    pin "SSA-26"
      "boundary lanes use their actual versions without an SSA stamp"
      (fun () ->
        let unused = v64 "stamp_unused" and arg = int_param 0 in
        let out = callee_saved 0 and target = Tid.create () in
        let sub, tids = raw_sub_of "stamp_local"
            [ [ Def.create unused (int_exp 7); Def.create arg (int_exp 10) ],
              [ (1, mk_goto) ];
              [ Def.create arg (Bil.BinOp (Bil.PLUS, Bil.Var arg, int_exp 1));
                Def.create ret_reg (int_exp 3) ],
              [ (2, fun t -> mk_call_jmp t target) ];
              [ Def.create out (Bil.Var ret_reg) ], [ (0, mk_ret) ] ] in
        let ssa = ssa_of sub in
        let call_blk = Term.find_exn blk_t ssa tids.(1) in
        check "SSA-26 unused dominating temporary omitted"
          (Base.Option.is_none (Hike.Stack_model.passed_version call_blk unused)
           && Base.Option.is_none (Hike.Stack_model.boundary_write call_blk unused));
        let read_arg =
          (Hike.Stack_model.effects (Term.first jmp_t call_blk
                                    |> Base.Option.value_exn)).reads
          |> Base.List.find_exn ~f:(fun v -> Var.same v arg) in
        let local_arg = Term.first def_t call_blk
          |> Base.Option.value_exn |> Def.lhs in
        check "SSA-26 same matches the base and preserves the actual version"
          (Var.index read_arg > 0 && Var.equal read_arg local_arg);
        Term.enum blk_t ssa |> Seq.iter ~f:(fun b ->
            check "SSA-26 block marked processed"
              (Term.has_attr b Hike.Stack_model.ssa_tag);
            Term.enum jmp_t b |> Seq.iter ~f:(fun j ->
                Base.List.iter (Hike.Stack_model.effects j).reads ~f:(fun v ->
                    check "SSA-26 boundary reads retain their version"
                      (Option.equal Var.equal
                         (Hike.Stack_model.boundary_read b v) (Some v)));
                Base.List.iter (Hike.Stack_model.effects j).writes ~f:(fun v ->
                    check "SSA-26 boundary writes retain their version"
                      (Option.equal Var.equal
                         (Hike.Stack_model.boundary_write b v) (Some v))))));

    pin "SSA-28"
      "an Edit session derives a new call's lanes and wires its result"
      (fun () ->
        let arg = int_param 0 and ret = int_ret 0 in
        let callee, _ = raw_sub_of "edit_callee" [ [], [ (0, mk_ret) ] ] in
        let callee =
          Term.append arg_t callee (Arg.create ~intent:Out ret (Bil.Var ret))
          |> fun s ->
          Term.append arg_t s (Arg.create ~intent:In arg (Bil.Var arg))
        in
        let caller, tids = raw_sub_of "edit_caller"
            [ [], [ (1, mk_goto) ];
              [ Def.create (v64 "edit_use") (Bil.Var ret) ], [ (0, mk_ret) ] ]
        in
        let ssa = ssa_of caller in
        let before = Term.find_exn blk_t ssa tids.(0) in
        let goto = Term.first jmp_t before |> Base.Option.value_exn in
        let call =
          Jmp.create ~cond:(Bil.Int (Word.one 1))
            (Call
               (Call.create ~return:(Direct tids.(1))
                  ~target:(Direct (Term.tid callee)) ()))
        in
        let callee_of t =
          Base.Option.some_if (Tid.equal t (Term.tid callee)) callee
        in
        let edit =
          Hike.Ssa.Edit.start ~synth:Hike.Synth.empty ~target:(x86_target ())
            ~callee:callee_of ssa
        in
        let edit = Hike.Ssa.Edit.remove_jmp edit (Term.tid goto) in
        let edit = Hike.Ssa.Edit.append_jmp edit tids.(0) call in
        let after = Hike.Ssa.Edit.finish edit in
        let call_blk = Term.find_exn blk_t after tids.(0) in
        let call' =
          Term.enum jmp_t call_blk
          |> Seq.find_map ~f:(fun j ->
                 Base.Option.some_if (Hike.Ssa.is_call_jmp j) j)
          |> Base.Option.value_exn
        in
        let writes =
          (Hike.Stack_model.effects call').Hike.Stack_model.Term_effects.writes
        in
        check "SSA-28 writes are versioned"
          (not (Base.List.is_empty writes)
           && Base.List.for_all writes ~f:(fun v -> Var.index v > 0));
        check "SSA-28 result lane is a write"
          (Base.List.exists writes ~f:(fun v -> Var.same v ret));
        let succ = Term.find_exn blk_t after tids.(1) in
        check "SSA-28 successor phi reads the mint"
          (Term.enum phi_t succ
          |> Seq.exists ~f:(fun p ->
                 Var.same (Var.base (Phi.lhs p)) ret
                 && Phi.values p
                    |> Seq.exists ~f:(fun (src, e) ->
                           Tid.equal src tids.(0)
                           && match e with
                              | Bil.Var v ->
                                  Base.List.exists writes ~f:(Var.equal v)
                              | _ -> false))));

    pin "SSA-29"
      "Edit.split_block gives a call its own block and rewires the successor phis"
      (fun () ->
        let ret = int_ret 0 and arg = int_param 0 in
        let callee, _ = raw_sub_of "edit_split_callee" [ [], [ (0, mk_ret) ] ] in
        let callee =
          Term.append arg_t callee (Arg.create ~intent:Out ret (Bil.Var ret))
          |> fun s ->
          Term.append arg_t s (Arg.create ~intent:In arg (Bil.Var arg))
        in
        let caller, tids = raw_sub_of "edit_split_caller"
            [ [], [ (1, mk_goto) ];
              [], [ (2, fun t -> mk_call_jmp t (Term.tid callee));
                    (2, mk_goto) ];
              [ Def.create (v64 "edit_split_use") (Bil.Var ret) ], [ (0, mk_ret) ] ]
        in
        let ssa = ssa_of caller in
        let blk = Term.find_exn blk_t ssa tids.(1) in
        let js = Term.enum jmp_t blk |> Seq.to_list in
        let call = Base.List.find_exn js ~f:Hike.Ssa.is_call_jmp in
        let goto = Base.List.find_exn js ~f:(fun j -> not (Hike.Ssa.is_call_jmp j)) in
        let edit =
          Hike.Ssa.Edit.start ~synth:Hike.Synth.empty ~target:(x86_target ())
            ~callee:(fun t ->
              Base.Option.some_if (Tid.equal t (Term.tid callee)) callee)
            ssa
        in
        let after =
          Hike.Ssa.Edit.finish
            (Hike.Ssa.Edit.split_block edit tids.(1)
               [ [ call ]; [ goto ] ])
        in
        let holder_of j =
          Term.enum blk_t after
          |> Seq.find_map ~f:(fun b ->
                 Base.Option.some_if
                   (Term.enum jmp_t b |> Seq.exists ~f:(fun x ->
                        Tid.equal (Term.tid x) (Term.tid j)))
                   (Term.tid b))
        in
        check "SSA-29 the call moved to its own block"
          (match holder_of call, holder_of goto with
           | Some a, Some g -> not (Tid.equal a g)
           | _ -> false);
        let call_holder =
          Base.Option.value_exn (holder_of call)
        in
        let call' =
          Term.find_exn blk_t after call_holder
          |> fun b ->
          Term.enum jmp_t b
          |> Seq.find_map ~f:(fun j ->
                 Base.Option.some_if
                   (Tid.equal (Term.tid j) (Term.tid call)) j)
          |> Base.Option.value_exn
        in
        let writes =
          (Hike.Stack_model.effects call').Hike.Stack_model.Term_effects.writes
        in
        let succ = Term.find_exn blk_t after tids.(2) in
        check "SSA-29 the successor keeps one incoming per holder"
          (Term.enum phi_t succ
          |> Seq.exists ~f:(fun p ->
                 Var.same (Var.base (Phi.lhs p)) ret
                 && Phi.values p
                    |> Seq.exists ~f:(fun (src, e) ->
                           Tid.equal src call_holder
                           && match e with
                              | Bil.Var v ->
                                  Base.List.exists writes ~f:(Var.equal v)
                              | _ -> false))));

    pin "SSA-30"
      "Edit.add_block and remove_block commit graph-only changes through SSA"
      (fun () ->
        let sub, tids =
          raw_sub_of "edit_graph" [ [], [ (0, mk_ret) ] ]
        in
        let old = ssa_of sub in
        let fresh = Tid.create () in
        let block =
          Blk.create ~tid:fresh
            ~jmps:[ Jmp.create (Goto (Direct tids.(0))) ] ()
        in
        let edit =
          Hike.Ssa.Edit.start ~synth:Hike.Synth.empty
            ~target:(x86_target ()) ~callee:(fun _ -> None) old
        in
        let added = Hike.Ssa.Edit.finish (Hike.Ssa.Edit.add_block edit block) in
        check "SSA-30 added block is committed"
          (Base.Option.is_some (Term.find blk_t added fresh));
        check "SSA-30 added block is named"
          (Term.find_exn blk_t added fresh
          |> fun b -> Term.has_attr b Hike.Stack_model.ssa_tag);
        let edit =
          Hike.Ssa.Edit.start ~synth:Hike.Synth.empty
            ~target:(x86_target ()) ~callee:(fun _ -> None) added
        in
        let removed =
          Hike.Ssa.Edit.finish (Hike.Ssa.Edit.remove_block edit fresh)
        in
        check "SSA-30 removed block is committed"
          (Base.Option.is_none (Term.find blk_t removed fresh));
        check "SSA-30 original block is kept"
          (Base.Option.is_some (Term.find blk_t removed tids.(0))))
  ]

let () = run "hike_ssa" tests
