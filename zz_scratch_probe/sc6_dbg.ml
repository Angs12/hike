(* SC6 introspection: the cells the seam derives for the two-check
   fixture, and whether the envs stamp at all. *)
open Bap.Std
open Test_common
open Test_strip_canaries

let () =
  ignore Probe_common.init ();
  let stub = fst (sub_of "__stack_chk_fail" [ [], [] ]) in
  let fail_jmp () =
    Jmp.create (Call (Call.create ~target:(Label.direct (Term.tid stub)) ()))
  in
  let fixture, tids =
    sub_of "sc6"
      [ [ def rbp (Bil.Var rsp);
          def rax tls_load;
          def m (cell_store 8 (Bil.Var rax)) ],
        [ (1, mk_goto) ];
        [ def rdx (cell_load 8);
          def rdx (Bil.BinOp (Bil.MINUS, Bil.Var rdx, tls_load));
          def zf (Bil.BinOp (Bil.EQ, zero64, Bil.Var rdx)) ],
        [ (3, fun t -> mk_jmp_to t (Bil.Var zf));
          (4, fun t -> mk_jmp_to t one) ];
        [ def rcx (cell_load 8);
          def rcx (Bil.BinOp (Bil.MINUS, Bil.Var rcx, tls_load));
          def zf (Bil.BinOp (Bil.EQ, zero64, Bil.Var rcx)) ],
        [ (3, fun t -> mk_jmp_to t (Bil.Var zf));
          (4, fun t -> mk_jmp_to t one) ];
        [], [ (0, mk_ret) ];
        [], [] ]
  in
  let ok = install_fixture_envs [ fixture ] in
  Printf.printf "install_fixture_envs: %b\n%!" ok;
  Term.enum blk_t fixture
  |> Seq.iter ~f:(fun blk ->
      Term.enum def_t blk
      |> Seq.iter ~f:(fun d ->
          let cell =
            Hike.Strip_canaries.cell_of blk d
          in
          Printf.printf "blk %s def %s -> %s\n%!"
            (Tid.name (Term.tid blk))
            (match Def.rhs d with
             | Bil.Store _ -> "store"
             | Bil.Load _ -> "load"
             | _ -> "other")
            (match cell with
             | Some c -> Printf.sprintf "cell %Ld" c
             | None -> "none")))
