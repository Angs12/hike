open Bap.Std
let w32 i = Word.of_int ~width:32 i
let () =
  (* block with: when c goto l1; call foo; goto l3 *)
  let ivar = Var.create ~is_virtual:false ~fresh:false "RAX" (Type.Imm 32) in
  let f1 = Var.create ~is_virtual:false ~fresh:false "RBX" (Type.Imm 32) in
  let c1 = Bil.BinOp (Bil.NEQ, Bil.Var ivar, Bil.Int (w32 1)) in
  let mk_target name v x =
    let b = Blk.Builder.create () in
    Blk.Builder.add_def b (Def.create v (Bil.Int (w32 x)));
    Blk.Builder.result b in
  let l1 = mk_target "l1" f1 100 in
  let l3 = mk_target "l3" f1 300 in
  (* a callee stub sub with a known tid *)
  let callee_b = Blk.Builder.create () in
  Blk.Builder.add_def callee_b (Def.create f1 (Bil.Int (w32 9)));
  let callee_blk = Blk.Builder.result callee_b in
  let callee_sub_b = Sub.Builder.create ~name:"callee" () in
  Sub.Builder.add_blk callee_sub_b callee_blk;
  let callee = Sub.Builder.result callee_sub_b in
  let l1_tid = Term.tid l1 in
  let l3_tid = Term.tid l3 in
  let chain = Blk.Builder.create () in
  Blk.Builder.add_jmp chain (Jmp.create ~cond:c1 (Goto (Direct l1_tid)));
  Blk.Builder.add_jmp chain (Jmp.create (Call (Call.create ~return:(Some (Direct l3_tid)) (Direct (Term.tid callee)))));
  let chain_r = Blk.Builder.result chain in
  let sub_b = Sub.Builder.create ~name:"p" () in
  Sub.Builder.add_blk sub_b chain_r;
  Sub.Builder.add_blk sub_b l1;
  Sub.Builder.add_blk sub_b l3;
  let sub = Sub.Builder.result sub_b in
  Printf.printf "=== call-block out-edges ===\n";
  let g = Sub.to_cfg sub in
  Graphs.Ir.nodes g |> Seq.iter ~f:(fun n ->
      let b = Graphs.Ir.Node.label n in
      Printf.printf "block %s:\n" (Tid.to_string (Term.tid b));
      Graphs.Ir.Node.outputs n g |> Seq.iter ~f:(fun e ->
          let dst = Graphs.Ir.Edge.dst e in
          Printf.printf "  -> %s  kind=%s  acc=%s\n"
            (Tid.to_string (Term.tid (Graphs.Ir.Node.label dst)))
            (match Jmp.kind (Graphs.Ir.Edge.jmp e) with
             | Goto _ -> "Goto" | Call _ -> "Call" | Ret _ -> "Ret" | Int _ -> "Int")
            (Format.asprintf "%a" Exp.pp (Graphs.Ir.Edge.cond e g))))
