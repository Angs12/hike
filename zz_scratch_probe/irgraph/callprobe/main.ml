open Bap.Std
let w32 i = Word.of_int ~width:32 i
let () =
  (* A Goto then a SECOND Goto (chain tail) — confirm conds; then check
     a bare direct Goto with cond Int 1 but a preceding FALSE-goto (an
     infeasible chain edge) — Edge.cond on an edge after a FALSE cond *)
  let ivar = Var.create ~is_virtual:false ~fresh:false "RAX" (Type.Imm 32) in
  let f1 = Var.create ~is_virtual:false ~fresh:false "RBX" (Type.Imm 32) in
  let mk_target v x =
    let b = Blk.Builder.create () in
    Blk.Builder.add_def b (Def.create v (Bil.Int (w32 x)));
    Blk.Builder.result b in
  let l1 = mk_target f1 100 in
  let l2 = mk_target f1 200 in
  let l3 = mk_target f1 300 in
  let l1_tid = Term.tid l1 in
  let l2_tid = Term.tid l2 in
  let l3_tid = Term.tid l3 in
  (* a chain with a FALSE literal cond in the middle *)
  let chain = Blk.Builder.create () in
  Blk.Builder.add_jmp chain (Jmp.create ~cond:(Bil.Int Word.b0) (Goto (Direct l1_tid)));
  Blk.Builder.add_jmp chain (Jmp.create ~cond:(Bil.BinOp (Bil.EQ, Bil.Var ivar, Bil.Int (w32 7))) (Goto (Direct l2_tid)));
  Blk.Builder.add_jmp chain (Jmp.create (Goto (Direct l3_tid)));
  let chain_r = Blk.Builder.result chain in
  let sub_b = Sub.Builder.create ~name:"p" () in
  Sub.Builder.add_blk sub_b chain_r;
  Sub.Builder.add_blk sub_b l1;
  Sub.Builder.add_blk sub_b l2;
  Sub.Builder.add_blk sub_b l3;
  let sub = Sub.Builder.result sub_b in
  Printf.printf "=== conds after a FALSE literal goto ===\n";
  let g = Sub.to_cfg sub in
  Graphs.Ir.edges g |> Seq.iter ~f:(fun e ->
      Printf.printf "  dst=%s own=%s acc=%s\n"
        (Tid.to_string (Term.tid (Graphs.Ir.Node.label (Graphs.Ir.Edge.dst e))))
        (Format.asprintf "%a" Exp.pp (Jmp.cond (Graphs.Ir.Edge.jmp e)))
        (Format.asprintf "%a" Exp.pp (Graphs.Ir.Edge.cond e g)));
  ()
