open Bap.Std
let w32 i = Word.of_int ~width:32 i
let () =
  let ivar = Var.create ~is_virtual:false ~fresh:false "RAX" (Type.Imm 32) in
  let f1 = Var.create ~is_virtual:false ~fresh:false "RBX" (Type.Imm 32) in
  let c1 = Bil.BinOp (Bil.NEQ, Bil.Var ivar, Bil.Int (w32 1)) in
  let c2 = Bil.BinOp (Bil.NEQ, Bil.Var ivar, Bil.Int (w32 2)) in
  let mk_target name v x =
    let b = Blk.Builder.create () in
    Blk.Builder.add_def b (Def.create v (Bil.Int (w32 x)));
    Blk.Builder.result b in
  let l1 = mk_target "l1" f1 100 in
  let l2 = mk_target "l2" f1 200 in
  let l3 = mk_target "l3" f1 300 in
  let l1_tid = Term.tid l1 in
  let l2_tid = Term.tid l2 in
  let l3_tid = Term.tid l3 in
  let chain = Blk.Builder.create () in
  Blk.Builder.add_jmp chain (Jmp.create ~cond:c1 (Goto (Direct l1_tid)));
  Blk.Builder.add_jmp chain (Jmp.create ~cond:c2 (Goto (Direct l2_tid)));
  Blk.Builder.add_jmp chain (Jmp.create (Goto (Direct l3_tid)));
  let chain_r = Blk.Builder.result chain in
  let sub_b = Sub.Builder.create ~name:"p" () in
  Sub.Builder.add_blk sub_b chain_r;
  Sub.Builder.add_blk sub_b l1;
  Sub.Builder.add_blk sub_b l2;
  Sub.Builder.add_blk sub_b l3;
  let sub = Sub.Builder.result sub_b in
  Printf.printf "=== nodes/edges: does Sub.to_cfg carry start/exit pseudo-nodes? ===\n";
  let g = Sub.to_cfg sub in
  Printf.printf "nodes: %d edges: %d\n"
    (Graphs.Ir.nodes g |> Seq.length)
    (Graphs.Ir.edges g |> Seq.length);
  Graphs.Ir.nodes g |> Seq.iter ~f:(fun n ->
      Printf.printf "node tid=%s defs=%d\n"
        (Tid.to_string (Term.tid (Graphs.Ir.Node.label n)))
        (Term.length def_t (Graphs.Ir.Node.label n)));
  Printf.printf "=== per-block out-edges via Node.outputs + Edge.cond ===\n";
  Graphs.Ir.nodes g |> Seq.iter ~f:(fun n ->
      let b = Graphs.Ir.Node.label n in
      Printf.printf "block %s:\n" (Tid.to_string (Term.tid b));
      Graphs.Ir.Node.outputs n g |> Seq.iter ~f:(fun e ->
          let dst = Graphs.Ir.Edge.dst e in
          Printf.printf "  -> %s  jmp_own_cond=%s  acc=%s\n"
            (Tid.to_string (Term.tid (Graphs.Ir.Node.label dst)))
            (Format.asprintf "%a" Exp.pp (Jmp.cond (Graphs.Ir.Edge.jmp e)))
            (Format.asprintf "%a" Exp.pp (Graphs.Ir.Edge.cond e g))))
