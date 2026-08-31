(* edgecond_probe.ml — TEST: does BAP's Graphs.Ir.Edge.cond accumulate the
   preceding when-chain conditions natively?

   The user's question (2026-08-30): in BAP the gotos are like
     `when c1 goto l1; when c2 goto l2; goto l3`
   — MULTIPLE jmp terms in ONE block, first-true-wins. For a cond, every
   previous cond that was not true must refine the edge (the accumulated
   path condition). Test whether the Graphlib IR-graph API gives it for
   free, vs hand-rolling the negation-conjunction walk.

   Fixture: one chain block + three targets; dump for every Graphs.Ir edge:
   - the edge's OWN jmp term cond (Jmp.cond)
   - the edge's ACCUMULATED cond (Graphs.Ir.Edge.cond e g)
   Also cross-check Sub.to_cfg vs Sub.to_graph (the tid graph hike uses).
   No binary needed — pure KBIL fixture. *)

open Bap.Std

let w32 i = Word.of_int ~width:32 i

let () =
  (* vars: i (the compared counter), f1/f2 (two other regs) *)
  let ivar = Var.create ~is_virtual:false ~fresh:false "RAX" (Type.Imm 32) in
  let f1 = Var.create ~is_virtual:false ~fresh:false "RBX" (Type.Imm 32) in
  let f2 = Var.create ~is_virtual:false ~fresh:false "RCX" (Type.Imm 32) in
  (* conds: c1 = i != 1, c2 = i != 2 (the jne-style NEQ guards) *)
  let c1 = Bil.BinOp (Bil.NEQ, Bil.Var ivar, Bil.Int (w32 1)) in
  let c2 = Bil.BinOp (Bil.NEQ, Bil.Var ivar, Bil.Int (w32 2)) in
  (* the targets: non-empty blocks (a def each) so the graph keeps them *)
  let mk_target name v x =
    let b = Blk.Builder.create () in
    Blk.Builder.add_def b (Def.create v (Bil.Int (w32 x)));
    let r = Blk.Builder.result b in
    Printf.printf "target %s = %s\n" name (Tid.to_string (Term.tid r));
    r in
  let l1 = mk_target "l1" f1 100 in
  let l2 = mk_target "l2" f2 200 in
  let l3 = mk_target "l3" f1 300 in
  let l1_tid = Term.tid l1 in
  let l2_tid = Term.tid l2 in
  let l3_tid = Term.tid l3 in
  (* THE CHAIN BLOCK: when c1 goto l1; when c2 goto l2; goto l3 *)
  let chain = Blk.Builder.create () in
  Blk.Builder.add_jmp chain (Jmp.create ~cond:c1 (Goto (Direct l1_tid)));
  Blk.Builder.add_jmp chain (Jmp.create ~cond:c2 (Goto (Direct l2_tid)));
  Blk.Builder.add_jmp chain (Jmp.create (Goto (Direct l3_tid)));
  let chain_r = Blk.Builder.result chain in
  let sub_b = Sub.Builder.create ~name:"chain_probe" () in
  Sub.Builder.add_blk sub_b chain_r;
  Sub.Builder.add_blk sub_b l1;
  Sub.Builder.add_blk sub_b l2;
  Sub.Builder.add_blk sub_b l3;
  let sub = Sub.Builder.result sub_b in
  let str_exp (e : Exp.t) : string =
    Format.asprintf "%a" Exp.pp e in
  (* 1) the raw jmps of the chain block, in order *)
  Printf.printf "=== chain block jmps (Term.enum, in order) ===\n";
  Term.enum jmp_t chain_r
  |> Seq.iter ~f:(fun jmp ->
      Printf.printf "  jmp own-cond = %s\n"
        (str_exp (Jmp.cond jmp)));
  (* 2) Graphs.Ir — Sub.to_cfg — Edge.cond vs own cond *)
  let g = Sub.to_cfg sub in
  Printf.printf "=== Graphs.Ir edges: own jmp cond vs ACCUMULATED Edge.cond ===\n";
  Graphs.Ir.edges g
  |> Seq.iter ~f:(fun e ->
      let own = Jmp.cond (Graphs.Ir.Edge.jmp e) in
      let acc = Graphs.Ir.Edge.cond e g in
      Printf.printf "  edge\n    own = %s\n    acc = %s\n"
        (str_exp own)
        (str_exp acc));
  (* 3) the tid graph (what hike's fixpoint uses) — edges + labels *)
  let tg = Sub.to_graph sub in
  Printf.printf "=== Sub.to_graph (Graphs.Tid) edges ===\n";
  Graphs.Tid.edges tg
  |> Seq.iter ~f:(fun e ->
      let src = Tid.to_string (Graphs.Tid.Edge.src e) in
      let dst = Tid.to_string (Graphs.Tid.Edge.dst e) in
      let lbl = Tid.to_string (Graphs.Tid.Edge.label e) in
      Printf.printf "  %s -> %s (label %s)\n" src dst lbl);
  ()
