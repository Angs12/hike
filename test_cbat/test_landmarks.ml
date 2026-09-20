(* The LM F1-family pins: landmark-directed widening end-to-end over the
   jle/jne counter loops — the head lands at the landmark K (F1, F1-NEQ),
   the walk-equals-vertex memo pin (F1-FT), the walk's soundness
   contract (F1-B1/B2/B3), and the walk's cell meet (F1-B4). *)
open Bap.Std
open Bap_core_theory
open Test_common
open Test_fixtures

let run () =
(  (* F1: JLE-counter head lands at TOP (inclusive taken row overshoots); pins sound invariants. *)
  let sub, l1_tid, b1_tid, _ = lm_jle_loop ~k1:(w32 100) () in
  let sol = run_anchored sub in
  let i = Var.create ~is_virtual:false ~fresh:false "lm_i" (Type.Imm 32) in
  let head_i = AI.find_word 32 (Graphlib.Std.Solution.get sol l1_tid) i in
  check_bound
    "property LM F1: the head's lower bound is the entry constant 0"
    (Ws.min_elem head_i) (fun lo -> Cbat_word.equal lo (w32 0));
  (* Taken view's state is the body's IN-state. *)
  let taken_i = AI.find_word 32 (Graphlib.Std.Solution.get sol b1_tid) i in
  check_bound
    "property LM F1: the taken view's lower bound is the entry constant 0"
    (Ws.min_elem taken_i) (fun lo -> Cbat_word.equal lo (w32 0));
  ()

(* F1-NEQ: NEQ-counter head lands at [0, K] (max == K) — Finite fires end-to-end. *))
;
(  let k = w32 100 in
  let sub, l1_tid, _ = lm_jne_loop ~k () in
  let sol = run_anchored sub in
  let i = Var.create ~is_virtual:false ~fresh:false "lm_ne_i" (Type.Imm 32) in
  let head_i = AI.find_word 32 (Graphlib.Std.Solution.get sol l1_tid) i in
  check_bound
    "property LM F1-NEQ: the head's lower bound is the entry constant 0"
    (Ws.min_elem head_i) (fun lo -> Cbat_word.equal lo (w32 0));
  check_bound
    "property LM F1-NEQ: the head's upper bound is the landmark K (Finite extrapolation fired end-to-end)"
    (Ws.max_elem head_i) (fun hi -> Cbat_word.equal hi k);
  ()

(* F1-FT: fallthrough edge fixture — the walk-equals-vertex pin for the shared memo.
   Same jne-counter loop as F1-NEQ (arrow-less [i - k] record operand through guarded
   refinement — the landmark-consumption lane): the head pins the vertex-computed
   values, the taken body pins its refined view, and the fallthrough exit pins the
   walk-observed refined pre-state. A memo keying bug moves one side, not both. *))
;
(  let k, sub, sol, l1_tid, b1_tid = lm_jne_run () in
   let i = Var.create ~is_virtual:false ~fresh:false "lm_ne_i" (Type.Imm 32) in
   let st tid = Graphlib.Std.Solution.get sol tid in
   let head_i = AI.find_word 32 (st l1_tid) i in
   check_bound
     "property LM F1-FT: the head's lower bound is the entry constant 0 (vertex side of the pin)"
     (Ws.min_elem head_i) (fun lo -> Cbat_word.equal lo (w32 0));
   check_bound
     "property LM F1-FT: the head's upper bound is the landmark K (vertex side of the pin)"
     (Ws.max_elem head_i) (fun hi -> Cbat_word.equal hi k);
  let body_i = AI.find_word 32 (st b1_tid) i in
  check_bound
    "property LM F1-FT: the taken body's lower bound is the entry constant 0"
    (Ws.min_elem body_i) (fun lo -> Cbat_word.equal lo (w32 0));
   check_bound
     "property LM F1-FT: the taken body's upper bound is K-1 (the guard excluded the landmark)"
     (Ws.max_elem body_i) (fun hi -> Cbat_word.equal hi (Cbat_word.pred k));
   let exits = exit_blocks_of sub in
   let exit_i =
     match exits with [ b ] -> AI.find_word 32 (st (Term.tid b)) i | _ -> assert false
   in
   check "property LM F1-FT: the fallthrough exit pins the counter to {K} exactly (walk side of the pin)"
     (Ws.equal exit_i (Ws.singleton k));
   ()

(* F1-B1 (walk soundness): the walks are the refinement carrier on this
   landmark loop, so the walk's soundness contract is pinned by the same
   invariants the refinement must satisfy: the head lands at [0, K]
   (never above K, never bottom) and the taken body lands at [0, K-1].
   If a walk NARROWED a state (the unsound direction) or manufactured
   bottom on a live block, these exact-value pins move. *))
;
(  let k, sub, sol, l1_tid, b1_tid = lm_jne_run () in
   let i = Var.create ~is_virtual:false ~fresh:false "lm_ne_i" (Type.Imm 32) in
   let head_i = AI.find_word 32 (Graphlib.Std.Solution.get sol l1_tid) i in
   let body_i = AI.find_word 32 (Graphlib.Std.Solution.get sol b1_tid) i in
   check_bound
     "property LM F1-B1: the head's lower bound is the entry constant 0"
     (Ws.min_elem head_i) (fun lo -> Cbat_word.equal lo (w32 0));
   check_bound
     "property LM F1-B1: the head's upper bound is the landmark K (never narrowed, never blown past)"
     (Ws.max_elem head_i) (fun hi -> Cbat_word.equal hi k);
   check_bound
     "property LM F1-B1: the taken body's upper bound is K-1 (the guard's exclusion survives)"
     (Ws.max_elem body_i) (fun hi -> Cbat_word.equal hi (Cbat_word.pred k));
   check
     "property LM F1-B1: the walk never manufactures bottom on a live block (the head's state is inhabited)"
     (not (Ws.is_bottom head_i));
   ()

(* F1-B2: two sequential SCCs refine independently — loop 1's walk spend
   cannot starve loop 2. *))
;
(  let sub, l1_tid, _, l2_tid = lm_jle_loop ~k1:(w32 40) ~k2:(w32 100) () in
   let sol = run_anchored sub in

   let i = Var.create ~is_virtual:false ~fresh:false "lm_i" (Type.Imm 32) in
   let l2_tid = match l2_tid with Some t -> t | None -> failwith "F1-B2: missing L2" in
  let i2 = AI.find_word 32 (Graphlib.Std.Solution.get sol l2_tid) i in
   check_bound
     "property LM F1-B2: loop 2's head lower bound is loop 1's exact exit value K1+1 (the compiled \
     fallthrough comparison refines the exit edge; both loops refine independently)"
     (Ws.min_elem i2) (fun lo -> Cbat_word.equal lo (Cbat_word.succ (w32 40)));
   let i1 = AI.find_word 32 (Graphlib.Std.Solution.get sol l1_tid) i in
   check_bound
     "property LM F1-B2: loop 1's head lower bound is the entry constant 0 (both loops refined independently)"
     (Ws.min_elem i1) (fun lo -> Cbat_word.equal lo (w32 0));
   ()

(* F1-B3: re-runs the F1-FT shape and pins the walk-delivered value
   (the fallthrough exit holds {K} exactly). *))
;
(  let k, sub, sol, _, b1_tid = lm_jne_run () in
   let i = Var.create ~is_virtual:false ~fresh:false "lm_ne_i" (Type.Imm 32) in
   let st tid = Graphlib.Std.Solution.get sol tid in
   let exits = exit_blocks_of sub in
   let exit_i =
     match exits with [ b ] -> AI.find_word 32 (st (Term.tid b)) i | _ -> assert false
   in
   check
     "property LM F1-B3: the fallthrough exit pins the counter to {K} exactly (the memoized walk delivery)"
     (Ws.equal exit_i (Ws.singleton k));
  check_bound
    "property LM F1-B3: the taken body's refined view survives (upper bound K-1)"
    (Ws.max_elem (AI.find_word 32 (st b1_tid) i))
    (fun hi -> Cbat_word.equal hi (Cbat_word.pred k));
   ()

(* F1-B4 (the walk's cell meet): the walk's product is the cell meet
   through a Load-producing def ([def_constraints] ->
   [constrain_cell_on_trace] fires INSIDE the walk), so the fixture seeds a
   Var constraint on a var whose guard-block def is a Load over a known cell
   with a WIDE stored range. The walk meets the cell down to the
   seed (the fixture's precondition for the landmark properties). *))
;
(  let k = w32 100 in
   let sub0, l1_tid, _b1_tid = lm_jne_loop ~k () in
   let i = Var.create ~is_virtual:false ~fresh:false "lm_ne_i" (Type.Imm 32) in
   let mem = Var.create ~is_virtual:true ~fresh:false "f1b4_m" (Type.Mem (`r64, `r8)) in
   (* Prepend to the guard block: t := Load[mem, RBP-8]; i := t.  The seed on
      i walks backward through i's def to t's Load and meets the cell. *)
   let guard_blk =
     Term.enum blk_t sub0 |> Seq.to_list |> List.find (fun b -> Term.tid b = l1_tid) in
   let t = Var.create ~is_virtual:true ~fresh:false "f1b4_t" (Type.Imm 32) in
   let rbp = v64 "RBP" in
   (* The seed defs ride phase 1 ahead of the guard's own body (BIR
      orders defs before jmps), so the rebuilt block is identical. *)
   let gb =
     with_jmps
       (blk_of_defs
          ([ Def.create t
               (Bil.Load (Bil.Var mem, Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))),
                          LittleEndian, `r32));
             Def.create i (Bil.Var t) ]
           @ (Term.enum def_t guard_blk |> Seq.to_list)))
       (Term.enum jmp_t guard_blk |> Seq.to_list)
   in
   let sub_b = Sub.Builder.create ~name:"f1b4_sub" () in
   Term.enum blk_t sub0 |> Seq.iter ~f:(fun b ->
       if Term.tid b = l1_tid then Sub.Builder.add_blk sub_b gb
       else Sub.Builder.add_blk sub_b b);
   let sub = Sub.Builder.result sub_b in
   let cfg =
     Sub.to_graph sub
     |> Graphs.Tid.Node.remove Graphs.Tid.start
     |> Graphs.Tid.Node.remove Graphs.Tid.exit in
   (* The entry — and therefore the solution snapshot the walk re-denotes
      against — must carry the memory binding (a missing mem var reads the
      map lattice's bottom and trips the width assert). *)
   let wide = Ws.of_clp (Clp.interval ~width:32 (w32 0) (w32 200)) in
   (* RBP is anchored at 0, so RBP-8 wraps to the unsigned -8 key. *)
   let key = match Mem.Key.of_wordset (Ws.singleton (w64 (-8))) with
     | Some k -> k | None -> failwith "F1-B4: bad key" in
   let wide_mem =
     Mem.add (Mem.top { Mem.addr_width = 64; Mem.addressable_width = 8 })
       ~key ~data:(Mem.Val.create wide LittleEndian) in
   let entry = AI.add_memory (anchored_entry ()) ~key:mem ~data:wide_mem in
   let sol =
     Vsa.static_graph_vsa ~abi:Hike_abi.x86_64_sysv (Program.create ~subs:[ sub ] ())
       sub (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv ~entry sub) in
   let rctx = Vsa.Test_seam.mk_rctx ~cfg ~abi:Hike_abi.x86_64_sysv sub in
   let walk () =
     let entry = AI.add_word entry ~key:i ~data:(Ws.singleton k) in
     Vsa.Test_seam.refine_edge ~sol ~rctx
       ~seeds:[ (i, Ws.singleton k) ]
       entry gb in
   let cell_of env =
     Result.fold
       (Vsa.Test_seam.denote_imm_exp
          (Bil.Load (Bil.Var mem, Bil.BinOp (Bil.MINUS, Bil.Var (v64 "RBP"),
                                             Bil.Int (Cbat_word.to_word (w64 8))), LittleEndian, `r32))
          env)
       ~ok:Fun.id ~error:(fun _ -> Ws.top 32) in
   let full_cell = cell_of (walk ()) in
   check
     "property LM F1-B4: the walk meets the cell (the fixture's precondition: the walk moves the cell off its wide range)"
     (Ws.precedes full_cell wide);
  ())
