open Core_kernel
open Bap.Std
module Vsa = Cbat_vsa
module AI = Cbat_vsa.AI
module Ws = Cbat_clp_set_composite
module Relevance = Hike.Relevance
module W = Bap.Std.Word

let w32 i = W.of_int ~width:32 i
let w64 i = W.of_int ~width:64 i
let v64 (n : string) : var = Var.create ~is_virtual:false ~fresh:false n (Type.Imm 64)
let v1 (n : string) : var = Var.create ~is_virtual:false ~fresh:false n (Type.Imm 1)
let memv (n : string) : var = Var.create ~is_virtual:false ~fresh:false n (Type.Mem (`r64, `r8))
let sp = v64 "RSP"
let anchored_entry () : AI.t =
  let e = AI.add_word AI.top ~key:sp ~data:(Ws.singleton (w64 0)) in
  AI.add_word e ~key:(v64 "RBP") ~data:(Ws.singleton (w64 0))
let tag_all (sub : sub term) : sub term =
  Term.map blk_t sub ~f:(fun b ->
      Term.map def_t b ~f:(fun d -> Term.set_attr d Cbat_vsa_utils.relevant ()))

let pp_ws (ws : Ws.t) : string =
  match Ws.min_elem ws, Ws.max_elem ws with
  | Some lo, Some hi -> Format.asprintf "[%s..%s] cardn=%s top=%b" (W.to_string lo) (W.to_string hi) (W.to_string (Ws.cardinality ws)) (Ws.is_top ws)
  | _ -> Format.asprintf "cardn=%s top=%b inf=%b" (W.to_string (Ws.cardinality ws)) (Ws.is_top ws) (Ws.is_infinite ws)

let () =
  let i = Var.create ~is_virtual:false ~fresh:false "r6_i" (Type.Imm 32) in
  let t = Var.create ~is_virtual:false ~fresh:false "r6_t" (Type.Imm 1) in
  let m = memv "r6_m" in
  let iv = Bil.Var i in
  let neq_exp = Bil.BinOp (Bil.NEQ, iv, Bil.Int (w32 9)) in
  let idx_addr =
    Bil.BinOp (Bil.PLUS, Bil.Var sp, Bil.BinOp (Bil.MINUS, Bil.Cast (Bil.UNSIGNED, 64, iv), Bil.Int (w64 32)))
  in
  let def_idx_store = Def.create m (Bil.Store (Bil.Var m, idx_addr, Bil.Int (w64 7), LittleEndian, `r64)) in
  let def_inc = Def.create i (Bil.BinOp (Bil.PLUS, iv, Bil.Int (w32 1))) in
  let def_flag = Def.create t neq_exp in
  let entry_b = Blk.Builder.create () in
  let loop_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b (Def.create i (Bil.Int (w32 0)));
  Blk.Builder.add_def loop_b def_idx_store;
  Blk.Builder.add_def loop_b def_inc;
  Blk.Builder.add_def loop_b def_flag;
  let entry0 = Blk.Builder.result entry_b in
  let loop0 = Blk.Builder.result loop_b in
  let exit0 = Blk.Builder.result exit_b in
  let loop_tid = Term.tid loop0 in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct loop_tid)));
  let loop_b = Blk.Builder.init ~copy_defs:true loop0 in
  Blk.Builder.add_jmp loop_b (Jmp.create ~cond:(Bil.Var t) (Goto (Direct loop_tid)));
  Blk.Builder.add_jmp loop_b (Jmp.create (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let loop = Blk.Builder.result loop_b in
  let exit = Blk.Builder.result exit_b in
  let sub_b = Sub.Builder.create ~name:"r6_jne_counter" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b loop;
  Sub.Builder.add_blk sub_b exit;
  let sub0 = Sub.Builder.result sub_b in
  let tagged_rel = Relevance.analyze sp sub0 in
  let tagged =
    Term.map blk_t tagged_rel ~f:(fun b ->
        Term.map def_t b ~f:(fun d ->
            if Tid.equal (Term.tid d) (Term.tid def_flag) then
              Term.set_attr d Cbat_vsa_utils.relevant ()
            else d))
  in
  let prog' = Program.create ~subs:[ tagged ] () in
  let sol = Vsa.static_graph_vsa [] prog' tagged (Vsa.init_sol ~entry:(anchored_entry ()) tagged) in
  Printf.printf "head(loop) i = %s\n" (pp_ws (AI.find_word 32 (Graphlib.Std.Solution.get sol loop_tid) i));
  Printf.printf "head(loop) t = %s\n" (pp_ws (AI.find_word 1 (Graphlib.Std.Solution.get sol loop_tid) t));
  (* The fused world has no per-edge views: the head's IN-state is the JOIN of
     the entry + refined back edges; the single-predecessor EXIT block's
     IN-state IS the fallthrough edge's refined state (the accumulated cond
     carries i = 9). *)
  Printf.printf "exit(per-edge fallthrough) i = %s\n"
    (pp_ws (AI.find_word 32 (Graphlib.Std.Solution.get sol exit_tid) i));
  (* What does edge_constraints produce for the bare-flag cond? *)
  let blk_state = Vsa.denote_defs loop (Graphlib.Std.Solution.get sol loop_tid) in
  let ctx : Vsa.analysis_ctx =
    { refineable = None; defs = Some (Vsa.defs_of_sub tagged); stores = Some (Vsa.stores_of_sub tagged);
      flag_state = None; sub = Some tagged; blk = Some loop } in
  let seeds = Vsa.edge_constraints ~env:blk_state ~ctx (Bil.Var t) (Ws.singleton Word.b1) in
  Printf.printf "seeds for bare-flag cond = %d\n" (List.length seeds);
  ignore ctx
