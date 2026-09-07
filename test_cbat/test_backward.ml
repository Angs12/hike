(* Backward-refinement rows: L3a, L3c tiers, jcc decoder, RSP restore, RBP blocker. *)
open Bap.Std
open Bap_core_theory
open Test_common

(* L3a: backward guard refinement. Walk fires on comparison guards; body input carries the cell. *)

(* Loop fixture: comparison guard in header, defs in header (fused walk fires first visit).
   Returns (sub, body tid). *)
let mk_l3a_loop ~(cmp : Bil.binop) ~(c : word) ~(rhs : exp) : sub term * tid =
  let m = memv "l3a_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let t = Var.create ~is_virtual:false ~fresh:false "l3a_t" (Type.Imm 32) in
  let v = Var.create ~is_virtual:false ~fresh:false "l3a_v" (Type.Imm 32) in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  let cond = Bil.BinOp (cmp, Bil.Var v, Bil.Int c) in
  let ncond = Bil.UnOp (Bil.NOT, cond) in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  (* Prologue def: RBP copies RSP. *)
  Blk.Builder.add_def entry_b (Def.create rbp (Bil.Var rsp));
  Blk.Builder.add_def header_b (Def.create t (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  Blk.Builder.add_def header_b (Def.create v rhs);
  let entry0 = Blk.Builder.result entry_b in
  let body0 = Blk.Builder.result body_b in
  let header0 = Blk.Builder.result header_b in
  let exit0 = Blk.Builder.result exit_b in
  let body_tid = Term.tid body0 in
  let header_tid = Term.tid header0 in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct header_tid)));
  let body_b = Blk.Builder.init ~copy_defs:true body0 in
  Blk.Builder.add_jmp body_b (Jmp.create (Goto (Direct header_tid)));
  let header_b = Blk.Builder.init ~copy_defs:true header0 in
  Blk.Builder.add_jmp header_b (Jmp.create ~cond (Goto (Direct body_tid)));
  Blk.Builder.add_jmp header_b (Jmp.create ~cond:ncond (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let body = Blk.Builder.result body_b in
  let header = Blk.Builder.result header_b in
  let exit = Blk.Builder.result exit_b in
  let sub_b = Sub.Builder.create ~name:"l3a_loop" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  (sub, body_tid)

(* Cell at RBP-8 in [st], read back as the load denotation reads it. *)
let l3a_cell_of (st : AI.t) : Ws.t =
  let m = memv "l3a_m" in
  let rbp = v64 "RBP" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  match Vsa.denote_imm_exp (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)) st with
  | Ok ws -> ws
  | Error _ -> Ws.top 32

(* Finite non-top non-bottom set bounded above by [maxv]. *)
let l3a_bounded (ws : Ws.t) (maxv : word) : bool =
  (not (Ws.is_top ws))
  && (not (Ws.is_bottom ws))
  && match Ws.max_elem ws with Some w -> Word.( <= ) w maxv | None -> false

(* Tagged-sub fixpoint; walk's cell meet observable at BODY input. *)
(* Iterate state of an edge is the single-predecessor target's IN-state. *)
let iter_state_of (_sub : sub term) (sol : Vsa.vsa_sol) (target_tid : tid) : AI.t =
  Graphlib.Std.Solution.get sol target_tid

let iter_cell_of (sub : sub term) (sol : Vsa.vsa_sol) (target_tid : tid) (cell_of : AI.t -> Ws.t) :
    Ws.t =
  cell_of (iter_state_of sub sol target_tid)

let l3a_run_analyzed (sub : sub term) (body_tid : tid) : Ws.t =
  (* Gate-free (spec §2.1): the raw sub runs; every def is denoted. *)
  let prog' = Program.create ~subs:[ sub ] () in
  let sol = Vsa.static_graph_vsa [] prog' sub (Vsa.init_sol ~entry:(anchored_entry ()) sub) in
  iter_cell_of sub sol body_tid l3a_cell_of

(* L3c-1: flag-state mechanism — bare-flag guards recover the comparison constraint. *)

(* Flag-indirected loop fixture. Returns (sub, body tid, back-edge jump). *)
let mk_l3c1_loop ~(extra_header_defs : def term list) : sub term * tid * jmp term =
  let m = memv "l3c1_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let t = Var.create ~is_virtual:false ~fresh:false "l3c1_t" (Type.Imm 32) in
  let cf = v1 "l3c1_cf" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  (* Prologue def: RBP copies RSP. *)
  Blk.Builder.add_def entry_b (Def.create rbp (Bil.Var rsp));
  Blk.Builder.add_def header_b (Def.create t (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  Blk.Builder.add_def header_b (Def.create cf (Bil.BinOp (Bil.LT, Bil.Var t, Bil.Int (w32 10))));
  List.iter (Blk.Builder.add_def header_b) extra_header_defs;
  let entry0 = Blk.Builder.result entry_b in
  let body0 = Blk.Builder.result body_b in
  let header0 = Blk.Builder.result header_b in
  let exit0 = Blk.Builder.result exit_b in
  let body_tid = Term.tid body0 in
  let header_tid = Term.tid header0 in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct header_tid)));
  let body_b = Blk.Builder.init ~copy_defs:true body0 in
  Blk.Builder.add_jmp body_b (Jmp.create (Goto (Direct header_tid)));
  let header_b = Blk.Builder.init ~copy_defs:true header0 in
  Blk.Builder.add_jmp header_b (Jmp.create ~cond:(Bil.Var cf) (Goto (Direct body_tid)));
  Blk.Builder.add_jmp header_b
    (Jmp.create ~cond:(Bil.UnOp (Bil.NOT, Bil.Var cf)) (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let body = Blk.Builder.result body_b in
  let header = Blk.Builder.result header_b in
  let exit = Blk.Builder.result exit_b in
  let sub_b = Sub.Builder.create ~name:"l3c1_loop" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  let jmp =
    match Term.enum jmp_t header |> Seq.to_list with [ j1; _ ] -> j1 | _ -> assert false
  in
  (sub, body_tid, jmp)

(* Cell at RBP-8 in [st] (mem-var parameterized). *)
let l3c1_cell_of (m : var) (st : AI.t) : Ws.t =
  let rbp = v64 "RBP" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  match Vsa.denote_imm_exp (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)) st with
  | Ok ws -> ws
  | Error _ -> Ws.top 32

(* Finite non-top non-bottom, max <= maxv. *)
let l3c1_bounded (ws : Ws.t) (maxv : word) : bool =
  (not (Ws.is_top ws))
  && (not (Ws.is_bottom ws))
  && match Ws.max_elem ws with Some w -> Word.( <= ) w maxv | None -> false

(* L3c-2: signed comparison rows (SLT/SLE). *)

(* Seeded counter loop; [flag] selects the flag-indirected guard, [prologue] drops it. Returns (sub, body tid). *)
let mk_l3c2_loop ~(prologue : bool) ~(seed : word option) ~(cmp : Bil.binop) ~(c : word)
    ~(body_op : Bil.binop) ~(body_k : word) ~(flag : bool) : sub term * tid =
  let m = memv "l3c2_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let t = Var.create ~is_virtual:false ~fresh:false "l3c2_t" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "l3c2_u" (Type.Imm 32) in
  let cf = v1 "l3c2_cf" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  let cond = Bil.BinOp (cmp, Bil.Var t, Bil.Int c) in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  (match seed with
  | Some v ->
      Blk.Builder.add_def entry_b
        (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int v, LittleEndian, `r32)))
  | None -> ());
  if prologue then Blk.Builder.add_def entry_b (Def.create rbp (Bil.Var rsp));
  Blk.Builder.add_def header_b (Def.create t (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  if flag then Blk.Builder.add_def header_b (Def.create cf (Bil.BinOp (cmp, Bil.Var t, Bil.Int c)));
  Blk.Builder.add_def body_b (Def.create u (Bil.BinOp (body_op, Bil.Var t, Bil.Int body_k)));
  Blk.Builder.add_def body_b
    (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Var u, LittleEndian, `r32)));
  let entry0 = Blk.Builder.result entry_b in
  let body0 = Blk.Builder.result body_b in
  let header0 = Blk.Builder.result header_b in
  let exit0 = Blk.Builder.result exit_b in
  let body_tid = Term.tid body0 in
  let header_tid = Term.tid header0 in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct header_tid)));
  let body_b = Blk.Builder.init ~copy_defs:true body0 in
  Blk.Builder.add_jmp body_b (Jmp.create (Goto (Direct header_tid)));
  let header_b = Blk.Builder.init ~copy_defs:true header0 in
  let jcond = if flag then Bil.Var cf else cond in
  Blk.Builder.add_jmp header_b (Jmp.create ~cond:jcond (Goto (Direct body_tid)));
  Blk.Builder.add_jmp header_b
    (Jmp.create ~cond:(Bil.UnOp (Bil.NOT, jcond)) (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let body = Blk.Builder.result body_b in
  let header = Blk.Builder.result header_b in
  let exit = Blk.Builder.result exit_b in
  let sub_b = Sub.Builder.create ~name:"l3c2_loop" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  (sub, body_tid)

(* Cell at RBP-8 in [st]. *)
let l3c2_cell_of (st : AI.t) : Ws.t =
  let m = memv "l3c2_m" in
  let rbp = v64 "RBP" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  match Vsa.denote_imm_exp (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)) st with
  | Ok ws -> ws
  | Error _ -> Ws.top 32

(* Finite non-top non-bottom, max <= maxv. *)
let l3c2_bounded (ws : Ws.t) (maxv : word) : bool =
  (not (Ws.is_top ws))
  && (not (Ws.is_bottom ws))
  && match Ws.max_elem ws with Some w -> Word.( <= ) w maxv | None -> false

(* Finite non-top non-bottom, all values in [lo, hi]. *)
let l3c2_in_high (ws : Ws.t) (lo : word) (hi : word) : bool =
  (not (Ws.is_top ws))
  && (not (Ws.is_bottom ws))
  &&
  match (Ws.min_elem ws, Ws.max_elem ws) with
  | Some mn, Some mx -> Word.( >= ) mn lo && Word.( <= ) mx hi
  | _ -> false

(* L3c-3: PLUS-hull, TIMES-const, RSHIFT/ARSHIFT-const rows. *)

(* Chain loop fixture: header loads, applies chain, guards. Returns (sub, body tid). *)
let mk_l3c3_loop ~(seed : word option) ~(chain : exp) ~(cmp : Bil.binop) ~(c : word)
    ~(body_k : word) : sub term * tid =
  let m = memv "l3c3_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let t = Var.create ~is_virtual:false ~fresh:false "l3c3_t" (Type.Imm 32) in
  let v = Var.create ~is_virtual:false ~fresh:false "l3c3_v" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "l3c3_u" (Type.Imm 32) in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  let cond = Bil.BinOp (cmp, Bil.Var v, Bil.Int c) in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  (match seed with
  | Some sv ->
      Blk.Builder.add_def entry_b
        (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int sv, LittleEndian, `r32)))
  | None -> ());
  (* Prologue def: RBP copies RSP. *)
  Blk.Builder.add_def entry_b (Def.create rbp (Bil.Var rsp));
  Blk.Builder.add_def header_b (Def.create t (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  Blk.Builder.add_def header_b (Def.create v chain);
  Blk.Builder.add_def body_b (Def.create u (Bil.BinOp (Bil.PLUS, Bil.Var t, Bil.Int body_k)));
  Blk.Builder.add_def body_b
    (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Var u, LittleEndian, `r32)));
  let entry0 = Blk.Builder.result entry_b in
  let body0 = Blk.Builder.result body_b in
  let header0 = Blk.Builder.result header_b in
  let exit0 = Blk.Builder.result exit_b in
  let body_tid = Term.tid body0 in
  let header_tid = Term.tid header0 in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct header_tid)));
  let body_b = Blk.Builder.init ~copy_defs:true body0 in
  Blk.Builder.add_jmp body_b (Jmp.create (Goto (Direct header_tid)));
  let header_b = Blk.Builder.init ~copy_defs:true header0 in
  Blk.Builder.add_jmp header_b (Jmp.create ~cond (Goto (Direct body_tid)));
  Blk.Builder.add_jmp header_b
    (Jmp.create ~cond:(Bil.UnOp (Bil.NOT, cond)) (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let body = Blk.Builder.result body_b in
  let header = Blk.Builder.result header_b in
  let exit = Blk.Builder.result exit_b in
  let sub_b = Sub.Builder.create ~name:"l3c3_loop" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  (sub, body_tid)

(* Cell at RBP-8 in [st]. *)
let l3c3_cell_of (st : AI.t) : Ws.t =
  let m = memv "l3c3_m" in
  let rbp = v64 "RBP" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  match Vsa.denote_imm_exp (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)) st with
  | Ok ws -> ws
  | Error _ -> Ws.top 32

(* Plain fixpoint; BODY input cell at RBP-8. *)
let l3c3_run (sub : sub term) (body_tid : tid) : Ws.t =
  let ctx = Program.create ~subs:[ sub ] () in
  let sol = Vsa.static_graph_vsa [] ctx sub (Vsa.init_sol ~entry:(anchored_entry ()) sub) in
  iter_cell_of sub sol body_tid l3c3_cell_of

(* L3c-4: Var-vs-Var overlap, DIVIDE-const, HIGH-extract rows. *)

(* Chain loop with compared-var width. Returns (sub, body tid). *)
let mk_l3c4_loop ~(seed : word option) ~(chain : exp) ~(v_w : int) ~(cmp : Bil.binop) ~(c : word)
    ~(body_k : word) : sub term * tid =
  let m = memv "l3c4_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let t = Var.create ~is_virtual:false ~fresh:false "l3c4_t" (Type.Imm 32) in
  let v = Var.create ~is_virtual:false ~fresh:false "l3c4_v" (Type.Imm v_w) in
  let u = Var.create ~is_virtual:false ~fresh:false "l3c4_u" (Type.Imm 32) in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  let cond = Bil.BinOp (cmp, Bil.Var v, Bil.Int c) in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  (match seed with
  | Some sv ->
      Blk.Builder.add_def entry_b
        (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int sv, LittleEndian, `r32)))
  | None -> ());
  (* Prologue def: RBP copies RSP. *)
  Blk.Builder.add_def entry_b (Def.create rbp (Bil.Var rsp));
  Blk.Builder.add_def header_b (Def.create t (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  Blk.Builder.add_def header_b (Def.create v chain);
  Blk.Builder.add_def body_b (Def.create u (Bil.BinOp (Bil.PLUS, Bil.Var t, Bil.Int body_k)));
  Blk.Builder.add_def body_b
    (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Var u, LittleEndian, `r32)));
  let entry0 = Blk.Builder.result entry_b in
  let body0 = Blk.Builder.result body_b in
  let header0 = Blk.Builder.result header_b in
  let exit0 = Blk.Builder.result exit_b in
  let body_tid = Term.tid body0 in
  let header_tid = Term.tid header0 in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct header_tid)));
  let body_b = Blk.Builder.init ~copy_defs:true body0 in
  Blk.Builder.add_jmp body_b (Jmp.create (Goto (Direct header_tid)));
  let header_b = Blk.Builder.init ~copy_defs:true header0 in
  Blk.Builder.add_jmp header_b (Jmp.create ~cond (Goto (Direct body_tid)));
  Blk.Builder.add_jmp header_b
    (Jmp.create ~cond:(Bil.UnOp (Bil.NOT, cond)) (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let body = Blk.Builder.result body_b in
  let header = Blk.Builder.result header_b in
  let exit = Blk.Builder.result exit_b in
  let sub_b = Sub.Builder.create ~name:"l3c4_loop" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  (sub, body_tid)

(* Two-load Var-vs-Var shape. Returns (sub, body tid). *)
let mk_l3c4_vv_loop ~(seed : word option) ~(seed2 : word option) ~(cmp : Bil.binop) ~(body_k : word)
    : sub term * tid =
  let m = memv "l3c4_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let t = Var.create ~is_virtual:false ~fresh:false "l3c4_t" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "l3c4_u" (Type.Imm 32) in
  let w = Var.create ~is_virtual:false ~fresh:false "l3c4_w" (Type.Imm 32) in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  let addr2 = Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 16)) in
  let cond = Bil.BinOp (cmp, Bil.Var t, Bil.Var u) in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  (match seed with
  | Some sv ->
      Blk.Builder.add_def entry_b
        (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int sv, LittleEndian, `r32)))
  | None -> ());
  (match seed2 with
  | Some sv ->
      Blk.Builder.add_def entry_b
        (Def.create m (Bil.Store (Bil.Var m, addr2, Bil.Int sv, LittleEndian, `r32)))
  | None -> ());
  (* Prologue def: RBP copies RSP. *)
  Blk.Builder.add_def entry_b (Def.create rbp (Bil.Var rsp));
  Blk.Builder.add_def header_b (Def.create t (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  Blk.Builder.add_def header_b (Def.create u (Bil.Load (Bil.Var m, addr2, LittleEndian, `r32)));
  Blk.Builder.add_def body_b (Def.create w (Bil.BinOp (Bil.PLUS, Bil.Var t, Bil.Int body_k)));
  Blk.Builder.add_def body_b
    (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Var w, LittleEndian, `r32)));
  let entry0 = Blk.Builder.result entry_b in
  let body0 = Blk.Builder.result body_b in
  let header0 = Blk.Builder.result header_b in
  let exit0 = Blk.Builder.result exit_b in
  let body_tid = Term.tid body0 in
  let header_tid = Term.tid header0 in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct header_tid)));
  let body_b = Blk.Builder.init ~copy_defs:true body0 in
  Blk.Builder.add_jmp body_b (Jmp.create (Goto (Direct header_tid)));
  let header_b = Blk.Builder.init ~copy_defs:true header0 in
  Blk.Builder.add_jmp header_b (Jmp.create ~cond (Goto (Direct body_tid)));
  Blk.Builder.add_jmp header_b
    (Jmp.create ~cond:(Bil.UnOp (Bil.NOT, cond)) (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let body = Blk.Builder.result body_b in
  let header = Blk.Builder.result header_b in
  let exit = Blk.Builder.result exit_b in
  let sub_b = Sub.Builder.create ~name:"l3c4_vv" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  (sub, body_tid)

(* Cell at RBP-8 in [st]. *)
let l3c4_cell_of (st : AI.t) : Ws.t =
  let m = memv "l3c4_m" in
  let rbp = v64 "RBP" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  match Vsa.denote_imm_exp (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)) st with
  | Ok ws -> ws
  | Error _ -> Ws.top 32

(* Plain fixpoint; BODY input cell at RBP-8. *)
let l3c4_run (sub : sub term) (body_tid : tid) : Ws.t =
  let ctx = Program.create ~subs:[ sub ] () in
  let sol = Vsa.static_graph_vsa [] ctx sub (Vsa.init_sol ~entry:(anchored_entry ()) sub) in
  iter_cell_of sub sol body_tid l3c4_cell_of

(* L3c-5: structural closure — identity rows, const-first arm, shrunk catch-all. *)

(* Optional-chain loop fixture. Returns (sub, body tid). *)
let mk_l3c5_loop ~(seed : word option) ~(chain : exp option) ~(cond : exp) ~(body_k : word) :
    sub term * tid =
  let m = memv "l3c5_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let t = Var.create ~is_virtual:false ~fresh:false "l3c5_t" (Type.Imm 32) in
  let v = Var.create ~is_virtual:false ~fresh:false "l3c5_v" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "l3c5_u" (Type.Imm 32) in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  (match seed with
  | Some sv ->
      Blk.Builder.add_def entry_b
        (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int sv, LittleEndian, `r32)))
  | None -> ());
  (* Prologue def: RBP copies RSP. *)
  Blk.Builder.add_def entry_b (Def.create rbp (Bil.Var rsp));
  Blk.Builder.add_def header_b (Def.create t (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  (match chain with Some ch -> Blk.Builder.add_def header_b (Def.create v ch) | None -> ());
  Blk.Builder.add_def body_b (Def.create u (Bil.BinOp (Bil.PLUS, Bil.Var t, Bil.Int body_k)));
  Blk.Builder.add_def body_b
    (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Var u, LittleEndian, `r32)));
  let entry0 = Blk.Builder.result entry_b in
  let body0 = Blk.Builder.result body_b in
  let header0 = Blk.Builder.result header_b in
  let exit0 = Blk.Builder.result exit_b in
  let body_tid = Term.tid body0 in
  let header_tid = Term.tid header0 in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct header_tid)));
  let body_b = Blk.Builder.init ~copy_defs:true body0 in
  Blk.Builder.add_jmp body_b (Jmp.create (Goto (Direct header_tid)));
  let header_b = Blk.Builder.init ~copy_defs:true header0 in
  Blk.Builder.add_jmp header_b (Jmp.create ~cond (Goto (Direct body_tid)));
  Blk.Builder.add_jmp header_b
    (Jmp.create ~cond:(Bil.UnOp (Bil.NOT, cond)) (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let body = Blk.Builder.result body_b in
  let header = Blk.Builder.result header_b in
  let exit = Blk.Builder.result exit_b in
  let sub_b = Sub.Builder.create ~name:"l3c5_loop" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  (sub, body_tid)

(* Cell at RBP-8 in [st]. *)
let l3c5_cell_of (st : AI.t) : Ws.t =
  let m = memv "l3c5_m" in
  let rbp = v64 "RBP" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  match Vsa.denote_imm_exp (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)) st with
  | Ok ws -> ws
  | Error _ -> Ws.top 32

(* Plain fixpoint; BODY input cell at RBP-8. *)
let l3c5_run (sub : sub term) (body_tid : tid) : Ws.t =
  let ctx = Program.create ~subs:[ sub ] () in
  let sol = Vsa.static_graph_vsa [] ctx sub (Vsa.init_sol ~entry:(anchored_entry ()) sub) in
  iter_cell_of sub sol body_tid l3c5_cell_of

(* Interrupt denotation: unknown external callee via call_abstraction. *)
(* L-3b: coalesce equal-lower merge arm — piles collapse, reads preserved. *)

(* Seeded RMW counter (traverse shape). Returns (sub, body tid, header tid). *)
let mk_l3b1_loop () : sub term * tid * tid =
  let m = memv "l3b1_m" in
  let rsp = v64 "RSP" in
  let t = Var.create ~is_virtual:false ~fresh:false "l3b1_t" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "l3b1_u" (Type.Imm 32) in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 8)) in
  let cond = Bil.BinOp (Bil.LT, Bil.Var t, Bil.Int (w32 8)) in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b
    (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int (w32 0), LittleEndian, `r32)));
  Blk.Builder.add_def header_b (Def.create t (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  Blk.Builder.add_def body_b (Def.create u (Bil.BinOp (Bil.PLUS, Bil.Var t, Bil.Int (w32 1))));
  Blk.Builder.add_def body_b
    (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Var u, LittleEndian, `r32)));
  let entry0 = Blk.Builder.result entry_b in
  let body0 = Blk.Builder.result body_b in
  let header0 = Blk.Builder.result header_b in
  let exit0 = Blk.Builder.result exit_b in
  let body_tid = Term.tid body0 in
  let header_tid = Term.tid header0 in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct header_tid)));
  let body_b = Blk.Builder.init ~copy_defs:true body0 in
  Blk.Builder.add_jmp body_b (Jmp.create (Goto (Direct header_tid)));
  let header_b = Blk.Builder.init ~copy_defs:true header0 in
  Blk.Builder.add_jmp header_b (Jmp.create ~cond (Goto (Direct body_tid)));
  Blk.Builder.add_jmp header_b
    (Jmp.create ~cond:(Bil.UnOp (Bil.NOT, cond)) (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let body = Blk.Builder.result body_b in
  let header = Blk.Builder.result header_b in
  let exit = Blk.Builder.result exit_b in
  let sub_b = Sub.Builder.create ~name:"l3b1_loop" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  (sub, body_tid, header_tid)

(* Diamond: both branches store {7} at [RSP-8]/[RSP-7]; merge unions them. Returns (sub, merge tid). *)
let mk_l3b4_diamond () : sub term * tid =
  let m = memv "l3b4_m" in
  let rsp = v64 "RSP" in
  let i = Var.create ~is_virtual:false ~fresh:false "l3b4_i" (Type.Imm 32) in
  let addr8 = Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 8)) in
  let addr7 = Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 7)) in
  let cond = Bil.BinOp (Bil.LT, Bil.Var i, Bil.Int (w32 1)) in
  let entry_b = Blk.Builder.create () in
  let a_b = Blk.Builder.create () in
  let b_b = Blk.Builder.create () in
  let merge_b = Blk.Builder.create () in
  Blk.Builder.add_def a_b
    (Def.create m (Bil.Store (Bil.Var m, addr8, Bil.Int (w32 7), LittleEndian, `r32)));
  Blk.Builder.add_def a_b
    (Def.create m (Bil.Store (Bil.Var m, addr7, Bil.Int (w32 7), LittleEndian, `r32)));
  Blk.Builder.add_def b_b
    (Def.create m (Bil.Store (Bil.Var m, addr8, Bil.Int (w32 7), LittleEndian, `r32)));
  Blk.Builder.add_def b_b
    (Def.create m (Bil.Store (Bil.Var m, addr7, Bil.Int (w32 7), LittleEndian, `r32)));
  let entry0 = Blk.Builder.result entry_b in
  let a0 = Blk.Builder.result a_b in
  let b0 = Blk.Builder.result b_b in
  let merge0 = Blk.Builder.result merge_b in
  let a_tid = Term.tid a0 in
  let b_tid = Term.tid b0 in
  let merge_tid = Term.tid merge0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create ~cond (Goto (Direct a_tid)));
  Blk.Builder.add_jmp entry_b (Jmp.create ~cond:(Bil.UnOp (Bil.NOT, cond)) (Goto (Direct b_tid)));
  let a_b = Blk.Builder.init ~copy_defs:true a0 in
  Blk.Builder.add_jmp a_b (Jmp.create (Goto (Direct merge_tid)));
  let b_b = Blk.Builder.init ~copy_defs:true b0 in
  Blk.Builder.add_jmp b_b (Jmp.create (Goto (Direct merge_tid)));
  let entry = Blk.Builder.result entry_b in
  let a = Blk.Builder.result a_b in
  let b = Blk.Builder.result b_b in
  let merge = Blk.Builder.result merge_b in
  let sub_b = Sub.Builder.create ~name:"l3b4_diamond" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b a;
  Sub.Builder.add_blk sub_b b;
  Sub.Builder.add_blk sub_b merge;
  let sub = Sub.Builder.result sub_b in
  (sub, merge_tid)

(* Cell count in [st]'s memory: counts "(height " sexp markers. *)
let l3b_cells_of (mv : var) (st : AI.t) : int =
  let mem = AI.find_memory { Mem.addr_width = 64; Mem.addressable_width = 8 } st mv in
  let s = Core_kernel.Sexp.to_string (Mem.sexp_of_t mem) in
  let marker = "(height " in
  let mlen = String.length marker in
  let n = ref 0 in
  for i = 0 to String.length s - mlen do
    if String.sub s i mlen = marker then incr n
  done;
  !n

(* Cell at RBP-8 in [st]. *)
let l3b1_cell_of (st : AI.t) : Ws.t =
  let m = memv "l3b1_m" in
  let rsp = v64 "RSP" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 8)) in
  match Vsa.denote_imm_exp (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)) st with
  | Ok ws -> ws
  | Error _ -> Ws.top 32

(* L-B: jcc-decoder pins — exact -O0 corpus block fixture. *)

(* jle/jl/ja guard nestings the decoder matcher accepts. *)
let l39_jle (zf : var) (sf : var) (ofv : var) : exp =
  Bil.BinOp
    ( Bil.OR,
      Bil.Var zf,
      Bil.BinOp
        ( Bil.AND,
          Bil.BinOp (Bil.OR, Bil.Var sf, Bil.Var ofv),
          Bil.UnOp (Bil.NOT, Bil.BinOp (Bil.AND, Bil.Var sf, Bil.Var ofv)) ) )

let l39_jl (sf : var) (ofv : var) : exp =
  Bil.BinOp
    ( Bil.AND,
      Bil.BinOp (Bil.OR, Bil.Var sf, Bil.Var ofv),
      Bil.UnOp (Bil.NOT, Bil.BinOp (Bil.AND, Bil.Var sf, Bil.Var ofv)) )

let l39_ja (cf : var) (zf : var) : exp =
  Bil.UnOp (Bil.NOT, Bil.BinOp (Bil.OR, Bil.Var cf, Bil.Var zf))

(* Exact corpus block fixture: seeded store, canonical cmp emission, compound guard. Returns (sub, body tid). *)
let mk_l39_loop ~(seed : word) ~(c : word) ~(body_op : Bil.binop) ~(body_k : word)
    ~(mk_cond : cf:var -> ofv:var -> sf:var -> zf:var -> exp)
    ~(extra_header_defs : var -> def term list) : sub term * tid =
  let m = memv "l39_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let t = Var.create ~is_virtual:false ~fresh:false "l39_t" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "l39_u" (Type.Imm 32) in
  let cf = v1 "CF" in
  let ofv = v1 "OF" in
  let sf = v1 "SF" in
  let zf = v1 "ZF" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  let load_e = Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32) in
  let cond = mk_cond ~cf ~ofv ~sf ~zf in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b
    (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int seed, LittleEndian, `r32)));
  (* Prologue def: RBP copies RSP. *)
  Blk.Builder.add_def entry_b (Def.create rbp (Bil.Var rsp));
  (* Canonical -O0 cmp emission, fixed order: temp, CF, OF, SF, ZF. *)
  Blk.Builder.add_def header_b (Def.create t (Bil.BinOp (Bil.MINUS, load_e, Bil.Int c)));
  Blk.Builder.add_def header_b (Def.create cf (Bil.BinOp (Bil.LT, load_e, Bil.Int c)));
  Blk.Builder.add_def header_b
    (Def.create ofv
       (Bil.Cast
          ( Bil.HIGH,
            1,
            Bil.BinOp
              ( Bil.AND,
                Bil.BinOp (Bil.XOR, load_e, Bil.Int c),
                Bil.BinOp (Bil.XOR, load_e, Bil.Var t) ) )));
  Blk.Builder.add_def header_b (Def.create sf (Bil.Cast (Bil.HIGH, 1, Bil.Var t)));
  Blk.Builder.add_def header_b
    (Def.create zf (Bil.BinOp (Bil.EQ, Bil.Int (Word.zero (Word.bitwidth c)), Bil.Var t)));
  List.iter (Blk.Builder.add_def header_b) (extra_header_defs m);
  Blk.Builder.add_def body_b (Def.create u (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  Blk.Builder.add_def body_b
    (Def.create m
       (Bil.Store
          (Bil.Var m, addr_e, Bil.BinOp (body_op, Bil.Var u, Bil.Int body_k), LittleEndian, `r32)));
  let entry0 = Blk.Builder.result entry_b in
  let body0 = Blk.Builder.result body_b in
  let header0 = Blk.Builder.result header_b in
  let exit0 = Blk.Builder.result exit_b in
  let body_tid = Term.tid body0 in
  let header_tid = Term.tid header0 in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct header_tid)));
  let body_b = Blk.Builder.init ~copy_defs:true body0 in
  Blk.Builder.add_jmp body_b (Jmp.create (Goto (Direct header_tid)));
  let header_b = Blk.Builder.init ~copy_defs:true header0 in
  Blk.Builder.add_jmp header_b (Jmp.create ~cond (Goto (Direct body_tid)));
  Blk.Builder.add_jmp header_b
    (Jmp.create ~cond:(Bil.UnOp (Bil.NOT, cond)) (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let body = Blk.Builder.result body_b in
  let header = Blk.Builder.result header_b in
  let exit = Blk.Builder.result exit_b in
  let sub_b = Sub.Builder.create ~name:"l39_loop" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  (sub, body_tid)

(* Record-path fixture: bare-flag guard with unique def. Returns (sub, body tid). *)
let mk_l39b5_loop () : sub term * tid =
  let m = memv "l39_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let v = Var.create ~is_virtual:false ~fresh:false "l39b5_v" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "l39b5_u" (Type.Imm 32) in
  let cf = v1 "CF" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b
    (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int (w32 0), LittleEndian, `r32)));
  (* Prologue def: RBP copies RSP. *)
  Blk.Builder.add_def entry_b (Def.create rbp (Bil.Var rsp));
  Blk.Builder.add_def header_b (Def.create v (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  Blk.Builder.add_def header_b (Def.create cf (Bil.BinOp (Bil.LT, Bil.Var v, Bil.Int (w32 3))));
  Blk.Builder.add_def body_b (Def.create u (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  Blk.Builder.add_def body_b
    (Def.create m
       (Bil.Store
          (Bil.Var m, addr_e, Bil.BinOp (Bil.PLUS, Bil.Var u, Bil.Int (w32 1)), LittleEndian, `r32)));
  let entry0 = Blk.Builder.result entry_b in
  let body0 = Blk.Builder.result body_b in
  let header0 = Blk.Builder.result header_b in
  let exit0 = Blk.Builder.result exit_b in
  let body_tid = Term.tid body0 in
  let header_tid = Term.tid header0 in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct header_tid)));
  let body_b = Blk.Builder.init ~copy_defs:true body0 in
  Blk.Builder.add_jmp body_b (Jmp.create (Goto (Direct header_tid)));
  let header_b = Blk.Builder.init ~copy_defs:true header0 in
  Blk.Builder.add_jmp header_b (Jmp.create ~cond:(Bil.Var cf) (Goto (Direct body_tid)));
  Blk.Builder.add_jmp header_b
    (Jmp.create ~cond:(Bil.UnOp (Bil.NOT, Bil.Var cf)) (Goto (Direct exit_tid)));
  let entry = Blk.Builder.result entry_b in
  let body = Blk.Builder.result body_b in
  let header = Blk.Builder.result header_b in
  let exit = Blk.Builder.result exit_b in
  let sub_b = Sub.Builder.create ~name:"l39b5_loop" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  (sub, body_tid)

(* Cell at RBP-8 in [st]. *)
let l39_cell_of (st : AI.t) : Ws.t =
  let m = memv "l39_m" in
  let rbp = v64 "RBP" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  match Vsa.denote_imm_exp (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)) st with
  | Ok ws -> ws
  | Error _ -> Ws.top 32

(* Plain fixpoint; BODY input cell at RBP-8. *)
let l39_run (sub : sub term) (body_tid : tid) : Ws.t =
  let ctx = Program.create ~subs:[ sub ] () in
  let sol = Vsa.static_graph_vsa [] ctx sub (Vsa.init_sol ~entry:(anchored_entry ()) sub) in
  iter_cell_of sub sol body_tid l39_cell_of

(* Finite non-top non-bottom, max <= maxv. *)
let l39_bounded (ws : Ws.t) (maxv : word) : bool =
  (not (Ws.is_top ws))
  && (not (Ws.is_bottom ws))
  && match Ws.max_elem ws with Some w -> Word.( <= ) w maxv | None -> false

(* L-E1: ON-path matched-pair RSP restoration (RSP := RSP + 8 on return). *)

(* Call-in-loop fixture. Returns (sub, header tid, rsp). *)
let mk_e1_loop_sub () : sub term * tid * var =
  let rsp = v64 "RSP" in
  let m = memv "e1_m" in
  let entry_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let cont_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b (Def.create rsp (Bil.Int (w64 0x1000)));
  Blk.Builder.add_def body_b (Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 8))));
  Blk.Builder.add_def body_b
    (Def.create m (Bil.Store (Bil.Var m, Bil.Var rsp, Bil.Int (w64 0xdead), LittleEndian, `r64)));
  let entry0 = Blk.Builder.result entry_b in
  let header0 = Blk.Builder.result header_b in
  let body0 = Blk.Builder.result body_b in
  let cont0 = Blk.Builder.result cont_b in
  let header_tid = Term.tid header0 in
  let body_tid = Term.tid body0 in
  let cont_tid = Term.tid cont0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct header_tid)));
  let header_b = Blk.Builder.init ~copy_defs:true header0 in
  Blk.Builder.add_jmp header_b (Jmp.create (Goto (Direct body_tid)));
  let body_b = Blk.Builder.init ~copy_defs:true body0 in
  Blk.Builder.add_jmp body_b
    (Jmp.create
       (Call (Call.create ~return:(Label.direct cont_tid) ~target:(Indirect (Bil.Int (w64 0))) ())));
  let cont_b = Blk.Builder.init ~copy_defs:true cont0 in
  Blk.Builder.add_jmp cont_b (Jmp.create (Goto (Direct header_tid)));
  let entry = Blk.Builder.result entry_b in
  let header = Blk.Builder.result header_b in
  let body = Blk.Builder.result body_b in
  let cont = Blk.Builder.result cont_b in
  let sub_b = Sub.Builder.create ~name:"e1_loop" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b cont;
  let sub = Sub.Builder.result sub_b in
  (sub, header_tid, rsp)

(* Straight-line call fixture. Returns (sub, post tid, rsp). *)
let mk_e1_flat_sub () : sub term * tid * var =
  let rsp = v64 "RSP" in
  let m = memv "e1_m" in
  let entry_b = Blk.Builder.create () in
  let post_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b (Def.create rsp (Bil.Int (w64 0x2000)));
  Blk.Builder.add_def entry_b (Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w64 8))));
  Blk.Builder.add_def entry_b
    (Def.create m (Bil.Store (Bil.Var m, Bil.Var rsp, Bil.Int (w64 0xcafe), LittleEndian, `r64)));
  let entry0 = Blk.Builder.result entry_b in
  let post0 = Blk.Builder.result post_b in
  let post_tid = Term.tid post0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b
    (Jmp.create
       (Call (Call.create ~return:(Label.direct post_tid) ~target:(Indirect (Bil.Int (w64 0))) ())));
  let post_b = Blk.Builder.init ~copy_defs:true post0 in
  let entry = Blk.Builder.result entry_b in
  let post = Blk.Builder.result post_b in
  let sub_b = Sub.Builder.create ~name:"e1_flat" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b post;
  let sub = Sub.Builder.result sub_b in
  (sub, post_tid, rsp)

(* ON-path fixpoint; RSP value-set at [tid]. *)
let e1_rsp_at (sub : sub term) (tid : tid) (rsp : var) : Ws.t =
  let ctx' = Program.create ~subs:[ sub ] () in
  let sol = Vsa.static_graph_vsa [] ctx' sub (Vsa.init_sol ~entry:(anchored_entry ()) sub) in
  AI.find_word 64 (Graphlib.Std.Solution.get sol tid) rsp

(* L-D6: RBP-anchored gate-free fixture — the dead epilogue def is denoted too. *)

(* RBP loop with dead epilogue def. Returns (sub, body tid). *)
let mk_l6_rbp_loop () : sub term * tid =
  let m = memv "l6_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let t = Var.create ~is_virtual:false ~fresh:false "l6_t" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "l6_u" (Type.Imm 32) in
  let cf = v1 "CF" in
  let ofv = v1 "OF" in
  let sf = v1 "SF" in
  let zf = v1 "ZF" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  let load_e = Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32) in
  let c = w32 63 in
  let cond = l39_jle zf sf ofv in
  let prologue_b = Blk.Builder.create () in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  let epilogue_b = Blk.Builder.create () in
  Blk.Builder.add_def prologue_b (Def.create rbp (Bil.Var rsp));
  Blk.Builder.add_def entry_b
    (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int (w32 0), LittleEndian, `r32)));
  (* Canonical -O0 cmp emission, RBP-based. *)
  Blk.Builder.add_def header_b (Def.create t (Bil.BinOp (Bil.MINUS, load_e, Bil.Int c)));
  Blk.Builder.add_def header_b (Def.create cf (Bil.BinOp (Bil.LT, load_e, Bil.Int c)));
  Blk.Builder.add_def header_b
    (Def.create ofv
       (Bil.Cast
          ( Bil.HIGH,
            1,
            Bil.BinOp
              ( Bil.AND,
                Bil.BinOp (Bil.XOR, load_e, Bil.Int c),
                Bil.BinOp (Bil.XOR, load_e, Bil.Var t) ) )));
  Blk.Builder.add_def header_b (Def.create sf (Bil.Cast (Bil.HIGH, 1, Bil.Var t)));
  Blk.Builder.add_def header_b
    (Def.create zf (Bil.BinOp (Bil.EQ, Bil.Int (Word.zero (Word.bitwidth c)), Bil.Var t)));
  Blk.Builder.add_def body_b (Def.create u (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)));
  Blk.Builder.add_def body_b
    (Def.create m
       (Bil.Store
          (Bil.Var m, addr_e, Bil.BinOp (Bil.PLUS, Bil.Var u, Bil.Int (w32 1)), LittleEndian, `r32)));
  (* Dead epilogue def: RBP := mem[RSP]. *)
  Blk.Builder.add_def epilogue_b
    (Def.create rbp (Bil.Load (Bil.Var m, Bil.Var rsp, LittleEndian, `r64)));
  let prologue0 = Blk.Builder.result prologue_b in
  let entry0 = Blk.Builder.result entry_b in
  let body0 = Blk.Builder.result body_b in
  let header0 = Blk.Builder.result header_b in
  let exit0 = Blk.Builder.result exit_b in
  let epilogue0 = Blk.Builder.result epilogue_b in
  let body_tid = Term.tid body0 in
  let header_tid = Term.tid header0 in
  let entry_tid = Term.tid entry0 in
  let exit_tid = Term.tid exit0 in
  let epilogue_tid = Term.tid epilogue0 in
  let prologue_b = Blk.Builder.init ~copy_defs:true prologue0 in
  Blk.Builder.add_jmp prologue_b (Jmp.create (Goto (Direct entry_tid)));
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct header_tid)));
  let body_b = Blk.Builder.init ~copy_defs:true body0 in
  Blk.Builder.add_jmp body_b (Jmp.create (Goto (Direct header_tid)));
  let header_b = Blk.Builder.init ~copy_defs:true header0 in
  Blk.Builder.add_jmp header_b (Jmp.create ~cond (Goto (Direct body_tid)));
  Blk.Builder.add_jmp header_b
    (Jmp.create ~cond:(Bil.UnOp (Bil.NOT, cond)) (Goto (Direct exit_tid)));
  let exit_b = Blk.Builder.init ~copy_defs:true exit0 in
  Blk.Builder.add_jmp exit_b (Jmp.create (Goto (Direct epilogue_tid)));
  let prologue = Blk.Builder.result prologue_b in
  let entry = Blk.Builder.result entry_b in
  let body = Blk.Builder.result body_b in
  let header = Blk.Builder.result header_b in
  let exit = Blk.Builder.result exit_b in
  let epilogue = Blk.Builder.result epilogue_b in
  let sub_b = Sub.Builder.create ~name:"l6_rbp_loop" () in
  Sub.Builder.add_blk sub_b prologue;
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  Sub.Builder.add_blk sub_b epilogue;
  let sub = Sub.Builder.result sub_b in
  (sub, body_tid)

(* Cell at RBP-8 in [st]. *)
let l6_cell_of (st : AI.t) : Ws.t =
  let m = memv "l6_m" in
  let rbp = v64 "RBP" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  match Vsa.denote_imm_exp (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)) st with
  | Ok ws -> ws
  | Error _ -> Ws.top 32

(* ON-path fixpoint; BODY input cell at RBP-8. *)
let l6_run (sub : sub term) (body_tid : tid) : Ws.t =
  let ctx' = Program.create ~subs:[ sub ] () in
  let sol = Vsa.static_graph_vsa [] ctx' sub (Vsa.init_sol ~entry:(anchored_entry ()) sub) in
  l6_cell_of (Graphlib.Std.Solution.get sol body_tid)

(* Refactor-2 new-shape pins: inline-arithmetic, NOT-edge, const-first flip, nested BinOp. *)

(* RBP-anchored ON-path fixture with optional two-path seed. Returns (sub, body tid). *)
let mk_r2_loop ~(seed : word) ~(seed2 : word option) ~(body_op : Bil.binop) ~(body_k : word)
    ~(mk_cond : t:var -> exp) : sub term * tid =
  let m = memv "r2_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let t = Var.create ~is_virtual:false ~fresh:false "r2_t" (Type.Imm 32) in
  let u = Var.create ~is_virtual:false ~fresh:false "r2_u" (Type.Imm 32) in
  let f = v1 "r2_f" in
  let g = v1 "r2_g" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  let load_e = Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32) in
  let prologue_b = Blk.Builder.create () in
  let split_b = Blk.Builder.create () in
  let entry_b = Blk.Builder.create () in
  let entry2_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  Blk.Builder.add_def prologue_b (Def.create rbp (Bil.Var rsp));
  Blk.Builder.add_def split_b (Def.create f (Bil.Var g));
  Blk.Builder.add_def entry_b
    (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int seed, LittleEndian, `r32)));
  (match seed2 with
  | Some s2 ->
      Blk.Builder.add_def entry2_b
        (Def.create m (Bil.Store (Bil.Var m, addr_e, Bil.Int s2, LittleEndian, `r32)))
  | None -> ());
  Blk.Builder.add_def header_b (Def.create t load_e);
  Blk.Builder.add_def body_b (Def.create u load_e);
  Blk.Builder.add_def body_b
    (Def.create m
       (Bil.Store
          (Bil.Var m, addr_e, Bil.BinOp (body_op, Bil.Var u, Bil.Int body_k), LittleEndian, `r32)));
  let prologue0 = Blk.Builder.result prologue_b in
  let split0 = Blk.Builder.result split_b in
  let entry0 = Blk.Builder.result entry_b in
  let entry20 = Blk.Builder.result entry2_b in
  let body0 = Blk.Builder.result body_b in
  let header0 = Blk.Builder.result header_b in
  let exit0 = Blk.Builder.result exit_b in
  let body_tid = Term.tid body0 in
  let header_tid = Term.tid header0 in
  let entry_tid = Term.tid entry0 in
  let entry2_tid = Term.tid entry20 in
  let split_tid = Term.tid split0 in
  let exit_tid = Term.tid exit0 in
  let prologue_b = Blk.Builder.init ~copy_defs:true prologue0 in
  let split_b = Blk.Builder.init ~copy_defs:true split0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  let entry2_b = Blk.Builder.init ~copy_defs:true entry20 in
  let body_b = Blk.Builder.init ~copy_defs:true body0 in
  let header_b = Blk.Builder.init ~copy_defs:true header0 in
  let exit_b = Blk.Builder.init ~copy_defs:true exit0 in
  (match seed2 with
  | Some _ ->
      Blk.Builder.add_jmp prologue_b (Jmp.create (Goto (Direct split_tid)));
      Blk.Builder.add_jmp split_b (Jmp.create ~cond:(Bil.Var f) (Goto (Direct entry_tid)));
      Blk.Builder.add_jmp split_b
        (Jmp.create ~cond:(Bil.UnOp (Bil.NOT, Bil.Var f)) (Goto (Direct entry2_tid)));
      Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct header_tid)));
      Blk.Builder.add_jmp entry2_b (Jmp.create (Goto (Direct header_tid)))
  | None ->
      Blk.Builder.add_jmp prologue_b (Jmp.create (Goto (Direct entry_tid)));
      Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct header_tid))));
  Blk.Builder.add_jmp body_b (Jmp.create (Goto (Direct header_tid)));
  let cond = mk_cond ~t in
  Blk.Builder.add_jmp header_b (Jmp.create ~cond (Goto (Direct body_tid)));
  Blk.Builder.add_jmp header_b
    (Jmp.create ~cond:(Bil.UnOp (Bil.NOT, cond)) (Goto (Direct exit_tid)));
  let prologue = Blk.Builder.result prologue_b in
  let split = Blk.Builder.result split_b in
  let entry = Blk.Builder.result entry_b in
  let entry2 = Blk.Builder.result entry2_b in
  let body = Blk.Builder.result body_b in
  let header = Blk.Builder.result header_b in
  let exit = Blk.Builder.result exit_b in
  let sub_b = Sub.Builder.create ~name:"r2_loop" () in
  Sub.Builder.add_blk sub_b prologue;
  (match seed2 with
  | Some _ ->
      Sub.Builder.add_blk sub_b split;
      Sub.Builder.add_blk sub_b entry;
      Sub.Builder.add_blk sub_b entry2
  | None -> Sub.Builder.add_blk sub_b entry);
  Sub.Builder.add_blk sub_b body;
  Sub.Builder.add_blk sub_b header;
  Sub.Builder.add_blk sub_b exit;
  let sub = Sub.Builder.result sub_b in
  (sub, body_tid)

(* Cell at RBP-8 in [st]. *)
let r2_cell_of (st : AI.t) : Ws.t =
  let m = memv "r2_m" in
  let rbp = v64 "RBP" in
  let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (w64 8)) in
  match Vsa.denote_imm_exp (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32)) st with
  | Ok ws -> ws
  | Error _ -> Ws.top 32

(* ON-path fixpoint; BODY input cell at RBP-8. *)
let r2_run (sub : sub term) (body_tid : tid) : Ws.t =
  let ctx' = Program.create ~subs:[ sub ] () in
  let sol = Vsa.static_graph_vsa [] ctx' sub (Vsa.init_sol ~entry:(anchored_entry ()) sub) in
  iter_cell_of sub sol body_tid r2_cell_of

let run () =
(  (* L3a-1: PLUS row — EQ(v,5) gives t' = {4}. *)
  let sub1, body1 =
    mk_l3a_loop ~cmp:Bil.EQ ~c:(w32 5)
      ~rhs:
        (Bil.BinOp
           ( Bil.PLUS,
             Bil.Var (Var.create ~is_virtual:false ~fresh:false "l3a_t" (Type.Imm 32)),
             Bil.Int (w32 1) ))
  in
  check
    "L3a-1: backward guard refinement through PLUS — the cell at RBP-8 is bounded (⊆ [0,9]; the \
     walk met {4} into the load cell)"
    (l3a_bounded (l3a_run_analyzed sub1 body1) (w32 9));
  (* L3a-2: MINUS row — LT(v,10) gives t' = [1,10]. *)
  let sub2, body2 =
    mk_l3a_loop ~cmp:Bil.LT ~c:(w32 10)
      ~rhs:
        (Bil.BinOp
           ( Bil.MINUS,
             Bil.Var (Var.create ~is_virtual:false ~fresh:false "l3a_t" (Type.Imm 32)),
             Bil.Int (w32 1) ))
  in
  check
    "L3a-2: backward guard refinement through MINUS — the cell at RBP-8 is bounded (⊆ [1,10]; the \
     walk met [1,10] into the load cell)"
    (l3a_bounded (l3a_run_analyzed sub2 body2) (w32 10));
  (* L3a-3: LSHIFT-const row — t' = [0,9]. *)
  let sub3, body3 =
    mk_l3a_loop ~cmp:Bil.LT ~c:(w32 40)
      ~rhs:
        (Bil.BinOp
           ( Bil.LSHIFT,
             Bil.Var (Var.create ~is_virtual:false ~fresh:false "l3a_t" (Type.Imm 32)),
             Bil.Int (w32 2) ))
  in
  check
    "L3a-3: backward guard refinement through LSHIFT-const — the cell at RBP-8 is bounded (⊆ \
     [0,9]; 40>>2 = 10)"
    (l3a_bounded (l3a_run_analyzed sub3 body3) (w32 9));
  (* L3a-4: TIMES over unbounded operand is the identity (sound). *)
  let sub4, body4 =
    mk_l3a_loop ~cmp:Bil.LT ~c:(w32 40)
      ~rhs:
        (Bil.BinOp
           ( Bil.TIMES,
             Bil.Var (Var.create ~is_virtual:false ~fresh:false "l3a_t" (Type.Imm 32)),
             Bil.Int (w32 2) ))
  in
  check
    "L3a-4: the TIMES rule over an unbounded operand is the identity (sound — the wrapped classes \
     hull to the domain; the cell is not narrowed)"
    (not (l3a_bounded (l3a_run_analyzed sub4 body4) (w32 19)));
  (* L3a-5: NEQ doubt — no walk, cell stays top. *)
  let sub5, body5 =
    mk_l3a_loop ~cmp:Bil.NEQ ~c:(w32 5)
      ~rhs:
        (Bil.BinOp
           ( Bil.PLUS,
             Bil.Var (Var.create ~is_virtual:false ~fresh:false "l3a_t" (Type.Imm 32)),
             Bil.Int (w32 1) ))
  in
  check
    "L3a-5: a NEQ guard is doubt (constraint_of_compare None) — no walk, the cell at RBP-8 stays \
     top"
    (Ws.is_top (l3a_run_analyzed sub5 body5));
  ())
;
(  let m = memv "l3c1_m" in
  (* L3c1-1: flag-indirected guard recovers the constraint. *)
  let sub1, body1, _ = mk_l3c1_loop ~extra_header_defs:[] in
  let ctx1 = Program.create ~subs:[ sub1 ] () in
  let sol1 = Vsa.static_graph_vsa [] ctx1 sub1 (Vsa.init_sol ~entry:(anchored_entry ()) sub1) in
  let cell1 = l3c1_cell_of m (iter_state_of sub1 sol1 body1) in
  check
    "L3c1-1: a flag-indirected guard (CF := LT(t, 10); if CF goto …) — the flag-state record \
     recovers the constraint on t and the cell at RBP-8 is bounded (⊆ [0,9])"
    (l3c1_bounded cell1 (w32 9));
  (* L3c1-2: later def of the operand clears the record. *)
  let t = Var.create ~is_virtual:false ~fresh:false "l3c1_t" (Type.Imm 32) in
  let sub2, body2, _ = mk_l3c1_loop ~extra_header_defs:[ Def.create t (Bil.Int (w32 42)) ] in
  let ctx2 = Program.create ~subs:[ sub2 ] () in
  let sol2 = Vsa.static_graph_vsa [] ctx2 sub2 (Vsa.init_sol ~entry:(anchored_entry ()) sub2) in
  let cell2 = l3c1_cell_of m (iter_state_of sub2 sol2 body2) in
  check
    "L3c1-2: a later def of the compared operand (t := 42) between the comparison and the jump \
     invalidates the flag record — no cell refinement"
    (Ws.is_top cell2);
  (* L3c1-3: non-comparison flag redefinition clears the record. *)
  let cf = v1 "l3c1_cf" in
  let sub3, body3, _ =
    mk_l3c1_loop ~extra_header_defs:[ Def.create cf (Bil.Unknown ("l3c1_bits", Type.Imm 1)) ]
  in
  let ctx3 = Program.create ~subs:[ sub3 ] () in
  let sol3 = Vsa.static_graph_vsa [] ctx3 sub3 (Vsa.init_sol ~entry:(anchored_entry ()) sub3) in
  let cell3 = l3c1_cell_of m (iter_state_of sub3 sol3 body3) in
  check
    "L3c1-3: a non-comparison redefinition of the flag (CF := unknown) invalidates the flag record \
     — no cell refinement"
    (Ws.is_top cell3);
  (* L3c1-4: multi-def base refines through the producer subtraction. *)
  let m4 = memv "l3c1_m4" in
  let rsp4 = v64 "RSP" in
  let t4 = Var.create ~is_virtual:false ~fresh:false "l3c1_t4" (Type.Imm 32) in
  let v4 = Var.create ~is_virtual:false ~fresh:false "l3c1_v4" (Type.Imm 32) in
  let addr4 = Bil.BinOp (Bil.MINUS, Bil.Var rsp4, Bil.Int (w64 8)) in
  let cond4 = Bil.BinOp (Bil.LT, Bil.Var v4, Bil.Int (w32 10)) in
  let e4 = Blk.Builder.create () in
  let b4 = Blk.Builder.create () in
  let h4 = Blk.Builder.create () in
  let x4 = Blk.Builder.create () in
  Blk.Builder.add_def h4 (Def.create t4 (Bil.Load (Bil.Var m4, addr4, LittleEndian, `r32)));
  Blk.Builder.add_def h4 (Def.create v4 (Bil.BinOp (Bil.MINUS, Bil.Var t4, Bil.Int (w32 1))));
  Blk.Builder.add_def b4 (Def.create v4 (Bil.BinOp (Bil.PLUS, Bil.Var t4, Bil.Int (w32 1))));
  let e0 = Blk.Builder.result e4 in
  let b0 = Blk.Builder.result b4 in
  let h0 = Blk.Builder.result h4 in
  let x0 = Blk.Builder.result x4 in
  let b_tid = Term.tid b0 in
  let h_tid = Term.tid h0 in
  let x_tid = Term.tid x0 in
  let e4 = Blk.Builder.init ~copy_defs:true e0 in
  Blk.Builder.add_jmp e4 (Jmp.create (Goto (Direct h_tid)));
  let b4 = Blk.Builder.init ~copy_defs:true b0 in
  Blk.Builder.add_jmp b4 (Jmp.create (Goto (Direct h_tid)));
  let h4 = Blk.Builder.init ~copy_defs:true h0 in
  Blk.Builder.add_jmp h4 (Jmp.create ~cond:cond4 (Goto (Direct b_tid)));
  Blk.Builder.add_jmp h4 (Jmp.create ~cond:(Bil.UnOp (Bil.NOT, cond4)) (Goto (Direct x_tid)));
  let e = Blk.Builder.result e4 in
  let b = Blk.Builder.result b4 in
  let h = Blk.Builder.result h4 in
  let x = Blk.Builder.result x4 in
  let sub_b = Sub.Builder.create ~name:"l3c1_multidef" () in
  Sub.Builder.add_blk sub_b e;
  Sub.Builder.add_blk sub_b b;
  Sub.Builder.add_blk sub_b h;
  Sub.Builder.add_blk sub_b x;
  let sub4 = Sub.Builder.result sub_b in
  let ctx4 = Program.create ~subs:[ sub4 ] () in
  let sol4 = Vsa.static_graph_vsa [] ctx4 sub4 (Vsa.init_sol ~entry:(anchored_entry ()) sub4) in
  let cell4 = l3c1_cell_of m4 (Graphlib.Std.Solution.get sol4 b_tid) in
  (* Body-IN cell is the exact taken-edge window [1,10]. *)
  check
    "L3c1-4 (migrated, single-pass §2): the multi-def base refines through the \
     per-block producer subtraction — the body-IN cell is the EXACT taken-edge \
     window [1,10] (1 ∈, 10 ∈, 0 ∉, 11 ∉; non-top)"
    ((not (Ws.is_top cell4))
    && (not (Ws.is_bottom cell4))
    && Ws.elem (w32 1) cell4
    && Ws.elem (w32 10) cell4
    && not (Ws.elem (w32 0) cell4)
    && not (Ws.elem (w32 11) cell4));
  (* L3c1-5: without ?defs the flag-state step is gated off. *)
  let sub5, _, jmp5 = mk_l3c1_loop ~extra_header_defs:[] in
  let ctx5 = Program.create ~subs:[ sub5 ] () in
  let sol5 = Vsa.static_graph_vsa [] ctx5 sub5 (Vsa.init_sol ~entry:(anchored_entry ()) sub5) in
  let hdr5 =
    match Term.enum blk_t sub5 |> Seq.to_list with [ _; _; h; _ ] -> h | _ -> assert false
  in
  let hdr_st = Graphlib.Std.Solution.get sol5 (Term.tid hdr5) in
  let res5 = Vsa.assume_jump_cond hdr_st jmp5 in
  let cell5 = l3c1_cell_of m res5 in
  check
    "L3c1-5: direct assume_jump_cond without ?defs — the flag-state refinement is gated off (no \
     cell refinement; the pre-L3c behavior)"
    (Ws.is_top cell5);
  ())
;
(  let half = w32 0x80000000 in
  let m_one = w32 0xFFFFFFFF in
  (* L3c2-1: direct SLT on seeded non-negative counter caps the cell. *)
  let sub1, body1 =
    mk_l3c2_loop ~prologue:true
      ~seed:(Some (w32 0))
      ~cmp:Bil.SLT ~c:(w32 4) ~body_op:Bil.PLUS ~body_k:(w32 1) ~flag:false
  in
  let ctx1 = Program.create ~subs:[ sub1 ] () in
  let sol1 = Vsa.static_graph_vsa [] ctx1 sub1 (Vsa.init_sol ~entry:(anchored_entry ()) sub1) in
  let cell1 = l3c2_cell_of (iter_state_of sub1 sol1 body1) in
  check
    "L3c2-1: a direct SLT(t, 4) guard on a seeded non-negative counter — the signed row fires (the \
     gate passes) and the cell at RBP-8 is bounded (⊆ [0,3])"
    (l3c2_bounded cell1 (w32 3));
  (* L3c2-2: unseeded operand refines to the two-piece rule. *)
  let sub2, body2 =
    mk_l3c2_loop ~prologue:true ~seed:None ~cmp:Bil.SLT ~c:(w32 10) ~body_op:Bil.PLUS
      ~body_k:(w32 1) ~flag:false
  in
  let ctx2 = Program.create ~subs:[ sub2 ] () in
  let sol2 = Vsa.static_graph_vsa [] ctx2 sub2 (Vsa.init_sol ~entry:(anchored_entry ()) sub2) in
  let cell2 = l3c2_cell_of (iter_state_of sub2 sol2 body2) in
  check
    "L3c2-2: the two-piece SLT rule — a signed guard whose operand is not provably non-negative \
     (top) still refines the cell to the two-piece [0, c−1] ∪ [2^31, max] (the gate is removed; no \
     None stop)"
    ((not (Ws.is_top cell2))
    && match Ws.min_elem cell2 with Some w -> Word.( >= ) w (w32 0) | None -> false);
  (* L3c2-3: c < 0 is one interval, no gate. *)
  let sub3, body3 =
    mk_l3c2_loop ~prologue:true ~seed:(Some half) ~cmp:Bil.SLT ~c:m_one ~body_op:Bil.MINUS
      ~body_k:(w32 1) ~flag:false
  in
  let ctx3 = Program.create ~subs:[ sub3 ] () in
  let sol3 = Vsa.static_graph_vsa [] ctx3 sub3 (Vsa.init_sol ~entry:(anchored_entry ()) sub3) in
  let cell3 = l3c2_cell_of (iter_state_of sub3 sol3 body3) in
  check
    "L3c2-3: SLT(t, -1) (c < 0) is a single high interval [2^31, c-1] with no gate — the cell \
     stays in the high half (the decrements into the low half are met away)"
    (l3c2_in_high cell3 half (w32 0xFFFFFFFE));
  (* L3c2-4: flag-indirected signed guard caps the cell. *)
  let sub4, body4 =
    mk_l3c2_loop ~prologue:true
      ~seed:(Some (w32 0))
      ~cmp:Bil.SLT ~c:(w32 4) ~body_op:Bil.PLUS ~body_k:(w32 1) ~flag:true
  in
  let ctx4 = Program.create ~subs:[ sub4 ] () in
  let sol4 = Vsa.static_graph_vsa [] ctx4 sub4 (Vsa.init_sol ~entry:(anchored_entry ()) sub4) in
  let cell4 = l3c2_cell_of (iter_state_of sub4 sol4 body4) in
  check
    "L3c2-4: the -O0 flag-indirected pattern (CF := SLT(t, 4); if CF goto …) — the flag-state \
     record + the signed row bound the cell at RBP-8 (⊆ [0,3])"
    (l3c2_bounded cell4 (w32 3));
  (* L3c2-5: no prologue def needed; trace/frame derives the range. *)
  let sub5, body5 =
    mk_l3c2_loop ~prologue:false
      ~seed:(Some (w32 0))
      ~cmp:Bil.SLT ~c:(w32 4) ~body_op:Bil.PLUS ~body_k:(w32 1) ~flag:false
  in
  let ctx5 = Program.create ~subs:[ sub5 ] () in
  let sol5 = Vsa.static_graph_vsa [] ctx5 sub5 (Vsa.init_sol ~entry:(anchored_entry ()) sub5) in
  let cell5 = l3c2_cell_of (iter_state_of sub5 sol5 body5) in
  check
    "L3c2-5: trace-exact cell refinement — without the RBP prologue def the cell is still bounded \
     by the SLT(4) iterate constraint"
    (l3c2_bounded cell5 (w32 3));
  (* L3c2-6: unsigned regression covered by the LT pins. *)
  ())
;
(  let t = Var.create ~is_virtual:false ~fresh:false "l3c3_t" (Type.Imm 32) in
  (* L3c3-1: PLUS-HULL caps the cell. *)
  let sub1, body1 =
    mk_l3c3_loop
      ~seed:(Some (w32 0))
      ~chain:(Bil.BinOp (Bil.PLUS, Bil.Var t, Bil.Int (w32 1)))
      ~cmp:Bil.SLT ~c:(w32 10) ~body_k:(w32 4)
  in
  check
    "L3c3-1: the PLUS-HULL row — `v := t + 1; if SLT(v, 10)` — the wrapped hull {−1} ∪ [0,8] caps \
     the cell at RBP-8 (bounded ⊆ [0,9])"
    (l3c2_bounded (l3c3_run sub1 body1) (w32 9));
  (* L3c3-2: TIMES over unbounded operand is the identity. *)
  let sub2, body2 =
    mk_l3c3_loop
      ~seed:(Some (w32 0))
      ~chain:(Bil.BinOp (Bil.TIMES, Bil.Var t, Bil.Int (w32 8)))
      ~cmp:Bil.SLT ~c:(w32 80) ~body_k:(w32 4)
  in
  check
    "L3c3-2: the TIMES rule over an unbounded operand is the identity (sound — the cell is not \
     bounded by the multiplier)"
    (not (l3c2_bounded (l3c3_run sub2 body2) (w32 9)));
  (* L3c3-3: RSHIFT-const row. *)
  let sub3, body3 =
    mk_l3c3_loop
      ~seed:(Some (w32 0))
      ~chain:(Bil.BinOp (Bil.RSHIFT, Bil.Var t, Bil.Int (w32 2)))
      ~cmp:Bil.SLT ~c:(w32 10) ~body_k:(w32 8)
  in
  check
    "L3c3-3: the RSHIFT-const row — `v := t >> 2; if SLT(v, 10)` — the cell at RBP-8 is bounded (⊆ \
     [0,39]; 10<<2 = 40)"
    (l3c2_bounded (l3c3_run sub3 body3) (w32 39));
  (* L3c3-4a: ARSHIFT with provably non-negative operand bounds the cell. *)
  let sub4a, body4a =
    mk_l3c3_loop
      ~seed:(Some (w32 0))
      ~chain:(Bil.BinOp (Bil.ARSHIFT, Bil.Var t, Bil.Int (w32 2)))
      ~cmp:Bil.SLT ~c:(w32 10) ~body_k:(w32 8)
  in
  check
    "L3c3-4a: the ARSHIFT-const row with a provably non-negative operand — the cell at RBP-8 is \
     bounded (⊆ [0,39])"
    (l3c2_bounded (l3c3_run sub4a body4a) (w32 39));
  (* L3c3-4b: ARSHIFT on top operand is a sound stop. *)
  let sub4b, body4b =
    mk_l3c3_loop ~seed:None
      ~chain:(Bil.BinOp (Bil.ARSHIFT, Bil.Var t, Bil.Int (w32 2)))
      ~cmp:Bil.SLT ~c:(w32 10) ~body_k:(w32 4)
  in
  check
    "L3c3-4b: the ARSHIFT gate — an operand not provably non-negative (top) does NOT refine (the \
     cell stays top; sound stop)"
    (Ws.is_top (l3c3_run sub4b body4b));
  (* L3c3-5: TIMES k = 0 is a sound stop. *)
  let sub5, body5 =
    mk_l3c3_loop ~seed:None
      ~chain:(Bil.BinOp (Bil.TIMES, Bil.Var t, Bil.Int (w32 0)))
      ~cmp:Bil.SLT ~c:(w32 10) ~body_k:(w32 4)
  in
  check "L3c3-5: TIMES with k = 0 is a sound stop — the cell at RBP-8 stays top"
    (Ws.is_top (l3c3_run sub5 body5));
  (* L3c3-6: TIMES non-divisible EQ singleton is empty — no refinement. *)
  let sub6, body6 =
    mk_l3c3_loop ~seed:None
      ~chain:(Bil.BinOp (Bil.TIMES, Bil.Var t, Bil.Int (w32 8)))
      ~cmp:Bil.EQ ~c:(w32 5) ~body_k:(w32 4)
  in
  check
    "L3c3-6: TIMES with an EQ singleton {5} and k = 8 (non-divisible) — the row is empty, no \
     refinement (the cell is not a bounded set; the guard is genuinely dead — no t makes t*8 = 5 — \
     the edge is pruned)"
    (not (l3c2_bounded (l3c3_run sub6 body6) (w32 39)));
  ())
;
(  let t = Var.create ~is_virtual:false ~fresh:false "l3c4_t" (Type.Imm 32) in
  (* L3c4-1: Var-vs-Var LT guard caps the cell. *)
  let sub1, body1 =
    mk_l3c4_vv_loop ~seed:(Some (w32 0)) ~seed2:(Some (w32 10)) ~cmp:Bil.LT ~body_k:(w32 4)
  in
  check
    "L3c4-1: the Var-vs-Var LT guard (`if (t < u) goto …`, u seeded {10}) — the interval-overlap \
     row caps the cell at RBP-8 (⊆ [0,9])"
    (l3c2_bounded (l3c4_run sub1 body1) (w32 9));
  (* L3c4-2: TOP operand makes refinement vacuous. *)
  let sub2, body2 = mk_l3c4_vv_loop ~seed:(Some (w32 0)) ~seed2:None ~cmp:Bil.LT ~body_k:(w32 4) in
  check
    "L3c4-2: a TOP Var-vs-Var operand makes the refinement vacuous — the cell at RBP-8 stays \
     unbounded (the semantic-top class, no wrong window)"
    (not (l3c2_bounded (l3c4_run sub2 body2) (w32 1000)));
  (* L3c4-3: DIVIDE-const row. *)
  let sub3, body3 =
    mk_l3c4_loop
      ~seed:(Some (w32 0))
      ~chain:(Bil.BinOp (Bil.DIVIDE, Bil.Var t, Bil.Int (w32 2)))
      ~v_w:32 ~cmp:Bil.SLT ~c:(w32 10) ~body_k:(w32 4)
  in
  check
    "L3c4-3: the DIVIDE-const row — `v := t / 2; if SLT(v, 10)` — the cell at RBP-8 is bounded (⊆ \
     [0,19])"
    (l3c2_bounded (l3c4_run sub3 body3) (w32 19));
  (* L3c4-4: HIGH-extract producer row. *)
  let sub4, body4 =
    mk_l3c4_loop
      ~seed:(Some (w32 0))
      ~chain:(Bil.Cast (Bil.HIGH, 8, Bil.Var t))
      ~v_w:8 ~cmp:Bil.SLT ~c:(Word.of_int ~width:8 10) ~body_k:(w32 0x10000000)
  in
  check
    "L3c4-4: the HIGH-extract producer row — `v := cast HIGH 8 t; if SLT(v, 10)` — the cell at \
     RBP-8 is bounded (⊆ [0, 0x09FFFFFF]; the 2^28-straddling value is dropped)"
    (l3c2_bounded (l3c4_run sub4 body4) (w32 0x09FFFFFF));
  (* L3c4-5: DIVIDE k = 0 is a sound stop. *)
  let sub5, body5 =
    mk_l3c4_loop ~seed:None
      ~chain:(Bil.BinOp (Bil.DIVIDE, Bil.Var t, Bil.Int (w32 0)))
      ~v_w:32 ~cmp:Bil.SLT ~c:(w32 10) ~body_k:(w32 4)
  in
  check "L3c4-5: DIVIDE with k = 0 is a sound stop — no refinement (the cell is not a bounded set)"
    (not (l3c2_bounded (l3c4_run sub5 body5) (w32 39)));
  ())
;
(  let t = Var.create ~is_virtual:false ~fresh:false "l3c5_t" (Type.Imm 32) in
  let v = Var.create ~is_virtual:false ~fresh:false "l3c5_v" (Type.Imm 32) in
  (* L3c5-1: const-first guard arm normalizes to const-second. *)
  let sub1, body1 =
    mk_l3c5_loop ~seed:None ~chain:None
      ~cond:(Bil.BinOp (Bil.EQ, Bil.Int (w32 10), Bil.Var t))
      ~body_k:(w32 4)
  in
  check
    "L3c5-1: the const-first guard arm — `if (10 = t) goto …` (EQ const-first) — the cell at RBP-8 \
     is bounded (⊆ [0,10]; pinned to {10})"
    (l3c2_bounded (l3c5_run sub1 body1) (w32 10));
  (* L3c5-2: MOD has no closed form — sound stop. *)
  let sub2, body2 =
    mk_l3c5_loop ~seed:None
      ~chain:(Some (Bil.BinOp (Bil.MOD, Bil.Var t, Bil.Int (w32 8))))
      ~cond:(Bil.BinOp (Bil.SLT, Bil.Var v, Bil.Int (w32 10)))
      ~body_k:(w32 4)
  in
  check
    "L3c5-2: the Tier-3 MOD row (periodic, no closed form) is a sound stop — no refinement (the \
     cell is not a bounded set)"
    (not (l3c2_bounded (l3c5_run sub2 body2) (w32 39)));
  (* L3c5-3a: AND-identity row. *)
  let sub3a, body3a =
    mk_l3c5_loop
      ~seed:(Some (w32 0))
      ~chain:(Some (Bil.BinOp (Bil.AND, Bil.Var t, Bil.Int (w32 0xFFFFFFFF))))
      ~cond:(Bil.BinOp (Bil.SLT, Bil.Var v, Bil.Int (w32 10)))
      ~body_k:(w32 4)
  in
  check
    "L3c5-3a: the AND-identity row — `v := t AND ~0` (≡ t) — the cell at RBP-8 is bounded (⊆ [0,9])"
    (l3c2_bounded (l3c5_run sub3a body3a) (w32 9));
  (* L3c5-3b: OR-identity row. *)
  let sub3b, body3b =
    mk_l3c5_loop
      ~seed:(Some (w32 0))
      ~chain:(Some (Bil.BinOp (Bil.OR, Bil.Var t, Bil.Int (w32 0))))
      ~cond:(Bil.BinOp (Bil.SLT, Bil.Var v, Bil.Int (w32 10)))
      ~body_k:(w32 4)
  in
  check
    "L3c5-3b: the OR-identity row — `v := t OR 0` (≡ t) — the cell at RBP-8 is bounded (⊆ [0,9])"
    (l3c2_bounded (l3c5_run sub3b body3b) (w32 9));
  (* L3c5-4: Unknown cond keeps env unchanged, never asserts. *)
  let m4 = memv "l3c5_m" in
  let rsp4 = v64 "RSP" in
  let t4 = Var.create ~is_virtual:false ~fresh:false "l3c5_t" (Type.Imm 32) in
  let addr4 = Bil.BinOp (Bil.MINUS, Bil.Var rsp4, Bil.Int (w64 8)) in
  let e4 = Blk.Builder.create () in
  let h4 = Blk.Builder.create () in
  let x4 = Blk.Builder.create () in
  Blk.Builder.add_def h4 (Def.create t4 (Bil.Load (Bil.Var m4, addr4, LittleEndian, `r32)));
  let e0 = Blk.Builder.result e4 in
  let h0 = Blk.Builder.result h4 in
  let x0 = Blk.Builder.result x4 in
  let h_tid = Term.tid h0 in
  let x_tid = Term.tid x0 in
  let e4 = Blk.Builder.init ~copy_defs:true e0 in
  Blk.Builder.add_jmp e4 (Jmp.create (Goto (Direct h_tid)));
  let h4 = Blk.Builder.init ~copy_defs:true h0 in
  Blk.Builder.add_jmp h4
    (Jmp.create ~cond:(Bil.Unknown ("l3c5_unknown", Type.Imm 1)) (Goto (Direct x_tid)));
  let sub_b = Sub.Builder.create ~name:"l3c5_unknown" () in
  Sub.Builder.add_blk sub_b (Blk.Builder.result e4);
  Sub.Builder.add_blk sub_b (Blk.Builder.result h4);
  Sub.Builder.add_blk sub_b (Blk.Builder.result x4);
  let sub4 = Sub.Builder.result sub_b in
  let ctx4 = Program.create ~subs:[ sub4 ] () in
  let sol4 = Vsa.static_graph_vsa [] ctx4 sub4 (Vsa.init_sol ~entry:(anchored_entry ()) sub4) in
  let h_st4 = Graphlib.Std.Solution.get sol4 h_tid in
  let jmp4 =
    match
      Term.enum jmp_t
        (match Term.enum blk_t sub4 |> Seq.to_list with [ _; h; _ ] -> h | _ -> assert false)
      |> Seq.to_list
    with
    | [ j ] -> j
    | _ -> assert false
  in
  check
    "L3c5-4: an Unknown condition — the fixpoint completes and assume_jump_cond keeps the env \
     unchanged (the shrunk catch-all, never asserts)"
    (AI.equal (Vsa.assume_jump_cond h_st4 jmp4) h_st4);
  ())
(* Lane A: mixed-width shifts via coerce-to-max. *)
;
(  (* A-1: mixed-width rshift exact. *)
  let r1 = Clp.rshift (Clp.create (w32 0xFF)) (Clp.create (w64 2)) in
  check
    "A-1: mixed-width rshift (32-bit {0xFF} >> 64-bit {2}) is EXACTLY {0x3F} at 32 bits (no guard \
     fire)"
    (Clp.equal r1 (Clp.create (w32 0x3F)));
  (* A-2: straddling amount gives non-top non-bottom. *)
  let amt40 = Clp.create ~width:64 ~step:(w64 1) ~cardn:(W.of_int ~width:65 40) (w64 0) in
  let r2 = Clp.rshift (Clp.create (w32 1)) amt40 in
  check
    "A-2: the 252-hit shape (32-bit >> 64-bit [0,40)) — the coerced three-way split yields a \
     non-top, non-bottom result"
    ((not (Clp.is_top r2)) && (not (Clp.is_bottom r2)) && Clp.bitwidth r2 = 32);
  (* A-3: mixed-width overshift is exactly {0}. *)
  let r3 = Clp.rshift (Clp.create (w32 8)) (Clp.create (w64 40)) in
  check "A-3: mixed-width rshift overshift (32-bit >> 64-bit {40}) is EXACTLY {0} at 32 bits"
    (Clp.equal r3 (Clp.create (w32 0)));
  (* A-4: arshift sign-fills through the coercion. *)
  let r4 = Clp.arshift (Clp.create (w32 0xFFFFFFFF)) (Clp.create (w64 40)) in
  check
    "A-4: mixed-width arshift sign-fill (32-bit {all-ones} arshift 64-bit {40}) is EXACTLY \
     {all-ones} at 32 bits (the SIGN-extension)"
    (Clp.equal r4 (Clp.create (w32 0xFFFFFFFF)));
  (* A-5: antipodal equal-width overshift image. *)
  let antipodal = Clp.of_list ~width:64 [ w64 1; W.lshift (w64 1) (w64 63) ] in
  let r5 = Clp.arshift antipodal (Clp.create (w64 70)) in
  check
    "A-5: the antipodal overshift image (64-bit {1, 2^63} arshift {70}) is {0, all-ones} \
     (equal-width path, no coercion)"
    (W.to_int_exn (Clp.cardinality r5) = 2
    && Clp.elem (w64 0) r5
    && Clp.elem (W.ones 64) r5
    && (not (Clp.elem (w64 1) r5))
    && not (Clp.is_top r5));
  ())
;
(  (* S-1: traverse shape collapses to ≤ 3 cells. *)
  let sub1, body1, hdr1 = mk_l3b1_loop () in
  let ctx1 = Program.create ~subs:[ sub1 ] () in
  let sol1 =
    Vsa.static_graph_vsa [] ctx1 sub1 (Vsa.init_sol ~entry:(anchored_entry ()) sub1)
  in
  let st1 = Graphlib.Std.Solution.get sol1 body1 in
  check
    "S-1a: the traverse shape (fixture F, the seeded RMW counter) collapses to <= 3 cells in the \
     solution state (pre-fix the [RSP-8] point-key pile was 16-17 — the restored equal-lower hull \
     union)"
    (l3b_cells_of (memv "l3b1_m") st1 <= 3);
  (* Exit IN-state is the fallthrough view; body IN-state the iterate view. *)
  let exit1 =
    match Term.enum blk_t sub1 |> Seq.to_list with
    | [ _; _; _; e ] -> e
    | _ -> failwith "S-1: fixture block layout changed"
  in
  let icell = l3b1_cell_of (Graphlib.Std.Solution.get sol1 body1) in
  let ecell = l3b1_cell_of (Graphlib.Std.Solution.get sol1 (Term.tid exit1)) in
  check
    "S-1b: the partition — the iterate view's cell is the loop-body values (⊆ [0,7], non-top) and \
     the exit view's cell carries the exit-iteration value (8 survives)"
    ((not (Ws.is_top icell))
    && (not (Ws.is_bottom icell))
    && (match Ws.max_elem icell with Some w -> Word.( <= ) w (w32 7) | None -> false)
    && (not (Ws.is_top ecell))
    && Ws.elem (w32 8) ecell);
  (* S-4: +1-adjacent equal-value cells merge to one hull. *)
  let sub4, merge4 = mk_l3b4_diamond () in
  let ctx4 = Program.create ~subs:[ sub4 ] () in
  let sol4 = Vsa.static_graph_vsa [] ctx4 sub4 (Vsa.init_sol ~entry:(anchored_entry ()) sub4) in
  let st4 = Graphlib.Std.Solution.get sol4 merge4 in
  check
    "S-4a: two +1-adjacent equal-value cells ([RSP-8] and [RSP-7], both {7}) through ONE merge \
     become a SINGLE cell (the +1-adjacent arm, not shadowed by the equal-lower arm)"
    (l3b_cells_of (memv "l3b4_m") st4 = 1);
  ())
;
(  let rsp = v64 "RSP" in
  let rdi = v64 "RDI" in
  let entry_b = Blk.Builder.create () in
  let blk_b = Blk.Builder.create () in
  let cont_b = Blk.Builder.create () in
  Blk.Builder.add_def blk_b (Def.create rdi (Bil.Int (w64 42)));
  let entry0 = Blk.Builder.result entry_b in
  let blk0 = Blk.Builder.result blk_b in
  let cont0 = Blk.Builder.result cont_b in
  let blk_tid = Term.tid blk0 in
  let cont_tid = Term.tid cont0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct blk_tid)));
  let blk_b = Blk.Builder.init ~copy_defs:true blk0 in
  (* Interrupt edge: return tid ignored by the arm. *)
  Blk.Builder.add_jmp blk_b (Jmp.create (Int (0x80, cont_tid)));
  Blk.Builder.add_jmp blk_b (Jmp.create (Goto (Direct cont_tid)));
  let entry = Blk.Builder.result entry_b in
  let blk = Blk.Builder.result blk_b in
  let cont = Blk.Builder.result cont_b in
  let sub_b = Sub.Builder.create ~name:"l37_intr" () in
  Sub.Builder.add_blk sub_b entry;
  Sub.Builder.add_blk sub_b blk;
  Sub.Builder.add_blk sub_b cont;
  let sub = Sub.Builder.result sub_b in
  let ctx = Program.create ~subs:[ sub ] () in
  let sol = Vsa.static_graph_vsa [] ctx sub (Vsa.init_sol ~entry:(anchored_entry ()) sub) in
  let cont_st = Graphlib.Std.Solution.get sol cont_tid in
  check
    "B-1: an interrupt edge is an unknown external callee — the continuation keeps the RSP anchor \
     ({0}) and the caller-saved rdi is topped (no AI.top degradation)"
    (Ws.equal (AI.find_word 64 cont_st rsp) (Ws.singleton (w64 0))
    && Ws.is_top (AI.find_word 64 cont_st rdi));
  ())
;
(  (* L-B1: jle corpus shape — decoder emits SLE. *)
  let sub1, body1 =
    mk_l39_loop ~seed:(w32 0) ~c:(w32 3) ~body_op:Bil.PLUS ~body_k:(w32 1)
      ~mk_cond:(fun ~cf:_ ~ofv ~sf ~zf -> l39_jle zf sf ofv)
      ~extra_header_defs:(fun _ -> [])
  in
  check
    "L-B1: the exact -O0 corpus block (t := Load-3; CF/SF/OF/ZF defs; the jle compound guard `ZF | \
     (SF|OF) & ~(SF&OF)`) — the jcc decoder recovers the loop-counter constraint (SLE, c=3, gated) \
     and the cell at RBP-8 is bounded (⊆ [0, 4))"
    (l39_bounded (l39_run sub1 body1) (w32 3));
  (* L-B2: jl shape — decoder emits SLT. *)
  let sub2, body2 =
    mk_l39_loop ~seed:(w32 0) ~c:(w32 3) ~body_op:Bil.PLUS ~body_k:(w32 1)
      ~mk_cond:(fun ~cf:_ ~ofv ~sf ~zf:_ -> l39_jl sf ofv)
      ~extra_header_defs:(fun _ -> [])
  in
  check
    "L-B2: the jl compound guard `(SF|OF) & ~(SF&OF)` (signed e < c — excludes equality) — the \
     decoder emits SLT and the cell at RBP-8 is bounded (⊆ [0, 3))"
    (l39_bounded (l39_run sub2 body2) (w32 2));
  (* L-B3: ja shape — decoder emits UGT; decrementing counter converges. *)
  let sub3, body3 =
    mk_l39_loop ~seed:(w32 8) ~c:(w32 3) ~body_op:Bil.MINUS ~body_k:(w32 1)
      ~mk_cond:(fun ~cf ~ofv:_ ~sf:_ ~zf -> l39_ja cf zf)
      ~extra_header_defs:(fun _ -> [])
  in
  let cell3 = l39_run sub3 body3 in
  check
    "L-B3: the ja compound guard `~(CF | ZF)` (unsigned e > c) — the decoder emits UGT (c=3 -> [4, \
     2^w)) and the decrementing counter converges inside the constraint: the cell at RBP-8 has \
     min_elem >= 4 and is not top"
    ((not (Ws.is_top cell3))
    && (not (Ws.is_bottom cell3))
    && match Ws.min_elem cell3 with Some w -> Word.( >= ) w (w32 4) | None -> false);
  (* L-B4: second cmp makes the gate reject the mixed group. *)
  let sub4, body4 =
    let f = Var.create ~is_virtual:false ~fresh:false "l39_f" (Type.Imm 32) in
    let t2 = Var.create ~is_virtual:false ~fresh:false "l39_t2" (Type.Imm 32) in
    let of2 = v1 "OF" in
    let sf2 = v1 "SF" in
    let zf2 = v1 "ZF" in
    mk_l39_loop ~seed:(w32 0) ~c:(w32 3) ~body_op:Bil.PLUS ~body_k:(w32 1)
      ~mk_cond:(fun ~cf:_ ~ofv:_ ~sf:_ ~zf:_ -> l39_jle zf2 sf2 of2)
      ~extra_header_defs:(fun m ->
        let rsp2 = v64 "RSP" in
        let addr2 = Bil.BinOp (Bil.MINUS, Bil.Var rsp2, Bil.Int (w64 16)) in
        let f_load = Bil.Load (Bil.Var m, addr2, LittleEndian, `r32) in
        [
          Def.create f f_load;
          Def.create t2 (Bil.BinOp (Bil.MINUS, f_load, Bil.Int (w32 5)));
          Def.create of2
            (Bil.Cast
               ( Bil.HIGH,
                 1,
                 Bil.BinOp
                   ( Bil.AND,
                     Bil.BinOp (Bil.XOR, Bil.Var f, Bil.Int (w32 5)),
                     Bil.BinOp (Bil.XOR, Bil.Var f, Bil.Var t2) ) ));
          Def.create sf2 (Bil.Cast (Bil.HIGH, 1, Bil.Var t2));
          Def.create zf2 (Bil.BinOp (Bil.EQ, Bil.Int (w32 0), Bil.Var t2));
        ])
  in
  check
    "L-B4: the same-comparison gate — a second cmp in the header (a dead-CF-eliminated \
     t2/OF2/SF2/ZF2 group referencing t2 := f - 5) makes the gate reject the mixed group — NO \
     decoder refinement (the cell stays top)"
    (Ws.is_top (l39_run sub4 body4));
  (* L-B5: record path survives (flag-state arm regression guard). *)
  let sub5, body5 = mk_l39b5_loop () in
  check
    "L-B5: the RECORD path (bare `when CF` with CF := v < 3, v := Load[RBP-8] unique) survives the \
     L-A2 wiring — the flag-state arm + the walk still refine the cell at RBP-8 (⊆ [0, 3))"
    (l39_bounded (l39_run sub5 body5) (w32 2));
  ())
(* L-D2: wide-bound pin — counter crosses widening before converging. *)
;
(  (* L-D2: c=63 ascending counter needs the relaxed gate. *)
  let sub, body =
    mk_l39_loop ~seed:(w32 0) ~c:(w32 63) ~body_op:Bil.PLUS ~body_k:(w32 1)
      ~mk_cond:(fun ~cf:_ ~ofv ~sf ~zf -> l39_jle zf sf ofv)
      ~extra_header_defs:(fun _ -> [])
  in
  check
    "L-D2: the WIDE-BOUND corpus shape (c=63, ascending counter seeded 0, crossing the i>10 \
     widening threshold) — the L-D1 gate-relaxed refinement (provably_nonneg_operand proving the \
     cell non-negative via the seed store) bounds the cell at RBP-8 (⊆ [0, 64), max ≤ 63) — FAILS \
     pre-L-D1 (the SLE gate rejects the widened infinite CLP, the cell stays top)"
    (l39_bounded (l39_run sub body) (w32 63));
  ())
;
(  (* E1-1: call-in-loop header RSP stays exactly {0x1000}. *)
  let sub, header_tid, rsp = mk_e1_loop_sub () in
  let rsp_hdr = e1_rsp_at sub header_tid rsp in
  check
    "E1-1: call-in-loop RSP stability — the ON-path matched-pair +8 (the callee's ret pops exactly \
     the retaddr the caller pushed) keeps the header RSP at EXACTLY the pre-push {0x1000} \
     (bounded, no drift — FAILS pre-L-E1: the header joins {−8k}/iteration and the i>10 widening \
     makes the infinite descending CLP)"
    (Ws.equal rsp_hdr (Ws.singleton (w64 0x1000)));
  (* E1-2: straight-line continuation RSP is exactly {0x2000}. *)
  let sub, post_tid, rsp = mk_e1_flat_sub () in
  let rsp_post = e1_rsp_at sub post_tid rsp in
  check
    "E1-2: straight-line call RSP exactness — the continuation RSP is EXACTLY the pre-call \
     singleton {0x2000} (truth, not truth−8 = {0x1ff8} — FAILS pre-L-E1)"
    (Ws.equal rsp_post (Ws.singleton (w64 0x2000)));
  ())
;
(  let sub, body = mk_l6_rbp_loop () in
  check
    "L-D6 (gate-free, spec §2.1): the RBP-anchored loop (prologue RBP := RSP + the c=63 jle \
     loop at RBP−8 + the dead epilogue RBP := mem[RSP]) — every def is denoted, so the jcc \
     decoder's cell meet binds the cell at RBP−8 to ⊆ [0, 64) at the BODY input"
    (l39_bounded (l6_run sub body) (w32 63));
  ())
;
(  (* R2-1: inline-arithmetic chain refines to the 64-element hull. *)
  let sub1, body1 =
    mk_r2_loop ~seed:(w32 0) ~seed2:None ~body_op:Bil.PLUS ~body_k:(w32 1) ~mk_cond:(fun ~t ->
        Bil.BinOp (Bil.LT, Bil.BinOp (Bil.PLUS, Bil.Var t, Bil.Int (w32 1)), Bil.Int (w32 64)))
  in
  let cell1 = r2_run sub1 body1 in
  check
    "R2-1: the INLINE-ARITHMETIC condition `(t+1) < 64` (the compared exp is BinOp PLUS of t := \
     Load[RBP-8]) — the producer-op recursion refines the (t+1) chain (guard row -> [0,64) on \
     (t+1) -> the PLUS row's circular hull {−1} ∪ [0, 62] on t -> the Var -> refine_backward -> \
     refine_cell) and the cell at RBP−8 is the 64-element hull (⊆ {−1} ∪ [0, 64); cardn 64; no \
     middle value — FAILS pre-refactor: the chain unrefined, the cell stays the full domain/top)"
    ((not (Ws.is_top cell1))
    && (not (Ws.is_bottom cell1))
    && Word.( <= ) (Ws.cardinality cell1) (Word.of_int ~width:33 64)
    && not (Ws.elem (w32 100) cell1));
  (* R2-2: NOT-edge keeps env — cell not narrowed to TRUE-edge window. *)
  let sub2, body2 =
    mk_r2_loop ~seed:(w32 3)
      ~seed2:(Some (w32 8))
      ~body_op:Bil.PLUS ~body_k:(w32 1)
      ~mk_cond:(fun ~t -> Bil.UnOp (Bil.NOT, Bil.BinOp (Bil.LT, Bil.Var t, Bil.Int (w32 5))))
  in
  let cell2 = r2_run sub2 body2 in
  check
    "R2-2: NOT-of-comparison `~(t < 5)` (the taken edge = t ≥ 5, the two-path seed cell {3, 8}) — \
     the comparison-operand keep-env gate (the FALSE-edge guard) leaves the cell UNSHARPENED by \
     the TRUE-edge row [0, 5): NOT bounded ⊆ [0, 4] (it is top/unbounded) — with the gate removed \
     the wrong window drops the live values (the cell wrongly ⊆ [0, 4])"
    (not (l39_bounded cell2 (w32 4)));
  (* R2-3: const-first LT flip — decrementing counter converges in [11, 2^w). *)
  let sub3, body3 =
    mk_r2_loop ~seed:(w32 20) ~seed2:None ~body_op:Bil.MINUS ~body_k:(w32 1) ~mk_cond:(fun ~t ->
        Bil.BinOp (Bil.LT, Bil.Int (w32 10), Bil.Var t))
  in
  let cell3 = r2_run sub3 body3 in
  check
    "R2-3: the CONST-FIRST LT flip `10 < t` (Bil.BinOp (Bil.LT, Bil.Int 10, t)) — the flip (ora-9 \
     Item 1(d)) dispatches on the guard_op enum (UGT): t > 10 unsigned -> [11, 2^w) and the \
     DECREMENTING counter converges inside the constraint (non-top, min_elem ≥ 11) — FAILS on the \
     current tree: the landed const-first arm is the EQ-only equivalence (LT const-first is still \
     a sound stop), so the cell goes top"
    ((not (Ws.is_top cell3))
    && (not (Ws.is_bottom cell3))
    && match Ws.min_elem cell3 with Some w -> Word.( >= ) w (w32 11) | None -> false);
  (* R2-4: nested TIMES chain — inline walk bounds the operand, exact slice fires. *)
  let sub4, body4 =
    mk_r2_loop ~seed:(w32 63) ~seed2:None ~body_op:Bil.PLUS ~body_k:(w32 1) ~mk_cond:(fun ~t ->
        Bil.BinOp (Bil.LT, Bil.BinOp (Bil.TIMES, Bil.Var t, Bil.Int (w32 8)), Bil.Int (w32 512)))
  in
  check
    "R2-4 (migrated, single-pass §2): the NESTED-BinOp chain `(t * 8) < 512` — the inline walk \
     bounds the operand, the exact TIMES no-wrap slice fires, and the body-IN cell is the EXACT \
     singleton {63} (the loop exits at t = 64; 63 ∈, 62 ∉, 64 ∉; non-top)"
    (let cell = r2_run sub4 body4 in
     (* Body-IN cell is the exact singleton {63}. *)
     (not (Ws.is_top cell))
     && (not (Ws.is_bottom cell))
     && Ws.equal cell (Ws.singleton (w32 63)));
  ())
(* M5: complete-rule pins — one per rule. *)
;
(  let t = Var.create ~is_virtual:false ~fresh:false "l3c3_t" (Type.Imm 32) in
  (* M5-1: MINUS wrap hull. *)
  let sub1, body1 =
    mk_l3c3_loop ~seed:None
      ~chain:(Bil.BinOp (Bil.MINUS, Bil.Var t, Bil.Int (w32 0xFFFFFFFF)))
      ~cmp:Bil.LT ~c:(w32 5) ~body_k:(w32 4)
  in
  let cell1 = l3c3_run sub1 body1 in
  check
    "M5-1: the MINUS wrap hull — `v := t − ~0; if (v < 5)` refines the cell to the wrapped \
     {0xFFFFFFFF, 0..3} (cardn 5; 0xFFFFFFFF ∈; 0 ∈; the wrap was handled, not emptied)"
    ((not (Ws.is_top cell1))
    && (not (Ws.is_bottom cell1))
    && Word.( = ) (Ws.cardinality cell1) (Word.of_int ~width:33 5)
    && Ws.elem (w32 0xFFFFFFFF) cell1
    && Ws.elem (w32 0) cell1
    && not (Ws.elem (w32 4) cell1));
  (* M5-2: TIMES k = 0 is the identity. *)
  let sub2, body2 =
    mk_l3c3_loop ~seed:None
      ~chain:(Bil.BinOp (Bil.TIMES, Bil.Var t, Bil.Int (w32 0)))
      ~cmp:Bil.EQ ~c:(w32 0) ~body_k:(w32 4)
  in
  let cell2 = l3c3_run sub2 body2 in
  check
    "M5-2: the TIMES k=0 rule is the identity — `v := t * 0; if EQ(v, 0)` leaves the cell \
     unconstrained (top)"
    (Ws.is_top cell2);
  (* M5-3: XOR-~0 bijection. *)
  let sub3, body3 =
    mk_l3c3_loop ~seed:None
      ~chain:(Bil.BinOp (Bil.XOR, Bil.Var t, Bil.Int (w32 0xFFFFFFFF)))
      ~cmp:Bil.EQ ~c:(w32 5) ~body_k:(w32 4)
  in
  let cell3 = l3c3_run sub3 body3 in
  check
    "M5-3: the XOR-~0 bijection — `v := t XOR ~0; if EQ(v, 5)` refines the cell to {~5} = \
     {0xFFFFFFFA} (0xFFFFFFFA ∈, 5 ∉)"
    ((not (Ws.is_top cell3)) && Ws.elem (w32 0xFFFFFFFA) cell3 && not (Ws.elem (w32 5) cell3));
  (* M5-4: LOW cast in the walk — truncation hull. *)
  let t4 = Var.create ~is_virtual:false ~fresh:false "l3c4_t" (Type.Imm 32) in
  let sub4, body4 =
    mk_l3c4_loop ~seed:None
      ~chain:(Bil.Cast (Bil.LOW, 8, Bil.Var t4))
      ~v_w:8 ~cmp:Bil.EQ ~c:(Word.of_int ~width:8 5) ~body_k:(w32 4)
  in
  let cell4 = l3c4_run sub4 body4 in
  check
    "M5-4: the LOW-cast rule in the walk — `v := cast LOW 8 t; if EQ(v, 5)` bounds the cell to the \
     truncation hull [5, 0xFFFFFF05] (5 ∈, 5+0x100 ∈, 4 ∉)"
    ((not (Ws.is_top cell4))
    && (not (Ws.is_bottom cell4))
    && Ws.elem (w32 5) cell4
    && Ws.elem (w32 0x105) cell4
    && (not (Ws.elem (w32 4) cell4))
    && match Ws.max_elem cell4 with Some w -> Word.( <= ) w (w32 0xFFFFFF05) | None -> false);
  (* M5-5: signed-division rule. *)
  let sub5, body5 =
    mk_l3c3_loop ~seed:None
      ~chain:(Bil.BinOp (Bil.SDIVIDE, Bil.Var t, Bil.Int (w32 2)))
      ~cmp:Bil.EQ ~c:(w32 0xFFFFFFFD) ~body_k:(w32 4)
  in
  let cell5 = l3c3_run sub5 body5 in
  check
    "M5-5: the signed-division rule — `v := t sdiv 2; if EQ(v, −3)` refines the cell to {−6, −5} \
     (0xFFFFFFFA ∈, 0xFFFFFFFB ∈, −3 ∉)"
    ((not (Ws.is_top cell5))
    && (not (Ws.is_bottom cell5))
    && Ws.elem (w32 0xFFFFFFFA) cell5
    && Ws.elem (w32 0xFFFFFFFB) cell5
    && not (Ws.elem (w32 0xFFFFFFFD) cell5));
  (* M5-6: Var-identity row propagates through the copy. *)
  let t_id = Var.create ~is_virtual:false ~fresh:false "l3c3_t" (Type.Imm 32) in
  let sub6, body6 =
    mk_l3c3_loop
      ~seed:(Some (w32 0))
      ~chain:(Bil.Var t_id)
      ~cmp:Bil.LT ~c:(w32 10) ~body_k:(w32 1)
  in
  let cell6 = l3c3_run sub6 body6 in
  check
    "M5-6: the Var-identity rule — `v := t; if (v < 10)` — the walk propagates the [0,10) window      through the identity to the loaded cell (the body-IN cell is bounded ≤ [0,9] — the store-only      join would be [0,10])"
    (l3c2_bounded cell6 (w32 9));
  ())
