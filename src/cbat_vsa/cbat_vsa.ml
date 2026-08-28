(* ************************************************************************* *)
(*  *)
(* Copyright (C) Draper Laboratory. Licensed under project LICENSE. *)
(*  *)
(* This file is provided under the license found in the LICENSE file in *)
(* the top-level directory of this project. *)
(*  *)
(* This work is funded in part by ONR/NAWC Contract N6833518C0107. Its *)
(* content does not necessarily reflect the position or policy of the US *)
(* Government and no official endorsement should be inferred. *)
(*  *)
(* ************************************************************************* *)

include Core_kernel
open Bap.Std
open Graphlib.Std
open Cbat_vsa_utils

module CG = Graphs.Callgraph
module CFG = Graphs.Tid

module AI = Cbat_ai_representation
module WordSet = Cbat_clp_set_composite
module Mem = Cbat_ai_memmap
module Word_ops = Cbat_word_ops
module Utils = Cbat_vsa_utils
module Back_edges = Cbat_back_edges

(* Bourdoncle WTO — inlined from cbat_wto.ml to avoid separate-file merlin config. *)
module Wto = struct
  type comp =
    | Vertex of Tid.t
    | SCC of Tid.t * comp list

  let rec flatten_comps (cs : comp list) : Tid.t list =
    List.concat_map cs ~f:(function
        | Vertex v -> [v]
        | SCC (h, inner) -> h :: flatten_comps inner)

  let rec heads_of_comps (cs : comp list) : Tid.Set.t =
    List.fold cs ~init:Tid.Set.empty ~f:(fun acc -> function
        | Vertex _ -> acc
        | SCC (h, inner) ->
          let acc = Core.Set.add acc h in
          Core.Set.union acc (heads_of_comps inner))

  let rec pp_comp (fmt : Format.formatter) (c : comp) : unit =
    match c with
    | Vertex v -> Format.fprintf fmt "%s" (Tid.to_string v)
    | SCC (h, inner) ->
      Format.fprintf fmt "(%s %a)" (Tid.to_string h)
        (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt " ") pp_comp) inner

  let scc_partition
      (nodes : Tid.t list)
      (succ : Tid.t -> Tid.t list)
      (pred : Tid.t -> Tid.t list)
    : Tid.t list list =
    let node_set = Tid.Set.of_list nodes in
    let visited = ref Tid.Set.empty in
    let order = ref [] in
    let rec dfs1 (n : Tid.t) : unit =
      if not (Core.Set.mem !visited n) then begin
        visited := Core.Set.add !visited n;
        List.iter (succ n) ~f:(fun m ->
            if Core.Set.mem node_set m then dfs1 m);
        order := n :: !order
      end
    in
    List.iter nodes ~f:dfs1;
    let visited2 = ref Tid.Set.empty in
    let comps = ref [] in
    List.iter !order ~f:(fun n ->
        if not (Core.Set.mem !visited2 n) then begin
          let cur = ref [] in
          let rec dfs2 (x : Tid.t) : unit =
            if not (Core.Set.mem !visited2 x) then begin
              visited2 := Core.Set.add !visited2 x;
              cur := x :: !cur;
              List.iter (pred x) ~f:(fun p ->
                  if Core.Set.mem node_set p then dfs2 p)
            end
          in
          dfs2 n;
          comps := !cur :: !comps
        end);
    !comps

  let wto_of_cfg (cfg : Graphs.Tid.t) : comp list =
    let all_nodes = Graphs.Tid.nodes cfg |> Seq.to_list in
    if List.is_empty all_nodes then [] else
      let succ_all (n : Tid.t) : Tid.t list =
        Graphs.Tid.Node.succs n cfg |> Seq.to_list in
      let pred_all (n : Tid.t) : Tid.t list =
        Graphs.Tid.Node.preds n cfg |> Seq.to_list in
      let rpo_index : (Tid.t, int) Hashtbl.t = Hashtbl.create (module Tid) in
      begin
        let visited = ref Tid.Set.empty in
        let order = ref [] in
        let rec dfs (n : Tid.t) : unit =
          if not (Core.Set.mem !visited n) then begin
            visited := Core.Set.add !visited n;
            List.iter (succ_all n) ~f:dfs;
            order := n :: !order
          end
        in
        List.iter all_nodes ~f:dfs;
        List.iteri !order ~f:(fun i n -> Hashtbl.set rpo_index ~key:n ~data:i)
      end;
      let get_rpo (n : Tid.t) : int =
        Hashtbl.find rpo_index n |> Option.value ~default:Int.max_value in
      let has_self_loop (n : Tid.t) : bool =
        List.mem (succ_all n) n ~equal:Tid.equal in
      let rec wto_rec (nodes : Tid.t list) : comp list =
        if List.is_empty nodes then [] else
          let node_set = Tid.Set.of_list nodes in
          let succ (n : Tid.t) : Tid.t list =
            List.filter (succ_all n) ~f:(fun m -> Core.Set.mem node_set m) in
          let pred (n : Tid.t) : Tid.t list =
            List.filter (pred_all n) ~f:(fun m -> Core.Set.mem node_set m) in
          let sccs = scc_partition nodes succ pred in
          let sccs_sorted =
            List.sort sccs ~compare:(fun a b ->
                let ma = List.map a ~f:get_rpo |> List.min_elt ~compare:Int.compare |> Option.value ~default:Int.max_value in
                let mb = List.map b ~f:get_rpo |> List.min_elt ~compare:Int.compare |> Option.value ~default:Int.max_value in
                Int.compare ma mb) in
          List.concat_map sccs_sorted ~f:(fun scc ->
              match scc with
              | [v] when not (has_self_loop v) -> [Vertex v]
              | _ ->
                let head =
                  List.min_elt scc ~compare:(fun a b -> Int.compare (get_rpo a) (get_rpo b))
                  |> Option.value_exn in
                let rest = List.filter scc ~f:(fun n -> not (Tid.equal n head)) in
                let inner = wto_rec rest in
                [SCC (head, inner)])
      in
      wto_rec all_nodes
end
module Cbat_wto = Wto

(* Raised by [static_graph_vsa] when the fixpoint's verification round finds the solution STILL CHANGING at the [~steps] cap — the returned solution would be an under-approximation (states reachable only on longer paths are missing), so it must not be consumed for the narrow-tag decisions. *)
exception Fixpoint_not_converged of int * (tid, AI.t) Solution.t
  * (tid * tid) option

(* [addr_bits_ref]: The program architecture's address size in bits (O1 — the Target-derived width, set by the production pass via [set_addr_bits] at project setup; 0 = not set, the BIL type's size is the fallback (unit tests run without a target). *)
let addr_bits_ref = ref 0
let set_addr_bits (n : int) : unit = addr_bits_ref := n

(* [mem_idx addr_sz addressable_sz]: The memory index of a memory type — the {addr_width; addressable_width} record built at every memory access site. *)
let mem_idx addr_sz addressable_sz : Mem.idx =
  { Mem.addr_width =
      (if !addr_bits_ref > 0 then !addr_bits_ref else Size.in_bits addr_sz);
    Mem.addressable_width = Size.in_bits addressable_sz }

(* a tag used in the analysis to indicate when to widen a precondition state *)
let do_widen = Value.Tag.register (module Unit)
    ~name:"widen state on recompute"
    ~uuid:"a8050d49-f451-4684-afbd-97c013dd8e4d"

let jmp_target (j : jmp term) : tid option =
  let mlbl = match Jmp.kind j with
    | Call c -> Some (Call.target c)
    | Goto lbl
    | Ret lbl -> Some lbl
    | Int _ -> None in
  Option.bind mlbl ~f:begin fun lbl ->
    match lbl with
    | Direct tid -> Some tid
    | Indirect _ -> None
  end

let label_widening_points (sub : sub term) : sub term =
  let open Monads.Std.Monad.Option.Syntax in
  Term.enum blk_t sub
  |> Seq.concat_map ~f:(Term.enum jmp_t)
  |> Seq.fold ~init:sub ~f:begin fun sub jmp ->
    if Term.has_attr jmp Back_edges.back_edge then
      Option.value ~default:sub begin
        Term.get_attr jmp Back_edges.back_edge >>= fun () ->
        jmp_target jmp >>= fun tid ->
        let set_do_widen blk = Term.set_attr blk do_widen () in
        !!(Term.change blk_t sub tid (Option.map ~f:set_do_widen))
      end
    else sub
  end

type wordset = WordSet.t


(* Denotations ========================================================= These functions are denotations of terms in BIR *)


(* bitwidth is the width of the two inputs *)
let denote_binop (op : Bil.binop) : wordset -> wordset -> wordset =
  let btrue = WordSet.singleton Word.b1 in
  let bfalse = WordSet.singleton Word.b0 in
  let wordset_of_bool b = if b then btrue else bfalse in
  let bool_top = WordSet.top 1 in
  let bool_bottom = WordSet.bottom 1 in
  (* [ordering ~signed ~le v1 v2]: The four ordering-comparison denotations (LT/LE/SLT/SLE) share one endpoint test — if every element of v1 orders below every element of v2 the result is definitely true, if v1's minimum does not order below v2's maximum. *)
  let ordering ~(signed : bool) ~(le : bool) v1 v2 =
    let open Monads.Std.Monad.Option in
    let max_elem = if signed then WordSet.max_elem_signed else WordSet.max_elem in
    let min_elem = if signed then WordSet.min_elem_signed else WordSet.min_elem in
    let sgn = if signed then Word.signed else Fun.id in
    Option.value ~default:bool_top begin
      max_elem v1 >>= fun v1_max ->
      min_elem v1 >>= fun v1_min ->
      max_elem v2 >>= fun v2_max ->
      min_elem v2 >>= fun v2_min ->
      if le then
        if Word.(<=) (sgn v1_max) (sgn v2_min) then return btrue
        else if Word.(>) (sgn v1_min) (sgn v2_max) then return bfalse
        else return bool_top
      else
        if Word.(<) (sgn v1_max) (sgn v2_min) then return btrue
        else if Word.(>=) (sgn v1_min) (sgn v2_max) then return bfalse
        else return bool_top
    end in
  (* [compare_eq ~negate v1 v2]: The shared EQ/NEQ decision — if either expression has no value, neither does the comparison result (bottom); two singletons are definitely-equal (or not); non-singletons that overlap may be true or false, disjoint non-singletons are definitely-false (EQ) / true (NEQ). *)
  let compare_eq ~(negate : bool) v1 v2 =
    let v1Size = WordSet.cardinality v1 in
    let v2Size = WordSet.cardinality v2 in
    if Word.is_zero v1Size || Word.is_zero v2Size then bool_bottom
    else if Word_ops.is_one v1Size && Word_ops.is_one v2Size then
      wordset_of_bool
        (if negate then not (WordSet.equal v1 v2) else WordSet.equal v1 v2)
    else if WordSet.overlap v1 v2 then bool_top
    else if negate then btrue else bfalse
  in
  match op with
  | Bil.PLUS -> WordSet.add
  | Bil.MINUS -> WordSet.sub
  | Bil.TIMES -> WordSet.mul
  | Bil.LSHIFT -> WordSet.lshift
  | Bil.RSHIFT -> WordSet.rshift
  | Bil.ARSHIFT -> WordSet.arshift
  | Bil.DIVIDE -> WordSet.div
  | Bil.SDIVIDE -> WordSet.sdiv
  | Bil.MOD -> WordSet.modulo
  | Bil.SMOD -> WordSet.smodulo
  | Bil.AND -> WordSet.logand
  | Bil.OR -> WordSet.logor
  | Bil.XOR -> WordSet.logxor
  | Bil.EQ -> compare_eq ~negate:false
  | Bil.NEQ -> compare_eq ~negate:true
  | Bil.LT -> ordering ~signed:false ~le:false
  | Bil.LE -> ordering ~signed:false ~le:true
  | Bil.SLT -> ordering ~signed:true ~le:false
  | Bil.SLE -> ordering ~signed:true ~le:true

type val_t = [`Mem of Mem.t | `Word of wordset]

module Monad_type_error = Monads.Std.Monad.Result.Make(Type.Error)(Monads.Std.Monad.Ident)
type 'a or_type_error = ('a, Type.error) Result.t

let val_as_mem (v : val_t) : Mem.t or_type_error =
  match v with
  | `Mem m -> Ok m
  | `Word _ -> Error Type.Error.bad_mem

let val_as_imm (v : val_t) : wordset or_type_error =
  match v with
  | `Word p -> Ok p
  | `Mem _ -> Error Type.Error.bad_imm

let val_join (v1 : val_t) (v2 : val_t) : val_t or_type_error =
  let open Monad_type_error in
  match v1 with
  | `Word p1 -> val_as_imm v2 >>= fun p2 -> return @@ `Word (WordSet.join p1 p2)
  | `Mem m1 -> val_as_mem v2 >>= fun m2 -> return @@ `Mem (Mem.join m1 m2)

let val_top : typ -> val_t = function
  | Type.Imm i -> `Word (WordSet.top i)
  | Type.Mem (addr_sz, addressable_sz) ->
    let k = mem_idx addr_sz addressable_sz in
    `Mem (Mem.top k)
  | Type.Unk -> failwith "Error in val_top: typ is not representable by Type.t"

(* ------------------------------------------------------------------ *)
(* Frame-relation facts (hike port: WYSINWYX-1 — the a-priori frame. *)
(* relation, stage 1). *)
(*  *)
(* [frame_facts_of_sub] derives, per block, the FRAME-DERIVED *)
(* registers: registers provably equal to the frame origin (the *)
(* sub's entry RSP) plus a constant plus a linear combination of *)
(* non-derived registers. The relation is DERIVED from the def chain *)
(* (syntactic — a def [RBP := RSP ± k] earns RBP frame-base status; *)
(* a GPR RBP gets nothing) and is a MUST-fact over paths (a register *)
(* is derived at a block only when every path reaching it derived *)
(* the same expression shape — a clobber on any path clears it below *)
(* the join). *)
(*  *)
(* The transfer mirrors the value-tracking of the fixpoint exactly: *)
(* untagged defs are skipped (the same gate as [denote_def]), and a *)
(* call restores RSP's offset by +8 (the retaddr pop — the L-E1 *)
(* matched-pair semantics, restated syntactically). *)
(*  *)
(* Consumption: [rewrite_addr] rewrites a Load/Store address [X + c] *)
(* (X derived, singleton const) into the equivalent OFFSET expression, *)
(* so memory keys become base-independent (WYSINWYX a-loc unification: *)
(* [rbp+c1] and [rsp+c2] hitting the same slot land on the same key *)
(* whenever the relation is derived). With the entry origin (0) the *)
(* rewritten key is set-equal to the direct key (byte-identical); *)
(* with the production top entry it stays exact while RSP's *)
(* value-set is top — the base-independence property the probe's *)
(* anchored-vs-default invariance check asserts. *)
(*  *)
(* Soundness surface: the facts must mirror the value tracking EXACTLY *)
(* (same defs — the relevance gate — same arithmetic); a divergence *)
(* would make normalized keys disagree with direct keys (unsound). *)
(* The singleton-const gate in [expr_of_term] is the safety margin: a *)
(* non-singleton const (a join of differing prologue paths) falls *)
(* back to the direct key instead of risking a mismatch. *)

(* [apply_frame_def f d]: The effect of one def on the per-block facts. *)
let apply_frame_def_list (f : AI.frame) (d : def term) : AI.frame =
  if not (Term.has_attr d Utils.relevant) then f
  else
    let v = AI.frame_key (Def.lhs d) in
    let remove = AI.frame_remove f v in
    (* [transfer ~shift y]: [v] inherits [y]'s fact shifted by [shift] (when y = v the fact is shifted in place); an absent fact removes. The copy rule shared by every BinOp arm. *)
    let transfer ~(shift : AI.frame_term -> AI.frame_term) (y : var)
        : AI.frame =
      if Var.equal y v then
        match AI.frame_lookup f v with
        | Some t -> AI.frame_set f v (shift t)
        | None -> remove
      else
        match AI.frame_lookup f y with
        | Some t -> AI.frame_set f v (shift t)
        | None -> remove in
    (* [if_not_derived z ~shift y]: the z-gate of the two-var arms — a derived [z] would double-count the origin, so [v] is removed; otherwise the transfer. *)
    let if_not_derived (z : var)
        ~(shift : AI.frame_term -> AI.frame_term) (y : var) : AI.frame =
      if Option.is_some (AI.frame_lookup f z) then remove
      else transfer ~shift y in
    match Def.rhs d with
    | Bil.Var y ->
      let y = AI.frame_key y in
      if Var.equal y v then f
      else (match AI.frame_lookup f y with
          | Some t -> AI.frame_set f v t
          | None -> remove)
    | Bil.Int _ -> remove
    | Bil.BinOp (op, e1, e2) ->
      (match op, e1, e2 with
       | Bil.PLUS, Bil.Var y, Bil.Int k
       | Bil.PLUS, Bil.Int k, Bil.Var y
       | Bil.MINUS, Bil.Var y, Bil.Int k ->
         (* v := y ± k: derived iff y derived *)
         let y = AI.frame_key y in
         let shift =
           match op with
           | Bil.PLUS -> fun t -> AI.frame_add_const t (WordSet.singleton k)
           | Bil.MINUS -> fun t -> AI.frame_sub_const t (WordSet.singleton k)
           | _ -> Fun.id in
         transfer ~shift y
       | Bil.PLUS, Bil.Var y, Bil.Var z ->
         (* v := y + z (both orders): derived iff y derived and z NOT derived (a derived z would double-count the origin). *)
         let y = AI.frame_key y in
         let z = AI.frame_key z in
         if_not_derived z ~shift:(fun t -> AI.frame_add_fvar t z 1) y
       | Bil.MINUS, Bil.Var y, Bil.Var z ->
         (* v := y - z: derived iff y derived and z NOT derived. *)
         let y = AI.frame_key y in
         let z = AI.frame_key z in
         if_not_derived z ~shift:(fun t -> AI.frame_add_fvar t z (-1)) y
       | Bil.PLUS, Bil.Var y, BinOp (Bil.TIMES, Bil.Var z, Bil.Int k)
       | Bil.PLUS, BinOp (Bil.TIMES, Bil.Var z, Bil.Int k), Bil.Var y ->
         (* v := y + z*k (the -O0 scaled-index shape): derived iff y derived and z NOT derived (z's scale enters the offset). *)
         let k = match Word.to_int k with Ok n -> n | Error _ -> 0 in
         let y = AI.frame_key y in
         let z = AI.frame_key z in
         if_not_derived z ~shift:(fun t -> AI.frame_add_fvar t z k) y
       | Bil.MINUS, Bil.Var y, BinOp (Bil.TIMES, Bil.Var z, Bil.Int k) ->
         (* v := y - z*k: derived iff y derived and z NOT derived. *)
         let k = match Word.to_int k with Ok n -> n | Error _ -> 0 in
         let y = AI.frame_key y in
         let z = AI.frame_key z in
         if_not_derived z ~shift:(fun t -> AI.frame_add_fvar t z (-k)) y
       | _ -> remove)
    | Bil.Load _ | Bil.Store _ | Bil.Cast _ | Bil.Extract _
    | Bil.Concat _ | Bil.Ite _ | Bil.UnOp _ | Bil.Let _ | Bil.Unknown _ ->
      remove

(* [apply_frame_def f d]: The transfer over the option — None (the BOTTOM state, vacuously everything derived) stays bottom (the LUB identity); Some f advances via [apply_frame_def_list]. *)
let apply_frame_def (f : AI.frame option) (d : def term) : AI.frame option =
  match f with
  | None -> None
  | Some f -> Some (apply_frame_def_list f d)

(* NOTE (dual address space REMOVED): the WYSINWYX-2 stack-space rebase (stack keys rebased into [2^63, 2^64), disjoint from the concrete keys) was removed — the analysis keys the SINGLE raw space: the frame-relative. *)

(* [expr_of_term t k]: The offset expression for a derived register plus an additive literal [k] — a BIL expression denoting the offset-from-origin word set. *)
let expr_of_term (t : AI.frame_term) (k : word) : exp option =
  match WordSet.min_elem t.fconst, WordSet.max_elem t.fconst with
  | Some lo, Some hi when Word.equal lo hi ->
    let base = Word.add lo k in
    Some (List.fold t.fvars ~init:(Bil.Int base) ~f:(fun acc (v, k') ->
        let scaled = Bil.BinOp (Bil.TIMES, Bil.Var v, Bil.Int (Word.of_int ~width:64 k')) in
        if k' >= 0 then Bil.BinOp (Bil.PLUS, acc, scaled)
        else Bil.BinOp (Bil.MINUS, acc, scaled)))
  | _ -> None

(* [rewrite_addr frame a]: Normalize a frame-derived Load/Store address to its offset-from-origin expression: every frame-derived sub-expression is replaced by its offset expression, and the derived-free residue (index arithmetic over GPRs,. *)
let rewrite_addr (frame : AI.frame option) (a : exp) : exp =
  let find (v : var) : AI.frame_term option =
    match frame with
    | None -> None
    | Some f -> AI.frame_lookup f v in
  let derived_free (e : exp) : bool =
    Exp.free_vars e
    |> Core.Set.for_all ~f:(fun v -> Option.is_none (find v)) in
  let rec go (e : exp) : exp option =
    match e with
    | Bil.Var x ->
      (match find x with
       | Some t -> expr_of_term t (Word.zero 64)
       | None -> None)
    | Bil.Int _ -> Some e
    | Bil.BinOp (Bil.PLUS, e1, e2) ->
      (match go e1, go e2 with
       | Some r1, Some r2 -> Some (Bil.BinOp (Bil.PLUS, r1, r2))
       | Some r1, None ->
         if derived_free e2 then Some (Bil.BinOp (Bil.PLUS, r1, e2)) else None
       | None, Some r2 ->
         if derived_free e1 then Some (Bil.BinOp (Bil.PLUS, e1, r2)) else None
       | None, None -> None)
    | Bil.BinOp (Bil.MINUS, e1, e2) ->
      (match go e1, go e2 with
       | Some r1, Some r2 -> Some (Bil.BinOp (Bil.MINUS, r1, r2))
       | Some r1, None ->
         if derived_free e2 then Some (Bil.BinOp (Bil.MINUS, r1, e2)) else None
       | None, Some _ -> None  (* e1 - derived: origin creep *)
       | None, None -> None)
    | _ -> None in
  match go a with
  | Some r -> r
  | None -> a

(* [frame_rewrite_rhs frame e]: rewrite a Load/Store rhs's address. *)
let frame_rewrite_rhs (frame : AI.frame option) (e : exp) : exp =
  match e with
  | Bil.Load (m, a, en, s) ->
    Bil.Load (m, rewrite_addr frame a, en, s)
  | Bil.Store (m, a, u, en, s) ->
    Bil.Store (m, rewrite_addr frame a, u, en, s)
  | _ -> e


(* Helper functions; define a denotation for expressions. Assumes that e has BIR type [Imm bitwidth] *)
(* [frame]: one state's frame relation — the representation module's type (the in-state port: the relation lives in [AI.t]). *)
type frame = AI.frame

(* [frame_of_state env]: the state's frame relation (None = the vacuous bottom state) — the in-state accessor for consumers. *)
let frame_of_state (env : AI.t) : frame option = AI.frame_of env

let rec denote_exp (e : exp) (env : AI.t) : val_t or_type_error =
  let open Monad_type_error in
  let monadic_assert (b : bool) (err : Type.error) =
    if b then !!() else fail err in
  let return_imm (v : wordset) = return @@ `Word v in
  let return_mem (v : Mem.t) = return @@ `Mem v in
  match e with
  | Bil.Var v -> begin match Var.typ v with
    | Type.Imm bitwidth -> return_imm @@ AI.find_word bitwidth env v
    | Type.Mem (addr_i, addressable_size) ->
      let k = mem_idx addr_i addressable_size in
      return_mem @@ AI.find_memory k env v
    | Type.Unk -> failwith "Error in denote_exp: var type is not representable by Type.t"
    end
  | Bil.Int bv -> return_imm @@ WordSet.singleton bv
  | Bil.BinOp (op, e1, e2) ->
    denote_exp e1 env >>= val_as_imm >>= fun v1 ->
    denote_exp e2 env >>= val_as_imm >>= fun v2 ->
    return_imm @@ denote_binop op v1 v2
  | Bil.Load (m, a, e, s) ->
    denote_exp a env >>= val_as_imm >>= fun addr ->
    denote_exp m env >>= val_as_mem >>= fun mv ->
    let resSize = Size.in_bits s in
    if WordSet.splits_by addr (Word.of_int ~width:resSize (Size.in_bytes s))
    then Option.value_map ~default:(return_imm @@ WordSet.bottom resSize) (Mem.Key.of_wordset addr)
        ~f:(fun k -> Mem.find (resSize, e) mv k |> Mem.Val.data |> return_imm)
    else return_imm @@ WordSet.top resSize
  | Bil.Store (m, a, u, e, s) ->
    Type.infer u >>= fun u_typ ->
    let sz = Size.in_bits s in
    let exp = Type.imm sz in
    let u_type_error = Type.Error.bad_type ~exp ~got:u_typ in
    monadic_assert Type.(exp = u_typ) u_type_error >>= fun () ->
    denote_exp a env >>= val_as_imm >>= fun addr ->
    denote_exp m env >>= val_as_mem >>= fun mv ->
    denote_exp u env >>= val_as_imm >>= fun v ->
    (* E2e-D, loop attempt 3 — stack-only residue (user directive: only the stack, not heap). *)
    if WordSet.is_top addr
    then return_mem mv
    else
    (* Check that the store can be represented by a repeating sequence of vs *)
    let v' = if WordSet.splits_by addr (Word.of_int ~width:sz (Size.in_bytes s))
      then v else WordSet.top sz in
    let data = Mem.Val.create v' e in
    return_mem @@ Option.value_map ~default:mv (Mem.Key.of_wordset addr)
      ~f:(fun key -> Mem.add mv ~key ~data)
  | Bil.Ite (cond, yes, no) ->
    denote_exp cond env >>= val_as_imm >>= fun condv ->
    denote_exp yes env >>= fun yesv ->
    denote_exp no env >>= fun nov ->
    if WordSet.is_top condv then val_join yesv nov
    else if WordSet.equal condv (WordSet.singleton Word.b1) then return yesv
    else if WordSet.equal condv (WordSet.singleton Word.b0) then return nov
    (* A non-singleton, non-top condition (e.g. *)
    else val_join yesv nov
  | Bil.Extract (hi, lo, e) ->
    denote_exp e env >>= val_as_imm >>= fun v ->
    return_imm @@ WordSet.extract ~hi ~lo v
  | Bil.Concat (e1, e2) ->
    denote_exp e1 env >>= val_as_imm >>= fun v1 ->
    denote_exp e2 env >>= val_as_imm >>= fun v2 ->
    return_imm @@ WordSet.concat v1 v2
  | Bil.UnOp (Bil.NOT, e) ->
    denote_exp e env >>= val_as_imm >>| WordSet.lnot >>= return_imm
  | Bil.UnOp (Bil.NEG, e) ->
    denote_exp e env >>= val_as_imm >>| WordSet.neg >>= return_imm
  | Bil.Cast (ct, sz, e) ->
    denote_exp e env >>= val_as_imm >>| WordSet.cast ct sz >>= return_imm
  | Bil.Let (var, value, body) ->
    denote_exp value env >>= fun v ->
    let env' = match v with
      | `Word p -> AI.add_word ~key:var ~data:p env
      | `Mem m -> AI.add_memory ~key:var ~data:m env
    in
    denote_exp body env'
  | Bil.Unknown (_,typ) -> return @@ val_top typ

let denote_imm_exp (e : exp) (env : AI.t) : WordSet.t or_type_error =
  let open Monad_type_error in
  denote_exp e env >>= val_as_imm

let denote_def (df : def term) (env : AI.t) : AI.t =
  (* The relevance RESTRICTION — a def is skipped entirely (its var and its memory effect are not tracked) iff it is not tagged [Utils.relevant]. *)
  if not (Term.has_attr df Utils.relevant)
  then env
  else
  let v = Def.lhs df in
  let e = Def.rhs df in
  (* WYSINWYX-2 — the frame-relation address rewrite: a Load/Store address over a frame-derived register (the STATE's relation — carried in [AI.t] since the in-state port) denotes its offset-from-origin expression (base-independent key). *)
  let frame = AI.frame_of env in
  let e = frame_rewrite_rhs frame e in
  (* WYSINWYX-3 (the value-side) — when the WHOLE rhs is a frame-derived affine expression (the [rewrite_addr] walk succeeds on it), its VALUE is the offset-from-origin expression: a frame-derived pointer value (lea'd, saved. *)
  let e = rewrite_addr frame e in
  exn_on_err @@
  let open Monad_type_error in
  (* TODO: throw errors here or later? *)
  denote_exp e env >>| fun ev ->
  (match ev with
   | `Word p -> AI.add_word env ~key:v ~data:p
   | `Mem m -> AI.add_memory env ~key:v ~data:m)
  |> fun env' ->
  AI.set_frame env' (apply_frame_def (AI.frame_of env) df)

(* Computes the denotation of a block's def statements, i.e. the effect they have on the precondition abstraction. *)
let denote_defs (b : blk term) : AI.t -> AI.t =
  (* E2e-A / Lane C — no phi nodes in the corpus (-O0 LLVM lift); BIR phis are removed by the pseudo-node cleanup. If one ever appears, the block-entry merge already approximates its value — the sound minimal fallback is the identity (the state unchanged), never a raise. *)
  (* WYSINWYX-2 — the frame relation lives IN the state (the in-state port): [denote_def] reads it for the address rewrite and advances it through each def, so a def's rewrite sees the relation at THAT point (e.g. *)
  fun env0 ->
    Term.enum def_t b
    |> Seq.fold ~init:env0 ~f:(fun env df -> denote_def df env)



(* Filters a sequence of jumps by which are reachable in the given environment *)
(* TODO: use jump condition processing to make this more accurate *)
let reachable_jumps (env : AI.t) (jmps : jmp term seq) : jmp term seq =
  Seq.unfold_with jmps  ~init:true ~f:begin fun reachable jmp ->
    let cond = exn_on_err @@ denote_imm_exp (Jmp.cond jmp) env in
    let can_fall_through = WordSet.elem Word.b0 cond in
    if not reachable then Seq.Step.Done
    else if WordSet.elem Word.b1 cond then Seq.Step.Yield {value = jmp; state = can_fall_through}
    else Seq.Step.Skip {state = can_fall_through}
  end

(* --- Hike port fix (Phase 2, change D4): branch-assume --------------- [reachable_jumps] only FILTERS edges by definitely-true/false conditions; no state refinement happens on taken edges, so loop counters join to [0,∞) -> top -> the runtime arm. *)

(* L-A1 — the jcc DECODER (recognition layer) ------------ The -O0 lifted loop guards are COMPOUND flag expressions (the canonical per-cmp emission, BIR-verified by the oracle, ora-6): `#t := e - c; CF := e < c; OF :=. *)
type guard_op = ULT | ULE | UGT | UGE | EQ | SLT | SLE | SGT | SGE

let decoded_condition (cond : exp) : guard_op option =
  (* [is_flag name e]: [e] is the flag var named [name] (Var.name equality — the lifter names the 1-bit flags CF/ZF/SF/OF). *)
  let is_flag (name : string) (e : exp) : bool =
    match e with
    | Bil.Var v -> String.equal (Var.name v) name
    | _ -> false in
  (* [xor_core e]: e = (SF | OF) & ~(SF & OF) — the signed-overflow XOR core shared by the jle and jl shapes. *)
  let xor_core (e : exp) : bool =
    match e with
    | Bil.BinOp (Bil.AND,
                 Bil.BinOp (Bil.OR, sf_or, of_or),
                 Bil.UnOp (Bil.NOT, Bil.BinOp (Bil.AND, sf_and, of_and))) ->
      is_flag "SF" sf_or && is_flag "OF" of_or
      && is_flag "SF" sf_and && is_flag "OF" of_and
    | _ -> false in
  match cond with
  | Bil.BinOp (Bil.OR, zf, core) when is_flag "ZF" zf && xor_core core ->
    (* jle: ZF | (SF|OF) & ~(SF&OF) — signed e <= c. NOTE (ora-6): the decoder emits the IDIOM'S OWN op (SLE), NEVER the record's op (LT) — reusing LT would wrongly exclude a = c. *)
    Some SLE
  | core when xor_core core ->
    (* jl: (SF|OF) & ~(SF&OF) — signed e < c *)
    Some SLT
  | Bil.UnOp (Bil.NOT, Bil.BinOp (Bil.OR, cf, zf))
    when is_flag "CF" cf && is_flag "ZF" zf ->
    (* ja: ~(CF | ZF) — unsigned e > c *)
    Some UGT
  | _ -> None

(* L-S2 (oracle item 10) — [interval_clp_of ~width ~cardn base]: the shared step-1 CLP-interval construction for [comparison_constraint]'s rows and [interval_of_bounds] (None on cardn 0 / WordSet top; the (width+1)-bit cardn — pinned convention). *)
let interval_clp_of ~(width : int) ~(cardn : word) (base : word)
    : wordset option =
  if Word.is_zero cardn then None
  else
    let ws = WordSet.of_clp
        (Cbat_clp.create ~width ~step:(Word.one width) ~cardn base) in
    if WordSet.is_top ws then None else Some ws

(* [comparison_constraint ?cur op c]: = the set of values [x] may take on the taken edge of a jump guarded by [x op c] (a BIL comparison of a variable against a constant), or [None] when the constraint is not a clean singleton / interval CLP (NEQ, signed. *)
let comparison_constraint ?(cur : wordset option = None)
    ?(known_nonneg : bool = false)
    (op : Bil.binop) (c : word) : wordset option =
  let width = Word.bitwidth c in
  let cardn_of_int (i : int) : word option =
    if i < 0 then None else Some (Word.of_int ~width:(width + 1) i) in
  let int_of_word (w : word) : int option =
    try Some (Word.to_int_exn w) with _ -> None in
  (* 2^(w-1) at [width]: the first word of the high (negative-signed) half — the non-negativity threshold *)
  let half = Word_ops.half width in
  let provably_nonneg : bool =
    Option.value_map cur ~default:false ~f:(fun ws ->
        match WordSet.max_elem ws with
        | None -> false
        | Some m -> Word.(<) m half) in
  match op with
  | Bil.LT -> Option.bind (int_of_word c) ~f:(fun i ->
      Option.bind (cardn_of_int i) ~f:(fun cardn ->
          interval_clp_of ~width ~cardn (Word.zero width)))
  | Bil.LE -> Option.bind (int_of_word c) ~f:(fun i ->
      Option.bind (cardn_of_int (i + 1)) ~f:(fun cardn ->
          interval_clp_of ~width ~cardn (Word.zero width)))
  | Bil.EQ -> Some (WordSet.singleton c)
  | Bil.SLT ->
    (* signed x < c *)
    if Word.(>=) c half
    then interval_clp_of ~width ~cardn:(Word.sub c half) half
    else if provably_nonneg || known_nonneg
    then interval_clp_of ~width ~cardn:c (Word.zero width)
    else None
  | Bil.SLE ->
    (* signed x <= c *)
    if Word.(>=) c half
    then interval_clp_of ~width ~cardn:(Word.succ (Word.sub c half)) half
    else if provably_nonneg || known_nonneg
    then interval_clp_of ~width ~cardn:(Word.succ c) (Word.zero width)
    else None
  | Bil.NEQ ->
    (* L3c-5 — non-convex two-sided constraint (x < c or x > c): no single interval (cf. the ASE'21 inverse-semantics result); sound stop. *)
    None
  | Bil.PLUS | Bil.MINUS | Bil.TIMES | Bil.DIVIDE | Bil.SDIVIDE
  | Bil.MOD | Bil.SMOD | Bil.LSHIFT | Bil.RSHIFT | Bil.ARSHIFT
  | Bil.AND | Bil.OR | Bil.XOR ->
    (* L3c-5 — a PRODUCER op used as a comparison guard: the guard's denotation already produced its value set; no backward constraint; sound stop (the structural closure). *)
    None

(* ------------------------------------------------------------------ *)
(* L3a — backward guard refinement (the backward_int_binop machinery, user-approved scope). *)

(* [interval_of_bounds width lo hi]: The CLP interval [lo, hi] at [width] as a wordset, or None on doubt (width mismatch, lo > hi = wrap, full range). *)
let interval_of_bounds (width : int) (lo : word) (hi : word) : wordset option =
  if Word.bitwidth lo <> width || Word.bitwidth hi <> width then None
  else if Word.(>) lo hi then None
  else
    let ws = WordSet.of_clp (Cbat_clp.interval ~width lo hi) in
    if WordSet.is_top ws then None else Some ws

(* L-A1 — [decoder_constraint ?cur op c]: the constraint rows for the jcc-decoder ops ([decoded_condition] above; the [guard_op] enum). *)
let decoder_constraint ?(cur : wordset option = None)
    ?(known_nonneg : bool = false)
    (op : guard_op) (c : word) : wordset option =
  let width = Word.bitwidth c in
  match op with
  | ULT -> comparison_constraint ~cur Bil.LT c
  | ULE -> comparison_constraint ~cur Bil.LE c
  | EQ -> comparison_constraint ~cur Bil.EQ c
  | SLT -> comparison_constraint ~cur ~known_nonneg Bil.SLT c
  | SLE -> comparison_constraint ~cur ~known_nonneg Bil.SLE c
  | UGT ->
    (* unsigned x > c = [c+1, 2^w) — exact, no gate *)
    let lo = Word.succ c in
    if Word.is_zero lo then None
    else interval_of_bounds width lo (Word.ones width)
  | UGE ->
    (* unsigned x >= c = [c, 2^w) — exact, no gate *)
    interval_of_bounds width c (Word.ones width)
  | SGT ->
    (* signed x > c = [c+1, 2^w) — single piece, no gate (why: see the comment above — the >-pieces merge) *)
    let lo = Word.succ c in
    if Word.is_zero lo then None
    else interval_of_bounds width lo (Word.ones width)
  | SGE ->
    (* signed x >= c = [c, 2^w) — single piece, no gate (see above) *)
    interval_of_bounds width c (Word.ones width)

(* L-D1 — [prove_nonneg ~defs ~stores e]: the PROVENANCE-based non-negativity proof that lets the SLT/SLE gate of [comparison_constraint] (its [?known_nonneg], added in this lane) accept the compared operand [e] even when the ABSTRACT current value set [cur] fails the [max_elem < 2^(w-1)] threshold. *)
let prove_nonneg ~(defs : (def term * bool) Var.Map.t)
    ~(stores : def term list) (e : exp) : bool =
  (* The signed-non-negative literal test: the MSB clear, i.e. *)
  let nonneg_word (n : word) : bool =
    let w = Word.bitwidth n in
    w > 0
    && Word.(<) n (Word_ops.half w) in
  let stack_anchor (v : var) : bool =
    let n = Var.name v in
    String.equal n "RSP" || String.equal n "RBP" in
  (* [cells]: the cell addrs under consideration (re-entry -> TRUE, the induction hypothesis, seeded); [vars]: the def-lhs vars already followed (re-entry -> FALSE — a cycle has no base). Both are the threaded helper param through the [Var]/[PLUS] recursion. *)
  let rec walk (cells : Exp.Set.t) (vars : Exp.Set.t) (e : exp) : bool =
    match e with
    | Bil.Int n -> nonneg_word n
    | Bil.Var v ->
      let seen = Core.Set.mem vars e in
      let info = Core.Map.find defs (Var.base v) in
      let result =
        if seen then
          (* A repeated variable may still be the load that closes the stack-cell induction. Follow that load with the existing [cells] memo; only a repeated non-load producer is a genuine unseeded value cycle. *)
          (match info with
           | Some (d, true) ->
             (match Def.rhs d with
              | Bil.Load _ -> walk cells vars (Def.rhs d)
              | _ -> false)
           | _ -> false)
        else begin match info with
          | Some (d, true) -> walk cells (Core.Set.add vars e) (Def.rhs d)
          | _ -> false
        end in
      result
    | Bil.BinOp (Bil.PLUS, a, b) ->
      let ra = walk cells vars a in
      let rb = walk cells vars b in
      ra && rb
    | Bil.BinOp (Bil.MINUS, a, b) ->
      (match b with
       | Bil.Int z when Word.is_zero z -> walk cells vars a
       | _ -> false)
    | Bil.BinOp (Bil.RSHIFT, _, Bil.Int k) ->
      (* A logical right shift by a positive amount clears the sign bit. The zero-shift case is the operand identity. *)
      (match Word.to_int k with
       | Ok n when n > 0 -> true
       | Ok 0 -> false
       | _ -> false)
    | Bil.BinOp (Bil.ARSHIFT, a, Bil.Int k) ->
      (match Word.to_int k with
       | Ok n when n > 0 -> walk cells vars a
       | Ok 0 -> walk cells vars a
       | _ -> false)
    | Bil.BinOp (Bil.TIMES, a, Bil.Int k) ->
      (* The row below computes the producer pre-image; once the result trace is constrained, the multiplier row is the relevant non-negative recurrence. *)
      if Word.is_zero k then true else walk cells vars a
    | Bil.BinOp (Bil.DIVIDE, a, Bil.Int k) ->
      (* Unsigned division by at least two has a non-negative signed result; division by one is the operand identity. *)
      (match Word.to_int k with
       | Ok n when n >= 2 -> true
       | Ok 1 -> walk cells vars a
       | _ -> false)
    | Bil.BinOp (Bil.AND, a, Bil.Int k) ->
      let w = Word.bitwidth k in
      let half = Word_ops.half w in
      if Word.(<) k half then true
      else if Word.(=) k (Word.ones w) then walk cells vars a
      else false
    | Bil.BinOp (Bil.OR, a, Bil.Int k)
      when Word.is_zero k -> walk cells vars a
    | Bil.BinOp (Bil.XOR, a, Bil.Int k)
      when Word.is_zero k -> walk cells vars a
    | Bil.Cast (Bil.HIGH, _, a) ->
      (* HIGH of a non-negative source has its result sign bit clear. *)
      walk cells vars a
    | Bil.Load (_, addr, _, _) ->
      let anchored = Exp.free_vars addr |> Core.Set.for_all ~f:stack_anchor in
      let reentry = Core.Set.mem cells addr in
      if not anchored then false
      else if reentry then true
      else
        let cells' = Core.Set.add cells addr in
        let matches = List.filter stores ~f:begin fun d ->
          match Def.rhs d with
          | Bil.Store (_, addr', _, _, _) -> Exp.equal addr addr'
          | _ -> false
        end in
        let has_seed = List.exists matches ~f:begin fun d ->
          match Def.rhs d with
          | Bil.Store (_, _, Bil.Int n, _, _) -> nonneg_word n
          | _ -> false
        end in
        let all_values = List.for_all matches ~f:begin fun d ->
          match Def.rhs d with
          | Bil.Store (_, _, u, _, _) -> walk cells' vars u
          | _ -> false
        end in
        let result = has_seed && all_values in
        result
    | _ -> false
  in
  walk Exp.Set.empty Exp.Set.empty e

(* L-S2 (oracle item 9) — [known_nonneg_of ~defs ~stores e]: the [prove_nonneg] gate (const-second row / decoder pre-step); defs or stores absent -> false (pre-L-D1 byte-identity). *)
let known_nonneg_of ~(defs : (def term * bool) Var.Map.t option)
    ~(stores : def term list option) (e : exp) : bool =
  match defs, stores with
  | Some dm, Some ss -> prove_nonneg ~defs:dm ~stores:ss e
  | _ -> false

(* L3c-3 — [circular_hull width lo hi]: the CIRCULAR hull [lo ... *)
let circular_hull (width : int) (lo : word) (hi : word) : wordset option =
  if Word.bitwidth lo <> width || Word.bitwidth hi <> width then None
  else
    let ws = WordSet.of_clp (Cbat_clp.interval ~width lo hi) in
    if WordSet.is_top ws then None else Some ws

(* [operand_constraints op cstr a_ws b_ws]: The operand-constraint rules for [v := op(a, b)] with the result constrained to [cstr]: return the constraint [a] (resp. *)
let operand_constraints (op : Bil.binop) (cstr : wordset)
    (a_ws : wordset) (b_ws : wordset) : wordset option * wordset option =
  let width = WordSet.bitwidth cstr in
  if WordSet.bitwidth a_ws <> width || WordSet.bitwidth b_ws <> width
  then None, None
  else
    (* the no-wrap threshold for a constant multiplier/shift: the largest operand value whose scaled image does not wrap *)
    let wrap_limit (k : word) : word = Word.div (Word.ones width) k in
    let operand_bounded (limit : word) : bool =
      match WordSet.max_elem a_ws with
      | Some m -> Word.(<=) m limit
      | None -> false in
    let ceil_div (k : word) (x : word) : word =
      let q = Word.div x k in
      let r = Word.modulo x k in
      if Word.is_zero r then q else Word.succ q in
    match op with
    | Bil.PLUS ->
      (* V = a + b, v in [vlo,vhi]: a' = [vlo − b_max, vhi − b_min]; b' = [vlo − a_max, vhi − a_min]. *)
      (match WordSet.min_elem cstr, WordSet.max_elem cstr with
       | Some vlo, Some vhi ->
         let a' = match WordSet.min_elem b_ws, WordSet.max_elem b_ws with
           | Some bmin, Some bmax ->
             circular_hull width (Word.sub vlo bmax) (Word.sub vhi bmin)
           | _ -> None in
         let b' = match WordSet.min_elem a_ws, WordSet.max_elem a_ws with
           | Some amin, Some amax ->
             circular_hull width (Word.sub vlo amax) (Word.sub vhi amin)
           | _ -> None in
         a', b'
       | _ -> None, None)
    | Bil.MINUS ->
      (* v = a − b: a' = [vlo + b_min, vhi + b_max]; b' = [a_min − vhi, a_max − vlo]. The wrapped bound (the underflow/overflow of the interval arithmetic) is the same circular hull construction as PLUS — sound. *)
      (match WordSet.min_elem cstr, WordSet.max_elem cstr with
       | Some vlo, Some vhi ->
         let a' = match WordSet.min_elem b_ws, WordSet.max_elem b_ws with
           | Some bmin, Some bmax ->
             circular_hull width (Word.add vlo bmin) (Word.add vhi bmax)
           | _ -> None in
         let b' = match WordSet.min_elem a_ws, WordSet.max_elem a_ws with
           | Some amin, Some amax ->
             circular_hull width (Word.sub amin vhi) (Word.sub amax vlo)
           | _ -> None in
         a', b'
       | _ -> None, None)
    | Bil.TIMES ->
      (* V = a·k, k a literal. *)
      (match WordSet.min_elem cstr, WordSet.max_elem cstr,
             WordSet.min_elem b_ws, WordSet.max_elem b_ws with
       | Some vlo, Some vhi, Some k, Some k' when Word.(=) k k' ->
         (match Word.to_int k with
          | Ok kk when kk > 0 && operand_bounded (wrap_limit k) ->
            (match interval_of_bounds width (ceil_div k vlo)
                     (Word.div vhi k) with
             | Some a' -> Some a', None
             | None -> None, None)
          | _ -> None, None)
       | _ -> None, None)
    | Bil.LSHIFT ->
      (* v = a << s: the operand rule a' = [vlo >> s, vhi >> s] (the inverse of the def-side rule; sound — [lo>>s, hi>>s] ⊇ the true {a | a·2^s ∈ [vlo,vhi]}). A variable shift hulls over the shift range: a' = [vlo >> s_max, vhi >> s_min] (the images are monotone in s). *)
      (match WordSet.min_elem cstr, WordSet.max_elem cstr,
             WordSet.min_elem b_ws, WordSet.max_elem b_ws with
       | Some vlo, Some vhi, Some smin, Some smax ->
         (match Word.to_int smin, Word.to_int smax with
          | Ok smin_i, Ok smax_i
            when smin_i >= 0 && smax_i < width && smin_i <= smax_i ->
            let lo_a = Word.rshift vlo smax in
            let hi_a = Word.rshift vhi smin in
            (match interval_of_bounds width lo_a hi_a with
             | Some a' -> Some a', None
             | None -> None, None)
          | _ -> None, None)
       | _ -> None, None)
    | Bil.RSHIFT | Bil.ARSHIFT ->
      (* V = a >> s (logical) / a arshift s: the inverse a' = [vlo << s, (vhi+1) << s − 1] — the shifted-out top bits of a are unconstrained (checked via (vhi+1) ≤ 2^(w−s); the exact wrap yields a' = the domain). *)
      (match WordSet.min_elem cstr, WordSet.max_elem cstr,
             WordSet.min_elem b_ws, WordSet.max_elem b_ws with
       | Some vlo, Some vhi, Some smin, Some smax ->
         (match Word.to_int smin, Word.to_int smax with
          | Ok smin_i, Ok smax_i
            when smin_i >= 0 && smax_i < width && smin_i <= smax_i ->
            let hi1 = Word.succ vhi in
            let mask = Word.lshift (Word.one width)
                (Word.of_int ~width:width (width - smax_i)) in
            if Word.(>) hi1 mask then None, None
            else
              let lo_a = Word.lshift vlo (Word.of_int ~width smin_i) in
              let hi_a = Word.pred (Word.lshift hi1 (Word.of_int ~width smax_i)) in
              (match interval_of_bounds width lo_a hi_a with
               | Some a' -> Some a', None
               | None -> None, None)
          | _ -> None, None)
       | _ -> None, None)
    | Bil.DIVIDE ->
      (* v = a / k: the inverse of the TIMES rule — a' = [vlo·k, (vhi+1)·k − 1] (exact: a/k = v ⟺ a ∈ [v·k, (v+1)·k − 1]). Sound only when (vhi+1)·k fits the width. A general divisor hulls over the range: [vlo·k_min, (vhi+1)·k_max − 1]. k = 0 -> the identity. *)
      (match WordSet.min_elem cstr, WordSet.max_elem cstr,
             WordSet.min_elem b_ws, WordSet.max_elem b_ws with
       | Some vlo, Some vhi, Some kmin, Some kmax ->
         (match Word.to_int kmin, Word.to_int kmax with
          | Ok kmin_i, Ok kmax_i when kmin_i > 0 && kmin_i <= kmax_i ->
            let hi1 = Word.succ vhi in
            let kmax_w = Word.of_int ~width kmax_i in
            let limit = Word.div (Word.ones width) kmax_w in
            if Word.(>) hi1 limit then None, None
            else
              let lo_a = Word.mul vlo (Word.of_int ~width kmin_i) in
              let hi_a = Word.pred (Word.mul hi1 kmax_w) in
              (match interval_of_bounds width lo_a hi_a with
               | Some a' -> Some a', None
               | None -> None, None)
          | _ -> None, None)
       | _ -> None, None)
    | Bil.SDIVIDE ->
      (* V = a sdiv k (k a literal): the signed-interval rule — a sdiv k = v ⟺ a ∈ [v·k, v·k + k − 1] (truncating toward zero), and the classes are contiguous over v, so a' = [slo·k, shi·k + k − 1] on the signed axis — the same circular interval on the word circle. *)
      (match WordSet.min_elem cstr, WordSet.max_elem cstr,
             WordSet.min_elem b_ws, WordSet.max_elem b_ws with
       | Some vlo, Some vhi, Some k, Some k' when
           width <= 32 && Word.(=) k k' ->
         (match Word.to_int k with
          | Ok kk when kk > 0 ->
            (* width <= 32: [to_int] is the signed 32-bit value and the products fit a 63-bit [int] — overflow-free *)
            (match Word.to_int vlo, Word.to_int vhi with
             | Ok slo, Ok shi ->
               let lo' = slo * kk in
               let hi' = (shi + 1) * kk - 1 in
               (match circular_hull width
                        (Word.of_int ~width lo') (Word.of_int ~width hi') with
                | Some a' -> Some a', None
                | None -> None, None)
             | _ -> None, None)
          | _ -> None, None)
       | _ -> None, None)
    | Bil.MOD | Bil.SMOD ->
      (* v = a mod k: the true operand set is the periodic union ⋃_j [vlo + jk, vhi + jk] — hulled over j it spans the full domain for any modulus ≪ 2^w, i.e. the identity (sound; the L3c5-2 pin pins the non-refinement). *)
      None, None
    | Bil.AND | Bil.OR | Bil.XOR ->
      (* The exact identities are real rules; a mask with any free bit (general m) makes the operand hull the full domain (the identity): a OR 0 = a -> a' = the constraint itself a XOR 0 = a -> a' = the constraint itself a AND. *)
      (match WordSet.min_elem b_ws, WordSet.max_elem b_ws with
       | Some k, Some k' when Word.(=) k k' ->
         if Word.is_zero k then
           (match op with
            | Bil.OR | Bil.XOR -> Some cstr, None
            | _ -> None, None)
         else if Word.(=) k (Word.ones width) then
           (match op with
            | Bil.AND -> Some cstr, None
            | Bil.XOR -> Some (WordSet.lnot cstr), None
            | _ -> None, None)
         else None, None
       | _ -> None, None)
    (* comparisons used as producers (EQ/NEQ/LT/LE/SLT/SLE): the def produces a boolean value — the operands are unconstrained (the identity; the guard's own rules constrain them on the guard edge, not through the boolean def) *)
    | _ -> None, None

(* [denote_operand env e]: the current word value of an operand [e] for the row arithmetic, or None on doubt (non-word type, denote error). *)
let denote_operand (env : AI.t) (e : exp) : wordset option =
  match e with
  | Bil.Var v ->
    (match Var.typ v with
     | Type.Imm w -> Some (AI.find_word w env v)
     | _ -> None)
  | Bil.Int w -> Some (WordSet.singleton w)
  | _ ->
    (match denote_imm_exp e env with
     | Ok ws -> Some ws
     | Error _ -> None)

(* [meet_var refineable_var env v refined]: meet [refined] into var [v] with the genuine-subset discipline (skip on wrap / disjoint / empty and skip non-refineable vars) — the :487-495 pattern reused by the backward walk. Env unchanged on any doubt. *)
let meet_var (refineable_var : var -> bool) (env : AI.t)
    (v : var) (refined : wordset) : AI.t =
  match Var.typ v with
  | Type.Imm w ->
    let cur = AI.find_word w env v in
    if WordSet.bitwidth cur <> w || WordSet.bitwidth refined <> w
    then env
    else
      let m = WordSet.meet cur refined in
      if Word.is_zero (WordSet.cardinality m)
         || not (WordSet.precedes m cur)
      then env
      else if refineable_var v then AI.add_word env ~key:v ~data:m
      else env
  | Type.Mem _ | Type.Unk -> env

(* [constrain_cell refineable_var env ~mem ~addr ~size ~endian cstr]: Meet the constraint [cstr] into the memory cell a load [mem := Load[addr, size, endian]] reads, mirroring the load denotation (denote_exp's Load arm :241-248: addr set -> Key -> Mem.find on the mem var's map, idx (resSize, endian)). *)
let rec constrain_cell
    (refineable_var : var -> bool) (env : AI.t)
    ~(mem : exp) ~(addr : exp) ~(size : Size.t) ~(endian : endian)
    (cstr : wordset) : AI.t =
  if not (Exp.free_vars addr |> Core.Set.for_all ~f:refineable_var)
  then env
  else
    (* WYSINWYX-2 (the re-keyed backward lane, always-on): the cell key is the REWRITTEN address (the offset-from-origin expression via the WALK's state frame — the SINGLE raw key space, the dual-space rebase was removed; the. *)
    let addr_opt =
      if
        Exp.free_vars addr
        |> Core.Set.exists ~f:(fun v -> String.equal (Var.name v) "RSP")
      then None
      else
        let a' = rewrite_addr (AI.frame_of env) addr in
        if Exp.free_vars a' |> Core.Set.is_empty then Some a' else None in
    match addr_opt with
    | None -> env
    | Some addr ->
    match mem with
    | Bil.Var m ->
      (match Var.typ m with
       | Type.Mem (addr_i, addressable_size) ->
         let k = mem_idx addr_i addressable_size in
         (match denote_imm_exp addr env with
          | Error _ -> env
          | Ok addr_ws ->
            (match Mem.Key.of_wordset addr_ws with
             | None -> env
             | Some key ->
               let resSize = Size.in_bits size in
               if WordSet.bitwidth cstr <> resSize then env
               else
                 let mv = AI.find_memory k env m in
                 let cur = Mem.find (resSize, endian) mv key in
                 let cur_ws = Mem.Val.data cur in
                 let refined = WordSet.meet cur_ws cstr in
                 if Word.is_zero (WordSet.cardinality refined)
                    || not (WordSet.precedes refined cur_ws)
                 then env
                 else
                   let new_cell =
                     Mem.Val.meet_at (resSize, endian) cur
                       (Mem.Val.create cstr endian) in
                   AI.add_memory env ~key:m
                     ~data:(Mem.add mv ~key ~data:new_cell)))
       | Type.Imm _ | Type.Unk -> env)
    | _ -> env

(* [refine_chain ~defs refineable_var ~visited env op a b cstr]: Apply the L3a row for [op] to the producer def [v := op(a, b)] (the result constrained to [cstr]) and refine the VAR operands (meet with the genuine-subset discipline, then recurse). *)
and refine_chain ~(defs : (def term * bool) Var.Map.t)
    (refineable_var : var -> bool) ~(visited : Var.Set.t)
    (env : AI.t) (op : Bil.binop) (a : exp) (b : exp)
    (cstr : wordset) : AI.t =
  let width = WordSet.bitwidth cstr in
  match op with
  | Bil.LSHIFT ->
    (* v = a << k with k a literal < width: a' = [lo >> k, hi >> k] (sound; imprecise on the low bits — the shifted-out bits are dropped rather than constrained) *)
    (match b with
     | Bil.Int k ->
       (match Word.to_int k with
        | Ok kk when kk >= 0 && kk < width ->
          (match WordSet.min_elem cstr, WordSet.max_elem cstr with
           | Some lo, Some hi ->
             let lo_a =
               WordSet.rshift (WordSet.singleton lo) (WordSet.singleton k) in
             let hi_a =
               WordSet.rshift (WordSet.singleton hi) (WordSet.singleton k) in
             (match WordSet.min_elem lo_a, WordSet.max_elem hi_a with
              | Some lo', Some hi' ->
                (match interval_of_bounds width lo' hi' with
                 | Some a' ->
                   let env' = match a with
                     | Bil.Var av -> meet_var refineable_var env av a'
                     | _ -> env in
                   constrain_def_chain ~defs refineable_var
                     ~visited env' a a'
                 | None -> env)
              | _ -> env)
           | _ -> env)
        | _ -> env)
     | _ -> env)
  | Bil.PLUS | Bil.MINUS | Bil.TIMES | Bil.DIVIDE | Bil.SDIVIDE
  | Bil.MOD | Bil.SMOD | Bil.AND | Bil.OR | Bil.XOR
  | Bil.RSHIFT | Bil.ARSHIFT ->
    (match denote_operand env a, denote_operand env b with
     | Some a_ws, Some b_ws ->
       (match operand_constraints op cstr a_ws b_ws with
        | a', b' ->
          let env' = match a, a' with
            | Bil.Var av, Some a_c -> meet_var refineable_var env av a_c
            | _ -> env in
          let env'' = match b, b' with
            | Bil.Var bv, Some b_c -> meet_var refineable_var env' bv b_c
            | _ -> env' in
          let env_a = match a, a' with
            | Bil.Var _, Some a_c ->
              constrain_def_chain ~defs refineable_var
                ~visited env'' a a_c
            | _ -> env'' in
          (match b, b' with
           | Bil.Var _, Some b_c ->
             constrain_def_chain ~defs refineable_var
               ~visited env_a b b_c
           | _ -> env_a))
     | _ -> env)
  | _ -> env

(* [constrain_def_chain ~defs refineable_var env e cstr]: Walk BACKWARD through the def chain of [e] from the taken-edge constraint [cstr] on [e], refining producers (meet + recursion). *)
and constrain_def_chain ~(defs : (def term * bool) Var.Map.t)
    (refineable_var : var -> bool) ?(visited : Var.Set.t = Var.Set.empty)
    (env : AI.t) (e : exp) (cstr : wordset) : AI.t =
  match e with
  | Bil.Load (m, a, en, s) ->
    (* e IS a load: constrain the cell directly *)
    constrain_cell refineable_var env ~mem:m ~addr:a ~size:s ~endian:en cstr
  | Bil.Var v ->
    let b = Var.base v in
    if Core.Set.mem visited b then env
    else
      let visited' = Core.Set.add visited b in
      (match Core.Map.find defs b with
       | None -> env
       | Some (d, unique) ->
         if not unique then env
         else
           match Def.rhs d with
           | Bil.Load (m, a, en, s) ->
             (* v := Load [cell]: the constraint on v IS the constraint on the cell (the re-keyed meet — [constrain_cell]'s always-on frame rewrite). *)
             constrain_cell refineable_var env ~mem:m
               ~addr:a ~size:s ~endian:en cstr
           | Bil.BinOp (op, a, b) ->
             refine_chain ~defs refineable_var
               ~visited:visited' env op a b cstr
           | Bil.Cast (Bil.HIGH, sz, a) ->
             (* L3c-4 — the HIGH-extract producer: v := cast HIGH a (v's width = sz < a's width) — the constraint on v shifts up into a's width (see [refine_cast_high]). *)
             refine_cast_high ~defs refineable_var
               ~visited:visited' env a sz cstr
         | Bil.Cast (ct, _sz, _a) ->
           (* L3c-5 — the remaining cast kinds are EXPLICIT sound stops (the structural closure): LOW is periodic (the low bits repeat every 2^sz — no closed-form on CLPs, cf. *)
           ignore ct; env
         | Bil.Int _ -> env
         | _ -> env)
  | _ -> env


(* L3c-4 — [refine_cast_high ~defs refineable_var ~visited env a sz cstr]: the HIGH-extract producer row for the def [v := cast HIGH a] with v's width [sz] and the constraint [cstr] on v: v ∈ [lo,hi] (N = sz bits) -> a ∈. *)
and refine_cast_high ~(defs : (def term * bool) Var.Map.t)
    (refineable_var : var -> bool) ~(visited : Var.Set.t)
    (env : AI.t) (a : exp) (sz : int) (cstr : wordset) : AI.t =
  match denote_operand env a with
  | Some a_ws ->
    let w = WordSet.bitwidth a_ws in
    let n = WordSet.bitwidth cstr in
    if w <= n then env
    else
      let shift = w - n in
      (match WordSet.min_elem cstr, WordSet.max_elem cstr with
       | Some lo, Some hi ->
         let hi1 = Word.succ hi in
         if Word.is_zero hi1 then env
         else
           let lo_w = Word.extract_exn ~hi:(w - 1) lo in
           let hi1_w = Word.extract_exn ~hi:(w - 1) hi1 in
           let mask = Word.lshift (Word.one w)
               (Word.of_int ~width:w n) in
           if Word.(>) hi1_w mask then env
           else
             let lo_a = Word.lshift lo_w (Word.of_int ~width:w shift) in
             let hi_a =
               Word.pred (Word.lshift hi1_w (Word.of_int ~width:w shift)) in
             (match interval_of_bounds w lo_a hi_a with
              | Some a' ->
                let env' = match a with
                  | Bil.Var av -> meet_var refineable_var env av a'
                  | _ -> env in
                constrain_def_chain ~defs refineable_var
                  ~visited env' a a'
               | None -> env)
        | _ -> env)
   | None -> env

(* [constrain_cell_on_trace ~st ~live env ~mem ~addr ~size ~endian cstr]: The TRACE-EXACT cell meet (the trace-partitioning design, docs/trace-partitioning-plan.md §1.3) — the cell gate's replacement. *)
let constrain_cell_on_trace ~(st : AI.t) ~(live : wordset Var.Map.t)
    (env : AI.t) ~(mem : exp) ~(addr : exp) ~(size : Size.t)
    ~(endian : endian) (cstr : wordset) : AI.t =
  match mem with
  | Bil.Var m ->
    (match Var.typ m with
     | Type.Mem (addr_i, addressable_size) ->
       let k = mem_idx addr_i addressable_size in
       let resSize = Size.in_bits size in
       if WordSet.bitwidth cstr <> resSize then env
       else
         (* the frame-correct offset via the LOAD's block state frame *)
         let addr' = rewrite_addr (AI.frame_of st) addr in
         (* the trace's var values: st's values ∩ the live constraints *)
         let st' =
           Exp.free_vars addr'
           |> Core.Set.fold ~init:st ~f:(fun acc v ->
               match Core.Map.find live (Var.base v) with
               | None -> acc
               | Some c ->
                 (match Var.typ v with
                  | Type.Imm w ->
                    let cur = AI.find_word w acc v in
                    let m = WordSet.meet cur c in
                    if Word.is_zero (WordSet.cardinality m)
                       || not (WordSet.precedes m cur)
                    then acc
                    else AI.add_word acc ~key:v ~data:m
                  | Type.Mem _ | Type.Unk -> acc)) in
         (match denote_imm_exp addr' st' with
          | Error _ -> env
          | Ok addr_ws ->
            (match Mem.Key.of_wordset addr_ws with
             | None -> env
             | Some key ->
               let mv = AI.find_memory k env m in
               let data = Mem.Val.create cstr endian in
               AI.add_memory env ~key:m
                 ~data:(Mem.meet_range mv ~key ~data)))
     | Type.Imm _ | Type.Unk -> env)
  | _ -> env

(* ================================================================== *)
(* The backward-refinement dataflow (the user design, 2026-08-13): *)
(* the COMPLETE backward traversal. Given the taken-edge constraint *)
(* [cstr] on the compared expression at the guard block, the *)
(* refinement propagates BACKWARD through the defs: *)
(* - the LIVE SET starts with the condition's (var, constraint) *)
(* pairs (the seeds); *)
(* - within a block, walk the defs in REVERSE order: a def whose *)
(* lhs is live gets its INVERSE applied (the row / the cell *)
(* meet — [def_constraints]); the lhs leaves the live set and the *)
(* rhs's derived constraints join it; a def whose lhs is not *)
(* live is SKIPPED; *)
(* - the phi nodes: a live lhs propagates its constraint to the *)
(* phi's source values (routed per predecessor edge); *)
(* - across blocks: the live sets flow to the PREDECESSORS (the *)
(* graph's reversed edges — the Graphlib fixpoint ~rev:true) *)
(* until the live sets (and hence the env) stabilize. *)
(* The env (the guard state) is refined in place (the meets); the *)
(* meets are idempotent, so the env stabilizes with the live sets. *)
(* ================================================================== *)

(* the live set: var base -> the constraint it must satisfy. *)
module Live = struct
  type t = wordset Var.Map.t

  let empty : t = Var.Map.empty
  let find (key : var) (m : t) : wordset option = Core.Map.find m key
  let add (key : var) (data : wordset) (m : t) : t =
    Core.Map.set m ~key ~data
  let remove (key : var) (m : t) : t = Core.Map.remove m key
  let equal (m1 : t) (m2 : t) : bool = Core.Map.equal WordSet.equal m1 m2

  (* the merge: a var live from several paths must satisfy the UNION of the per-path constraints (the value came from ONE path — it satisfies THAT path's constraint, so the union contains it — sound; the CLP union hull over-approximates the gap). *)
  let join (m1 : t) (m2 : t) : t =
    Core.Map.merge m1 m2 ~f:(fun ~key:_ -> function
        | `Left c | `Right c -> Some c
        | `Both (c1, c2) -> Some (WordSet.union c1 c2))
end

(* The edge_constraint: a constraint the taken-edge trace imposes, ready for the dataflow: - [Var (v, cstr)]: the var must satisfy [cstr] on the trace — flows backward through the defs (the walk's live set); - [Cell (mem,. *)
type edge_constraint =
  | Var of var * wordset
  | Cell of exp * exp * Size.t * endian * wordset
  | Infeasible

(* [high_cast_constraint env a sz cstr]: the pure HIGH-extract row — [v := cast HIGH a] (v's width = sz < a's width), the constraint [cstr] on v -> the pre-image on [a] (the top (w−N) bits' value). Extracted from [refine_cast_high] (the row, without the walk). *)
let high_cast_constraint (env : AI.t) (a : exp) (sz : int)
    (cstr : wordset) : wordset option =
  match denote_operand env a with
  | Some a_ws ->
    let w = WordSet.bitwidth a_ws in
    let n = WordSet.bitwidth cstr in
    if w <= n then None
    else
      let shift = w - n in
      (match WordSet.min_elem cstr, WordSet.max_elem cstr with
       | Some lo, Some hi ->
         let hi1 = Word.succ hi in
         if Word.is_zero hi1 then None
         else
           let lo_w = Word.extract_exn ~hi:(w - 1) lo in
           let hi1_w = Word.extract_exn ~hi:(w - 1) hi1 in
           let mask = Word.lshift (Word.one w)
               (Word.of_int ~width:w n) in
           if Word.(>) hi1_w mask then None
           else
             let lo_a = Word.lshift lo_w (Word.of_int ~width:w shift) in
             let hi_a =
               Word.pred (Word.lshift hi1_w (Word.of_int ~width:w shift)) in
             interval_of_bounds w lo_a hi_a
       | _ -> None)
  | None -> None

(* [ext_cast_constraint ~is_signed env a cstr]: The UNSIGNED/SIGNED (zero-/sign-extension) row — [v := cast ct a] (a's width n < v's width w), the constraint [cstr] on v -> the pre-image on [a]: - UNSIGNED (zero-extension): a ∈ [lo, hi] ∩ [0, 2^n − 1] - SIGNED. *)
let ext_cast_constraint ~(is_signed : bool) (env : AI.t) (a : exp)
    (cstr : wordset) : wordset option =
  match denote_operand env a with
  | Some a_ws ->
    let n = WordSet.bitwidth a_ws in
    let w = WordSet.bitwidth cstr in
    if w <= n then None
    else
      let zero = Word.zero w in
      let two_n =
        Word.lshift (Word.one w) (Word.of_int ~width:w n) in
      let half =
        Word.lshift (Word.one w) (Word.of_int ~width:w (n - 1)) in
      let maxn = Word.pred two_n in
      (match WordSet.min_elem cstr, WordSet.max_elem cstr with
       | Some lo, Some hi ->
         let pieces =
           if not is_signed then
             (* zero-extension: a = v ∈ [0, 2^n − 1] *)
             if Word.(>) lo maxn then []
             else [ (lo, Word.min hi maxn) ]
           else begin
             (* sign-extension: the positive half (sext(a) = a) and the negative half (sext(a) = 2^w − 2^n + a) *)
             let pos =
               if Word.(>) lo (Word.pred half) then []
               else [ Word.max lo zero, Word.min hi (Word.pred half) ] in
             let neg =
               let neg_sext_lo =
                 Word.sub (Word.ones w) (Word.pred half) in
               let lo' = Word.max lo neg_sext_lo in
               let hi' = Word.min hi (Word.ones w) in
               if Word.(>) lo' hi' then []
               else
                 (* a = v + 2^n (mod 2^w) — the wrap lands in [2^(n−1), 2^n − 1] *)
                 [ Word.add lo' two_n, Word.add hi' two_n ] in
             pos @ neg
           end
         in
         (match pieces with
          | [] -> None
          | (p0, p1) :: rest ->
            let lo' =
              List.fold rest ~init:p0 ~f:(fun acc (l, _) ->
                  Word.min acc l) in
            let hi' =
              List.fold rest ~init:p1 ~f:(fun acc (_, h) ->
                  Word.max acc h) in
            (* the pieces' words carry the WIDER constraint width [w] — truncate to the pre-image's width [n] (the pieces' values are < 2^n by construction — the truncation is the identity there; the BAP's mixed-width interval would otherwise reject the pair) *)
            interval_of_bounds n
              (Word.extract_exn ~hi:(n - 1) lo')
              (Word.extract_exn ~hi:(n - 1) hi'))
       | _ -> None)
  | None -> None

(* [low_cast_constraint env a cstr]: The LOW-cast (truncation) row — v := cast LOW n a (v's width n < a's width w), the constraint [vlo, vhi] on v: the pre-image a's low n bits ∈ [vlo, vhi] — the pieces [vlo + j·2^n, vhi + j·2^n] hulled to the circular. *)
let low_cast_constraint (env : AI.t) (a : exp) (cstr : wordset)
    : wordset option =
  match denote_operand env a with
  | Some a_ws ->
    let w = WordSet.bitwidth a_ws in
    let n = WordSet.bitwidth cstr in
    if n >= w then None
    else
      (match WordSet.min_elem cstr, WordSet.max_elem cstr with
       | Some vlo, Some vhi ->
         (* the constraint's words carry the width n — zero-extend to the pre-image's width w (the BAP's mixed-width arithmetic truncates to the narrowest — a wrong window) *)
         let vlo_w = Word.extract_exn ~hi:(w - 1) vlo in
         let vhi_w = Word.extract_exn ~hi:(w - 1) vhi in
         let two_n =
           Word.lshift (Word.one w) (Word.of_int ~width:w n) in
         let hi_a = Word.add vhi_w (Word.sub (Word.ones w) two_n) in
         interval_of_bounds w vlo_w hi_a
       | _ -> None)
  | None -> None

(* [extract_constraint env a hi lo cstr]: the Extract(hi, lo, a) row — v's width n = hi − lo + 1, the constraint [vlo, vhi] on v: a's bits [hi..lo] ∈ [vlo, vhi] — the embedding [vlo << lo, (vhi+1) << lo − 1] hulled over the don't-care bits (the low bits 1, the bits above hi 1). *)
let extract_constraint (env : AI.t) (a : exp) (hi : int) (lo : int)
    (cstr : wordset) : wordset option =
  match denote_operand env a with
  | Some a_ws ->
    let w = WordSet.bitwidth a_ws in
    let n = WordSet.bitwidth cstr in
    if n <> hi - lo + 1 then None
    else
      (match WordSet.min_elem cstr, WordSet.max_elem cstr with
       | Some vlo, Some vhi ->
         let shift = Word.of_int ~width:w lo in
         let lo_a = Word.lshift vlo shift in
         let hi_emb =
           Word.pred (Word.lshift (Word.succ vhi) shift) in
         let hi_a =
           if hi + 1 >= w then hi_emb
           else
             Word.add hi_emb
               (Word.sub (Word.ones w)
                  (Word.lshift (Word.one w)
                     (Word.of_int ~width:w (hi + 1)))) in
         interval_of_bounds w lo_a hi_a
       | _ -> None)
  | None -> None

(* [def_constraints ~refineable_var env d cstr]: The def-level inverse for the backward walk — [v := rhs] with the constraint [cstr] on v: refine the env (the cell meet for a Load producer, the word meets for the BinOp/Cast operands — refineable-gated) and return the. *)
let def_constraints ~(sol : (tid, AI.t) Solution.t) (env : AI.t ref)
    (d : def term) (blk : blk term) (live : Live.t) (cstr : wordset)
    : (var * wordset) list =
  match Def.rhs d with
  | Bil.Load (m, a, en, s) ->
    (* The cell gets the constraint; the address vars are not constrained by the loaded value. *)
    env := constrain_cell_on_trace
      ~st:(Solution.get sol (Term.tid blk)) ~live
      !env ~mem:m ~addr:a ~size:s ~endian:en cstr;
    []
  | Bil.BinOp (Bil.LSHIFT, a, b) ->
    (* v = a << k with k a literal < width (the refine_chain LSHIFT row, ported to the dataflow): a' = [lo >> k, hi >> k] (sound; imprecise on the low bits) *)
    let width = WordSet.bitwidth cstr in
    (match b with
     | Bil.Int k -> (
         match Word.to_int k with
         | Ok kk when kk >= 0 && kk < width -> (
             match WordSet.min_elem cstr, WordSet.max_elem cstr with
             | Some lo, Some hi ->
               let lo_a =
                 WordSet.rshift (WordSet.singleton lo)
                   (WordSet.singleton k) in
               let hi_a =
                 WordSet.rshift (WordSet.singleton hi)
                   (WordSet.singleton k) in
               (match WordSet.min_elem lo_a, WordSet.max_elem hi_a with
                | Some lo', Some hi' -> (
                    match interval_of_bounds width lo' hi' with
                    | Some a' -> (
                        match a with
                        | Bil.Var av -> [ (Var.base av, a') ]
                        | _ -> [])
                    | None -> [])
                | _ -> [])
             | _ -> [])
         | _ -> [])
     | _ -> [])
  | Bil.BinOp (op, a, b) ->
    (* The pre-image pairs join the live set; the WORD values are NOT met into the view env here — the walk's fixpoint re-runs the inverse at every iteration and a repeated meet would drift the view (the D4 class: the iterate view lost {4} to the circular hull and gained the wrap). *)
    (match denote_operand !env a, denote_operand !env b with
     | Some a_ws, Some b_ws ->
       (match operand_constraints op cstr a_ws b_ws with
        | a', b' ->
          let pairs = ref [] in
          (match a, a' with
           | Bil.Var av, Some a_c ->
             pairs := (Var.base av, a_c) :: !pairs
           | _ -> ());
          (match b, b' with
           | Bil.Var bv, Some b_c ->
             pairs := (Var.base bv, b_c) :: !pairs
           | _ -> ());
          !pairs)
     | _ -> [])
  | Bil.Cast (Bil.HIGH, sz, a) ->
    (match high_cast_constraint !env a sz cstr with
     | Some a' -> (
         match a with
         | Bil.Var av -> [ (Var.base av, a') ]
         | _ -> [])
     | None -> [])
  | Bil.Cast (ct, _, a) when
      (match ct with Bil.SIGNED | Bil.UNSIGNED -> true | _ -> false) ->
    (match ext_cast_constraint
       ~is_signed:(match ct with Bil.SIGNED -> true | _ -> false)
       !env a cstr with
     | Some a' -> (
         match a with
         | Bil.Var av -> [ (Var.base av, a') ]
         | _ -> [])
     | None -> [])
  | Bil.Cast (Bil.LOW, _, a) ->
    (* v := cast LOW a — the truncation rule: the pre-image is the periodic hull [vlo, vhi + 2^n − 1]-class (the constraint's words carry the truncated width; [low_cast_constraint] zero-extends them to the pre-image's width). *)
    (match low_cast_constraint !env a cstr with
     | Some a' -> (
         match a with
         | Bil.Var av -> [ (Var.base av, a') ]
         | _ -> [])
     | None -> [])
  | Bil.UnOp (Bil.NOT, a) ->
    (* v := NOT a — the bijection: v ∈ cstr ⟺ a ∈ NOT cstr (the complement is exact on the wordset domain). *)
    (match a with
     | Bil.Var av -> [ (Var.base av, WordSet.lnot cstr) ]
     | _ -> [])
  | Bil.UnOp (Bil.NEG, a) ->
    (* v := NEG a — the wrapped mirror: v ∈ cstr ⟺ a ∈ neg cstr. *)
    (match a with
     | Bil.Var av -> [ (Var.base av, WordSet.neg cstr) ]
     | _ -> [])
  | Bil.Var g ->
    (* v := g — the identity: g ∈ cstr. *)
    [ (Var.base g, cstr) ]
  | Bil.Concat (a, b) ->
    (* v := a ‖ b — the slice rules: the high part's constraint is the extracted high slice of cstr, the low part's the low slice. *)
    (match a, b with
     | Bil.Var av, Bil.Var bv ->
       (match denote_operand !env b with
        | Some b_ws ->
          let bw = WordSet.bitwidth b_ws in
          let w = WordSet.bitwidth cstr in
          if bw >= w then [ (Var.base av, cstr) ]
          else
            [ (Var.base av, WordSet.extract ~hi:(w - 1) ~lo:bw cstr);
              (Var.base bv, WordSet.extract ~hi:(bw - 1) ~lo:0 cstr) ]
        | None -> [])
     | _ -> [])
  | Bil.Extract (hi, lo, a) ->
    (* v := Extract(hi, lo, a) — the embedding rule. *)
    (match extract_constraint !env a hi lo cstr with
     | Some a' -> (
         match a with
         | Bil.Var av -> [ (Var.base av, a') ]
         | _ -> [])
     | None -> [])
  | _ -> []

(* [reverse_def_walk ~defs ~refineable_var env live blk]: The reverse-def walk of one block — the defs in REVERSE order, the def inverse at each live lhs (the lhs leaves the live set, the rhs's derived pairs join it); a def whose lhs is not live is skipped. *)
let reverse_def_walk ~(defs : (def term * bool) Var.Map.t)
    ~(sol : (tid, AI.t) Solution.t)
    (env : AI.t ref) (live : Live.t)
    (blk : blk term) : Live.t =
  let live = ref live in
  Term.enum def_t blk |> Seq.to_list |> List.rev
  |> List.iter ~f:(fun d ->
      let v = Var.base (Def.lhs d) in
      match Live.find v !live with
      | None -> ()   (* the lhs not live: skip *)
      | Some cstr ->
        match Core.Map.find defs v with
        | Some _ ->
          (* the producer subtraction: the constraint applies only to the values THIS def produced *)
          let post_v =
            match Var.typ (Def.lhs d) with
            | Type.Imm w ->
              Some (AI.find_word w
                      (denote_def d (Solution.get sol (Term.tid blk)))
                      (Def.lhs d))
            | Type.Mem _ | Type.Unk -> None in
          (match post_v with
           | Some pv ->
             let cstr' = WordSet.meet cstr pv in
             if Word.is_zero (WordSet.cardinality cstr') then
               (* the def produced nothing satisfying the constraint: its pre-image is empty — the lhs leaves the live set *)
               live := Live.remove v !live
             else begin
               live := Live.remove v !live;
               let pairs = def_constraints ~sol env d blk !live cstr' in
               List.iter pairs ~f:(fun (pv', pc) ->
                   live := Live.add pv' pc !live)
             end
           | None -> live := Live.remove v !live)
        | _ -> ());
  !live

(* [route_phi_constraints ~sol env target live blk]: The phi propagation for the edge toward [target] — a live phi lhs at the block's START propagates its constraint to the phi's source values whose predecessor tid is [target] (a Var source joins the live set; a Load. *)
let route_phi_constraints ~(sol : (tid, AI.t) Solution.t)
    (env : AI.t ref) (target : tid)
    (live : Live.t) (blk : blk term) : Live.t =
  let live = ref live in
  Term.enum phi_t blk |> Seq.iter ~f:(fun ph ->
      let v = Var.base (Phi.lhs ph) in
      match Live.find v !live with
      | None -> ()
      | Some cstr ->
        live := Live.remove v !live;
        Phi.values ph |> Seq.iter ~f:(fun (ptid, e) ->
            if Tid.equal ptid target then
              match e with
              | Bil.Var sv ->
                live := Live.add (Var.base sv) cstr !live
              | Bil.Load (m, a, en, s) ->
                (* the trace-exact cell meet (M2) — the phi's load source's cell on this trace *)
                env := constrain_cell_on_trace
                  ~st:(Solution.get sol (Term.tid blk)) ~live:!live
                  !env ~mem:m ~addr:a ~size:s ~endian:en cstr
              | _ -> ()));
  !live

(* [refine_edge ~sol ~defs ~stores env sub blk seeds]: The COMPLETE backward traversal — the Graphlib fixpoint over the REVERSED CFG ([~rev:true] — the live sets flow from the guard to the PREDECESSORS, the per-edge [~target] routing the phi sources) until the live sets. *)
let refine_edge ~(sol : (tid, AI.t) Solution.t)
    ?(defs : (def term * bool) Var.Map.t option = None)
    ?(stores : def term list option = None)
    (env : AI.t) (sub : sub term) (blk : blk term)
    (seeds : edge_constraint list) : AI.t * (tid, Live.t) Solution.t =
  match defs with
  | None -> env, Solution.create Tid.Map.empty Live.empty
  | Some defs_map ->
    let cfg =
      Graphs.Tid.Node.remove Graphs.Tid.start (Sub.to_graph sub)
      |> Graphs.Tid.Node.remove Graphs.Tid.exit in
    let seed_constraints, env0 =
      List.fold seeds ~init:(Live.empty, env) ~f:(fun (m, e) -> function
          | Var (v, c) ->
            (* The guard's own edge constraint meets the view env ONCE: on the taken trace the compared operand satisfies [c]. A width-mismatched or unchanged meet leaves the env as-is; a disjoint meet makes the trace's view bottom (no state on this edge satisfies the constraint). *)
            let e' = match Var.typ v with
              | Type.Imm w ->
                let cur = AI.find_word w e v in
                let m2 = WordSet.meet cur c in
                if Word.is_zero (WordSet.cardinality m2) then AI.bottom
                else if WordSet.equal m2 cur then e
                else AI.add_word e ~key:v ~data:m2
              | Type.Mem _ | Type.Unk -> e in
            Live.add v c m, e'
          | Cell (mem, addr, size, endian, cstr) ->
            m, constrain_cell_on_trace ~st:env ~live:m e
              ~mem:mem ~addr:addr ~size:size ~endian:endian cstr
          | Infeasible -> m, AI.bottom) in
    let env = ref env0 in
    let live_sol =
      Cbat_contextual_fixpoint.fixpoint (module Graphs.Tid)
        ~init:(Solution.create (Tid.Map.singleton (Term.tid blk) seed_constraints)
                 Live.empty)
        ~equal:Live.equal ~merge:Live.join
        ~steps:256 ~rev:true
        ~f:(fun ~source:n ->
            fun live ->
              match Term.find blk_t sub n with
              | Some b ->
                (* The guard block's own constraints are part of its walk INPUT (joined with the incoming live), so the guard's defs are walked over the seed — a fixture whose guard block defines the compared operand (e.g. *)
                let live =
                  if Tid.equal (Term.tid b) (Term.tid blk)
                  then Live.join live seed_constraints
                  else live in
                let base =
                  reverse_def_walk ~defs:defs_map ~sol
                    env live b in
                fun ~target:t ->
                  route_phi_constraints ~sol env t
                    base b
              | None -> fun ~target:_ -> live)
        ~step:(fun _ _ -> fun _ x' -> x')
        cfg in
    (* The guard block's own value in the fixpoint is the raw seed (the init's [Const] — a block with no predecessors never gets its walk instantiated). *)
    let live_sol =
      match Term.find blk_t sub (Term.tid blk) with
      | Some gb ->
        let walked =
          reverse_def_walk ~defs:defs_map ~sol env
            (Live.join (Solution.get live_sol (Term.tid blk))
               seed_constraints) gb in
        Solution.derive live_sol
          ~f:(fun n _ ->
              if Tid.equal n (Term.tid blk) then Some walked else None)
          Live.empty
      | None -> live_sol in
    !env, live_sol

(* The per-sub/per-block ANALYSIS context of the backward walk, bundled into ONE record (the user's signature decision): refineable (the per-sub relevant set, [refineable_of_sub]), defs (the per-sub def-chain map), stores (the per-sub store list), flag_state (the per-block flag record). *)
type analysis_ctx = {
  refineable : Var.Set.t option;
  defs : (def term * bool) Var.Map.t option;
  stores : def term list option;
  flag_state : (var * Bil.binop * exp * word) option;
  (* The backward-refinement dataflow : the sub + the guard block — the CFG the complete backward traversal runs over (both None for the direct API -> the traversal is skipped). *)
  sub : sub term option;
  blk : blk term option;
}


(* ================================================================== *)
(* the edge_constraint collector (the trace-partitioning design, *)
(* docs/trace-partitioning-plan.md §3): the PURE constraint *)
(* derivation. The guard's taken-edge constraint [cstr] on [cond] *)
(* is decomposed into the leaf seeds for the backward dataflow (M4). *)
(* The env is an INPUT (the guard's state — the value lookups the *)
(* rows need); NOTHING is mutated (the meets belong to the dataflow). *)
(* TOTAL: every shape has a row (the NO-FALLBACK doctrine — the *)
(* identity / no-edge_constraint for the trivial shapes, never a stop). *)
(* ================================================================== *)

(* [guard_op_of_binop op]: the BIL comparison op -> the guard_op (the greater-forms exist only in the internal enum). *)
let guard_op_of_binop (op : Bil.binop) : guard_op = match op with
  | Bil.LT -> ULT
  | Bil.LE -> ULE
  | Bil.EQ -> EQ
  | Bil.SLT -> SLT
  | Bil.SLE -> SLE
  | _ -> EQ

(* [complement_guard_op op]: the FALSE-edge guard_op (the complement of the TRUE-edge row): ULT <-> UGE, ULE <-> UGT, EQ -> (EQ; NEQ is handled separately), SLT <-> SGE, SLE <-> SGT. The BIL-comparison entry point is [complement_binop_guard] below. *)
let complement_guard_op (op : guard_op) : guard_op = match op with
  | ULT -> UGE | ULE -> UGT
  | UGT -> ULT | UGE -> ULE
  | EQ -> EQ
  | SLT -> SGE | SLE -> SGT
  | SGT -> SLT | SGE -> SLE

(* [complement_binop_guard op]: the FALSE-edge guard_op of a BIL comparison (via [guard_op_of_binop] — the NEQ / non-comparison inputs land on EQ, as before). *)
let complement_binop_guard (op : Bil.binop) : guard_op =
  complement_guard_op (guard_op_of_binop op)

(* [flip_guard_op op]: the const-first flip — (c op e) becomes the row on e: ULT -> UGT, ULE -> UGE, SLT -> SGT, SLE -> SGE, EQ stays. *)
let flip_guard_op (op : guard_op) : guard_op = match op with
  | ULT -> UGT | UGT -> ULT
  | ULE -> UGE | UGE -> ULE
  | SLT -> SGT | SGT -> SLT
  | SLE -> SGE | SGE -> SLE
  | EQ -> EQ

(* [guard_constraint w op c]: The TRUE-edge row on the operand of (e op c) — the complete set (docs/trace-partitioning-plan.md §4.1): the two-piece signed rows (the non-negativity gates REMOVED — the negative half is always < c signed), the UGT/UGE/SGT/SGE direct rows. *)
let guard_constraint (w : int) (op : guard_op) (c : word)
    : wordset option =
  let maxw = Word.ones w in
  let half = Word_ops.half w in
  let iv lo hi = interval_of_bounds w lo hi in
  match op with
  | EQ -> Some (WordSet.singleton c)
  | ULT ->
    (if Word.is_zero c then None
     else iv (Word.zero w) (Word.pred c))
  | ULE -> iv (Word.zero w) c
  | UGT ->
    (if Word.(=) c maxw then None
     else iv (Word.succ c) maxw)
  | UGE -> iv c maxw
  | SLT ->
    let pos =
      if Word.is_zero c then None
      else iv (Word.zero w) (Word.pred c) in
    (match iv half maxw with
     | Some neg ->
       Some (match pos with
         | Some p -> WordSet.union p neg
         | None -> neg)
     | None -> pos)
  | SLE ->
    (match iv half maxw with
     | Some neg ->
       (match iv (Word.zero w) c with
        | Some lo -> Some (WordSet.union lo neg)
        | None -> Some neg)
     | None -> iv (Word.zero w) c)
  | SGT ->
    (if Word.(=) c (Word.pred half) then None
     else iv (Word.succ c) (Word.pred half))
  | SGE -> iv c (Word.pred half)

(* [overlap_constraints op a_ws b_ws]: The var-vs-var / generic-comparison TRUE rows — the constraint on the LEFT operand from the RIGHT's extrema and vice versa (the L3c4 interval-overlap rows "as today", docs/trace-partitioning-plan.md §4.1) + the. *)
let overlap_constraints (op : Bil.binop) (a_ws : wordset) (b_ws : wordset)
    : wordset option * wordset option =
  let w = WordSet.bitwidth a_ws in
  if WordSet.bitwidth b_ws <> w then None, None
  else
    let half = Word_ops.half w in
    let maxw = Word.ones w in
    let signed =
      match op with Bil.SLT | Bil.SLE -> true | _ -> false in
    let mn_x =
      if signed then WordSet.min_elem_signed a_ws
      else WordSet.min_elem a_ws in
    let mx_y =
      if signed then WordSet.max_elem_signed b_ws
      else WordSet.max_elem b_ws in
    let mn_y =
      if signed then WordSet.min_elem_signed b_ws
      else WordSet.min_elem b_ws in
    let mx_x =
      if signed then WordSet.max_elem_signed a_ws
      else WordSet.max_elem a_ws in
    let provably_nonneg_x =
      match WordSet.max_elem a_ws with
      | Some m -> Word.(<) m half
      | None -> false in
    (match mn_x, mx_y, mn_y, mx_x with
     | Some mn_x, Some mx_y, Some mn_y, Some mx_x ->
       let x_cstr, y_cstr =
         match op with
         | Bil.LT ->
           ((if Word.is_zero mx_y then None
             else interval_of_bounds w (Word.zero w) (Word.pred mx_y)),
            (if Word.(=) mn_x maxw then None
             else interval_of_bounds w (Word.succ mn_x) maxw))
         | Bil.LE ->
           (interval_of_bounds w (Word.zero w) mx_y,
            interval_of_bounds w mn_x maxw)
         | Bil.SLT ->
           ((if Word.(>=) mx_y half then
               interval_of_bounds w half (Word.pred mx_y)
             else if provably_nonneg_x then
               if Word.is_zero mx_y then None
               else interval_of_bounds w (Word.zero w) (Word.pred mx_y)
             else None),
            (if Word.(>=) mn_x half then None
             else interval_of_bounds w (Word.succ mn_x) (Word.pred half)))
         | Bil.SLE ->
           ((if Word.(>=) mx_y half then
               interval_of_bounds w half mx_y
             else if provably_nonneg_x then
               interval_of_bounds w (Word.zero w) mx_y
             else None),
            (if Word.(>=) mn_x half then None
             else interval_of_bounds w mn_x (Word.pred half)))
         | Bil.EQ ->
           let ov = WordSet.meet a_ws b_ws in
           if Word.is_zero (WordSet.cardinality ov)
           then None, None
           else Some ov, Some ov
         | Bil.NEQ ->
           let ov = WordSet.meet a_ws b_ws in
           if Word.is_zero (WordSet.cardinality ov)
           then Some a_ws, Some b_ws
           else Some (WordSet.diff a_ws ov), Some (WordSet.diff b_ws ov)
         | _ -> None, None in
       x_cstr, y_cstr
     | _ -> None, None)

(* [row_for ~env ~ctx e op c]: The taken-edge constraint on the operand [e] of (e op c) — [decoder_constraint] (the provenance- gated signed rows; a PROVEN non-negative operand gets the exact single piece, anything else the TOTAL two-piece rule — the. *)
let row_for ~(env : AI.t) ?(ctx : analysis_ctx option)
    (e : exp) (op : guard_op) (c : word) : wordset option =
  let cur = match denote_imm_exp e env with
    | Ok ws -> Some ws
    | Error _ -> None in
  match ctx with
  | None -> guard_constraint (Word.bitwidth c) op c
  | Some { defs; stores; _ } ->
    let known_nonneg = known_nonneg_of ~defs ~stores e in
    (match decoder_constraint ~cur ~known_nonneg op c with
     | Some cstr -> Some cstr
     | None -> guard_constraint (Word.bitwidth c) op c)

(* [edge_constraints ~env ?ctx cond cstr]: The pure constraint derivation — the guard's edge constraint decomposed into the leaf seeds. *)
let rec edge_constraints ~(env : AI.t) ?(ctx : analysis_ctx option)
    (cond : exp) (cstr : wordset) : edge_constraint list =
  (* The signed rows are represented by the wordset domain as a two-piece set. *)
  match cond with
  | Bil.Var v ->
    begin match Var.typ v with
    | Type.Imm 1 ->
      (* the bare-flag shape: the {1}/{0} edge_constraint + the flag-state recovery (the comparison constraint applies on the flag-SET edge) *)
      let seeds = ref [ Var (Var.base v, cstr) ] in
      if WordSet.bitwidth cstr = 1
         && WordSet.elem Word.b1 cstr
      then
        (match ctx with
         | Some { flag_state = Some (fv, op, e0, c0); _ }
           when Var.same fv v ->
           (match denote_imm_exp e0 env with
            | Ok cur_e ->
              (match row_for ~env ?ctx e0 (guard_op_of_binop op) c0 with
               | Some cstr_e ->
                 seeds := edge_constraints ~env ?ctx e0 cstr_e @ !seeds
               | None -> ())
            | Error _ -> ())
         | _ -> ());
      !seeds
    | Type.Imm w when w >= 2 -> [ Var (Var.base v, cstr) ]
    | Type.Imm _ | Type.Mem _ | Type.Unk -> []
    end
  | Bil.Int c ->
    (* the constant: the constraint disjoint -> the edge has NO states (the Bakhirkin case — the view becomes bottom) *)
    if WordSet.elem c cstr then [] else [ Infeasible ]
  | Bil.BinOp (op, a, b) ->
    begin match op with
    | Bil.EQ | Bil.NEQ | Bil.LT | Bil.LE | Bil.SLT | Bil.SLE ->
      let acc = ref [] in
      let side (side : [ `True | `False ]) : unit =
        match a, b with
        | _, Bil.Int c0 ->
          let cstr_opt =
            match side, op with
            | `True, Bil.NEQ ->
              Some (WordSet.diff (WordSet.top (Word.bitwidth c0))
                      (WordSet.singleton c0))
            | `False, Bil.NEQ ->
              Some (WordSet.singleton c0)
            | `False, Bil.EQ ->
              (* the EQ's FALSE side = the NEQ complement (the complement_guard_op maps EQ to itself — the guard_op has no NEQ) *)
              Some (WordSet.diff (WordSet.top (Word.bitwidth c0))
                      (WordSet.singleton c0))
            | `True, _ ->
              row_for ~env ?ctx a (guard_op_of_binop op) c0
            | `False, _ ->
              row_for ~env ?ctx a (complement_binop_guard op) c0 in
          (match cstr_opt with
           | Some cstr_a ->
             acc := edge_constraints ~env ?ctx a cstr_a @ !acc
           | None -> ())
        | Bil.Int c0, e0 ->
          let cstr_opt =
            match side, op with
            | `True, Bil.NEQ ->
              Some (WordSet.diff (WordSet.top (Word.bitwidth c0))
                      (WordSet.singleton c0))
            | `False, Bil.NEQ ->
              Some (WordSet.singleton c0)
            | `False, Bil.EQ ->
              Some (WordSet.diff (WordSet.top (Word.bitwidth c0))
                      (WordSet.singleton c0))
            | `True, _ ->
              row_for ~env ?ctx e0 (flip_guard_op (guard_op_of_binop op)) c0
            | `False, _ ->
              row_for ~env ?ctx e0 (flip_guard_op (complement_binop_guard op)) c0 in
          (match cstr_opt with
           | Some cstr_e ->
             acc := edge_constraints ~env ?ctx e0 cstr_e @ !acc
           | None -> ())
        | Bil.Var x, Bil.Var y ->
          (match Var.typ x, Var.typ y with
           | Type.Imm w, Type.Imm wy when w = wy ->
             let cur_x = AI.find_word w env x in
             let cur_y = AI.find_word w env y in
             if WordSet.bitwidth cur_x <> w
                || WordSet.bitwidth cur_y <> w
             then ()
             else
               let x_true, y_true = overlap_constraints op cur_x cur_y in
               let rows =
                 match side with
                 | `True -> x_true, y_true
                 | `False ->
                   (match x_true with
                    | Some xc -> Some (WordSet.diff cur_x xc)
                    | None -> None),
                   (match y_true with
                    | Some yc -> Some (WordSet.diff cur_y yc)
                    | None -> None) in
               (match rows with
                | Some xc, Some yc ->
                  acc :=
                    edge_constraints ~env ?ctx (Bil.Var x) xc
                    @ edge_constraints ~env ?ctx (Bil.Var y) yc
                    @ !acc
                | Some xc, None ->
                  acc := edge_constraints ~env ?ctx (Bil.Var x) xc @ !acc
                | None, Some yc ->
                  acc := edge_constraints ~env ?ctx (Bil.Var y) yc @ !acc
                | None, None -> ())
           | _ -> ())
        | _ ->
          (* the generic comparison (non-const non-var operands): the rows apply with the OTHER operand's denoted value-set, then the recursion into both operands' structures *)
          (match denote_operand env a, denote_operand env b with
           | Some a_ws, Some b_ws ->
             let x_true, y_true = overlap_constraints op a_ws b_ws in
             let rows =
               match side with
               | `True -> x_true, y_true
               | `False ->
                 (match x_true with
                  | Some xc -> Some (WordSet.diff a_ws xc)
                  | None -> None),
                 (match y_true with
                  | Some yc -> Some (WordSet.diff b_ws yc)
                  | None -> None) in
             (match rows with
              | Some xc, Some yc ->
                acc :=
                  edge_constraints ~env ?ctx a xc
                  @ edge_constraints ~env ?ctx b yc @ !acc
              | Some xc, None ->
                acc := edge_constraints ~env ?ctx a xc @ !acc
              | None, Some yc ->
                acc := edge_constraints ~env ?ctx b yc @ !acc
              | None, None -> ())
           | _ -> ()) in
      if WordSet.elem Word.b1 cstr then side `True;
      if WordSet.elem Word.b0 cstr then side `False;
      if not (WordSet.elem Word.b1 cstr)
         && not (WordSet.elem Word.b0 cstr)
      then [ Infeasible ]
      else !acc
    | Bil.PLUS | Bil.MINUS | Bil.TIMES | Bil.DIVIDE | Bil.SDIVIDE
    | Bil.MOD | Bil.SMOD | Bil.LSHIFT | Bil.RSHIFT | Bil.ARSHIFT
    | Bil.AND | Bil.OR | Bil.XOR ->
      (* the producer rows ([operand_constraints]) on the operands + the recursion into each operand's structure *)
      (match denote_operand env a, denote_operand env b with
       | Some a_ws, Some b_ws ->
         (match operand_constraints op cstr a_ws b_ws with
          | a', b' ->
            let acc = ref [] in
            (match a' with
             | Some a_c ->
               acc := edge_constraints ~env ?ctx a a_c @ !acc
             | None -> ());
            (match b' with
             | Some b_c ->
               acc := edge_constraints ~env ?ctx b b_c @ !acc
             | None -> ());
            !acc)
       | _ -> [])
    end
  | Bil.Load (m, a, en, s) ->
    (* e IS a load: the cell edge_constraint — the trace-exact meet in the dataflow *)
    [ Cell (m, a, s, en, cstr) ]
  | Bil.UnOp (Bil.NOT, e) ->
    (* the bijection row — no gates (the {1}-singleton gate and the comparison-shape stop are removed) *)
    edge_constraints ~env ?ctx e (WordSet.lnot cstr)
  | Bil.UnOp (Bil.NEG, e) ->
    edge_constraints ~env ?ctx e (WordSet.neg cstr)
  | Bil.Cast (ct, sz, a) ->
    (* the cast rows: HIGH/SIGNED/UNSIGNED/LOW *)
    let pre = match ct with
      | Bil.HIGH -> high_cast_constraint env a sz cstr
      | Bil.SIGNED -> ext_cast_constraint ~is_signed:true env a cstr
      | Bil.UNSIGNED -> ext_cast_constraint ~is_signed:false env a cstr
      | Bil.LOW -> low_cast_constraint env a cstr in
    (match pre with
     | Some a' -> edge_constraints ~env ?ctx a a'
     | None -> [])
  | Bil.Concat (a, b) ->
    (* the slice rows: the high part's constraint = the extracted high slice of the constraint; the low part's = the low slice *)
    (match denote_operand env b with
     | Some b_ws ->
       let bw = WordSet.bitwidth b_ws in
       let w = WordSet.bitwidth cstr in
       if bw >= w then edge_constraints ~env ?ctx a cstr
       else
         edge_constraints ~env ?ctx a
           (WordSet.extract ~hi:(w - 1) ~lo:bw cstr)
         @ edge_constraints ~env ?ctx b
             (WordSet.extract ~hi:(bw - 1) ~lo:0 cstr)
     | None -> [])
  | Bil.Extract (hi, lo, a) ->
    (match extract_constraint env a hi lo cstr with
     | Some a' -> edge_constraints ~env ?ctx a a'
     | None -> [])
  | Bil.Ite (_, t, f) ->
    (* the two-branch union: the constraint holds on the taken edge whichever branch produced the value *)
    edge_constraints ~env ?ctx t cstr @ edge_constraints ~env ?ctx f cstr
  | Bil.Let (_, _, e) ->
    edge_constraints ~env ?ctx e cstr
  | Bil.Unknown _ -> []
  | Bil.Store (_, _, u, _, _) ->
    (* the value-side row: the cell's constraint transfers to the stored value's trace *)
    edge_constraints ~env ?ctx u cstr


(* The per-guard views (the trace-partitioning design, docs/trace-partitioning-plan.md §1.2): the two views of one guard — the ITERATE view (the taken-edge trace: the guard's invariant state refined by the walk) and the. *)
type edge_view = {
  guard_tid : tid;
  (* the edge whose condition defines this view; the target lets clients distinguish the taken/body edge from the fallthrough edge when a BAP block contains the explicit complementary pair of jumps. *)
  target_tid : tid option;
  taken : AI.t;
  fallthrough : AI.t;
  live_taken : (tid, Live.t) Solution.t;
  live_fallthrough : (tid, Live.t) Solution.t;
}



(* The direct-API backward refinement ([inverse_denote_exp]) is the M3 collector ([edge_constraints]) applied at the leaves — see the function's own comment below; this historical block (the pre- Refactor-1b structural walker) was deleted 2026-08-15. *)

(* L-S2 (oracle item 8) — [refineable_var_of refineable v]: the verbatim refineability closure of [inverse_denote_exp] and [assume_jump_cond] (restriction OFF -> true; ON -> base in set). *)
let refineable_var_of (refineable : Var.Set.t option) (v : var) : bool =
  Option.value_map refineable ~default:false
    ~f:(fun set -> Core.Set.mem set (Var.base v))

(* L-S2 (oracle item 7) — [apply_operand_constraint ~defs refineable_var env e cstr]: the meet-if-Var-then-constrain_def_chain tail of the jcc-decoder pre-step (genuine-subset, refineable-gated meet; None defs -> env). *)
let apply_operand_constraint
    ~(defs : (def term * bool) Var.Map.t option)
    (refineable_var : var -> bool) (env : AI.t) (e : exp) (cstr : wordset)
    : AI.t =
  match defs with
  | None -> env
  | Some dm ->
    (match e with
     | Bil.Var x ->
       let env' = meet_var refineable_var env x cstr in
       constrain_def_chain ~defs:dm refineable_var env'
         (Bil.Var x) cstr
     | _ ->
       constrain_def_chain ~defs:dm refineable_var env e cstr)

(* [inverse_denote_exp ?ctx cond cstr env]: Refine [env] under the taken-edge constraint [cstr] on [cond], walking the CONDITION STRUCTURE (the mirror of [denote_exp]) and recursing into sub-expressions; the leaves call the existing backward kernels. *)
(* [inverse_denote_exp ?ctx cond cstr env]: Refine [env] under the taken-edge constraint [cstr] on [cond] — the DIRECT-API backward refinement (the fixpoint path no-ops below: Phase B — [edge_views_of] — owns the refinement there; the [sub = Some _] marker makes. *)
let inverse_denote_exp ?(ctx : analysis_ctx option) (cond : exp)
    (cstr : wordset) (env : AI.t) : AI.t =
  match ctx with
  | None -> env
  | Some { sub = Some _; _ } -> env
  | Some ctx ->
    let refineable_var (v : var) : bool =
      refineable_var_of ctx.refineable v in
    List.fold (edge_constraints ~env ~ctx cond cstr) ~init:env
      ~f:(fun env seed ->
        match seed with
        | Var (v, c) -> meet_var refineable_var env v c
        | Cell (mem, addr, size, endian, cstr) ->
          constrain_cell refineable_var env ~mem ~addr ~size ~endian cstr
        | Infeasible -> env)

(* L3c-1 — the flag-state record (the Laporte / Blazy-Laporte-Pichardie design): per BLOCK, the (flag var, op, e, c) of the LAST in-scope 1-bit def whose rhs is a comparison [e op c] the walk understands (comparison_constraint's LT/LE/EQ/SLT/SLE vs constant — L3c-2 added the signed rows). *)

(* L-A2 — the per-block flag GROUP. *)
type flag_group = {
  flags : (var * def term) Var.Map.t;
  (* the block's 1-bit defs (the lifter's flag vars), keyed by [Var.base] lhs: (lhs, def) pairs — the defs the gate looks up for the idiom flags *)
  cmp : def term option;
  (* [t := e - c]: For the RECORD's (e, c), by structural equality ([Exp.equal] on the operand, [Word.equal] on the constant — the BIR reuses the SSA var/exp objects, so the equality is exact); None = no such def in the block = the gate fails (the flags cannot be bound to the record's comparison). *)
}

let flag_state_of_block (b : blk term) :
    (var * Bil.binop * exp * word) option * flag_group =
  let ds = Term.enum def_t b |> Seq.to_list in
  let understood (op : Bil.binop) : bool =
    match op with
    | Bil.LT | Bil.LE | Bil.EQ | Bil.SLT | Bil.SLE -> true
    | _ -> false in
  let rec go (st : (var * Bil.binop * exp * word) option)
      (ds : def term list) : (var * Bil.binop * exp * word) option =
    match ds with
    | [] -> st
    | d :: rest ->
      let lhs = Def.lhs d in
      let lhs_base = Var.base lhs in
      (* (a) any def of a free var of the recorded operand clears *)
      let st =
        match st with
        | Some (fv, op, e, c)
          when Exp.free_vars e |> Core.Set.exists ~f:(fun x ->
              Var.same x lhs_base) ->
          None
        | _ -> st in
      (* (b) a def of the flag var itself: an understood comparison re-binds; anything else clears *)
      let st =
        match st, Var.typ lhs, Def.rhs d with
        | Some (fv, _, _, _), Type.Imm 1, Bil.BinOp (op', e', Bil.Int c') ->
          if Var.same fv lhs_base then
            (if understood op' then Some (lhs, op', e', c') else None)
          else st
        | Some (fv, _, _, _), Type.Imm 1, _ ->
          if Var.same fv lhs_base then None else st
        | None, Type.Imm 1, Bil.BinOp (op', e', Bil.Int c') ->
          if understood op' then Some (lhs, op', e', c') else None
        | _ -> st in
      go st rest
  in
  let record = go None ds in
  (* the flag group: every 1-bit def, keyed by [Var.base] lhs *)
  let flags =
    Term.enum def_t b
    |> Seq.fold ~init:Var.Map.empty ~f:begin fun g d ->
      let lhs = Def.lhs d in
      match Var.typ lhs with
      | Type.Imm 1 -> Core.Map.set g ~key:(Var.base lhs) ~data:(lhs, d)
      | Type.Imm _ | Type.Mem _ | Type.Unk -> g
    end in
  (* the t-def for the record's (e, c) — structural equality *)
  let cmp =
    match record with
    | None -> None
    | Some (_, _, e, c) ->
      List.find ds ~f:begin fun d ->
        match Def.rhs d with
        | Bil.BinOp (Bil.MINUS, e', Bil.Int c') ->
          Exp.equal e' e && Word.equal c' c
        | _ -> false
      end in
  (record, { flags; cmp })

(* L-A2 — [same_comparison_group fg fv e cond]: the same-comparison GATE for the compound-guard (jcc-decoder) arm of [assume_jump_cond] (the oracle's Q3(d) group extension). *)
let same_comparison_group (fg : flag_group) (fv : var) (e : exp)
    (cond : exp) : bool =
  (* [is_flag v]: [v] is one of the lifter's 1-bit flag names *)
  let is_flag (v : var) : bool =
    match Var.name v with
    | "CF" | "ZF" | "SF" | "OF" -> true
    | _ -> false in
  (* the flags to check: every flag var mentioned in [cond], plus the record's own [fv] (its def is the record's understood comparison — the subset check passes trivially; included per the signature) *)
  let flag_vars =
    Exp.free_vars cond
    |> Core.Set.fold ~init:Var.Set.empty ~f:begin fun acc v ->
      if is_flag v then Core.Set.add acc (Var.base v) else acc
    end in
  let flag_vars =
    if is_flag fv then Core.Set.add flag_vars (Var.base fv)
    else flag_vars in
  match fg.cmp with
  | None -> false
  | Some td ->
    let t = Def.lhs td in
    let fvs_e = Exp.free_vars e in
    Core.Set.for_all flag_vars ~f:begin fun v ->
      match Core.Map.find fg.flags v with
      | None -> false
      | Some (_, d) ->
        Exp.free_vars (Def.rhs d)
        |> Core.Set.for_all ~f:begin fun w ->
          (* w ∈ free_vars(e) ∪ {t}, by base equality ([Var.same] — the env-key idiom; the BIR reuses the SSA var objects) *)
          Core.Set.exists fvs_e ~f:(fun x -> Var.same w x)
          || Var.same w t
        end
    end

(* The Phase B post-pass driver (the trace-partitioning design, docs/trace-partitioning-plan.md §2.2): over the converged forward solution, run a separate taken/exit walk for every conditional edge. *)
let edge_views_of ?(defs : (def term * bool) Var.Map.t option = None)
    ?(stores : def term list option = None)
    (s : sub term) (sol : (tid, AI.t) Solution.t) : edge_view list =
  match defs with
  | None -> []
  | Some _ ->
    (* The C9-style TAG-RELEVANCE PRUNING : the Phase B per-guard backward walks ([refine_edge]) are the dominant post-pass cost on big subs (measured: ~25s partitioned on date's parse_datetime_body without pruning). *)
    let refineable =
      (* the inline [refineable_of_sub] (defined later in the file): the vars with at least one RELEVANT def — the vars the merged tagging tracks. *)
      Term.enum blk_t s
      |> Seq.concat_map ~f:(Term.enum def_t)
      |> Seq.fold ~init:Var.Set.empty ~f:(fun acc d ->
          let v = Var.base (Def.lhs d) in
          if Term.has_attr d Utils.relevant then Core.Set.add acc v else acc)
    in
    let tag_relevant (cond : exp) : bool =
      Exp.free_vars cond
      |> Core.Set.exists ~f:(fun v ->
          Core.Set.mem refineable (Var.base v))
    in
    Term.enum blk_t s
    |> Seq.concat_map ~f:(fun b ->
        (* [Solution.get] is the block-entry invariant. Guards are evaluated after the block's defs, so Phase B must derive the edge constraints from the block-post state; this is essential for loads/producer chains and Var-vs-Var rows whose operands are defined in the guard block itself. *)
        let blk_state =
          denote_defs b (Solution.get sol (Term.tid b)) in
        let flag_state, flag_group = flag_state_of_block b in
        let ctx : analysis_ctx =
          { refineable = None; defs; stores; flag_state;
            sub = Some s; blk = Some b } in
        let edge_constraints_of (cond : exp) ~(complement : bool)
              : edge_constraint list =
          let recorded_op =
            match flag_state with
            | Some (fv, bop, e, _) ->
              let gop = guard_op_of_binop bop in
              (match cond with
               | Bil.Var v when Var.same fv v -> Some gop
               | Bil.UnOp (Bil.NOT, Bil.Var v)
                 when Var.same fv v -> Some (complement_guard_op gop)
               | _ ->
                 (match decoded_condition cond with
                  | Some decoded
                    when same_comparison_group flag_group fv e cond ->
                    Some decoded
                  | _ -> None))
            | None -> None in
          match recorded_op with
          | Some op ->
            let op = if complement then complement_guard_op op else op in
            (match flag_state with
             | Some (_, _, e, c) ->
               (match row_for ~env:blk_state ~ctx e op c with
                | Some cstr -> edge_constraints ~env:blk_state ~ctx e cstr
                | None -> [Infeasible])
             | None -> [Infeasible])
          | None ->
            let e = if complement then Bil.UnOp (Bil.NOT, cond) else cond in
            edge_constraints ~env:blk_state ~ctx e
              (WordSet.singleton Word.b1) in
        Term.enum jmp_t b
        |> Seq.filter_map ~f:(fun j ->
            let cond = Jmp.cond j in
            match cond with
            | Bil.Int w when Word.(w = Word.b1) -> None
            | _ when not (tag_relevant cond) ->
                (* the guard cannot affect any tag — the invariant view (the sound both-trace fallback) instead of the backward walks. *)
                Some { guard_tid = Term.tid b;
                       target_tid = jmp_target j;
                       taken = blk_state;
                       fallthrough = blk_state;
                       live_taken = Solution.create Tid.Map.empty Var.Map.empty;
                       live_fallthrough =
                         Solution.create Tid.Map.empty Var.Map.empty }
            | _ ->
              let taken = edge_constraints_of cond ~complement:false in
              let fallthrough = edge_constraints_of cond ~complement:true in
              let taken_env, live_taken =
                refine_edge ~sol ~defs ~stores
                  blk_state s b taken in
              let fallthrough_env, live_fallthrough =
                refine_edge ~sol ~defs ~stores
                  blk_state s b fallthrough in
              Some { guard_tid = Term.tid b;
                     target_tid = jmp_target j;
                     taken = taken_env; fallthrough = fallthrough_env;
                     live_taken;
                     live_fallthrough }))
    |> Seq.to_list

(* The per-block TAG states (docs/trace-partitioning-plan.md §1.4). *)
let partitioned_states (s : sub term) (sol : (tid, AI.t) Solution.t)
    (views : edge_view list) : (tid, AI.t) Solution.t =
  let cfg =
    Graphs.Tid.Node.remove Graphs.Tid.start (Sub.to_graph s)
    |> Graphs.Tid.Node.remove Graphs.Tid.exit in
  (* [reach guard target]: the blocks reachable from [target] in the forward CFG without passing [guard]. *)
  let reach (guard : tid) (target : tid) : Tid.Set.t =
    let seen = ref Tid.Set.empty in
    let rec go = function
      | [] -> ()
      | n :: rest ->
        if Core.Set.mem !seen n || Tid.equal n guard then go rest
        else begin
          seen := Core.Set.add !seen n;
          let next = Graphs.Tid.Node.succs n cfg |> Seq.to_list in
          go (rest @ next)
        end in
    go [ target ];
    !seen in
  (* group the views by guard block *)
  let by_guard =
    List.fold views ~init:Tid.Map.empty ~f:(fun m v ->
        match Core.Map.find m v.guard_tid with
        | Some vs -> Core.Map.set m ~key:v.guard_tid ~data:(v :: vs)
        | None -> Core.Map.set m ~key:v.guard_tid ~data:[ v ]) in
  (* per guard: (the iterate view, the iterate region, the exit region); the iterate view is the one whose target reaches back to the guard (the loop-back) — a single-edge guard's target region is the iterate region, with no explicit fallthrough region. *)
  let regions = ref [] in
  Core.Map.iteri by_guard ~f:(fun ~key:g ~data:gviews ->
      let gviews = List.rev gviews in
      match gviews with
      | [] -> ()
      | [ v ] ->
        regions := (v, reach g (Option.value ~default:g v.target_tid),
                    Tid.Set.empty) :: !regions
      | v1 :: v2 :: _ ->
        let t1 = Option.value ~default:g v1.target_tid in
        let t2 = Option.value ~default:g v2.target_tid in
        let r1 = reach g t1 in
        if Core.Set.mem r1 g then
          (* v1's target loops back: v1 is the iterate edge *)
          regions := (v1, r1, reach g t2) :: !regions
        else
          regions := (v2, reach g t2, r1) :: !regions);
  let meet_live (st : AI.t) (live : Live.t) : AI.t =
    Core.Map.fold live ~init:st ~f:(fun ~key:v ~data:cstr acc ->
        match Var.typ v with
        | Type.Imm w when WordSet.bitwidth cstr = w ->
          let cur = AI.find_word w acc v in
          let m = WordSet.meet cur cstr in
          (* a disjoint meet keeps the invariant (a sound over-approximation — never a bottom state that would silently drop the block's tags) *)
          if Word.is_zero (WordSet.cardinality m)
             || WordSet.equal m cur
          then acc
          else AI.add_word acc ~key:v ~data:m
        | Type.Imm _ -> acc
        | Type.Mem _ | Type.Unk -> acc) in
  (* : the cell-denotation cache SHARED across every [meet_cells] call of this [partitioned_states] run — the same load shape (view × m × a × en × sz) repeats per (region × block × load-def), and the per-call cache (the first O3 attempt) missed the cross-block repetition. *)
  let cell_cache :
      (tid * exp * exp * endian * Size.t * WordSet.t) list ref =
    ref []
  in
  let same_en a b =
    match (a, b) with
    | LittleEndian, LittleEndian | BigEndian, BigEndian -> true
    | _ -> false
  in
  let same_size (a : Size.t) (b : Size.t) : bool =
    Size.compare a b = 0
  in
  (* [meet_cells st view]: The iterate-region Load defs inherit their cells' view-env constraints (the guard's load-chain meets in the view env) — the loaded var's value on the trace IS the cell's value, so the tag meets the cell's view-env value into the loaded var. *)
  (* Lite (the partitioned-stage redundancy fix): [meet_cells] is called once PER iterate-region block [btid] with that block's own state. *)
  let meet_cells (st : AI.t) (view : edge_view) (b : blk term) : AI.t =
    (* [meet_load acc v cell_ws]: meet the cell's constraint [cell_ws] (at the load's width) into the loaded var [v], widening it to [v]'s width when the load is cast-wrapped (the -O0 `pad:64[Load r32]` index shape — the 32-bit constraint zero-extends into the 64-bit index). *)
    let meet_load (acc : AI.t) (v : var) (cell_ws : WordSet.t) : AI.t =
      match Var.typ v with
      | Type.Imm w ->
        let c =
          if WordSet.bitwidth cell_ws = w then cell_ws
          else if WordSet.bitwidth cell_ws < w
          then WordSet.cast Bil.UNSIGNED w cell_ws
          else WordSet.top w in
        if WordSet.is_top c then acc
        else
          let cur = AI.find_word w acc v in
          let mm = WordSet.meet cur c in
          if Word.is_zero (WordSet.cardinality mm)
             || WordSet.equal mm cur
          then acc
          else AI.add_word acc ~key:v ~data:mm
      | Type.Mem _ | Type.Unk -> acc in
    (* [cell_of acc m a en sz]: The cell's value in the VIEW env (the guard's load-chain meets) — denoted exactly as the fixpoint reads it, so the alignment/width rules match. *)
    let cell_of (acc : AI.t) (m : exp) (a : exp)
        (en : endian) (sz : Size.t) : WordSet.t option =
      let g = view.guard_tid in
      match
        Base.List.find !cell_cache ~f:(fun (g', m', a', en', sz', _) ->
            Tid.equal g g' && Exp.equal m m' && Exp.equal a a'
            && same_en en en' && same_size sz sz')
      with
      | Some (_, _, _, _, _, ws) -> Some ws
      | None -> (
          match
            denote_imm_exp
              (Bil.Load (m, rewrite_addr (AI.frame_of acc) a, en, sz))
              view.taken
          with
          | Ok ws when not (WordSet.is_top ws) ->
              cell_cache := (g, m, a, en, sz, ws) :: !cell_cache;
              Some ws
          | Ok _ | Error _ -> None)
    in
    Term.enum def_t b
    |> Seq.fold ~init:st ~f:(fun acc d ->
        match Def.rhs d with
            | Bil.Cast (_, _, Bil.Load (m, a, en, sz))
            | Bil.Load (m, a, en, sz) ->
              (match cell_of acc m a en sz with
               | Some ws ->
                 (* Meet into the loaded var AND the tag state's memory cell — the emitter's sequential walk re-denotes [v := Load(cell)] and must read the constrained cell, not the solution's widened one. *)
                 let acc = meet_load acc (Def.lhs d) ws in
                 constrain_cell_on_trace
                   ~st:acc ~live:Live.empty
                   acc ~mem:m ~addr:a ~size:sz ~endian:en ws
               | None -> acc)
            | _ -> acc) in
  let m =
    Term.enum blk_t s
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m b ->
        let btid = Term.tid b in
        let st = Solution.get sol btid in
        let in_it = List.exists !regions ~f:(fun (_, r_it, _) ->
            Core.Set.mem r_it btid) in
        let in_ex = List.exists !regions ~f:(fun (_, _, r_ex) ->
            Core.Set.mem r_ex btid) in
        let st' =
          if in_it && not in_ex then
            List.fold !regions ~init:st ~f:(fun acc (v, r_it, _) ->
                if Core.Set.mem r_it btid
                then meet_cells (meet_live acc (Solution.get v.live_taken btid)) v b
                else acc)
          else if in_ex && not in_it then
            List.fold !regions ~init:st ~f:(fun acc (v, _, r_ex) ->
                if Core.Set.mem r_ex btid
                then meet_live acc (Solution.get v.live_fallthrough btid)
                else acc)
          else st in
        Core.Map.set m ~key:btid ~data:st')
  in
  Solution.create m AI.top

(* Refines [env] for the taken edge of the conditional jump [jmp]: the concrete states on the taken edge are exactly those where [Jmp.cond jmp] evaluates to true, so the refined state must over-approximate { s in env | cond(s) = true }. *)
let assume_jump_cond_with_group ?(refineable : Var.Set.t option)
    ?(defs : (def term * bool) Var.Map.t option)
    ?(stores : def term list option)
    ?(flag_state : (var * Bil.binop * exp * word) option = None)
    ?(flag_group : flag_group option = None)
    ?(sub : sub term option = None)
    ?(blk : blk term option = None)
    (env : AI.t) (jmp : jmp term) : AI.t =
  (* Relevance restriction (user design, ora-4, reworked per ora-5 / P2d-1b) — the frozen-flag guard: when the restriction is on, refine only vars in the per-sub relevant set (a skipped def's var would otherwise freeze at. *)
  let refineable_var (v : var) : bool = refineable_var_of refineable v in
  (* Refactor-1b (the arm collapse): the SIX shape arms of the pre- Refactor-1a [assume_jump_cond_with_group] and the decoder arm's manual wiring collapse to (a) the jcc-decoder idiom PRE-STEP below ([decoded_condition] ->. *)
  let ctx : analysis_ctx =
    { refineable; defs; stores; flag_state; sub; blk } in
  let cond = Jmp.cond jmp in
  match decoded_condition cond with
  | Some op ->
    (* L-A2 — the jcc-DECODER PRE-STEP (kept, runs FIRST and RETURNS when it fires): the -O0 loop guards are compound flag expressions (jle = `ZF | (SF|OF) & ~(SF&OF)`, jl = `(SF|OF) & ~(SF&OF)`, ja = `~(CF | ZF)`) that match. *)
    begin match flag_state with
    | Some (fv, _, e, c)
      when Option.value_map flag_group ~default:false
          ~f:(fun fg -> same_comparison_group fg fv e cond) ->
      let cur_e = match denote_imm_exp e env with
        | Ok ws -> Some ws
        | Error _ -> None in
      (* L-D1 — the provenance-based non-negativity proof for the SLT/SLE gate: [e]'s def chain (a Load from the RSP/RBP-anchored loop slot, seeded and incremented) proves the true concretization is [0, ∞) even when [cur]'s. *)
      let known_nonneg = known_nonneg_of ~defs ~stores e in
      (match decoder_constraint ~cur:cur_e ~known_nonneg op c with
       | Some cstr ->
         apply_operand_constraint ~defs refineable_var env e cstr
       | None -> env)
    | _ -> env
    end
  | None ->
    (* The general structural refinement: the taken edge forces the condition TRUE, so the {1} wordset at width 1 ([WordSet.singleton Word.b1]) is the forced value; [inverse_denote_exp ~ctx] decomposes [cond] through the M3. *)
    inverse_denote_exp ~ctx cond (WordSet.singleton Word.b1) env

(* L-A2 — the exported [assume_jump_cond] (the L3c-1 signature, .mli-typed): the group-aware implementation is [assume_jump_cond_with_group] above; this wrapper OCCLUDES the ?flag_group parameter (OCaml rejects optional. *)
let assume_jump_cond ?(refineable : Var.Set.t option)
    ?(defs : (def term * bool) Var.Map.t option)
    ?(flag_state : (var * Bil.binop * exp * word) option = None)
    (env : AI.t) (jmp : jmp term) : AI.t =
  assume_jump_cond_with_group ?refineable ?defs ~flag_state
    env jmp


(* Computes the denotation of the jumps of a basic block. *)
let denote_jump ?refineable ?preserved ?defs ?stores
    ?(flag_state : (var * Bil.binop * exp * word) option = None)
    ?(flag_group : flag_group option = None)
    ?(sub : sub term option = None)
    (denote_call : sub:tid -> AI.t -> target:tid -> AI.t)
    (b : blk term)  (env : AI.t) ~(target : tid) : AI.t =
  Term.enum jmp_t b
  |> reachable_jumps env
  |> Seq.map ~f:begin fun jmp ->
    (* Refine the state for the taken edge by the jump's condition (see [assume_jump_cond]). *)
    let env =
      assume_jump_cond_with_group ?refineable ?defs ?stores ~flag_state
        ~flag_group ~sub ~blk:(Some b) env jmp in
    (* E2e-B, ora-7 — remove hot-loop eprintf; gate per-hit event log (the old debug line flushed stderr on EVERY Call denotation, per fixpoint iteration). *)
    let inspect_call c =
      match Call.return c with
        | None -> AI.bottom
        | Some (Direct tid) when compare_tid target tid <> 0 -> AI.bottom
        | Some (Indirect _)
        | Some (Direct _) ->
          (* P2d-1b (lane B) — relevance-restricted call handling (user design, ora-5): when the restriction is engaged, a call (direct AND indirect — the same abstraction, which is better than the [AI.top] below for indirect. *)
          begin
            let rsp =
              Var.create ~is_virtual:false ~fresh:false "RSP" (Type.Imm 64) in
            (* Hike addition (the call-abstraction precision lane — the whole-memory-top gap fix): the pointer-argument ESCAPE set — the value sets of the SysV integer/pointer arg registers at the call, plus the caller's own frame boundary (the post-push RSP). *)
            let escape =
              (* The pointer-argument ESCAPE set: the SysV integer/pointer arg registers WRITTEN IN THIS CALL BLOCK (the -O0 arg setup lives in the call block). *)
              List.filter_map [ "RDI"; "RSI"; "RDX"; "RCX"; "R8"; "R9" ]
                ~f:(fun n ->
                  let v = Var.create ~is_virtual:false ~fresh:false
                      n (Type.Imm 64) in
                  let written =
                    Term.enum def_t b |> Seq.exists ~f:(fun d ->
                        Var.same (Def.lhs d) v) in
                  if written then Some (AI.find_word 64 env v)
                  else None) in
            let abs =
              AI.call_abstraction_frame
                ~preserved:(Option.value ~default:Var.Set.empty preserved)
                ~rsp:(AI.find_word 64 env rsp)
                ~escape env in
            (* L-E1 (ora-9 Item 2, user-prioritized) — the matched-pair RSP restoration on the ON-path return edge: the caller models the push as defs (RSP := RSP − 8; mem[RSP] := retaddr; call) and the callee's ret — the pop (t :=. *)
            let pushed =
              (* The push evidence: the call block WRITES RSP — the [RSP := RSP − 8] decrement (the fixture's minimal push) or the retaddr store at [RSP] (the real lifted calls' push pair). *)
              Term.enum def_t b
              |> Seq.exists ~f:(fun d ->
                  Var.same (Def.lhs d) rsp) in
            if pushed then begin
              let abs =
                AI.add_word abs ~key:rsp
                  ~data:(WordSet.add (AI.find_word 64 abs rsp)
                           (WordSet.singleton (Word.of_int ~width:64 8))) in
              (* WYSINWYX-2 (the in-state port) — the matched- pair restoration applied to the state's RELATION too: RSP's offset restores by +8 (the relation is path- invariant across calls modulo this). *)
              AI.set_frame abs (AI.frame_add_rsp (AI.frame_of abs))
            end else abs
          end in
    begin match Jmp.kind jmp with
      | Int _ ->
        (* NOT_IMPLEMENTED IMPLEMENTATION (lane B, ora-2): an interrupt/trap edge is an unknown EXTERNAL callee (kernel / signal handler). *)
        AI.call_abstraction
          ~preserved:(Option.value ~default:Var.Set.empty preserved) env
      | Call c -> inspect_call c
      | Goto (Direct tid)
      | Ret (Direct tid) ->  if compare_tid target tid = 0 then env else AI.bottom
      | Goto (Indirect _)
      | Ret (Indirect _) -> env
      end
  end
  |> Seq.fold ~init:AI.bottom ~f:AI.join

(* Computes the denotation of a block in a context-sensitive way, dependent on which block is next reached. *)
(* L-D1 — the internal, stores-aware block denotation (the per-sub store list for the provenance-based SLE/SLT gate, see [stores_of_sub]); the fixpoint path ([static_graph_vsa]) calls it with ~stores (absent -> the decoder arm's [known_nonneg] stays false). *)
let denote_block_with_stores ?refineable ?preserved ?defs ?stores
    ?(sub : sub term option = None)
    (denote_call : sub:tid -> AI.t -> target:tid -> AI.t)
    (ctx : program term) ~(source : tid) (env : AI.t) : target:tid -> AI.t =
 match (Program.lookup blk_t ctx source) with
   | Some b ->
     let postcond = denote_defs b env in
     (* L3c-1 — the per-block flag-state record (the BLP design): the last understood comparison that set a flag in scope in THIS block, for the bare-flag arm of [assume_jump_cond] (flag-indirected guards). *)
     let flag_state, flag_group = flag_state_of_block b in
     denote_jump ?refineable ?preserved ?defs ?stores ~flag_state
       ~flag_group:(Some flag_group) ~sub denote_call b postcond
   | None -> invalid_arg "source tid does not represent block"

type vsa_sol = (tid, AI.t) Solution.t


(* [default_entry]: The entry state of the UNANCHORED run — AI.top (the RSP := 0 anchor [set_stack_0] was REMOVED: the base-independence endgame — the frame relation (seeded by [init_sol]'s [seed_frame]) makes the stack addressing. *)
let default_entry () : AI.t = AI.top

(* Set up the initial solution for a general VSA pass over a subroutine. Assumes that the inputs can be any valid values for their types. *)
let init_sol ?entry (sub : sub term) =
  let empty_map = Tid.Map.empty in
  let msb = Term.first blk_t sub in
  let entry_state = Option.value ~default:(default_entry ()) entry in
  (* WYSINWYX-2 (the in-state port) — the ORIGIN definition: the sub's entry RSP has offset 0 (in BOTH anchored and unanchored runs — the origin is the entry RSP, not an assumption about its absolute value). *)
  let entry_state = AI.set_frame entry_state AI.seed_frame in
  let set_init sb = Map.set empty_map ~key:(Term.tid sb) ~data:entry_state in
  let base_map = Option.value_map ~default:empty_map ~f:set_init msb in
  (* Other than the first block, we assume that other blocks can only be reached via flow in the CFG. If the CFG is partial, this will produce an unsound result. (Note, however, that iterated VSA with explicit edge introduction can overcome this) *)
  Solution.create base_map AI.bottom

(* E2e-A, ora-7 — the call handling below is NOT "highly unoptimal": the call abstraction (the ON path, gated on [Utils.restriction_enabled]) is the production treatment; the recursion below is the OFF-path fallback. *)

(* The per-sub refineable var set for the relevance restriction — { v | v has a def tagged [Utils.relevant] } (the merged single-pass forward D-set tagging: relevant = RSP-derived at its position ∪ the resets ∪ L-E2. *)
let refineable_of_sub (s : sub term) : Var.Set.t =
  Term.enum blk_t s
  |> Seq.concat_map ~f:(Term.enum def_t)
  |> Seq.fold ~init:Var.Set.empty ~f:begin fun acc d ->
    if Term.has_attr d Utils.relevant then
      Core.Set.add acc (Var.base (Def.lhs d))
    else acc
  end

(* L3c-1 — the per-sub def-chain map for the backward guard refinement ([constrain_def_chain]): Var.base-normalized lhs -> (the def term that defines it, whether the base has EXACTLY ONE def in the sub). *)
let defs_of_sub (s : sub term) : (def term * bool) Var.Map.t =
  Term.enum blk_t s
  |> Seq.concat_map ~f:(Term.enum def_t)
  |> Seq.fold ~init:Var.Map.empty ~f:begin fun m d ->
    let key = Var.base (Def.lhs d) in
    match Core.Map.find m key with
    | None -> Core.Map.set m ~key ~data:(d, true)
    | Some _ -> Core.Map.set m ~key ~data:(d, false)
  end

(* L-D1 — the per-sub STORE list for the SLE/SLT gate relaxation ([prove_nonneg]): every def whose rhs is a [Bil.Store] — the store sites ([Bil.Store (m, a, u, e, s)]: memory, address, value, endian, size — the [denote_def] constructor shape). *)
let stores_of_sub (s : sub term) : def term list =
  Term.enum blk_t s
  |> Seq.concat_map ~f:(Term.enum def_t)
  |> Seq.filter ~f:begin fun d ->
    match Def.rhs d with
    | Bil.Store _ -> true
    | _ -> false
  end
  |> Seq.to_list

(* P2d-1b (lane B) — the per-sub preserved var set for the call abstraction (user design, ora-5): {RSP, RBP, RBX, R12, R13, R14, R15} (the call+ret identity registers and the callee-saved registers; built like the fork —. *)
let preserved_of_sub (s : sub term) : Var.Set.t =
  let regs =
    [ "RSP"; "RBP"; "RBX"; "R12"; "R13"; "R14"; "R15" ]
    |> List.map ~f:(fun n ->
        Var.create ~is_virtual:false ~fresh:false n (Type.Imm 64))
    |> Var.Set.of_list in
  let virt =
    Term.enum blk_t s
    |> Seq.concat_map ~f:(Term.enum def_t)
    |> Seq.fold ~init:Var.Set.empty ~f:begin fun acc d ->
      let acc =
        if Var.is_virtual (Def.lhs d)
        then Core.Set.add acc (Var.base (Def.lhs d)) else acc in
      Exp.free_vars (Def.rhs d)
      |> Core.Set.fold ~init:acc ~f:begin fun acc v ->
        if Var.is_virtual v then Core.Set.add acc (Var.base v) else acc
      end
    end in
  Core.Set.union regs virt

let rec static_graph_vsa (stack : tid list) (ctx : Program.t) (s : Sub.t) (init : vsa_sol) : vsa_sol =
  (* P2d-1b (lane B) — per-sub sets, computed ONCE at fixpoint entry from the (analyze-tagged) sub: the refineable vars for [assume_jump_cond] and the preserved vars for the call abstraction (see [refineable_of_sub]/[preserved_of_sub]). *)
  let refineable = refineable_of_sub s in
  let preserved = preserved_of_sub s in
  (* L3a — the per-sub def-chain map for the backward guard refinement, computed once at fixpoint entry like [refineable] and threaded through [denote_block] (see [defs_of_sub]). Inert when no conditional jump constrains a def-chained expression. *)
  let defs = defs_of_sub s in
  (* L-D1 — the per-sub store list for the provenance-based SLE/SLT gate ([prove_nonneg]), computed once at fixpoint entry like [defs] and threaded the same way (see [stores_of_sub]). *)
  let stores = stores_of_sub s in
  (* WYSINWYX-1 — the per-sub frame facts (per-block frame-derived registers and offset expressions), computed ONCE at fixpoint entry like [defs]/[stores] and threaded through [denote_block_with_stores] for the Load/Store address rewrite (the relation itself lives IN the state — the in-state port). *)
  (* E2e-A, ora-7 — the recursion below is the OFF-path fallback required for the byte-identical baseline (the ON path abstracts calls without recursing); keep. *)
  let rec denote_call stack ~sub env ~target =
    match (Program.lookup sub_t ctx sub) with
    | None -> invalid_arg "sub tid does not represent a subroutine"
    | Some sub ->
      if List.mem stack (Term.tid s) ~equal:Tid.equal && List.length stack > 6 then AI.top else begin
        (* P2d-1b (lane A transitional) — the caller's relevant-vars capture and the caller-alias union were deleted with the refs (ora-5 removes the caller-union: lane B replaces this whole recursion with the call abstraction gated on [Utils.restriction_enabled]). *)
        let fun_sol = static_graph_vsa (Term.tid sub::stack) ctx sub (init_sol ~entry:env sub) in
        sub
        |> Term.enum blk_t
        |> Seq.fold ~init:AI.bottom ~f: begin fun acc blk ->
          let source = Term.tid blk in
          let precond = Solution.get fun_sol source in
           AI.join acc @@
           denote_block_with_stores ~refineable ~preserved ~defs ~stores
             ~sub:(Some s)
             (denote_call (Term.tid sub::stack)) ctx ~source precond ~target
        end
      end
  in
  let s = Back_edges.label_back_edges s in
  let s = label_widening_points s in
  (* Hike addition (docs/widening-thresholds-plan.md): the per-sub threshold ladders. *)
  let thresholds = Cbat_thresholds.collect s in
  let cfg = Sub.to_graph s in
  (* BAP 2.6's Sub.to_graph adds the [start]/[exit] pseudo-nodes; the fixpoint would apply the block denotation to them and crash (Program.lookup fails). *)
  let cfg = Graphs.Tid.Node.remove Graphs.Tid.start cfg
            |> Graphs.Tid.Node.remove Graphs.Tid.exit in
  (* Bourdoncle WTO fixpoint — replaces chunk=3000 + convergence_gap + max_runs.
     WTO ordering stabilizes inner SCCs before outer; widen only at WTO heads
     after 10 outer sweeps via widen_join_threshold. Always runs; no fallback. *)
  let wto = Cbat_wto.wto_of_cfg cfg in
  let heads = Cbat_wto.heads_of_comps wto in
  (* SiftAbs H3 — selective widen: per-head value-flow cycle vars. *)
  let need_map : Var.Set.t Tid.Map.t =
    let rec collect_heads comps acc =
      List.fold comps ~init:acc ~f:(fun acc -> function
        | Cbat_wto.Vertex _ -> acc
        | Cbat_wto.SCC (h, inner) ->
            let blocks = Tid.Set.of_list (h :: Cbat_wto.flatten_comps inner) in
            let acc = Core.Map.set acc ~key:h ~data:blocks in
            collect_heads inner acc)
    in
    let head_to_blocks = collect_heads wto Tid.Map.empty in
    let compute_need (blocks : Tid.Set.t) : Var.Set.t =
      let defs =
        Core.Set.to_list blocks
        |> List.concat_map ~f:(fun tid ->
            match Term.find blk_t s tid with
            | Some blk -> Term.enum def_t blk |> Seq.to_list
            | None -> [])
        |> List.filter ~f:(fun d -> Term.has_attr d Utils.relevant)
      in
      let def_vars = Var.Set.of_list (List.map defs ~f:(fun d -> Var.base (Def.lhs d))) in
      if Core.Set.is_empty def_vars then Var.Set.empty
      else begin
        let succ_tbl : (Var.t, Var.t list) Hashtbl.t = Hashtbl.create (module Var) in
        let pred_tbl : (Var.t, Var.t list) Hashtbl.t = Hashtbl.create (module Var) in
        List.iter defs ~f:(fun d ->
          let lhs = Var.base (Def.lhs d) in
          let uses = Exp.free_vars (Def.rhs d) |> Core.Set.to_list |> List.map ~f:Var.base in
          List.iter uses ~f:(fun u ->
            if Core.Set.mem def_vars u then begin
              Hashtbl.add_multi succ_tbl ~key:lhs ~data:u;
              Hashtbl.add_multi pred_tbl ~key:u ~data:lhs
            end));
        let var_nodes = Core.Set.to_list def_vars in
        let visited = ref Var.Set.empty in
        let order = ref [] in
        let rec dfs1 v =
          if not (Core.Set.mem !visited v) then begin
            visited := Core.Set.add !visited v;
            let succs = Hashtbl.find_multi succ_tbl v in
            List.iter succs ~f:dfs1;
            order := v :: !order
          end
        in
        List.iter var_nodes ~f:dfs1;
        let visited2 = ref Var.Set.empty in
        let comps = ref [] in
        List.iter !order ~f:(fun v ->
          if not (Core.Set.mem !visited2 v) then begin
            let cur = ref [] in
            let rec dfs2 x =
              if not (Core.Set.mem !visited2 x) then begin
                visited2 := Core.Set.add !visited2 x;
                cur := x :: !cur;
                let preds = Hashtbl.find_multi pred_tbl x in
                List.iter preds ~f:dfs2
              end
            in
            dfs2 v;
            comps := !cur :: !comps
          end);
        let need = ref Var.Set.empty in
        List.iter !comps ~f:(fun comp ->
          match comp with
          | [v] ->
              let succs = Hashtbl.find_multi succ_tbl v in
              if List.mem succs v ~equal:Var.equal then
                need := Core.Set.add !need v
          | vs when List.length vs > 1 ->
              List.iter vs ~f:(fun v -> need := Core.Set.add !need v)
          | _ -> ());
        !need
      end
    in
    Core.Map.mapi head_to_blocks ~f:(fun ~key:_ ~data:blocks -> compute_need blocks)
  in
  let sol_map = ref (Solution.enum init |> Seq.fold ~init:Tid.Map.empty ~f:(fun m (k,v) -> Core.Map.set m ~key:k ~data:v)) in
  let sol_default = Solution.default init in
  let get n = match Core.Map.find !sol_map n with Some v -> v | None -> sol_default in
  let set n v = sol_map := Core.Map.set !sol_map ~key:n ~data:v in
  let total_processed = ref 0 in
  let max_steps = 6000 in
  let process_vertex (v : Tid.t) : bool =
    incr total_processed;
    if !total_processed > max_steps then begin
      let sol = Solution.create !sol_map sol_default in
      raise (Fixpoint_not_converged (max_steps, sol, None))
    end;
    let old = get v in
    let preds = CFG.Node.preds v cfg |> Seq.to_list in
    let incoming =
      if List.is_empty preds then old
      else
        let outs = List.map preds ~f:(fun p ->
            let p_entry = get p in
            let out_fn = denote_block_with_stores ~refineable ~preserved ~defs ~stores ~sub:(Some s) (denote_call stack) ctx ~source:p p_entry in
            out_fn ~target:v) in
        match List.reduce outs ~f:AI.join with
        | Some j -> j
        | None -> old
    in
    let new_val =
      if List.is_empty preds then old
      else if Core.Set.mem heads v && !total_processed > 10 then
        let need = Option.value ~default:Var.Set.empty (Core.Map.find need_map v) in
        Cbat_ai_representation.selective_widen_join_threshold thresholds ~need old incoming
      else
        AI.join old incoming
    in
    if not (AI.equal old new_val) then (set v new_val; true) else false
  in
  let rec stabilize_comps (comps : Cbat_wto.comp list) : bool =
    let changed = ref false in
    List.iter comps ~f:(function
        | Cbat_wto.Vertex v -> if process_vertex v then changed := true
        | Cbat_wto.SCC (h, inner) -> if stabilize_scc h inner then changed := true);
    !changed
  and stabilize_scc (h : Tid.t) (inner : Cbat_wto.comp list) : bool =
    let any_changed = ref false in
    let rec loop () =
      let ch = process_vertex h in
      let ci = stabilize_comps inner in
      if ch then any_changed := true;
      if ci then any_changed := true;
      if ch || ci then loop ()
    in
    loop ();
    !any_changed
  in
  ignore (stabilize_comps wto);
  let result = Solution.create !sol_map sol_default in
  (try
     let oc = open_out_gen [Open_append; Open_creat] 0o644 "/tmp/vsa_steps.txt" in
     Printf.fprintf oc "%s\t%d\t%d\n" (Sub.name s) (Term.length blk_t s) !total_processed;
     close_out oc
   with _ -> ());
  result

(* the view-carrying entry point. The legacy [static_graph_vsa] API remains solution-only for callers that have not migrated yet; Phase-B consumers must use this entry point so the computed views are not discarded at the analysis boundary. *)
let static_graph_vsa_with_views (stack : tid list) (ctx : Program.t)
    (s : Sub.t) (init : vsa_sol) : vsa_sol * edge_view list =
  let result = static_graph_vsa stack ctx s init in
  let views =
    edge_views_of
      ~defs:(Some (defs_of_sub s))
      ~stores:(Some (stores_of_sub s)) s result in
  result, views
