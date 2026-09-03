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
module Abi = Hike_abi

module Stages = Cbat_vsa_stages

module CG = Graphs.Callgraph
module CFG = Graphs.Tid

module AI = Cbat_ai_representation
module WordSet = Cbat_clp_set_composite
module Mem = Cbat_ai_memmap
module Word_ops = Cbat_word_ops
module Utils = Cbat_vsa_utils

(* WTO over the engine cfg; swapped accessors reverse it. *)

let wto_of_cfg (cfg : Graphs.Tid.t) : Cbat_wto.comp list =
  Cbat_wto.wto
    ~nodes:(Graphs.Tid.nodes cfg |> Seq.to_list)
    ~succ:(fun n -> Graphs.Tid.Node.succs n cfg |> Seq.to_list)
    ~pred:(fun n -> Graphs.Tid.Node.preds n cfg |> Seq.to_list)

(* Version-keyed memos for walk and transfer. *)
module Cbat_memo = Cbat_memo



module Walk_memo = Cbat_memo.Make (struct
  type t = AI.t
end)

module Transfer_memo = Cbat_memo.Make (struct
  type t = AI.t * bool
end)

(* Solution still changing at the step cap. *)
exception Fixpoint_not_converged of int * (tid, AI.t) Solution.t
  * (tid * tid) option

(* Address size in bits; 0 falls back to BIL width. *)
let addr_bits_ref = ref 0
let set_addr_bits (n : int) : unit = addr_bits_ref := n

(* Memory index of a memory type. *)
let mem_idx addr_sz addressable_sz : Mem.idx =
  { Mem.addr_width =
      (if !addr_bits_ref > 0 then !addr_bits_ref else Size.in_bits addr_sz);
    Mem.addressable_width = Size.in_bits addressable_sz }

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

type wordset = WordSet.t





(* Widths of both inputs. *)
let denote_binop (op : Bil.binop) : wordset -> wordset -> wordset =
  let btrue = WordSet.singleton Word.b1 in
  let bfalse = WordSet.singleton Word.b0 in
  let wordset_of_bool b = if b then btrue else bfalse in
  let bool_top = WordSet.top 1 in
  let bool_bottom = WordSet.bottom 1 in
  (* Shared LT/LE/SLT/SLE endpoint test. *)
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
  (* Shared EQ/NEQ decision. *)
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


(* Frame-derived registers equal entry RSP plus an offset; must-facts. *)

















(* Addresses rewrite to offsets for base-independent keys. *)









(* Facts must mirror value tracking exactly. *)


(* Non-singleton consts fall back to the direct key. *)



(* Effect of one def on facts. *)
let apply_frame_def_list (f : AI.frame) (d : def term) : AI.frame =
  if not (Term.has_attr d Utils.relevant) then f
  else
    let v = AI.frame_key (Def.lhs d) in
    let remove = AI.frame_remove f v in
    (* Copy rule with shift. *)
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
    (* A derived [z] drops the fact. *)
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
         (* Derived iff y derived. *)
         let y = AI.frame_key y in
         let shift =
           match op with
           | Bil.PLUS -> fun t -> AI.frame_add_const t (WordSet.singleton k)
           | Bil.MINUS -> fun t -> AI.frame_sub_const t (WordSet.singleton k)
           | _ -> Fun.id in
         transfer ~shift y
       | Bil.PLUS, Bil.Var y, Bil.Var z ->
         (* Derived iff y derived. *)
         let y = AI.frame_key y in
         let z = AI.frame_key z in
         if_not_derived z ~shift:(fun t -> AI.frame_add_fvar t z 1) y
       | Bil.MINUS, Bil.Var y, Bil.Var z ->
         (* Derived iff y derived. *)
         let y = AI.frame_key y in
         let z = AI.frame_key z in
         if_not_derived z ~shift:(fun t -> AI.frame_add_fvar t z (-1)) y
       | Bil.PLUS, Bil.Var y, BinOp (Bil.TIMES, Bil.Var z, Bil.Int k)
       | Bil.PLUS, BinOp (Bil.TIMES, Bil.Var z, Bil.Int k), Bil.Var y ->
         (* Derived iff y derived. *)
         let k = match Word.to_int k with Ok n -> n | Error _ -> 0 in
         let y = AI.frame_key y in
         let z = AI.frame_key z in
         if_not_derived z ~shift:(fun t -> AI.frame_add_fvar t z k) y
       | Bil.MINUS, Bil.Var y, BinOp (Bil.TIMES, Bil.Var z, Bil.Int k) ->
         (* Derived iff y derived. *)
         let k = match Word.to_int k with Ok n -> n | Error _ -> 0 in
         let y = AI.frame_key y in
         let z = AI.frame_key z in
         if_not_derived z ~shift:(fun t -> AI.frame_add_fvar t z (-k)) y
       | _ -> remove)
    | Bil.Load _ | Bil.Store _ | Bil.Cast _ | Bil.Extract _
    | Bil.Concat _ | Bil.Ite _ | Bil.UnOp _ | Bil.Let _ | Bil.Unknown _ ->
      remove

(* None stays bottom. *)
let apply_frame_def (f : AI.frame option) (d : def term) : AI.frame option =
  match f with
  | None -> None
  | Some f -> Some (apply_frame_def_list f d)



(* Offset expression plus literal. *)
let expr_of_term (t : AI.frame_term) (k : word) : exp option =
  match WordSet.min_elem t.fconst, WordSet.max_elem t.fconst with
  | Some lo, Some hi when Word.equal lo hi ->
    let base = Word.add lo k in
    Some (List.fold t.fvars ~init:(Bil.Int base) ~f:(fun acc (v, k') ->
        let scaled = Bil.BinOp (Bil.TIMES, Bil.Var v, Bil.Int (Word.of_int ~width:64 k')) in
        if k' >= 0 then Bil.BinOp (Bil.PLUS, acc, scaled)
        else Bil.BinOp (Bil.MINUS, acc, scaled)))
  | _ -> None

(* Rewrite an address to its offset expression. *)
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
       | None, Some _ -> None  
       | None, None -> None)
    | _ -> None in
  match go a with
  | Some r -> r
  | None -> a

(* Rewrite an rhs address. *)
let frame_rewrite_rhs (frame : AI.frame option) (e : exp) : exp =
  match e with
  | Bil.Load (m, a, en, s) ->
    Bil.Load (m, rewrite_addr frame a, en, s)
  | Bil.Store (m, a, u, en, s) ->
    Bil.Store (m, rewrite_addr frame a, u, en, s)
  | _ -> e



(* Frame relation of a state. *)
type frame = AI.frame

(* Frame relation of a state. *)
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
    
    if WordSet.is_top addr
    then return_mem mv
    else
    
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
  (* Untagged defs are skipped. *)
  if not (Term.has_attr df Utils.relevant)
  then env
  else
  let v = Def.lhs df in
  let e = Def.rhs df in
  (* Addresses rewrite to offsets. *)
  let frame = AI.frame_of env in
  let e = frame_rewrite_rhs frame e in
  (* Frame-derived values denote offsets. *)
  let e = rewrite_addr frame e in
  exn_on_err @@
  let open Monad_type_error in
  
  denote_exp e env >>| fun ev ->
  (match ev with
   | `Word p -> AI.add_word env ~key:v ~data:p
   | `Mem m -> AI.add_memory env ~key:v ~data:m)
  |> fun env' ->
  AI.set_frame env' (apply_frame_def (AI.frame_of env) df)

(* Denotation of a block's defs. *)
let denote_defs (b : blk term) : AI.t -> AI.t =
  (* Phis are the identity. *)
  (* Frame advances through each def. *)
  fun env0 ->
    Term.enum def_t b
    |> Seq.fold ~init:env0 ~f:(fun env df -> denote_def df env)



(* Jumps reachable in the env. *)

let reachable_jumps (env : AI.t) (jmps : jmp term seq) : jmp term seq =
  Seq.unfold_with jmps  ~init:true ~f:begin fun reachable jmp ->
    let cond = exn_on_err @@ denote_imm_exp (Jmp.cond jmp) env in
    let can_fall_through = WordSet.elem Word.b0 cond in
    if not reachable then Seq.Step.Done
    else if WordSet.elem Word.b1 cond then Seq.Step.Yield {value = jmp; state = can_fall_through}
    else Seq.Step.Skip {state = can_fall_through}
  end



(* Flag-expression decoder for loop guards. *)
type guard_op = ULT | ULE | UGT | UGE | EQ | NEQ | SLT | SLE | SGT | SGE

let decoded_condition (cond : exp) : guard_op option =
  (* True for the named flag var. *)
  let is_flag (name : string) (e : exp) : bool =
    match e with
    | Bil.Var v -> String.equal (Var.name v) name
    | _ -> false in
  (* Shared signed-overflow core. *)
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
    (* Signed e <= c. *)
    Some SLE
  | core when xor_core core ->
    (* Signed e < c. *)
    Some SLT
  | Bil.UnOp (Bil.NOT, Bil.BinOp (Bil.OR, cf, zf))
    when is_flag "CF" cf && is_flag "ZF" zf ->
    (* Unsigned e > c. *)
    Some UGT
  | Bil.UnOp (Bil.NOT, zf) when is_flag "ZF" zf ->
    (* e != c; refines to cur minus {c}. *)
    Some NEQ
  | Bil.Var _ as zf when is_flag "ZF" zf ->
    (* e == c. *)
    Some EQ
  | _ -> None

(* Shared step-1 CLP interval. *)
let interval_clp_of ~(width : int) ~(cardn : word) (base : word)
    : wordset option =
  if Word.is_zero cardn then None
  else
    let ws = WordSet.of_clp
        (Cbat_clp.create ~width ~step:(Word.one width) ~cardn base) in
    if WordSet.is_top ws then None else Some ws

(* Values allowed on a taken edge. *)
let comparison_constraint ?(cur : wordset option = None)
    ?(known_nonneg : bool = false)
    (op : Bil.binop) (c : word) : wordset option =
  let width = Word.bitwidth c in
  let cardn_of_int (i : int) : word option =
    if i < 0 then None else Some (Word.of_int ~width:(width + 1) i) in
  let int_of_word (w : word) : int option =
    try Some (Word.to_int_exn w) with _ -> None in
  (* Non-negativity threshold. *)
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
    (* Signed less-than row. *)
    if Word.(>=) c half
    then interval_clp_of ~width ~cardn:(Word.sub c half) half
    else if provably_nonneg || known_nonneg
    then interval_clp_of ~width ~cardn:c (Word.zero width)
    else None
  | Bil.SLE ->
    (* Signed less-equal row. *)
    if Word.(>=) c half
    then interval_clp_of ~width ~cardn:(Word.succ (Word.sub c half)) half
    else if provably_nonneg || known_nonneg
    then interval_clp_of ~width ~cardn:(Word.succ c) (Word.zero width)
    else None
  | Bil.NEQ ->
    (* Two-sided constraints stay identity. *)
    None
  | Bil.PLUS | Bil.MINUS | Bil.TIMES | Bil.DIVIDE | Bil.SDIVIDE
  | Bil.MOD | Bil.SMOD | Bil.LSHIFT | Bil.RSHIFT | Bil.ARSHIFT
  | Bil.AND | Bil.OR | Bil.XOR ->
    (* Producer guards stay identity. *)
    None


(* Backward guard refinement. *)

(* CLP interval or None on doubt. *)
let interval_of_bounds (width : int) (lo : word) (hi : word) : wordset option =
  if Word.bitwidth lo <> width || Word.bitwidth hi <> width then None
  else if Word.(>) lo hi then None
  else
    let ws = WordSet.of_clp (Cbat_clp.interval ~width lo hi) in
    if WordSet.is_top ws then None else Some ws

(* Constraint rows for decoded ops. *)
let decoder_constraint ?(cur : wordset option = None)
    ?(known_nonneg : bool = false)
    (op : guard_op) (c : word) : wordset option =
  let width = Word.bitwidth c in
  match op with
  | ULT -> comparison_constraint ~cur Bil.LT c
  | ULE -> comparison_constraint ~cur Bil.LE c
  | EQ -> comparison_constraint ~cur Bil.EQ c
  | NEQ ->
    (* NEQ is the exact two-piece complement. *)
    let cstr =
      WordSet.diff (WordSet.top (Word.bitwidth c)) (WordSet.singleton c) in
    if Cbat_clp_set_composite.is_bottom cstr then None else Some cstr
  | SLT -> comparison_constraint ~cur ~known_nonneg Bil.SLT c
  | SLE -> comparison_constraint ~cur ~known_nonneg Bil.SLE c
  | UGT ->
    (* Unsigned greater-than row. *)
    let lo = Word.succ c in
    if Word.is_zero lo then None
    else interval_of_bounds width lo (Word.ones width)
  | UGE ->
    (* Unsigned greater-equal row. *)
    interval_of_bounds width c (Word.ones width)
  | SGT ->
    (* Signed greater-than row. *)
    let lo = Word.succ c in
    if Word.is_zero lo then None
    else interval_of_bounds width lo (Word.ones width)
  | SGE ->
    (* Signed greater-equal row. *)
    interval_of_bounds width c (Word.ones width)

(* Provenance-based non-negativity proof. *)
let prove_nonneg ~(defs : (def term * bool) Var.Map.t)
    ~(stores : def term list) (e : exp) : bool =
  (* MSB-clear literals. *)
  let nonneg_word (n : word) : bool =
    let w = Word.bitwidth n in
    w > 0
    && Word.(<) n (Word_ops.half w) in
  let stack_anchor (v : var) : bool = Abi.is_stack_reg Abi.x86_64_sysv v in
  (* Threaded cycle guards. *)
  let rec walk (cells : Exp.Set.t) (vars : Exp.Set.t) (e : exp) : bool =
    match e with
    | Bil.Int n -> nonneg_word n
    | Bil.Var v ->
      let seen = Core.Set.mem vars e in
      let info = Core.Map.find defs (Var.base v) in
      let result =
        if seen then
          (* Loads may close the induction. *)
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
      (* Positive rshift clears the sign. *)
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
      (* Multiplier recurrence row. *)
      if Word.is_zero k then true else walk cells vars a
    | Bil.BinOp (Bil.DIVIDE, a, Bil.Int k) ->
      (* Division by 2+ is non-negative. *)
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
      (* HIGH of non-negative is non-negative. *)
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

(* Non-negativity gate. *)
let known_nonneg_of ~(defs : (def term * bool) Var.Map.t option)
    ~(stores : def term list option) (e : exp) : bool =
  match defs, stores with
  | Some dm, Some ss -> prove_nonneg ~defs:dm ~stores:ss e
  | _ -> false

(* Circular hull. *)
let circular_hull (width : int) (lo : word) (hi : word) : wordset option =
  if Word.bitwidth lo <> width || Word.bitwidth hi <> width then None
  else
    let ws = WordSet.of_clp (Cbat_clp.interval ~width lo hi) in
    if WordSet.is_top ws then None else Some ws

(* Operand constraints for a constrained result. *)
let operand_constraints (op : Bil.binop) (cstr : wordset)
    (a_ws : wordset) (b_ws : wordset) : wordset option * wordset option =
  let width = WordSet.bitwidth cstr in
  if WordSet.bitwidth a_ws <> width || WordSet.bitwidth b_ws <> width
  then None, None
  else
    (* No-wrap threshold. *)
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
      (* Plus: shift intervals by the other operand. *)
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
      (* Minus: shift intervals by the other operand. *)
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
      (* Times by literal. *)
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
      (* Minus: shift intervals by the other operand. *)
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
      (* Shift-right inverse. *)
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
      (* Minus: shift intervals by the other operand. *)
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
      (* Signed-division inverse. *)
      (match WordSet.min_elem cstr, WordSet.max_elem cstr,
             WordSet.min_elem b_ws, WordSet.max_elem b_ws with
       | Some vlo, Some vhi, Some k, Some k' when
           width <= 32 && Word.(=) k k' ->
         (match Word.to_int k with
          | Ok kk when kk > 0 ->
            (* Small widths avoid overflow. *)
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
      (* Minus: shift intervals by the other operand. *)
      None, None
    | Bil.AND | Bil.OR | Bil.XOR ->
      (* Exact masks constrain; general masks stay identity. *)
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
    (* Boolean producers stay identity. *)
    | _ -> None, None

(* Current word value or None on doubt. *)
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

(* Genuine-subset meet into a var. *)
let meet_var (refineable_var : var -> bool) (env : AI.t)
    (v : var) (refined : wordset) : AI.t =
  match Var.typ v with
  | Type.Imm w ->
    let cur = AI.find_word w env v in
    if WordSet.bitwidth cur <> w || WordSet.bitwidth refined <> w
    then env
    else
      let m = WordSet.meet cur refined in
      if Word.is_zero (WordSet.cardinality m) then begin
        Cbat_landmarks.observe_unsat_var v ~p:cur ~cstr:refined;
        env
      end else if not (WordSet.precedes m cur)
      then env
      else if refineable_var v then AI.add_word env ~key:v ~data:m
      else env
  | Type.Mem _ | Type.Unk -> env

(* Meet a constraint into a load cell. *)
let rec constrain_cell
    (refineable_var : var -> bool) (env : AI.t)
    ~(mem : exp) ~(addr : exp) ~(size : Size.t) ~(endian : endian)
    (cstr : wordset) : AI.t =
  if not (Exp.free_vars addr |> Core.Set.for_all ~f:refineable_var)
  then env
  else
    (* Cell keys use rewritten addresses. *)
    let addr_opt =
      if
        Exp.free_vars addr
        |> Core.Set.exists ~f:(Abi.is_sp Abi.x86_64_sysv)
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

(* Refine var operands through a producer def. *)
and refine_chain ~(defs : (def term * bool) Var.Map.t)
    (refineable_var : var -> bool) ~(visited : Var.Set.t)
    (env : AI.t) (op : Bil.binop) (a : exp) (b : exp)
    (cstr : wordset) : AI.t =
  let width = WordSet.bitwidth cstr in
  match op with
  | Bil.LSHIFT ->
    (* Minus: shift intervals by the other operand. *)
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

(* Refine producers backward through defs. *)
and constrain_def_chain ~(defs : (def term * bool) Var.Map.t)
    (refineable_var : var -> bool) ?(visited : Var.Set.t = Var.Set.empty)
    (env : AI.t) (e : exp) (cstr : wordset) : AI.t =
  match e with
  | Bil.Load (m, a, en, s) ->
    (* Loads constrain the cell. *)
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
             (* Load value is the cell value. *)
             constrain_cell refineable_var env ~mem:m
               ~addr:a ~size:s ~endian:en cstr
           | Bil.BinOp (op, a, b) ->
             refine_chain ~defs refineable_var
               ~visited:visited' env op a b cstr
           | Bil.Cast (Bil.HIGH, sz, a) ->
             (* HIGH-extract producer row. *)
             refine_cast_high ~defs refineable_var
               ~visited:visited' env a sz cstr
         | Bil.Cast (ct, _sz, _a) ->
           (* Other casts stay identity. *)
           ignore ct; env
         | Bil.Int _ -> env
         | _ -> env)
  | Bil.BinOp (op, a, b) ->
    (* Inline compares use producer rows. *)
    refine_chain ~defs refineable_var ~visited env op a b cstr
  | _ -> env


(* HIGH-extract pre-image. *)
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

(* Trace-exact cell meet. *)
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
         (* Offset via the load block state. *)
         let addr' = rewrite_addr (AI.frame_of st) addr in
         (* Trace values meet live constraints. *)
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
(* Backward walk: seeds flow to predecessors until stable. *)

















(* ================================================================== *)

(* Live set: var base to constraint. *)
module Live = struct
  type t = wordset Var.Map.t

  let empty : t = Var.Map.empty
  let find (key : var) (m : t) : wordset option = Core.Map.find m key
  let add (key : var) (data : wordset) (m : t) : t =
    Core.Map.set m ~key ~data
  let remove (key : var) (m : t) : t = Core.Map.remove m key
  let equal (m1 : t) (m2 : t) : bool = Core.Map.equal WordSet.equal m1 m2

  (* Merged constraints union; hulls over-approximate gaps. *)
  let join (m1 : t) (m2 : t) : t =
    Core.Map.merge m1 m2 ~f:(fun ~key:_ -> function
        | `Left c | `Right c -> Some c
        | `Both (c1, c2) -> Some (WordSet.union c1 c2))
end

(* Taken-edge constraint for the dataflow. *)
type edge_constraint =
  | Var of var * wordset
  | Cell of exp * exp * Size.t * endian * wordset
  | Infeasible

(* HIGH-extract pre-image. *)
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

(* Extension pre-image. *)
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
             (* Zero-extension case. *)
             if Word.(>) lo maxn then []
             else [ (lo, Word.min hi maxn) ]
           else begin
             (* Sign-extension halves. *)
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
                 (* Wrapped negative half. *)
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
            (* Truncate pieces to the operand width. *)
            interval_of_bounds n
              (Word.extract_exn ~hi:(n - 1) lo')
              (Word.extract_exn ~hi:(n - 1) hi'))
       | _ -> None)
  | None -> None

(* Truncation pre-image. *)
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
         (* Zero-extend to the operand width. *)
         let vlo_w = Word.extract_exn ~hi:(w - 1) vlo in
         let vhi_w = Word.extract_exn ~hi:(w - 1) vhi in
         let two_n =
           Word.lshift (Word.one w) (Word.of_int ~width:w n) in
         let hi_a = Word.add vhi_w (Word.sub (Word.ones w) two_n) in
         interval_of_bounds w vlo_w hi_a
       | _ -> None)
  | None -> None

(* Extract pre-image. *)
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


let def_constraints ~(sol : (tid, AI.t) Solution.t) (env : AI.t ref)
    (d : def term) (blk : blk term) (live : Live.t) (cstr : wordset)
    : (var * wordset) list =
  match Def.rhs d with
  | Bil.Load (m, a, en, s) ->
    (* Cells only; addresses unconstrained. *)
    env := constrain_cell_on_trace
      ~st:(Solution.get sol (Term.tid blk)) ~live
      !env ~mem:m ~addr:a ~size:s ~endian:en cstr;
    []
  | Bil.BinOp (Bil.LSHIFT, a, b) ->
    (* Minus: shift intervals by the other operand. *)
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
    (* Truncation pre-image. *)
    (match low_cast_constraint !env a cstr with
     | Some a' -> (
         match a with
         | Bil.Var av -> [ (Var.base av, a') ]
         | _ -> [])
     | None -> [])
  | Bil.UnOp (Bil.NOT, a) ->
    (* NOT is exact. *)
    (match a with
     | Bil.Var av -> [ (Var.base av, WordSet.lnot cstr) ]
     | _ -> [])
  | Bil.UnOp (Bil.NEG, a) ->
    (* NEG is exact. *)
    (match a with
     | Bil.Var av -> [ (Var.base av, WordSet.neg cstr) ]
     | _ -> [])
  | Bil.Var g ->
    (* Copy is identity. *)
    [ (Var.base g, cstr) ]
  | Bil.Concat (a, b) ->
    (* Slice rules. *)
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
    (* Extract rule. *)
    (match extract_constraint !env a hi lo cstr with
     | Some a' -> (
         match a with
         | Bil.Var av -> [ (Var.base av, a') ]
         | _ -> [])
     | None -> [])
  | _ -> []


(* Per-block flag group. *)
type flag_group = {
  flags : (var * def term) Var.Map.t;
  (* 1-bit defs by base lhs. *)
  cmp : def term option;
  (* Record def by structural equality. *)
}


(* Per-run analysis context. *)
type refine_ctx = {
  (* All-defs-tagged set. *)
  rc_all_tagged : Var.Set.t;
  (* Per-block solution versions. *)
  rc_versions : int Tid.Map.t;
  (* Walk CFG without pseudo-nodes. *)
  rc_walk_cfg : Graphs.Tid.t;
  (* Cached walks. *)
  rc_cache : Walk_memo.t;

  

  (* Per-block flag states. *)
  rc_flag_states :
    ((var * Bil.binop * exp * word) option * flag_group) Tid.Map.t;
  (* Per-block call facts. *)
  rc_call_facts : (var list * bool) Tid.Map.t;
  (* Memoized block transfers with replayed acquisition. *)
  (* Transfer memo. *)
  rc_out_cache : Transfer_memo.t;
}

(* Reverse-def walk of one block. *)
let reverse_def_walk ~(defs : (def term * bool) Var.Map.t)
    ~(sol : (tid, AI.t) Solution.t)
    (env : AI.t ref) (live : Live.t)
    (blk : blk term) : Live.t =
  let live = ref live in
  Term.enum def_t blk |> Seq.to_list |> List.rev
  |> List.iter ~f:(fun d ->
      let v = Var.base (Def.lhs d) in
      match Live.find v !live with
      | None -> ()   (* Skip non-live lhs. *)
      | Some cstr ->
        match Core.Map.find defs v with
        | Some _ ->
          (* Constraints cover only produced values. *)
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
               (* Empty pre-image drops the lhs. *)
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

(* Phi propagation toward the target. *)
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
                
                env := constrain_cell_on_trace
                  ~st:(Solution.get sol (Term.tid blk)) ~live:!live
                  !env ~mem:m ~addr:a ~size:s ~endian:en cstr
              | _ -> ()));
  !live


let refine_edge ~(sol : (tid, AI.t) Solution.t)
    ~(rctx : refine_ctx)
    ?(defs : (def term * bool) Var.Map.t option = None)
    ?(stores : def term list option = None)
    ?(reads : Tid.Set.t ref option = None)
    (env : AI.t) (sub : sub term) (blk : blk term)
    (seeds : edge_constraint list) : AI.t * (tid, Live.t) Solution.t =
  (* Visited set is closure-local. *)
  match defs with
  | None -> env, Solution.create Tid.Map.empty Live.empty
  | Some defs_map ->
    (* Walk reuses the hoisted CFG. *)
    
    let cfg = rctx.rc_walk_cfg in
    let seed_constraints, env0 =
      List.fold seeds ~init:(Live.empty, env) ~f:(fun (m, e) -> function
          | Var (v, c) ->
            
            Live.add v c m, e
          | Cell (mem, addr, size, endian, cstr) ->
            m, constrain_cell_on_trace ~st:env ~live:m e
              ~mem:mem ~addr:addr ~size:size ~endian:endian cstr
          | Infeasible -> m, AI.bottom) in
    let env = ref env0 in
    (* Closure counts pops. *)
    let pops = ref 0 in
    let live_sol =
      Cbat_contextual_fixpoint.fixpoint (module Graphs.Tid)
        ~init:(Solution.create (Tid.Map.singleton (Term.tid blk) seed_constraints)
                 Live.empty)
        ~equal:Live.equal ~merge:Live.join
        ~steps:256 ~rev:true
        ~f:(fun ~source:n ->
            fun live ->
              incr pops;
              (* Visited blocks are recorded. *)
              Option.iter reads ~f:(fun r ->
                  r := Core.Set.add !r n);
              match Term.find blk_t sub n with
              | Some b ->
                (* Guard defs walk over the seed. *)
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
    (* Commit walk metrics. *)
    Stages.bump_walk_pops
      ~pops:!pops
      ~blocks:(match reads with
          | Some r -> Core.Set.length !r
          | None -> 0)
      ~truncated:(!pops >= 256)
      ();
    (* Guard with no preds keeps the seed. *)
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

(* Backward-walk context record. *)
type analysis_ctx = {
  refineable : Var.Set.t option;
  defs : (def term * bool) Var.Map.t option;
  stores : def term list option;
  flag_state : (var * Bil.binop * exp * word) option;
  (* Sub and guard block of the walk. *)
  sub : sub term option;
  blk : blk term option;
}


(* ================================================================== *)
(* Leaf constraints of a guard; every shape has a row. *)







(* ================================================================== *)

(* BIL op to guard op. *)
let guard_op_of_binop (op : Bil.binop) : guard_op = match op with
  | Bil.LT -> ULT
  | Bil.LE -> ULE
  | Bil.EQ -> EQ
  | Bil.NEQ -> NEQ
  | Bil.SLT -> SLT
  | Bil.SLE -> SLE
  | _ -> EQ

(* False-edge complement. *)
let complement_guard_op (op : guard_op) : guard_op = match op with
  | ULT -> UGE | ULE -> UGT
  | UGT -> ULT | UGE -> ULE
  | EQ -> EQ | NEQ -> EQ
  | SLT -> SGE | SLE -> SGT
  | SGT -> SLT | SGE -> SLE

(* False-edge of a BIL comparison. *)
let complement_binop_guard (op : Bil.binop) : guard_op =
  complement_guard_op (guard_op_of_binop op)

(* Const-first flip. *)
let flip_guard_op (op : guard_op) : guard_op = match op with
  | ULT -> UGT | UGT -> ULT
  | ULE -> UGE | UGE -> ULE
  | SLT -> SGT | SGT -> SLT
  | SLE -> SGE | SGE -> SLE
  | EQ -> EQ | NEQ -> NEQ


let negate_guard_op (op : guard_op) : guard_op = match op with
  | ULT -> UGE | ULE -> UGT
  | UGT -> ULT | UGE -> ULE
  | EQ -> NEQ | NEQ -> EQ
  | SLT -> SGE | SLE -> SGT
  | SGT -> SLT | SGE -> SLE


let guard_constraint (w : int) (op : guard_op) (c : word)
    : wordset option =
  let maxw = Word.ones w in
  let half = Word_ops.half w in
  let iv lo hi = interval_of_bounds w lo hi in
  match op with
  | EQ -> Some (WordSet.singleton c)
  | NEQ ->
    (* Full domain minus the point. *)
    (match WordSet.diff (WordSet.top w) (WordSet.singleton c) with
     | d -> if Cbat_clp_set_composite.is_bottom d then None else Some d)
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

(* Taken-edge constraint on an operand. *)
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

(* Leaf seeds of a guard. *)
let rec edge_constraints ~(env : AI.t) ?(ctx : analysis_ctx option)
    (cond : exp) (cstr : wordset) : edge_constraint list =
  (* Signed rows are two-piece. *)
  match cond with
  | Bil.Var v ->
    begin match Var.typ v with
    | Type.Imm 1 ->
      (* Bare-flag shape with recovery. *)
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
    (* Disjoint constants kill the edge. *)
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
              (* False EQ is NEQ. *)
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
          (* Generic comparisons recurse both sides. *)
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
    | Bil.AND ->
      
      if WordSet.bitwidth cstr = 1
         && WordSet.elem Word.b1 cstr
         && not (WordSet.elem Word.b0 cstr)
      then
        edge_constraints ~env ?ctx a cstr @ edge_constraints ~env ?ctx b cstr
      else
        (match denote_operand env a, denote_operand env b with
         | Some a_ws, Some b_ws ->
           (match operand_constraints op cstr a_ws b_ws with
            | a', b' ->
              let acc = ref [] in
              (match a' with
               | Some a_c -> acc := edge_constraints ~env ?ctx a a_c @ !acc
               | None -> ());
              (match b' with
               | Some b_c -> acc := edge_constraints ~env ?ctx b b_c @ !acc
               | None -> ());
              !acc)
         | _ -> [])
    | Bil.PLUS | Bil.MINUS | Bil.TIMES | Bil.DIVIDE | Bil.SDIVIDE
    | Bil.MOD | Bil.SMOD | Bil.LSHIFT | Bil.RSHIFT | Bil.ARSHIFT
    | Bil.OR | Bil.XOR ->
      (* Producer rows plus recursion. *)
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
    
    [ Cell (m, a, s, en, cstr) ]
  | Bil.UnOp (Bil.NOT, e) ->
    (* Bijection row. *)
    let base = edge_constraints ~env ?ctx e (WordSet.lnot cstr) in
    
    let unwrap () : edge_constraint list =
      match ctx, e with
      | Some ({ flag_state = Some (fv, op, e0, c0); _ }), Bil.Var v
        when Var.same fv v ->
        (* Clear edge uses the negated op. *)
        (match row_for ~env ?ctx e0 (negate_guard_op (guard_op_of_binop op)) c0 with
         | Some cstr -> edge_constraints ~env ?ctx e0 cstr
         | None -> [])
      | _ -> [] in
    base @ unwrap ()
  | Bil.UnOp (Bil.NEG, e) ->
    edge_constraints ~env ?ctx e (WordSet.neg cstr)
  | Bil.Cast (ct, sz, a) ->
    (* Cast rows. *)
    let pre = match ct with
      | Bil.HIGH -> high_cast_constraint env a sz cstr
      | Bil.SIGNED -> ext_cast_constraint ~is_signed:true env a cstr
      | Bil.UNSIGNED -> ext_cast_constraint ~is_signed:false env a cstr
      | Bil.LOW -> low_cast_constraint env a cstr in
    (match pre with
     | Some a' -> edge_constraints ~env ?ctx a a'
     | None -> [])
  | Bil.Concat (a, b) ->
    (* Slice rows. *)
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
    (* Union holds on either branch. *)
    edge_constraints ~env ?ctx t cstr @ edge_constraints ~env ?ctx f cstr
  | Bil.Let (_, _, e) ->
    edge_constraints ~env ?ctx e cstr
  | Bil.Unknown _ -> []
  | Bil.Store (_, _, u, _, _) ->
    (* Cell constraints transfer to stored values. *)
    edge_constraints ~env ?ctx u cstr




(* Refineability closure. *)
let refineable_var_of (refineable : Var.Set.t option) (v : var) : bool =
  Option.value_map refineable ~default:false
    ~f:(fun set -> Core.Set.mem set (Var.base v))


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

(* Refine by a taken-edge constraint. *)
(* Direct-API backward refinement. *)
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

(* Last understood flag-setting comparison. *)


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
      (* Operand clobber clears. *)
      let st =
        match st with
        | Some (fv, op, e, c)
          when Exp.free_vars e |> Core.Set.exists ~f:(fun x ->
              Var.same x lhs_base) ->
          None
        | _ -> st in
      (* Flag rebinds or clears. *)
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
  (* 1-bit defs by base. *)
  let flags =
    Term.enum def_t b
    |> Seq.fold ~init:Var.Map.empty ~f:begin fun g d ->
      let lhs = Def.lhs d in
      match Var.typ lhs with
      | Type.Imm 1 -> Core.Map.set g ~key:(Var.base lhs) ~data:(lhs, d)
      | Type.Imm _ | Type.Mem _ | Type.Unk -> g
    end in
  (* Record def; temp or inline shape. *)
  let cmp =
    match record with
    | None -> None
    | Some (_, _, e, c) ->
      let temp_shape (d : def term) : bool =
        match Def.rhs d with
        | Bil.BinOp (Bil.MINUS, e', Bil.Int c') ->
          Exp.equal e' e && Word.equal c' c
        | _ -> false in
      let inline_shape (d : def term) : bool =
        match Def.rhs d with
        | Bil.BinOp ((Bil.EQ | Bil.LT | Bil.LE | Bil.SLT | Bil.SLE), e', Bil.Int c') ->
          Exp.equal e' e && Word.equal c' c
        | _ -> false in
      match List.find ds ~f:temp_shape with
      | Some d -> Some d
      | None -> List.find ds ~f:inline_shape in
  (record, { flags; cmp })

(* Same-comparison gate. *)
let same_comparison_group (fg : flag_group) (fv : var) (e : exp)
    (cond : exp) : bool =
  (* True for flag vars. *)
  let is_flag (v : var) : bool =
    match Var.name v with
    | "CF" | "ZF" | "SF" | "OF" -> true
    | _ -> false in
  (* Flags in cond plus the record flag. *)
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
          (* Base-equal free vars. *)
          Core.Set.exists fvs_e ~f:(fun x -> Var.same w x)
          || Var.same w t
        end
    end


let acquire_unsat_fallthrough ?(ctx : analysis_ctx option)
    ?(flag_group : flag_group option = None)
    (cond : exp) (env : AI.t) : unit =
  match ctx with
  | None -> ()
  | Some ctx ->
    
    begin match ctx.flag_state with
    | Some (_fv, bop, e, c) ->
      let gate_ok =
        Option.value_map flag_group ~default:false
          ~f:(fun fg -> same_comparison_group fg _fv e cond) in
      if gate_ok then begin
      let bop = bop and e = e and c = c in
      let gop = guard_op_of_binop bop in
      let op = complement_guard_op gop in
      (match row_for ~env ?ctx:(Some ctx) e op c with
       | Some cstr_e ->
         (match e with
          | Bil.Var v ->
            (match Var.typ v with
             | Type.Imm w ->
               let cur = AI.find_word w env v in
               if WordSet.bitwidth cur = w
               then Cbat_landmarks.observe_unsat_var v ~p:cur ~cstr:cstr_e
             | _ -> ())
          | _ ->
            List.iter (edge_constraints ~env ~ctx e cstr_e) ~f:(fun seed ->
              match seed with
              | Var (v, cstr_leaf) ->
                (match Var.typ v with
                 | Type.Imm w ->
                   let cur = AI.find_word w env v in
                   if WordSet.bitwidth cur = w
                   then Cbat_landmarks.observe_unsat_var v ~p:cur ~cstr:cstr_leaf
                 | _ -> ())
              | Cell _ | Infeasible -> ()))
       | None -> ())
      end else ()
      | None -> ()
    end

(* Refine by a taken jump condition. *)
let assume_jump_cond_with_group ?(refineable : Var.Set.t option)
    ?(defs : (def term * bool) Var.Map.t option)
    ?(stores : def term list option)
    ?(flag_state : (var * Bil.binop * exp * word) option = None)
    ?(flag_group : flag_group option = None)
    ?(sub : sub term option = None)
    ?(blk : blk term option = None)
    (env : AI.t) (jmp : jmp term) : AI.t =
  (* Refine only relevant vars. *)
  let refineable_var (v : var) : bool = refineable_var_of refineable v in
  
  let ctx : analysis_ctx =
    { refineable; defs; stores; flag_state; sub; blk } in
  let cond = Jmp.cond jmp in
  acquire_unsat_fallthrough ~ctx ~flag_group cond env;
  match decoded_condition cond with
  | Some op ->
    (* Decoder pre-step runs first. *)
    begin match flag_state with
    | Some (fv, _, e, c)
      when Option.value_map flag_group ~default:false
          ~f:(fun fg -> same_comparison_group fg fv e cond) ->
      let cur_e = match denote_imm_exp e env with
        | Ok ws -> Some ws
        | Error _ -> None in
      (* Non-negativity proof for signed gates. *)
      let known_nonneg = known_nonneg_of ~defs ~stores e in
      (match decoder_constraint ~cur:cur_e ~known_nonneg op c with
       | Some cstr ->
         apply_operand_constraint ~defs refineable_var env e cstr
       | None -> env)
    | _ -> env
    end
  | None ->
    (* Taken edge forces {1}. *)
    inverse_denote_exp ~ctx cond (WordSet.singleton Word.b1) env

(* Group-aware wrapper. *)
let assume_jump_cond ?(refineable : Var.Set.t option)
    ?(defs : (def term * bool) Var.Map.t option)
    ?(flag_state : (var * Bil.binop * exp * word) option = None)
    (env : AI.t) (jmp : jmp term) : AI.t =
  assume_jump_cond_with_group ?refineable ?defs ~flag_state
    env jmp

(* ================================================================== *)
(* Per-edge refinement uses accumulated edge conds. *)









(* ================================================================== *)

(* One edge's jmp plus accumulated cond. *)
type edge_cond = {
  cond_of_edge : jmp term;
  acc_cond : exp;
}

(* Per-sub static edge table. *)
let edge_conds_of (sub : sub term) : edge_cond Tid.Map.t Tid.Map.t =
  let ircfg = Sub.to_cfg sub in
  let tbl : (Tid.t, edge_cond Tid.Map.t) Hashtbl.t =
    Hashtbl.create (module Tid) in
  Graphs.Ir.edges ircfg
  |> Seq.iter ~f:(fun e ->
      let src = Graphs.Ir.Node.label (Graphs.Ir.Edge.src e) in
      let jmp = Graphs.Ir.Edge.jmp e in
      let jt = Term.tid jmp in
      let by_jmp =
        match Hashtbl.find tbl (Term.tid src) with
        | None -> Tid.Map.empty
        | Some m -> m in
      let by_jmp =
        Core.Map.set by_jmp ~key:jt
          ~data:{ cond_of_edge = jmp; acc_cond = Graphs.Ir.Edge.cond e ircfg } in
      Hashtbl.set tbl ~key:(Term.tid src) ~data:by_jmp);
  Hashtbl.fold tbl ~init:Tid.Map.empty ~f:(fun ~key ~data acc ->
      Core.Map.set acc ~key ~data)

(* ================================================================== *)
(* Deep walk cached per (block, jmp). *)















































(* ================================================================== *)



(* Static per-block call facts. *)
let call_facts_of_block (b : blk term) : var list * bool =
  let defs = Term.enum def_t b |> Seq.to_list in
  let written =
    List.filter Abi.x86_64_sysv.int_param_regs ~f:(fun v ->
        List.exists defs ~f:(fun d -> Var.same (Def.lhs d) v)) in
  let rsp = Abi.x86_64_sysv.sp in
  let pushed = List.exists defs ~f:(fun d -> Var.same (Def.lhs d) rsp) in
  (written, pushed)

(* Block version; 0 means never set. *)
(* Per-run analysis context. *)
let mk_rctx ~(cfg : Graphs.Tid.t) (s : sub term) : refine_ctx = {
  rc_all_tagged =
    Term.enum blk_t s
    |> Seq.concat_map ~f:(Term.enum def_t)
    |> Seq.fold ~init:Var.Map.empty ~f:(fun m d ->
        let k = Var.base (Def.lhs d) in
        let tagged = Term.has_attr d Utils.relevant in
        match Core.Map.find m k with
        | None -> Core.Map.set m ~key:k ~data:tagged
        | Some true -> m
        | Some false -> Core.Map.set m ~key:k ~data:false)
    |> Core.Map.filter ~f:Fn.id
    |> Core.Map.keys
    |> Var.Set.of_list;
  rc_versions = Tid.Map.empty;
  rc_walk_cfg = cfg;
  rc_cache = Walk_memo.empty;
  rc_flag_states =
    Term.enum blk_t s
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m b ->
        Core.Map.set m ~key:(Term.tid b) ~data:(flag_state_of_block b));
  rc_call_facts =
    Term.enum blk_t s
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m b ->
        Core.Map.set m ~key:(Term.tid b) ~data:(call_facts_of_block b));
  rc_out_cache = Transfer_memo.empty;
}

let ver_of (rc : refine_ctx) (t : Tid.t) : int =
  match Core.Map.find rc.rc_versions t with
  | Some v -> v
  | None -> 0







let refine_edge_inline
    ~(sol : (tid, AI.t) Solution.t)
    ~(defs : (def term * bool) Var.Map.t option)
    ~(stores : def term list option)
    ~(flag_state : (var * Bil.binop * exp * word) option)
    ~(flag_group : flag_group option)
    ?(refineable : Var.Set.t option)
    ~(rctx : refine_ctx)
    ~(jt : Tid.t)
    ~(sub : sub term)
    ~(discarded : bool)
    (b : blk term) (env : AI.t) (acc_cond : exp)
    : AI.t * refine_ctx option * Tid.Set.t =
  
  (* Threaded context plus visited set. *)
  let ctx : analysis_ctx =
    { refineable = None; defs; stores; flag_state;
      sub = Some sub; blk = Some b } in
  let seeds = edge_constraints ~env ~ctx acc_cond (WordSet.singleton Word.b1) in
  
  (* Infeasible seeds stay identity, never bottom. *)
  let seeds =
    List.filter seeds ~f:(fun s -> match s with Infeasible -> false | _ -> true) in
  match seeds with
  | [] -> (env, Some rctx, Tid.Set.empty)
  | _ ->
    
    
    
    let all_tagged : Var.Set.t = rctx.rc_all_tagged in
    let refineable_var (v : var) : bool = refineable_var_of refineable v in
    
    let env =
      List.fold seeds ~init:env ~f:(fun e -> function
          | Var (v, c) ->
            if Core.Set.mem all_tagged (Var.base v)
            then meet_var refineable_var e v c
            else e
          | Cell _ | Infeasible -> e) in
    
    (* Cached walk with threaded context. *)
    (* No-defs callers keep the uncached walk. *)
    let walk env seeds : AI.t * refine_ctx option * Tid.Set.t =
      if discarded then (env, Some rctx, Tid.Set.empty)
      else
      match defs with
      | Some _ ->
        let rc = rctx in
        let bt = Term.tid b in
        (* Memo handles validity. *)
        let version = ver_of rc in
        (match Walk_memo.find ~version rc.rc_cache bt jt with
         | Some refined ->
           (* Walk reads subset the transfer reads. *)
           (refined, Some rc, Tid.Set.empty)
         | None ->
           let walk_reads = ref (Tid.Set.singleton bt) in
           let refined, _live =
             Stages.time `Walk (fun () ->
                 refine_edge ~sol ~rctx:rc ~defs ~stores
                   ~reads:(Some walk_reads)
                   env sub b seeds) in
           let rc =
             { rc with
               rc_cache =
                 Walk_memo.add ~version rc.rc_cache bt jt
                   ~reads:!walk_reads refined } in
           (refined, Some rc, !walk_reads))
      | None ->
        let refined, _live =
          refine_edge ~sol ~rctx:rctx ~defs ~stores env sub b seeds in
        (refined, Some rctx, Tid.Set.empty) in
    walk env seeds

(* Denotation of a block's jumps. *)
let denote_jump ?refineable ?preserved ?defs ?stores
    ?(flag_state : (var * Bil.binop * exp * word) option = None)
    ?(flag_group : flag_group option = None)
    ?(sub : sub term option = None)
    ?(no_walk : bool option)
    ?edge_conds ?sol
    ~(rctx : refine_ctx)
    (denote_call : sub:tid -> AI.t -> target:tid -> AI.t)
    (b : blk term)  (env : AI.t) ~(target : tid)
    : AI.t * refine_ctx option * Tid.Set.t =
  (* Fold joins per-jump results. *)
  let rc0 = rctx in
  let per_jump (acc, rctx, reads) jmp =
    (* Refine by the jump cond. *)
    let env =
      assume_jump_cond_with_group ?refineable ?defs ?stores ~flag_state
        ~flag_group ~sub ~blk:(Some b) env jmp in
    (* Deep walk uses the accumulated cond. *)
    let env, rctx, reads =
      match edge_conds, sol, sub with
      | Some tbl, Some snap, Some s ->
        let acc_cond =
          Core.Map.find tbl (Term.tid b)
          |> Option.bind ~f:(fun by_jmp ->
              Core.Map.find by_jmp (Term.tid jmp))
          |> Option.map ~f:(fun ec -> ec.acc_cond) in
        (match acc_cond with
         | Some acc_cond ->
           (* Discard test mirrors bottom arms. *)
           let discarded =
             Option.value ~default:false no_walk ||
             match Jmp.kind jmp with
             | Goto (Direct tid) | Ret (Direct tid) ->
               compare_tid target tid <> 0
             | Call c ->
               (match Call.return c with
                | Some (Direct tid) -> compare_tid target tid <> 0
                | Some (Indirect _) | None -> false)
             | Goto (Indirect _) | Ret (Indirect _) | Int _ -> false in
           (* Accumulator threads optional context. *)
           let env', rctx', reads' =
             refine_edge_inline ~sol:snap ~defs ~stores ~flag_state
               ~flag_group ?refineable
               ~rctx:(Option.value ~default:rc0 rctx) ~jt:(Term.tid jmp)
               ~sub:s ~discarded b env acc_cond in
           (env', rctx', Core.Set.union reads reads')
         | None -> (env, rctx, reads))
      | _ -> (env, rctx, reads) in
    
    let inspect_call c =
      match Call.return c with
        | None -> AI.bottom
        | Some (Direct tid) when compare_tid target tid <> 0 -> AI.bottom
        | Some (Indirect _)
        | Some (Direct _) ->
          (* Relevance-restricted calls. *)
          begin
            let rsp = Abi.x86_64_sysv.sp in
            (* Escape set plus caller frame boundary. *)
            (* Written registers are static. *)
            let escape =
              
              let written =
                match Core.Map.find rc0.rc_call_facts (Term.tid b) with
                | Some (w, _) -> w
                | None -> fst (call_facts_of_block b) in
              List.map written ~f:(fun v -> AI.find_word 64 env v) in
            let abs =
              AI.call_abstraction_frame
                ~preserved:(Option.value ~default:Var.Set.empty preserved)
                ~rsp:(AI.find_word 64 env rsp)
                ~escape env in
            (* RSP restores by +8 on returns. *)
            
            
            let pushed =
              match Core.Map.find rc0.rc_call_facts (Term.tid b) with
              | Some (_, p) -> p
              | None -> snd (call_facts_of_block b) in
            if pushed then begin
              let abs =
                AI.add_word abs ~key:rsp
                  ~data:(WordSet.add (AI.find_word 64 abs rsp)
                           (WordSet.singleton (Word.of_int ~width:64 8))) in
              (* Relation restores RSP by +8. *)
              AI.set_frame abs (AI.frame_add_rsp (AI.frame_of abs))
            end else abs
          end in
    (* Per-jump transfer results. *)
    let env_res, rctx, reads =
      match Jmp.kind jmp with
      | Int _ ->
        (* Traps are external callees. *)
        (AI.call_abstraction
           ~preserved:(Option.value ~default:Var.Set.empty preserved) env,
         rctx, reads)
      | Call c -> (inspect_call c, rctx, reads)
      | Goto (Direct tid)
      | Ret (Direct tid) ->
        ((if compare_tid target tid = 0 then env else AI.bottom), rctx, reads)
      | Goto (Indirect _)
      | Ret (Indirect _) -> (env, rctx, reads) in
    (AI.join acc env_res, rctx, reads) in
  Seq.fold (reachable_jumps env (Term.enum jmp_t b))
    ~init:(AI.bottom, Some rctx, Tid.Set.empty)
    ~f:per_jump

(* Block denotation toward a target. *)




(* Stores-aware block denotation. *)
let denote_block_with_stores ?refineable ?preserved ?defs ?stores
    ?(sub : sub term option = None)
    ?(edge_conds : edge_cond Tid.Map.t Tid.Map.t option = None)
    ?(sol : (tid, AI.t) Solution.t option = None)
    ~(rctx : refine_ctx)
    ?(no_walk : bool option)
    (denote_call : sub:tid -> AI.t -> target:tid -> AI.t)
    (ctx : program term) ~(source : tid) (env : AI.t)
    : target:tid -> AI.t * refine_ctx option * Tid.Set.t =
 (* Threaded context plus read set. *)
 match (Program.lookup blk_t ctx source) with
   | Some b ->
     let postcond = denote_defs b env in
     (* Last understood flag-setting comparison. *)
     
     let flag_state, flag_group =
       match Core.Map.find rctx.rc_flag_states (Term.tid b) with
       | Some fs -> fs
       | None -> flag_state_of_block b in
     fun ~target ->
       let (res, rctx', reads) =
         denote_jump ?refineable ?preserved ?defs ?stores ~flag_state
           ~flag_group:(Some flag_group) ~sub ?no_walk ?edge_conds ?sol
           ~rctx
           denote_call b postcond ~target in
       (res, rctx', Core.Set.add reads (Term.tid b))
   | None -> fun ~target ->
       ignore (invalid_arg "source tid does not represent block");
       (AI.bottom, Some rctx, Tid.Set.empty)

type vsa_sol = (tid, AI.t) Solution.t


(* Entry state is top. *)
let default_entry () : AI.t = AI.top

(* Initial solution of a sub. *)
let init_sol ?entry (sub : sub term) =
  let empty_map = Tid.Map.empty in
  let msb = Term.first blk_t sub in
  let entry_state = Option.value ~default:(default_entry ()) entry in
  (* Entry RSP has offset 0. *)
  let entry_state = AI.set_frame entry_state AI.seed_frame in
  let set_init sb = Map.set empty_map ~key:(Term.tid sb) ~data:entry_state in
  let base_map = Option.value_map ~default:empty_map ~f:set_init msb in
  (* Partial CFGs give unsound results. *)
  Solution.create base_map AI.bottom

(* Calls abstract; recursion is fallback. *)

(* Vars with tagged defs. *)
let refineable_of_sub (s : sub term) : Var.Set.t =
  Term.enum blk_t s
  |> Seq.concat_map ~f:(Term.enum def_t)
  |> Seq.fold ~init:Var.Set.empty ~f:begin fun acc d ->
    if Term.has_attr d Utils.relevant then
      Core.Set.add acc (Var.base (Def.lhs d))
    else acc
  end

(* Per-sub def-chain map. *)
let defs_of_sub (s : sub term) : (def term * bool) Var.Map.t =
  Term.enum blk_t s
  |> Seq.concat_map ~f:(Term.enum def_t)
  |> Seq.fold ~init:Var.Map.empty ~f:begin fun m d ->
    let key = Var.base (Def.lhs d) in
    match Core.Map.find m key with
    | None -> Core.Map.set m ~key ~data:(d, true)
    | Some _ -> Core.Map.set m ~key ~data:(d, false)
  end

(* Per-sub store list. *)
let stores_of_sub (s : sub term) : def term list =
  Term.enum blk_t s
  |> Seq.concat_map ~f:(Term.enum def_t)
  |> Seq.filter ~f:begin fun d ->
    match Def.rhs d with
    | Bil.Store _ -> true
    | _ -> false
  end
  |> Seq.to_list

(* Preserved registers. *)
let preserved_of_sub (s : sub term) : Var.Set.t =
  let regs =
    Abi.x86_64_sysv.sp :: Abi.x86_64_sysv.fp :: Abi.x86_64_sysv.callee_saved
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
  (* Per-sub sets computed once. *)
  let refineable = refineable_of_sub s in
  let preserved = preserved_of_sub s in
  (* Per-sub def-chain map. *)
  let defs = defs_of_sub s in
  (* Store list computed once. *)
  let stores = stores_of_sub s in
  (* Frame facts computed once. *)
  (* Recursion is fallback. *)
  let rec denote_call stack ~sub env ~target =
    match (Program.lookup sub_t ctx sub) with
    | None -> invalid_arg "sub tid does not represent a subroutine"
    | Some sub ->
      if List.mem stack (Term.tid s) ~equal:Tid.equal && List.length stack > 6 then AI.top else begin
        
        let fun_sol = static_graph_vsa (Term.tid sub::stack) ctx sub (init_sol ~entry:env sub) in
        (* Nested runs build callee contexts. *)
        let callee_cfg =
          Graphs.Tid.Node.remove Graphs.Tid.start (Sub.to_graph sub)
          |> Graphs.Tid.Node.remove Graphs.Tid.exit in
        let callee_rctx = mk_rctx ~cfg:callee_cfg sub in
        sub
        |> Term.enum blk_t
        |> Seq.fold ~init:AI.bottom ~f: begin fun acc blk ->
          let source = Term.tid blk in
          let precond = Solution.get fun_sol source in
           AI.join acc @@
           let (res, _, _) =
             denote_block_with_stores ~refineable ~preserved ~defs ~stores
               ~sub:(Some s) ~rctx:callee_rctx
               (denote_call (Term.tid sub::stack)) ctx ~source precond
               ~target in
           res
        end
      end
  in
  (* Per-sub static edge table. *)
  let edge_conds = edge_conds_of s in
  let cfg = Sub.to_graph s in
  (* Pseudo-nodes never reach denotation. *)
  let cfg_tmp = Graphs.Tid.Node.remove Graphs.Tid.start cfg
            |> Graphs.Tid.Node.remove Graphs.Tid.exit in
  (* Run context built once per run. *)
  let rctx = mk_rctx ~cfg:cfg_tmp s in
  (* WTO fixpoint; inner SCCs stabilize first. *)
  let wto = wto_of_cfg cfg_tmp in
  let heads = Cbat_wto.heads_of_comps wto in
  let cfg = cfg_tmp in
  Cbat_landmarks.clear ();
  let head_to_blocks : (Tid.t, Tid.Set.t) Hashtbl.t = Hashtbl.create (module Tid) in
  let rec collect_heads comps =
    List.iter comps ~f:(function
      | Cbat_wto.Vertex _ -> ()
      | Cbat_wto.SCC (h, inner) ->
        let blocks = Tid.Set.of_list (h :: Cbat_wto.flatten_comps inner) in
        Hashtbl.set head_to_blocks ~key:h ~data:blocks;
        collect_heads inner)
  in
  collect_heads wto;
  let block_to_head : (Tid.t, Tid.t) Hashtbl.t = Hashtbl.create (module Tid) in
  Hashtbl.iteri head_to_blocks ~f:(fun ~key:h ~data:blocks ->
    Core.Set.iter blocks ~f:(fun btid ->
      match Hashtbl.find block_to_head btid with
      | None -> Hashtbl.set block_to_head ~key:btid ~data:h
      | Some existing ->
        (* Innermost wins. *)
        let existing_set = Hashtbl.find_exn head_to_blocks existing in
        if Core.Set.length blocks < Core.Set.length existing_set then
          Hashtbl.set block_to_head ~key:btid ~data:h));

  (* Widen cycle vars per head. *)
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
  (* Versions key the caches. *)
  (* Context threads through the engine. *)
  let rc_cell = ref rctx in
  let set n v =
    sol_map := Core.Map.set !sol_map ~key:n ~data:v;
    let rc = !rc_cell in
    let versions =
      match Core.Map.find rc.rc_versions n with
      | None -> Core.Map.set rc.rc_versions ~key:n ~data:1
      | Some k -> Core.Map.set rc.rc_versions ~key:n ~data:(k + 1) in
    rc_cell := { rc with rc_versions = versions } in
  Stages.reset ();
  let total_processed = ref 0 in
  let max_steps = 6000 in
  let process_vertex (v : Tid.t) : bool =
    (* Scaffold times engine glue. *)
    Stages.time `Scaffold (fun () ->
    incr total_processed;
    if !total_processed > max_steps then begin
      let sol = Solution.create !sol_map sol_default in
      raise (Fixpoint_not_converged (max_steps, sol, None))
    end;
    let old = get v in
    let preds = CFG.Node.preds v cfg |> Seq.to_list in
    (* Snapshot for the deep walk. *)
    let sol_snap = Solution.create !sol_map sol_default in
    let incoming =
      if List.is_empty preds then old
      else
        let outs = List.map preds ~f:(fun p ->
            (* Per-pred glue. *)
            let head_opt, p_entry =
              Stages.time `Glue (fun () ->
                let head_opt = Hashtbl.find block_to_head p in
                Cbat_landmarks.widening_at_head := head_opt;
                let p_entry = get p in
                (head_opt, p_entry)) in
            
            (* Context threads through transfers. *)
            let rc = !rc_cell in
             let res = Stages.time `Denote (fun () ->
               (* Memo handles validity. *)
               let version = ver_of rc in
               match Transfer_memo.find ~version rc.rc_out_cache p v with
               | Some (hit_res, fired) ->
                 
                 (if Option.is_some head_opt && fired then
                    match Program.lookup blk_t ctx p with
                    | Some _pb ->
                      ignore (denote_block_with_stores ~refineable ~preserved
                                ~defs ~stores ~sub:(Some s)
                                ~edge_conds:(Some edge_conds)
                                ~sol:(Some sol_snap) ~rctx:rc
                                ~no_walk:true (denote_call stack) ctx
                                ~source:p p_entry ~target:v)
                    | None -> ());

                 hit_res
               | None ->
                 (* Latch reports acquisition. *)
                 let flatch = Cbat_landmarks.start_fired_latch () in
                 let (res, rc', reads) =
                   denote_block_with_stores ~refineable ~preserved ~defs
                     ~stores ~sub:(Some s) ~edge_conds:(Some edge_conds)
                     ~sol:(Some sol_snap) ~rctx:rc (denote_call stack)
                     ctx ~source:p p_entry ~target:v in
                 let fired = Cbat_landmarks.end_fired_latch flatch in
                 (* Read set covers inputs. *)
                 let reads = Core.Set.add reads p in
                 rc_cell :=
                   { (Option.value ~default:rc rc') with
                     rc_out_cache =
                       Transfer_memo.add ~version rc.rc_out_cache p v
                         ~reads (res, fired) };
                 res) in
            Cbat_landmarks.widening_at_head := None;
            res) in
        (Stages.time `Join (fun () ->
           match List.reduce outs ~f:AI.join with
           | Some j -> j
           | None -> old))
    in
    let new_val =
      if List.is_empty preds then old
      else if Core.Set.mem heads v && !total_processed > 10 then begin
        (* Stable heads skip side effects. *)
        (* Join computed once. *)
        let j = Stages.time `Join (fun () -> AI.join old incoming) in
        if Stages.time `Equal (fun () -> AI.equal old j)
        then old
        else begin
        (* Finite extrapolates; Zero joins; Inf widens. *)
        let need = Option.value ~default:Var.Set.empty (Core.Map.find need_map v) in
        Cbat_landmarks.widening_at_head := Some v;
        let res = match Cbat_landmarks.lm_calc_steps v with
          | `Finite n ->
            let r = Stages.time `Widen (fun () -> AI.selective_widen_extrapolate ~head:(Some v) ~need ~steps:n old incoming) in
            Cbat_landmarks.clear_head v (Hashtbl.find_exn head_to_blocks v);
            r
          | `Zero ->
            Cbat_landmarks.lm_advance v;
            j
          | `Inf ->
            Stages.time `Widen (fun () -> AI.widen_join old incoming)
        in
        Cbat_landmarks.widening_at_head := None;
        res
        end
      end else
        (* Non-heads join once. *)
        Stages.time `Join (fun () -> AI.join old incoming)
    in
    (* Stability compare is timed. *)
    if not (Stages.time `Equal (fun () -> AI.equal old new_val))
    then (Stages.time `Glue (fun () -> set v new_val); true) else false)
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
  Stages.report (Sub.name s);
  Solution.create !sol_map sol_default

(* ================================================================== *)
(* Per-def classification over the converged solution. *)













(* ================================================================== *)
module Cbat_extraction = struct
(* Classification vocabulary. *)
type kind =
  | Range of int64 * int64
  | Infinite of int64 * int64
  | Unbounded
  | Dead
  | VLA of Tid.t
[@@deriving equal]

(* Kind of a word set. *)
let classify ?vla_tid (ws : WordSet.t) : kind option =
  if WordSet.is_top ws then Some Unbounded
  else if WordSet.is_bottom ws then Some Dead
  else
    match WordSet.min_elem ws, WordSet.max_elem ws with
    | Some lo, Some hi ->
      (match Word.to_int64 lo, Word.to_int64 hi with
       | Ok lo, Ok hi ->
         let is_inf = WordSet.is_infinite ws || Stdlib.Int64.compare lo hi > 0 in
         if is_inf && Option.is_some vla_tid then
           Some (VLA (Option.value_exn vla_tid))
         else if is_inf then Some (Infinite (lo, hi))
         else Some (Range (lo, hi))
       | _ -> Some Unbounded)
    | _ -> Some Unbounded

(* Signed bounds or None. *)
let bounds_of (ws : WordSet.t) : (int64 * int64) option =
  if WordSet.is_top ws || WordSet.is_bottom ws then None
  else
    match WordSet.min_elem ws, WordSet.max_elem ws with
    | Some lo, Some hi -> (
        match Word.to_int64 lo, Word.to_int64 hi with
        | Ok lo, Ok hi -> Some (lo, hi)
        | _ -> None)
    | _ -> None

(* ABI-visible k-range. *)
let k_range_of (ws : WordSet.t) (rsp_ws : WordSet.t) :
    (int64 * int64) option =
  match bounds_of ws, bounds_of rsp_ws with
  | Some (alo, ahi), Some (rlo, rhi) ->
      Some (Stdlib.Int64.sub alo rhi, Stdlib.Int64.sub ahi rlo)
  | _ -> None

(* Address of a stack-access rhs. *)
let stack_address_of_rhs (rhs : Bil.exp) : Bil.exp option =
  match rhs with
  | Bil.Load (_, addr, _, _) | Bil.Store (_, addr, _, _, _)
  | Bil.Cast (_, _, Bil.Load (_, addr, _, _))
  | Bil.Cast (_, _, Bil.Store (_, addr, _, _, _)) -> Some addr
  | _ -> None


let st_tag_of ~(tags : (tid, AI.t) Solution.t) (blk : blk term)
    (addr' : exp) (st_before : AI.t) : AI.t =
  Exp.free_vars addr'
  |> Core.Set.fold ~init:st_before ~f:(fun acc v ->
      match Var.typ v with
      | Type.Imm w ->
        let tag_v = AI.find_word w
            (Solution.get tags (Term.tid blk)) v in
        let cur = AI.find_word w acc v in
        let mm = WordSet.meet cur tag_v in
        if WordSet.is_top cur
           && Word.is_one (WordSet.cardinality mm)
           || Word.is_zero (WordSet.cardinality mm)
           || WordSet.equal mm cur
        then acc
        else AI.add_word acc ~key:v ~data:mm
      | Type.Mem _ | Type.Unk -> acc)


let rec extract ~(sp : var) ~(stack_access : def term -> bool)
    ~(dynamic_alloc : def term -> bool)
    ~(sol : (tid, AI.t) Solution.t)
    (sub : sub term) :
    kind Tid.Map.t * (int64 * int64) Tid.Map.t
    * (int64 * int64) Tid.Map.t =
  let tags = sol in
  let raw, kraw =
    Term.enum blk_t sub
    |> Seq.fold ~init:([], []) ~f:(fun (acc, kacc) blk ->
        (* Walk ends at the last tagged def. *)
        let defs = Term.enum def_t blk |> Seq.to_list in
        let last_tagged =
          Base.List.foldi defs ~init:None ~f:(fun i acc d ->
              if stack_access d then Some i else acc)
        in
        match last_tagged with
        | None -> (acc, kacc)
        | Some i ->
        let defs' = Base.List.take defs (i + 1) in
        let _, acc, kacc =
          Base.List.fold_left defs'
            ~init:(Solution.get tags (Term.tid blk), acc, kacc)
            ~f:(fun (st, acc, kacc) d ->
                 let st_before = st in
                 let st = denote_def d st in
                 match stack_address_of_rhs (Def.rhs d) with
                 | Some addr when stack_access d ->
                     let addr' =
                       rewrite_addr (frame_of_state st_before) addr in
                     (* Addresses use tag-state values. *)
                     let st_tag = st_tag_of ~tags blk addr' st_before in
                     (match
                        denote_imm_exp
                          (* Addresses rewrite to offsets. *)
                          addr' st_tag
                      with
                      | Ok ws -> (
                          match classify ws with
                          | Some kind ->
                              let acc = (Term.tid d, kind, ws) :: acc in
                              let kacc =
                                match
                                  k_range_of ws
                                    (AI.find_word 64 st_before sp)
                                with
                                | Some (klo, khi) ->
                                    (Term.tid d, klo, khi) :: kacc
                                | None -> kacc
                              in
                              (st, acc, kacc)
                          | None ->
                              let ws = WordSet.top 64 in
                              let acc = (Term.tid d, Unbounded, ws) :: acc in
                              (st, acc, kacc))
                      | Error _ ->
                          let ws = WordSet.top 64 in
                          let acc = (Term.tid d, Unbounded, ws) :: acc in
                          (st, acc, kacc))
                 | None when stack_access d ->
                     let ws = WordSet.top 64 in
                     let acc = (Term.tid d, Unbounded, ws) :: acc in
                     (st, acc, kacc)
                 | _ -> (st, acc, kacc))
        in
        (acc, kacc))
  in
  let raw = List.rev raw in
  (* Overlapping addresses merge. *)
  let span_of = function
    | Range (lo, hi) -> (lo, hi)
    | Infinite (lo, hi) -> (Stdlib.Int64.min lo hi, Stdlib.Int64.max lo hi)
    | Unbounded | Dead | VLA _ -> (0L, 0L)
  in
  let merged_tags : kind Tid.Map.t =
    let bounded, unbounded_or_dead =
      Base.List.partition_tf raw ~f:(fun (_, kind, _) ->
          match kind with
          | Range _ | Infinite _ | VLA _ -> true
          | Unbounded | Dead -> false)
    in
    let items =
      Base.List.map bounded ~f:(fun (dtid, kind, ws) -> (dtid, kind, ws))
    in
    (* Transitive overlap components. *)
    let rec components acc = function
      | [] -> acc
      | (dtid, kind, ws) :: rest ->
          let overlapping, non_overlapping =
            Base.List.partition_tf acc ~f:(fun comp ->
                Base.List.exists comp ~f:(fun (_, _, ws') -> WordSet.overlap ws ws'))
          in
          let new_comp =
            (dtid, kind, ws) :: Base.List.concat overlapping
          in
          components (new_comp :: non_overlapping) rest
    in
    let init_map =
      Base.List.fold unbounded_or_dead ~init:Tid.Map.empty ~f:(fun acc (dtid, kind, _) ->
          Core.Map.set acc ~key:dtid ~data:kind)
    in
    Base.List.fold_left (components [] items) ~init:init_map
      ~f:(fun acc comp ->
        match comp with
        | [ (dtid, kind, _) ] -> Core.Map.set acc ~key:dtid ~data:kind
        | _ ->
            let lo, hi =
              match comp with
              | (_, k0, _) :: rest ->
                let slo0, shi0 = span_of k0 in
                Base.List.fold_left rest ~init:(slo0, shi0)
                  ~f:(fun (l, h) (_, k, _) ->
                    let slo, shi = span_of k in
                    (Stdlib.Int64.min l slo, Stdlib.Int64.max h shi))
              | [] -> (0L, 0L) (* Non-empty components. *)
            in
            Base.List.fold_left comp ~init:acc
              ~f:(fun acc (dtid, _, _) ->
                  Core.Map.set acc ~key:dtid ~data:(Range (lo, hi))))
  in
  let offsets =
      Base.List.fold raw ~init:Tid.Map.empty ~f:(fun m (dtid, kind, _) ->
          let k = match Core.Map.find merged_tags dtid with
            | Some k -> k
            | None -> kind in
          Core.Map.set m ~key:dtid ~data:k) in
  let k_ranges =
    Base.List.fold kraw ~init:Tid.Map.empty
      ~f:(fun m (dtid, lo, hi) -> Core.Map.set m ~key:dtid ~data:(lo, hi)) in
  let vla_bounds =
    Term.enum blk_t sub
    |> Seq.concat_map ~f:(fun blk ->
        let blk_tid = Term.tid blk in
        Term.enum def_t blk
        |> Seq.filter ~f:dynamic_alloc
        |> Seq.filter_map ~f:(fun d ->
            match vla_size_of_rhs sp sub (Def.rhs d) with
            | None -> None
            | Some size ->
                let st = Solution.get tags blk_tid in
                match denote_imm_exp size st with
                | Ok ws -> (
                    match WordSet.min_elem ws, WordSet.max_elem ws with
                    | Some lo, Some hi -> (
                        match Word.to_int64 lo, Word.to_int64 hi with
                        | Ok lo, Ok hi -> Some (Term.tid d, (lo, hi))
                        | _ -> None)
                    | _ -> None)
                | Error _ -> None))
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m (dtid, b) ->
           Core.Map.set m ~key:dtid ~data:b)
  in
  (offsets, k_ranges, vla_bounds)

(* Dynamic-allocation size expression. *)
(* True for [RSP := RSP - size]. *)
and vla_decrement_p (sp_base : var) (rhs : Bil.exp) : bool =
  match rhs with
  | Bil.BinOp (Bil.MINUS, Bil.Var a, size) ->
      Var.same (Var.base a) sp_base
      && (match size with Bil.Int _ -> false | _ -> true)
  | _ -> false

and vla_size_of_rhs (sp : var) (sub : sub term) (rhs : Bil.exp) :
    Bil.exp option =
  let def_of_lhs =
    Term.enum blk_t sub
    |> Seq.concat_map ~f:(Term.enum def_t)
    |> Seq.fold ~init:Var.Map.empty ~f:(fun m d ->
        Core.Map.set m ~key:(Var.base (Def.lhs d)) ~data:d)
  in
  match rhs with
  | Bil.BinOp (Bil.MINUS, Bil.Var _, size) when vla_decrement_p (Var.base sp) rhs ->
      Some size
  | Bil.Var tmp -> (
      match Core.Map.find def_of_lhs (Var.base tmp) with
      | Some d' -> (
          match Def.rhs d' with
          | Bil.BinOp (Bil.MINUS, Bil.Var _, size)
            when vla_decrement_p (Var.base sp) (Def.rhs d') ->
              Some size
          | _ -> None)
      | None -> None)
  | _ -> None

end