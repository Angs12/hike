(* Forward transfer: frame facts, value denotation over BIL. Pure;
   the walk and driver consume it (one-directional dep). *)

include Core_kernel
open Bap.Std
open Graphlib.Std
open Cbat_vsa_utils
module AI = Cbat_ai_representation
module WordSet = Cbat_clp_set_composite
module Mem = Cbat_ai_memmap
module Word_ops = Cbat_word


(* Address size in bits; 0 falls back to BIL width. *)
let addr_bits_ref = ref 0
let set_addr_bits (n : int) : unit = addr_bits_ref := n

(* Memory index of a memory type. *)
let mem_idx addr_sz addressable_sz : Mem.idx =
  { Mem.addr_width =
      (if !addr_bits_ref > 0 then !addr_bits_ref else Size.in_bits addr_sz);
    Mem.addressable_width = Size.in_bits addressable_sz }

type wordset = WordSet.t





(* Widths of both inputs. *)
let denote_binop (op : Bil.binop) : wordset -> wordset -> wordset =
  let btrue = WordSet.singleton (Cbat_word.b1) in
  let bfalse = WordSet.singleton (Cbat_word.b0) in
  let wordset_of_bool b = if b then btrue else bfalse in
  let bool_top = WordSet.top 1 in
  let bool_bottom = WordSet.bottom 1 in
  (* Shared LT/LE/SLT/SLE endpoint test. *)
  let ordering ~(signed : bool) ~(le : bool) v1 v2 =
    let open Monads.Std.Monad.Option in
    let max_elem = if signed then WordSet.max_elem_signed else WordSet.max_elem in
    let min_elem = if signed then WordSet.min_elem_signed else WordSet.min_elem in
    let sgn = if signed then Cbat_word.signed else Fun.id in
    Option.value ~default:bool_top begin
      max_elem v1 >>= fun v1_max ->
      min_elem v1 >>= fun v1_min ->
      max_elem v2 >>= fun v2_max ->
      min_elem v2 >>= fun v2_min ->
      if le then
        if Cbat_word.(<=) (sgn v1_max) (sgn v2_min) then return btrue
        else if Cbat_word.(>) (sgn v1_min) (sgn v2_max) then return bfalse
        else return bool_top
      else
        if Cbat_word.(<) (sgn v1_max) (sgn v2_min) then return btrue
        else if Cbat_word.(>=) (sgn v1_min) (sgn v2_max) then return bfalse
        else return bool_top
    end in
  (* Shared EQ/NEQ decision. *)
  let compare_eq ~(negate : bool) v1 v2 =
    let v1Size = WordSet.cardinality v1 in
    let v2Size = WordSet.cardinality v2 in
    if Cbat_word.is_zero v1Size || Cbat_word.is_zero v2Size then bool_bottom
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

(* Effect of one def on facts; every def is denoted (spec §2.1). *)
let apply_frame_def_list (f : AI.frame) (d : def term) : AI.frame =
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
       let c = WordSet.singleton (Cbat_word.of_word k) in
       let shift =
         match op with
         | Bil.PLUS -> fun t -> AI.frame_add_const t c
         | Bil.MINUS -> fun t -> AI.frame_sub_const t c
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
       let k = match Cbat_word.to_int (Cbat_word.of_word k) with Ok n -> n | Error _ -> 0 in
       let y = AI.frame_key y in
       let z = AI.frame_key z in
       if_not_derived z ~shift:(fun t -> AI.frame_add_fvar t z k) y
     | Bil.MINUS, Bil.Var y, BinOp (Bil.TIMES, Bil.Var z, Bil.Int k) ->
       (* Derived iff y derived. *)
       let k = match Cbat_word.to_int (Cbat_word.of_word k) with Ok n -> n | Error _ -> 0 in
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
let expr_of_term (t : AI.frame_term) (k : Cbat_word.t) : exp option =
  match WordSet.min_elem t.fconst, WordSet.max_elem t.fconst with
  | Some lo, Some hi when Cbat_word.equal lo hi ->
    let base = Cbat_word.add lo k in
    Some (List.fold t.fvars ~init:(Bil.Int (Cbat_word.to_word base)) ~f:(fun acc (v, k') ->
        let scaled = Bil.BinOp (Bil.TIMES, Bil.Var v, Bil.Int (Cbat_word.to_word (Cbat_word.of_int ~width:64 k'))) in
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
       | Some t -> expr_of_term t (Cbat_word.zero 64)
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
  | Bil.Int bv -> return_imm @@ WordSet.singleton (Cbat_word.of_word bv)
  | Bil.BinOp (op, e1, e2) ->
    denote_exp e1 env >>= val_as_imm >>= fun v1 ->
    denote_exp e2 env >>= val_as_imm >>= fun v2 ->
    return_imm @@ denote_binop op v1 v2
  | Bil.Load (m, a, e, s) ->
    denote_exp a env >>= val_as_imm >>= fun addr ->
    denote_exp m env >>= val_as_mem >>= fun mv ->
    let resSize = Size.in_bits s in
    if WordSet.splits_by addr (Cbat_word.of_int ~width:resSize (Size.in_bytes s))
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
    (* The store may write any cell: whole-memory top. *)
    then return_mem @@ Mem.top (Mem.get_idx mv)
    else
    
    let v' = if WordSet.splits_by addr (Cbat_word.of_int ~width:sz (Size.in_bytes s))
      then v else WordSet.top sz in
    let data = Mem.Val.create v' e in
    return_mem @@ Option.value_map ~default:mv (Mem.Key.of_wordset addr)
      ~f:(fun key -> Mem.add mv ~key ~data)
  | Bil.Ite (cond, yes, no) ->
    denote_exp cond env >>= val_as_imm >>= fun condv ->
    denote_exp yes env >>= fun yesv ->
    denote_exp no env >>= fun nov ->
    if WordSet.is_top condv then val_join yesv nov
    else if WordSet.equal condv (WordSet.singleton (Cbat_word.b1)) then return yesv
    else if WordSet.equal condv (WordSet.singleton Cbat_word.b0) then return nov
    
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
  (* Every def is denoted (spec §2.1); the restriction gate is deleted. *)
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
    let can_fall_through = WordSet.elem Cbat_word.b0 cond in
    if not reachable then Seq.Step.Done
    else if WordSet.elem (Cbat_word.b1) cond then Seq.Step.Yield {value = jmp; state = can_fall_through}
    else Seq.Step.Skip {state = can_fall_through}
  end
