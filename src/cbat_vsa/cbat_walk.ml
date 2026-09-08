(* Backward walk: guard rows, pre-images, the deep walk, edge transfer.
   Consumes the transfer (open, bodies untouched); the driver consumes
   this module. Trace-partitioning lives here (ADR-0002). *)

include Core_kernel
open Bap.Std
open Graphlib.Std
open Cbat_vsa_utils
module AI = Cbat_ai_representation
module WordSet = Cbat_clp_set_composite
module Mem = Cbat_ai_memmap
module Word_ops = Cbat_word

module Abi = Hike_abi
module Stages = Cbat_vsa_stages
open Cbat_transfer




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
let interval_clp_of ~(width : int) ~(cardn : Cbat_word.t) (base : Cbat_word.t)
    : wordset option =
  if Cbat_word.is_zero cardn then None
  else
    let ws = WordSet.of_clp
        (Cbat_clp.create ~width ~step:(Cbat_word.one width) ~cardn base) in
    if WordSet.is_top ws then None else Some ws

(* Values allowed on a taken edge. *)
let comparison_constraint ?(cur : wordset option = None)
    ?(known_nonneg : bool = false)
    (op : Bil.binop) (c : Cbat_word.t) : wordset option =
  let width = Cbat_word.bitwidth c in
  let cardn_of_int (i : int) : Cbat_word.t option =
    if i < 0 then None else Some (Cbat_word.of_int ~width:(width + 1) i) in
  let int_of_word (w : Cbat_word.t) : int option =
    try Some (Cbat_word.to_int_exn w) with _ -> None in
  (* Non-negativity threshold. *)
  let half = Word_ops.half width in
  let provably_nonneg : bool =
    Option.value_map cur ~default:false ~f:(fun ws ->
        match WordSet.max_elem ws with
        | None -> false
        | Some m -> Cbat_word.(<) m half) in
  match op with
  | Bil.LT -> Option.bind (int_of_word c) ~f:(fun i ->
      Option.bind (cardn_of_int i) ~f:(fun cardn ->
          interval_clp_of ~width ~cardn (Cbat_word.zero width)))
  | Bil.LE -> Option.bind (int_of_word c) ~f:(fun i ->
      Option.bind (cardn_of_int (i + 1)) ~f:(fun cardn ->
          interval_clp_of ~width ~cardn (Cbat_word.zero width)))
  | Bil.EQ -> Some (WordSet.singleton c)
  | Bil.SLT ->
    (* Signed less-than row. *)
    if Cbat_word.(>=) c half
    then interval_clp_of ~width ~cardn:(Cbat_word.sub c half) half
    else if provably_nonneg || known_nonneg
    then interval_clp_of ~width ~cardn:c (Cbat_word.zero width)
    else None
  | Bil.SLE ->
    (* Signed less-equal row. *)
    if Cbat_word.(>=) c half
    then interval_clp_of ~width ~cardn:(Cbat_word.succ (Cbat_word.sub c half)) half
    else if provably_nonneg || known_nonneg
    then interval_clp_of ~width ~cardn:(Cbat_word.succ c) (Cbat_word.zero width)
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

(* CLP interval or None on doubt; the lo>hi guard is load-bearing: this is
   the NON-wrapping constructor. The wrapping twin below exists because the
   backward PLUS/MINUS/SDIVIDE rows pin wrapped hulls (S8, L3c3-1, R2-1,
   M5-1) — do not merge them; the one-line difference is the contract. *)
let interval_of_bounds (width : int) (lo : Cbat_word.t) (hi : Cbat_word.t) : wordset option =
  if Cbat_word.bitwidth lo <> width || Cbat_word.bitwidth hi <> width then None
  else if Cbat_word.(>) lo hi then None
  else
    let ws = WordSet.of_clp (Cbat_clp.interval ~width lo hi) in
    if WordSet.is_top ws then None else Some ws

(* TOP minus a point: the exact two-piece NEQ complement. *)
let neq_complement (c : Cbat_word.t) : wordset option =
  let cstr =
    WordSet.diff (WordSet.top (Cbat_word.bitwidth c)) (WordSet.singleton c) in
  if Cbat_clp_set_composite.is_bottom cstr then None else Some cstr

(* Constraint rows for decoded ops. *)
let decoder_constraint ?(cur : wordset option = None)
    ?(known_nonneg : bool = false)
    (op : guard_op) (c : Cbat_word.t) : wordset option =
  let width = Cbat_word.bitwidth c in
  match op with
  | ULT -> comparison_constraint ~cur Bil.LT c
  | ULE -> comparison_constraint ~cur Bil.LE c
  | EQ -> comparison_constraint ~cur Bil.EQ c
  | NEQ -> neq_complement c
  | SLT -> comparison_constraint ~cur ~known_nonneg Bil.SLT c
  | SLE -> comparison_constraint ~cur ~known_nonneg Bil.SLE c
  | UGT ->
    (* Unsigned greater-than row. *)
    let lo = Cbat_word.succ c in
    if Cbat_word.is_zero lo then None
    else interval_of_bounds width lo (Cbat_word.ones width)
  | UGE ->
    (* Unsigned greater-equal row. *)
    interval_of_bounds width c (Cbat_word.ones width)
  | SGT ->
    (* Signed greater-than row. *)
    let lo = Cbat_word.succ c in
    if Cbat_word.is_zero lo then None
    else interval_of_bounds width lo (Cbat_word.ones width)
  | SGE ->
    (* Signed greater-equal row. *)
    interval_of_bounds width c (Cbat_word.ones width)

(* Provenance-based non-negativity proof. *)
let prove_nonneg ~(defs : (def term * bool) Var.Map.t)
    ~(stores : def term list)
    ~(env : AI.t) (e : exp) : bool =
  (* MSB-clear literals. *)
  let nonneg_word (n : Cbat_word.t) : bool =
    let w = Cbat_word.bitwidth n in
    w > 0
    && Cbat_word.(<) n (Word_ops.half w) in
  let frame = AI.frame_of env in
  (* Anchored = the var's offset from the entry frame is a PROVEN CONSTANT:
     a term carrying fvars varies with the index and proves no constant
     bound (ADR 0008 — stack-ness is proven, never granted by name). *)
  let stack_anchor (v : var) : bool =
    match frame with
    | None -> false
    | Some f ->
      (match AI.frame_lookup f (AI.frame_key v) with
       | Some t -> List.is_empty t.fvars
       | None -> false) in
  (* Threaded cycle guards. *)
  let rec walk (cells : Exp.Set.t) (vars : Exp.Set.t) (e : exp) : bool =
    match e with
    | Bil.Int n -> nonneg_word (Cbat_word.of_word n)
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
       | Bil.Int z when Cbat_word.is_zero (Cbat_word.of_word z) -> walk cells vars a
       | _ -> false)
    | Bil.BinOp (Bil.RSHIFT, _, Bil.Int k) ->
      let k = Cbat_word.of_word k in
      (* Positive rshift clears the sign. *)
      (match Cbat_word.to_int k with
       | Ok n when n > 0 -> true
       | Ok 0 -> false
       | _ -> false)
    | Bil.BinOp (Bil.ARSHIFT, a, Bil.Int k) ->
      let k = Cbat_word.of_word k in
      (match Cbat_word.to_int k with
       | Ok n when n > 0 -> walk cells vars a
       | Ok 0 -> walk cells vars a
       | _ -> false)
    | Bil.BinOp (Bil.TIMES, a, Bil.Int k) ->
      let k = Cbat_word.of_word k in
      (* Multiplier recurrence row. *)
      if Cbat_word.is_zero k then true else walk cells vars a
    | Bil.BinOp (Bil.DIVIDE, a, Bil.Int k) ->
      let k = Cbat_word.of_word k in
      (* Division by 2+ is non-negative. *)
      (match Cbat_word.to_int k with
       | Ok n when n >= 2 -> true
       | Ok 1 -> walk cells vars a
       | _ -> false)
    | Bil.BinOp (Bil.AND, a, Bil.Int k) ->
      let k = Cbat_word.of_word k in
      let w = Cbat_word.bitwidth k in
      let half = Word_ops.half w in
      if Cbat_word.(<) k half then true
      else if Cbat_word.(=) k (Cbat_word.ones w) then walk cells vars a
      else false
    | Bil.BinOp (Bil.OR, a, Bil.Int k)
      when Cbat_word.is_zero (Cbat_word.of_word k) -> walk cells vars a
    | Bil.BinOp (Bil.XOR, a, Bil.Int k)
      when Cbat_word.is_zero (Cbat_word.of_word k) -> walk cells vars a
    | Bil.Cast (Bil.HIGH, _, a) ->
      (* HIGH of non-negative is non-negative. *)
      walk cells vars a
    | Bil.Load (_, addr, _, _) ->
      (* Anchored = every address var has a CONSTANT frame term, AND there
         is at least one (a constant address is a global — NOT private to
         this sub; the old [for_all] over empty free-vars passed those
         vacuously, proving non-negativity for cells other subs write).
         The frame term IS the privacy proof: it places the cell in this
         sub's own frame. *)
      let anchored =
        not (Core.Set.is_empty (Exp.free_vars addr))
        && Core.Set.for_all (Exp.free_vars addr) ~f:stack_anchor in
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
          | Bil.Store (_, _, Bil.Int n, _, _) -> nonneg_word (Cbat_word.of_word n)
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
    ~(stores : def term list option) ~(env : AI.t) (e : exp) : bool =
  match defs, stores with
  | Some dm, Some ss -> prove_nonneg ~defs:dm ~stores:ss ~env e
  | _ -> false

(* Wrapping CLP interval or None on doubt: the twin of the constructor
   above MINUS the lo>hi guard (a wrapped pair is the circular interval).
   Only the backward arithmetic rows call it; every other site wants the
   non-wrapping contract. *)
let circular_hull (width : int) (lo : Cbat_word.t) (hi : Cbat_word.t) : wordset option =
  if Cbat_word.bitwidth lo <> width || Cbat_word.bitwidth hi <> width then None
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
    let wrap_limit (k : Cbat_word.t) : Cbat_word.t = Cbat_word.div (Cbat_word.ones width) k in
    let operand_bounded (limit : Cbat_word.t) : bool =
      match WordSet.max_elem a_ws with
      | Some m -> Cbat_word.(<=) m limit
      | None -> false in
    let ceil_div (k : Cbat_word.t) (x : Cbat_word.t) : Cbat_word.t =
      let q = Cbat_word.div x k in
      let r = Cbat_word.modulo x k in
      if Cbat_word.is_zero r then q else Cbat_word.succ q in
    match op with
    | Bil.PLUS ->
      (* Plus: shift intervals by the other operand. *)
      (match WordSet.min_elem cstr, WordSet.max_elem cstr with
       | Some vlo, Some vhi ->
         let a' = match WordSet.min_elem b_ws, WordSet.max_elem b_ws with
           | Some bmin, Some bmax ->
             circular_hull width (Cbat_word.sub vlo bmax) (Cbat_word.sub vhi bmin)
           | _ -> None in
         let b' = match WordSet.min_elem a_ws, WordSet.max_elem a_ws with
           | Some amin, Some amax ->
             circular_hull width (Cbat_word.sub vlo amax) (Cbat_word.sub vhi amin)
           | _ -> None in
         a', b'
       | _ -> None, None)
    | Bil.MINUS ->
      (* Minus: shift intervals by the other operand. *)
      (match WordSet.min_elem cstr, WordSet.max_elem cstr with
       | Some vlo, Some vhi ->
         let a' = match WordSet.min_elem b_ws, WordSet.max_elem b_ws with
           | Some bmin, Some bmax ->
             circular_hull width (Cbat_word.add vlo bmin) (Cbat_word.add vhi bmax)
           | _ -> None in
         let b' = match WordSet.min_elem a_ws, WordSet.max_elem a_ws with
           | Some amin, Some amax ->
             circular_hull width (Cbat_word.sub amin vhi) (Cbat_word.sub amax vlo)
           | _ -> None in
         a', b'
       | _ -> None, None)
    | Bil.TIMES ->
      (* Times by literal. *)
      (match WordSet.min_elem cstr, WordSet.max_elem cstr,
             WordSet.min_elem b_ws, WordSet.max_elem b_ws with
       | Some vlo, Some vhi, Some k, Some k' when Cbat_word.(=) k k' ->
         (match Cbat_word.to_int k with
          | Ok kk when kk > 0 && operand_bounded (wrap_limit k) ->
            (match interval_of_bounds width (ceil_div k vlo)
                     (Cbat_word.div vhi k) with
             | Some a' -> Some a', None
             | None -> None, None)
          | _ -> None, None)
       | _ -> None, None)
    | Bil.LSHIFT ->
      (* Minus: shift intervals by the other operand. *)
      (match WordSet.min_elem cstr, WordSet.max_elem cstr,
             WordSet.min_elem b_ws, WordSet.max_elem b_ws with
       | Some vlo, Some vhi, Some smin, Some smax ->
         (match Cbat_word.to_int smin, Cbat_word.to_int smax with
          | Ok smin_i, Ok smax_i
            when smin_i >= 0 && smax_i < width && smin_i <= smax_i ->
            let lo_a = Cbat_word.rshift vlo smax in
            let hi_a = Cbat_word.rshift vhi smin in
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
         (match Cbat_word.to_int smin, Cbat_word.to_int smax with
          | Ok smin_i, Ok smax_i
            when smin_i >= 0 && smax_i < width && smin_i <= smax_i ->
            let hi1 = Cbat_word.succ vhi in
            let mask = Cbat_word.lshift (Cbat_word.one width)
                (Cbat_word.of_int ~width:width (width - smax_i)) in
            if Cbat_word.(>) hi1 mask then None, None
            else
              let lo_a = Cbat_word.lshift vlo (Cbat_word.of_int ~width smin_i) in
              let hi_a = Cbat_word.pred (Cbat_word.lshift hi1 (Cbat_word.of_int ~width smax_i)) in
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
         (match Cbat_word.to_int kmin, Cbat_word.to_int kmax with
          | Ok kmin_i, Ok kmax_i when kmin_i > 0 && kmin_i <= kmax_i ->
            let hi1 = Cbat_word.succ vhi in
            let kmax_w = Cbat_word.of_int ~width kmax_i in
            let limit = Cbat_word.div (Cbat_word.ones width) kmax_w in
            if Cbat_word.(>) hi1 limit then None, None
            else
              let lo_a = Cbat_word.mul vlo (Cbat_word.of_int ~width kmin_i) in
              let hi_a = Cbat_word.pred (Cbat_word.mul hi1 kmax_w) in
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
           width <= 32 && Cbat_word.(=) k k' ->
         (match Cbat_word.to_int k with
          | Ok kk when kk > 0 ->
            (* Small widths avoid overflow. *)
            (match Cbat_word.to_int vlo, Cbat_word.to_int vhi with
             | Ok slo, Ok shi ->
               let lo' = slo * kk in
               let hi' = (shi + 1) * kk - 1 in
               (match circular_hull width
                        (Cbat_word.of_int ~width lo') (Cbat_word.of_int ~width hi') with
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
       | Some k, Some k' when Cbat_word.(=) k k' ->
         if Cbat_word.is_zero k then
           (match op with
            | Bil.OR | Bil.XOR -> Some cstr, None
            | _ -> None, None)
         else if Cbat_word.(=) k (Cbat_word.ones width) then
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
  | Bil.Int w -> Some (WordSet.singleton (Cbat_word.of_word w))
  | _ ->
    (match denote_imm_exp e env with
     | Ok ws -> Some ws
     | Error _ -> None)

(* LSHIFT pre-image: shift the result interval back by the literal. *)
let lshift_preimage (width : int) (k : Cbat_word.t) (cstr : wordset)
    : wordset option =
  match Cbat_word.to_int k with
  | Ok kk when kk >= 0 && kk < width ->
    (match WordSet.min_elem cstr, WordSet.max_elem cstr with
     | Some lo, Some hi ->
       let lo_a =
         WordSet.rshift (WordSet.singleton lo) (WordSet.singleton k) in
       let hi_a =
         WordSet.rshift (WordSet.singleton hi) (WordSet.singleton k) in
       (match WordSet.min_elem lo_a, WordSet.max_elem hi_a with
        | Some lo', Some hi' -> interval_of_bounds width lo' hi'
        | _ -> None)
     | _ -> None)
  | _ -> None

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
         let hi1 = Cbat_word.succ hi in
         if Cbat_word.is_zero hi1 then None
         else
           let lo_w = Cbat_word.extract_exn ~hi:(w - 1) lo in
           let hi1_w = Cbat_word.extract_exn ~hi:(w - 1) hi1 in
           let mask = Cbat_word.lshift (Cbat_word.one w)
               (Cbat_word.of_int ~width:w n) in
           if Cbat_word.(>) hi1_w mask then None
           else
             let lo_a = Cbat_word.lshift lo_w (Cbat_word.of_int ~width:w shift) in
             let hi_a =
               Cbat_word.pred (Cbat_word.lshift hi1_w (Cbat_word.of_int ~width:w shift)) in
             interval_of_bounds w lo_a hi_a
       | _ -> None)
  | None -> None

(* Genuine-subset meet into a var; gate-free (spec §2.1). *)
let meet_var (env : AI.t)
    (v : var) (refined : wordset) : AI.t =
  match Var.typ v with
  | Type.Imm w ->
    let cur = AI.find_word w env v in
    if WordSet.bitwidth cur <> w || WordSet.bitwidth refined <> w
    then env
    else
      let m = WordSet.meet cur refined in
      if Cbat_word.is_zero (WordSet.cardinality m) then begin
        Cbat_landmarks.observe_unsat_var v ~p:cur ~cstr:refined;
        env
      end else if not (WordSet.precedes m cur)
      then env
      else AI.add_word env ~key:v ~data:m
  | Type.Mem _ | Type.Unk -> env

(* Meet a constraint into a load cell; gate-free (spec §2.1). *)
let rec constrain_cell
    (env : AI.t)
    ~(mem : exp) ~(addr : exp) ~(size : Size.t) ~(endian : endian)
    (cstr : wordset) : AI.t =
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
               if Cbat_word.is_zero (WordSet.cardinality refined)
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
    ~(visited : Var.Set.t)
    (env : AI.t) (op : Bil.binop) (a : exp) (b : exp)
    (cstr : wordset) : AI.t =
  let width = WordSet.bitwidth cstr in
  match op with
  | Bil.LSHIFT ->
    (* Minus: shift intervals by the other operand. *)
    (match b with
     | Bil.Int k ->
       (match lshift_preimage width (Cbat_word.of_word k) cstr with
        | Some a' ->
          let env' = match a with
            | Bil.Var av -> meet_var env av a'
            | _ -> env in
          constrain_def_chain ~defs
            ~visited env' a a'
        | None -> env)
     | _ -> env)
  | Bil.PLUS | Bil.MINUS | Bil.TIMES | Bil.DIVIDE | Bil.SDIVIDE
  | Bil.MOD | Bil.SMOD | Bil.AND | Bil.OR | Bil.XOR
  | Bil.RSHIFT | Bil.ARSHIFT ->
    (match denote_operand env a, denote_operand env b with
     | Some a_ws, Some b_ws ->
       (match operand_constraints op cstr a_ws b_ws with
        | a', b' ->
          let env' = match a, a' with
            | Bil.Var av, Some a_c -> meet_var env av a_c
            | _ -> env in
          let env'' = match b, b' with
            | Bil.Var bv, Some b_c -> meet_var env' bv b_c
            | _ -> env' in
          let env_a = match a, a' with
            | Bil.Var _, Some a_c ->
              constrain_def_chain ~defs
                ~visited env'' a a_c
            | _ -> env'' in
          (match b, b' with
           | Bil.Var _, Some b_c ->
             constrain_def_chain ~defs
               ~visited env_a b b_c
           | _ -> env_a))
     | _ -> env)
  | _ -> env

(* Refine producers backward through defs. *)
and constrain_def_chain ~(defs : (def term * bool) Var.Map.t)
    ?(visited : Var.Set.t = Var.Set.empty)
    (env : AI.t) (e : exp) (cstr : wordset) : AI.t =
  match e with
  | Bil.Load (m, a, en, s) ->
    (* Loads constrain the cell. *)
    constrain_cell env ~mem:m ~addr:a ~size:s ~endian:en cstr
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
             constrain_cell env ~mem:m
               ~addr:a ~size:s ~endian:en cstr
           | Bil.BinOp (op, a, b) ->
             refine_chain ~defs
               ~visited:visited' env op a b cstr
           | Bil.Cast (Bil.HIGH, sz, a) ->
             (* HIGH-extract producer row. *)
             refine_cast_high ~defs
               ~visited:visited' env a sz cstr
         | Bil.Cast (ct, _sz, _a) ->
           (* Other casts stay identity. *)
           ignore ct; env
         | Bil.Int _ -> env
         | _ -> env)
  | Bil.BinOp (op, a, b) ->
    (* Inline compares use producer rows. *)
    refine_chain ~defs ~visited env op a b cstr
  | _ -> env


(* HIGH-extract producer row: the pure pre-image, met and recursed. *)
and refine_cast_high ~(defs : (def term * bool) Var.Map.t)
    ~(visited : Var.Set.t)
    (env : AI.t) (a : exp) (sz : int) (cstr : wordset) : AI.t =
  match high_cast_constraint env a sz cstr with
  | None -> env
  | Some a' ->
    let env' = match a with
      | Bil.Var av -> meet_var env av a'
      | _ -> env in
    constrain_def_chain ~defs
      ~visited env' a a'

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
                     if Cbat_word.is_zero (WordSet.cardinality m)
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

(* Extension pre-image. *)
let ext_cast_constraint ~(is_signed : bool) (env : AI.t) (a : exp)
    (cstr : wordset) : wordset option =
  match denote_operand env a with
  | Some a_ws ->
    let n = WordSet.bitwidth a_ws in
    let w = WordSet.bitwidth cstr in
    if w <= n then None
    else
      let zero = Cbat_word.zero w in
      let two_n =
        Cbat_word.lshift (Cbat_word.one w) (Cbat_word.of_int ~width:w n) in
      let half =
        Cbat_word.lshift (Cbat_word.one w) (Cbat_word.of_int ~width:w (n - 1)) in
      let maxn = Cbat_word.pred two_n in
      (match WordSet.min_elem cstr, WordSet.max_elem cstr with
       | Some lo, Some hi ->
         let pieces =
           if not is_signed then
             (* Zero-extension case. *)
             if Cbat_word.(>) lo maxn then []
             else [ (lo, Cbat_word.min hi maxn) ]
           else begin
             (* Sign-extension halves. *)
             let pos =
               if Cbat_word.(>) lo (Cbat_word.pred half) then []
               else [ Cbat_word.max lo zero, Cbat_word.min hi (Cbat_word.pred half) ] in
             let neg =
               let neg_sext_lo =
                 Cbat_word.sub (Cbat_word.ones w) (Cbat_word.pred half) in
               let lo' = Cbat_word.max lo neg_sext_lo in
               let hi' = Cbat_word.min hi (Cbat_word.ones w) in
               if Cbat_word.(>) lo' hi' then []
               else
                 (* Wrapped negative half. *)
                 [ Cbat_word.add lo' two_n, Cbat_word.add hi' two_n ] in
             pos @ neg
           end
         in
         (match pieces with
          | [] -> None
          | (p0, p1) :: rest ->
            let lo' =
              List.fold rest ~init:p0 ~f:(fun acc (l, _) ->
                  Cbat_word.min acc l) in
            let hi' =
              List.fold rest ~init:p1 ~f:(fun acc (_, h) ->
                  Cbat_word.max acc h) in
            (* Truncate pieces to the operand width. *)
            interval_of_bounds n
              (Cbat_word.extract_exn ~hi:(n - 1) lo')
              (Cbat_word.extract_exn ~hi:(n - 1) hi'))
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
         let vlo_w = Cbat_word.extract_exn ~hi:(w - 1) vlo in
         let vhi_w = Cbat_word.extract_exn ~hi:(w - 1) vhi in
         let two_n =
           Cbat_word.lshift (Cbat_word.one w) (Cbat_word.of_int ~width:w n) in
         let hi_a = Cbat_word.add vhi_w (Cbat_word.sub (Cbat_word.ones w) two_n) in
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
         let shift = Cbat_word.of_int ~width:w lo in
         let lo_a = Cbat_word.lshift vlo shift in
         let hi_emb =
           Cbat_word.pred (Cbat_word.lshift (Cbat_word.succ vhi) shift) in
         let hi_a =
           if hi + 1 >= w then hi_emb
           else
             Cbat_word.add hi_emb
               (Cbat_word.sub (Cbat_word.ones w)
                  (Cbat_word.lshift (Cbat_word.one w)
                     (Cbat_word.of_int ~width:w (hi + 1)))) in
         interval_of_bounds w lo_a hi_a
       | _ -> None)
  | None -> None


let def_constraints ~(blk_state : AI.t) (env : AI.t ref)
    (d : def term) (live : Live.t) (cstr : wordset)
    : (var * wordset) list =
  (* The block's state is fixed for this def; the caller derived it. *)
  match Def.rhs d with
  | Bil.Load (m, a, en, s) ->
    (* Cells only; addresses unconstrained. *)
    env := constrain_cell_on_trace
      ~st:blk_state ~live
      !env ~mem:m ~addr:a ~size:s ~endian:en cstr;
    []
  | Bil.BinOp (Bil.LSHIFT, a, b) ->
    (* Minus: shift intervals by the other operand. *)
    let width = WordSet.bitwidth cstr in
    (match b with
     | Bil.Int k ->
       (match lshift_preimage width (Cbat_word.of_word k) cstr with
        | Some a' ->
          (match a with
           | Bil.Var av -> [ (Var.base av, a') ]
           | _ -> [])
        | None -> [])
     | _ -> [])
  | Bil.BinOp (op, a, b) ->
    
    (match denote_operand !env a, denote_operand !env b with
     | Some a_ws, Some b_ws ->
       (match operand_constraints op cstr a_ws b_ws with
        | a', b' ->
          (match a, a', b, b' with
           | Bil.Var av, Some a_c, Bil.Var bv, Some b_c ->
             [ (Var.base av, a_c); (Var.base bv, b_c) ]
           | Bil.Var av, Some a_c, _, _ -> [ (Var.base av, a_c) ]
           | _, _, Bil.Var bv, Some b_c -> [ (Var.base bv, b_c) ]
           | _ -> []))
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


(* Reverse-def walk of one block. *)
let reverse_def_walk ~(defs : (def term * bool) Var.Map.t)
    ~(sol : (tid, AI.t) Solution.t)
    (env : AI.t ref) (live : Live.t)
    (blk : blk term) : Live.t =
  let live = ref live in
  (* The block's state is loop-invariant over its own defs. *)
  let blk_state = Solution.get sol (Term.tid blk) in
  Term.enum ~rev:true def_t blk
  |> Seq.iter ~f:(fun d ->
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
                      (denote_def d blk_state)
                      (Def.lhs d))
            | Type.Mem _ | Type.Unk -> None in
          (match post_v with
           | Some pv ->
             let cstr' = WordSet.meet cstr pv in
             if Cbat_word.is_zero (WordSet.cardinality cstr') then
               (* Empty pre-image drops the lhs. *)
               live := Live.remove v !live
             else begin
               live := Live.remove v !live;
               let pairs = def_constraints ~blk_state env d !live cstr' in
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
  (* The block's state is loop-invariant over its own phis. *)
  let blk_state = Solution.get sol (Term.tid blk) in
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
                  ~st:blk_state ~live:!live
                  !env ~mem:m ~addr:a ~size:s ~endian:en cstr
              | _ -> ()));
  !live


let refine_edge ~(sol : (tid, AI.t) Solution.t)
    ~(rctx : Cbat_runctx.refine_ctx)
    ?(defs : (def term * bool) Var.Map.t option = None)
    ?(reads : Tid.Set.t ref option = None)
    ?(steps : int option = None)
    (env : AI.t) (blk : blk term)
    (seeds : edge_constraint list) : AI.t * (tid, Live.t) Solution.t =
  (* Visited set is closure-local. *)
  match defs with
  | None -> env, Solution.create Tid.Map.empty Live.empty
  | Some defs_map ->
    (* Walk reuses the hoisted CFG. *)

    let cfg = rctx.rc_walk_cfg in
    (* The 256 default; the per-SCC budget may lower it. *)
    let cap = Option.value ~default:Cbat_runctx.cap_default steps in
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
        ~steps:cap ~rev:true
        ~f:(fun ~source:n ->
            fun live ->
              incr pops;
              (* One pop spends one unit of the shared per-SCC budget. *)
              rctx.rc_walk_budget :=
                max 0 (pred !(rctx.rc_walk_budget));
              (* Visited blocks are recorded. *)
              Option.iter reads ~f:(fun r ->
                  r := Core.Set.add !r n);
              match Core.Map.find rctx.rc_blocks n with
              | Some b ->
                (* Guard defs walk over the seed. *)
                let live =
                  if Tid.equal (Term.tid b) (Term.tid blk)
                  then Live.join live seed_constraints
                  else live in
                (* Nothing live propagates nothing: skip both walks. *)
                if Core.Map.is_empty live then fun ~target:_ -> live
                else begin
                let base =
                  reverse_def_walk ~defs:defs_map ~sol
                    env live b in
                fun ~target:t ->
                  route_phi_constraints ~sol env t
                    base b
                end
              | None -> fun ~target:_ -> live)
        ~step:(fun _ _ -> fun _ x' -> x')
        cfg in
    (* Commit walk metrics (debug-only; the production adapter drops them). *)
    Stages.bump_walk_pops
      ~pops:!pops
#ifdef VSA_DEBUG
      ~blocks:(match reads with
          | Some r -> Core.Set.length !r
          | None -> 0)
#else
      ~blocks:0
#endif
      ~truncated:(!pops >= cap)
      ~budget_cap:cap
      ();
    (* Guard with no preds keeps the seed. The walk runs for its [env]
       side effects (cell meets commit through the ref); the derived
       solution is discarded by both callers, so no derive. *)
    (match Core.Map.find rctx.rc_blocks (Term.tid blk) with
     | Some gb ->
       ignore
         (reverse_def_walk ~defs:defs_map ~sol env
            (Live.join (Solution.get live_sol (Term.tid blk))
               seed_constraints) gb
           : Live.t)
     | None -> ());
    !env, live_sol

(* Backward-walk context record. *)
type analysis_ctx = {
  defs : (def term * bool) Var.Map.t option;
  stores : def term list option;
  flag_state : (var * Bil.binop * exp * word) option;
  (* True when the ctx comes from a real walk: the direct-API refinement
     ([inverse_denote_exp]) is then a no-op. *)
  has_sub : bool;
}

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


let guard_constraint (w : int) (op : guard_op) (c : Cbat_word.t)
    : wordset option =
  let maxw = Cbat_word.ones w in
  let half = Word_ops.half w in
  let iv lo hi = interval_of_bounds w lo hi in
  match op with
  | EQ -> Some (WordSet.singleton c)
  | NEQ -> neq_complement c
  | ULT ->
    (if Cbat_word.is_zero c then None
     else iv (Cbat_word.zero w) (Cbat_word.pred c))
  | ULE -> iv (Cbat_word.zero w) c
  | UGT ->
    (if Cbat_word.(=) c maxw then None
     else iv (Cbat_word.succ c) maxw)
  | UGE -> iv c maxw
  | SLT ->
    let pos =
      if Cbat_word.is_zero c then None
      else iv (Cbat_word.zero w) (Cbat_word.pred c) in
    (match iv half maxw with
     | Some neg ->
       Some (match pos with
         | Some p -> WordSet.union p neg
         | None -> neg)
     | None -> pos)
  | SLE ->
    (match iv half maxw with
     | Some neg ->
       (match iv (Cbat_word.zero w) c with
        | Some lo -> Some (WordSet.union lo neg)
        | None -> Some neg)
     | None -> iv (Cbat_word.zero w) c)
  | SGT ->
    (if Cbat_word.(=) c (Cbat_word.pred half) then None
     else iv (Cbat_word.succ c) (Cbat_word.pred half))
  | SGE -> iv c (Cbat_word.pred half)


let overlap_constraints (op : Bil.binop) (a_ws : wordset) (b_ws : wordset)
    : wordset option * wordset option =
  let w = WordSet.bitwidth a_ws in
  if WordSet.bitwidth b_ws <> w then None, None
  else
    let half = Word_ops.half w in
    let maxw = Cbat_word.ones w in
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
      | Some m -> Cbat_word.(<) m half
      | None -> false in
    (match mn_x, mx_y, mn_y, mx_x with
     | Some mn_x, Some mx_y, Some mn_y, Some mx_x ->
       let x_cstr, y_cstr =
         match op with
         | Bil.LT ->
           ((if Cbat_word.is_zero mx_y then None
             else interval_of_bounds w (Cbat_word.zero w) (Cbat_word.pred mx_y)),
            (if Cbat_word.(=) mn_x maxw then None
             else interval_of_bounds w (Cbat_word.succ mn_x) maxw))
         | Bil.LE ->
           (interval_of_bounds w (Cbat_word.zero w) mx_y,
            interval_of_bounds w mn_x maxw)
         | Bil.SLT ->
           ((if Cbat_word.(>=) mx_y half then
               interval_of_bounds w half (Cbat_word.pred mx_y)
             else if provably_nonneg_x then
               if Cbat_word.is_zero mx_y then None
               else interval_of_bounds w (Cbat_word.zero w) (Cbat_word.pred mx_y)
             else None),
            (if Cbat_word.(>=) mn_x half then None
             else interval_of_bounds w (Cbat_word.succ mn_x) (Cbat_word.pred half)))
         | Bil.SLE ->
           ((if Cbat_word.(>=) mx_y half then
               interval_of_bounds w half mx_y
             else if provably_nonneg_x then
               interval_of_bounds w (Cbat_word.zero w) mx_y
             else None),
            (if Cbat_word.(>=) mn_x half then None
             else interval_of_bounds w mn_x (Cbat_word.pred half)))
         | Bil.EQ ->
           let ov = WordSet.meet a_ws b_ws in
           if Cbat_word.is_zero (WordSet.cardinality ov)
           then None, None
           else Some ov, Some ov
         | Bil.NEQ ->
           let ov = WordSet.meet a_ws b_ws in
           if Cbat_word.is_zero (WordSet.cardinality ov)
           then Some a_ws, Some b_ws
           else Some (WordSet.diff a_ws ov), Some (WordSet.diff b_ws ov)
         | _ -> None, None in
       x_cstr, y_cstr
     | _ -> None, None)

(* Taken-edge constraint on an operand. *)
let row_for ~(env : AI.t) ?(ctx : analysis_ctx option)
    (e : exp) (op : guard_op) (c : Cbat_word.t) : wordset option =
  let cur = match denote_imm_exp e env with
    | Ok ws -> Some ws
    | Error _ -> None in
  match ctx with
  | None -> guard_constraint (Cbat_word.bitwidth c) op c
  | Some { defs; stores; _ } ->
    let known_nonneg = known_nonneg_of ~defs ~stores ~env e in
    (match decoder_constraint ~cur ~known_nonneg op c with
     | Some cstr -> Some cstr
     | None -> guard_constraint (Cbat_word.bitwidth c) op c)

(* Leaf seeds of a guard. *)
let rec edge_constraints ~(env : AI.t) ?(ctx : analysis_ctx option)
    (cond : exp) (cstr : wordset) : edge_constraint list =
  (* Signed rows are two-piece. *)
  match cond with
  | Bil.Var v ->
    begin match Var.typ v with
    | Type.Imm 1 ->
      (* Bare-flag shape with recovery. *)
      let base = [ Var (Var.base v, cstr) ] in
      if WordSet.bitwidth cstr = 1
         && WordSet.elem Cbat_word.b1 cstr
      then
        (match ctx with
         | Some { flag_state = Some (fv, op, e0, c0); _ }
           when Var.same fv v ->
           let c0 = Cbat_word.of_word c0 in
           (match denote_imm_exp e0 env with
            | Ok cur_e ->
              (match row_for ~env ?ctx e0 (guard_op_of_binop op) c0 with
               | Some cstr_e -> edge_constraints ~env ?ctx e0 cstr_e @ base
               | None -> base)
            | Error _ -> base)
         | _ -> base)
      else base
    | Type.Imm w when w >= 2 -> [ Var (Var.base v, cstr) ]
    | Type.Imm _ | Type.Mem _ | Type.Unk -> []
    end
  | Bil.Int c ->
    (* Disjoint constants kill the edge. *)
    if WordSet.elem (Cbat_word.of_word c) cstr then [] else [ Infeasible ]
  | Bil.BinOp (op, a, b) ->
    begin match op with
    | Bil.EQ | Bil.NEQ | Bil.LT | Bil.LE | Bil.SLT | Bil.SLE ->
      (* Const on either side: the row, flipped for const-first. *)
      let const_side (e : exp) (flip : bool) (side : [ `True | `False ])
          (op : Bil.binop) (c : word) : edge_constraint list =
        let c0 = Cbat_word.of_word c in
        let row o = if flip then flip_guard_op o else o in
        let cstr_opt =
          match side, op with
          | `True, Bil.NEQ -> neq_complement c0
          | `False, Bil.NEQ -> Some (WordSet.singleton c0)
          | `False, Bil.EQ -> neq_complement c0
          | `True, _ ->
            row_for ~env ?ctx e (row (guard_op_of_binop op)) c0
          | `False, _ ->
            row_for ~env ?ctx e (row (complement_binop_guard op)) c0 in
        (match cstr_opt with
         | Some cstr_e -> edge_constraints ~env ?ctx e cstr_e
         | None -> []) in
      let side (side : [ `True | `False ]) : edge_constraint list =
        match a, b with
        | _, Bil.Int c0 -> const_side a false side op c0
        | Bil.Int c0, e0 -> const_side e0 true side op c0
        | Bil.Var x, Bil.Var y ->
          (match Var.typ x, Var.typ y with
           | Type.Imm w, Type.Imm wy when w = wy ->
             let cur_x = AI.find_word w env x in
             let cur_y = AI.find_word w env y in
             if WordSet.bitwidth cur_x <> w
                || WordSet.bitwidth cur_y <> w
             then []
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
                                      edge_constraints ~env ?ctx (Bil.Var x) xc
                    @ edge_constraints ~env ?ctx (Bil.Var y) yc
                   
                | Some xc, None ->
                  edge_constraints ~env ?ctx (Bil.Var x) xc
                | None, Some yc ->
                  edge_constraints ~env ?ctx (Bil.Var y) yc
                | None, None -> [])
           | _ -> [])
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
                                  edge_constraints ~env ?ctx a xc
                  @ edge_constraints ~env ?ctx b yc
              | Some xc, None ->
                edge_constraints ~env ?ctx a xc
              | None, Some yc ->
                edge_constraints ~env ?ctx b yc
              | None, None -> [])
           | _ -> []) in
      let t = if WordSet.elem Cbat_word.b1 cstr then side `True else [] in
      let f = if WordSet.elem Cbat_word.b0 cstr then side `False else [] in
      if not (WordSet.elem Cbat_word.b1 cstr)
         && not (WordSet.elem Cbat_word.b0 cstr)
      then [ Infeasible ]
      else f @ t
    | Bil.AND ->
      
      if WordSet.bitwidth cstr = 1
         && WordSet.elem Cbat_word.b1 cstr
         && not (WordSet.elem Cbat_word.b0 cstr)
      then
        edge_constraints ~env ?ctx a cstr @ edge_constraints ~env ?ctx b cstr
      else
        (match denote_operand env a, denote_operand env b with
         | Some a_ws, Some b_ws ->
           (match operand_constraints op cstr a_ws b_ws with
            | a', b' ->
              let xs = match a' with
                | Some a_c -> edge_constraints ~env ?ctx a a_c
                | None -> [] in
              let ys = match b' with
                | Some b_c -> edge_constraints ~env ?ctx b b_c
                | None -> [] in
              xs @ ys)
         | _ -> [])
    | Bil.PLUS | Bil.MINUS | Bil.TIMES | Bil.DIVIDE | Bil.SDIVIDE
    | Bil.MOD | Bil.SMOD | Bil.LSHIFT | Bil.RSHIFT | Bil.ARSHIFT
    | Bil.OR | Bil.XOR ->
      (* Producer rows plus recursion. *)
      (match denote_operand env a, denote_operand env b with
       | Some a_ws, Some b_ws ->
         (match operand_constraints op cstr a_ws b_ws with
          | a', b' ->
            let xs = match a' with
              | Some a_c -> edge_constraints ~env ?ctx a a_c
              | None -> [] in
            let ys = match b' with
              | Some b_c -> edge_constraints ~env ?ctx b b_c
              | None -> [] in
            xs @ ys)
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
        let c0 = Cbat_word.of_word c0 in
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

let apply_operand_constraint
    ~(defs : (def term * bool) Var.Map.t option)
    (env : AI.t) (e : exp) (cstr : wordset)
    : AI.t =
  match defs with
  | None -> env
  | Some dm ->
    (match e with
     | Bil.Var x ->
       let env' = meet_var env x cstr in
       constrain_def_chain ~defs:dm env'
         (Bil.Var x) cstr
     | _ ->
       constrain_def_chain ~defs:dm env e cstr)

(* Refine by a taken-edge constraint. *)
(* Direct-API backward refinement. *)
let inverse_denote_exp ?(ctx : analysis_ctx option) (cond : exp)
    (cstr : wordset) (env : AI.t) : AI.t =
  match ctx with
  | None -> env
  | Some { has_sub = true; _ } -> env
  | Some ctx ->
    (* Gate-free (spec §2.1): every var refines. *)
    List.fold (edge_constraints ~env ~ctx cond cstr) ~init:env
      ~f:(fun env seed ->
        match seed with
        | Var (v, c) -> meet_var env v c
        | Cell (mem, addr, size, endian, cstr) ->
          constrain_cell env ~mem ~addr ~size ~endian cstr
        | Infeasible -> env)




(* Record an unsat var observation from a refined constraint. *)
let observe_refined (env : AI.t) (v : var) (cstr : wordset) : unit =
  match Var.typ v with
  | Type.Imm w ->
    let cur = AI.find_word w env v in
    if WordSet.bitwidth cur = w
    then Cbat_landmarks.observe_unsat_var v ~p:cur ~cstr:cstr
  | _ -> ()

let acquire_unsat_fallthrough ?(ctx : analysis_ctx option)
    ?(flag_group : Cbat_runctx.flag_group option = None)
    (cond : exp) (env : AI.t) : unit =
  match ctx with
  | None -> ()
  | Some ctx ->
    
    begin match ctx.flag_state with
    | Some (_fv, bop, e, c) ->
      let gate_ok =
        Option.value_map flag_group ~default:false
          ~f:(fun fg -> Cbat_runctx.same_comparison_group fg _fv e cond) in
      if gate_ok then begin
      let bop = bop and e = e and c = Cbat_word.of_word c in
      let gop = guard_op_of_binop bop in
      let op = complement_guard_op gop in
      (match row_for ~env ?ctx:(Some ctx) e op c with
       | Some cstr_e ->
         (match e with
          | Bil.Var v -> observe_refined env v cstr_e
          | _ ->
            List.iter (edge_constraints ~env ~ctx e cstr_e) ~f:(fun seed ->
              match seed with
              | Var (v, cstr_leaf) -> observe_refined env v cstr_leaf
              | Cell _ | Infeasible -> ()))
       | None -> ())
      end else ()
      | None -> ()
    end

(* Refine by a taken jump condition. *)
let assume_jump_cond_with_group
    ?(defs : (def term * bool) Var.Map.t option)
    ?(stores : def term list option)
    ?(flag_state : (var * Bil.binop * exp * word) option = None)
    ?(flag_group : Cbat_runctx.flag_group option = None)
    ?(sub : sub term option = None)
    (env : AI.t) (jmp : jmp term) : AI.t =
  let ctx : analysis_ctx =
    { defs; stores; flag_state; has_sub = Option.is_some sub } in
  let cond = Jmp.cond jmp in
  acquire_unsat_fallthrough ~ctx ~flag_group cond env;
  match decoded_condition cond with
  | Some op ->
    (* Decoder pre-step runs first. *)
    begin match flag_state with
    | Some (fv, _, e, c)
      when Option.value_map flag_group ~default:false
          ~f:(fun fg -> Cbat_runctx.same_comparison_group fg fv e cond) ->
      let cur_e = match denote_imm_exp e env with
        | Ok ws -> Some ws
        | Error _ -> None in
      (* Non-negativity proof for signed gates. *)
      let known_nonneg = known_nonneg_of ~defs ~stores ~env e in
      (match decoder_constraint ~cur:cur_e ~known_nonneg op (Cbat_word.of_word c) with
       | Some cstr ->
         apply_operand_constraint ~defs env e cstr
       | None -> env)
    | _ -> env
    end
  | None ->
    (* Taken edge forces {1}. *)
    inverse_denote_exp ~ctx cond (WordSet.singleton (Cbat_word.b1)) env

(* Group-aware wrapper. *)
let assume_jump_cond
    ?(defs : (def term * bool) Var.Map.t option)
    ?(flag_state : (var * Bil.binop * exp * word) option = None)
    (env : AI.t) (jmp : jmp term) : AI.t =
  assume_jump_cond_with_group ?defs ~flag_state
    env jmp
type walk_record = {
  wr_guard : Tid.t;
  wr_jmp : Tid.t;
  wr_seq : int;
  wr_nvar : int;
  wr_ncell : int;
  wr_reads : Tid.Set.t;
}

#ifdef VSA_DEBUG
let walk_records : walk_record list ref = ref []
let walk_seq : int ref = ref 0

let record_walk (bt : Tid.t) (jt : Tid.t)
    (seeds : edge_constraint list) (reads : Tid.Set.t) : unit =
  incr walk_seq;
  let nvar = ref 0 and ncell = ref 0 in
  List.iter seeds ~f:(function
    | Var _ -> incr nvar
    | Cell _ -> incr ncell
    | Infeasible -> ());
  walk_records :=
    {
      wr_guard = bt;
      wr_jmp = jt;
      wr_seq = !walk_seq;
      wr_nvar = !nvar;
      wr_ncell = !ncell;
      wr_reads = reads;
    }
    :: !walk_records

let walk_records_reset () =
  walk_records := [];
  walk_seq := 0

let walk_records_dump () = List.rev !walk_records
#else
let walk_records_reset () = ()
let walk_records_dump () : walk_record list = []
#endif


let refine_edge_inline
    ~(sol : (tid, AI.t) Solution.t)
    ~(defs : (def term * bool) Var.Map.t option)
    ~(stores : def term list option)
    ~(flag_state : (var * Bil.binop * exp * word) option)
    ~(flag_group : Cbat_runctx.flag_group option)
    ~(rctx : Cbat_runctx.refine_ctx)
    ~(jt : Tid.t)
    ~(discarded : bool)
    (b : blk term) (env : AI.t) (acc_cond : exp)
    : AI.t * Cbat_runctx.refine_ctx =
  
  (* Threaded context plus visited set. *)
  let ctx : analysis_ctx =
    { defs; stores; flag_state; has_sub = true } in
  let seeds = edge_constraints ~env ~ctx acc_cond (WordSet.singleton Cbat_word.b1) in
  
  (* Infeasible seeds stay identity, never bottom. *)
  let seeds =
    List.filter seeds ~f:(fun s -> match s with Infeasible -> false | _ -> true) in
  match seeds with
  | [] -> (env, rctx)
  | _ ->
    (* Gate-free (spec §2.1): every seed meets. *)
    let env =
      List.fold seeds ~init:env ~f:(fun e -> function
          | Var (v, c) -> meet_var e v c
          | Cell _ | Infeasible -> e) in
    
    (* Cached walk with threaded context. *)
    (* No-defs callers keep the uncached walk. *)
    let walk env seeds : AI.t * Cbat_runctx.refine_ctx =
      if discarded then (env, rctx)
      else
      match defs with
      | Some _ ->
        let rc = rctx in
        let bt = Term.tid b in
        (* Memo handles validity. *)
        let version = Cbat_runctx.ver_of rc in
        (match Cbat_runctx.Walk_memo.find ~version rc.rc_state.fs_cache bt jt with
         | Some refined -> (refined, rc)
         | None ->
           let walk_reads = ref (Tid.Set.singleton bt) in
           (* Per-SCC budget caps the walk; the floor keeps the walk
              launching (spec §2.4 — never skipped). *)
           let budget = max 0 !(rc.rc_walk_budget) in
           let cap =
             max 1 (min Cbat_runctx.cap_default budget) in
           let refined, _live =
             Stages.time `Walk (fun () ->
                 refine_edge ~sol ~rctx:rc ~defs
                   ~reads:(Some walk_reads) ~steps:(Some cap)
                   env b seeds) in
           (* A budget-limited walk is not memoized: the shortened
              read-set would trap a future reader (spec §2.4). *)
           let rc =
             if cap >= Cbat_runctx.cap_default then
               Cbat_runctx.with_cache rc
                 (Cbat_runctx.Walk_memo.add ~version rc.rc_state.fs_cache
                    bt jt ~reads:!walk_reads refined)
             else rc in
           (let res = (refined, rc) in
#ifdef VSA_DEBUG
            record_walk bt jt seeds !walk_reads;
#endif
            res))
      | None ->
        (* Uncached no-defs walk: spends from the same shared cell, so it is
           bounded by it too (symmetric with the cached arm). *)
        let budget = max 0 !(rctx.rc_walk_budget) in
        let cap = max 1 (min Cbat_runctx.cap_default budget) in
        let refined, _live =
          refine_edge ~sol ~rctx:rctx ~defs ~steps:(Some cap)
            env b seeds in
        (refined, rctx) in
    walk env seeds

(* Denotation of a block's jumps. *)
let denote_jump ?preserved ?defs ?stores
    ?(flag_state : (var * Bil.binop * exp * word) option = None)
    ?(flag_group : Cbat_runctx.flag_group option = None)
    ?(sub : sub term option = None)
    ?edge_conds ?sol
    ~(rctx : Cbat_runctx.refine_ctx)
    (b : blk term)  (env : AI.t) ~(target : tid)
    : AI.t * Cbat_runctx.refine_ctx =
  (* Fold joins per-jump results. *)
  let rc0 = rctx in
  let per_jump (acc, rctx) jmp =
    (* Refine by the jump cond. *)
    let env =
      assume_jump_cond_with_group ?defs ?stores ~flag_state
        ~flag_group ~sub env jmp in
    (* Deep walk uses the accumulated cond. *)
    let env, rctx =
      match edge_conds, sol, sub with
      | Some tbl, Some snap, Some _ ->
        let acc_cond =
          Core.Map.find tbl (Term.tid b)
          |> Option.bind ~f:(fun by_jmp ->
              Core.Map.find by_jmp (Term.tid jmp)) in
        (match acc_cond with
         | Some acc_cond ->
           (* Discard test mirrors bottom arms. *)
           let discarded =
             match Jmp.kind jmp with
             | Goto (Direct tid) | Ret (Direct tid) ->
               compare_tid target tid <> 0
             | Call c ->
               (match Call.return c with
                | Some (Direct tid) -> compare_tid target tid <> 0
                | Some (Indirect _) | None -> false)
             | Goto (Indirect _) | Ret (Indirect _) | Int _ -> false in
           (* Accumulator threads optional context. *)
           let env', rctx' =
             refine_edge_inline ~sol:snap ~defs ~stores ~flag_state
               ~flag_group
               ~rctx:rctx ~jt:(Term.tid jmp)
               ~discarded b env acc_cond in
           (env', rctx')
         | None -> (env, rctx))
      | _ -> (env, rctx) in
    
    let inspect_call c =
      match Call.return c with
        | None -> AI.bottom
        | Some (Direct tid) when compare_tid target tid <> 0 -> AI.bottom
        | Some (Indirect _)
        | Some (Direct _) ->
          (* Calls abstract; every caller's def is denoted. *)
          begin
            let rsp = Abi.x86_64_sysv.sp in
            (* Escape set plus caller frame boundary. *)
            (* Written registers are static. *)
            let escape =
              
              let written =
                match Core.Map.find rc0.rc_call_facts (Term.tid b) with
                | Some (w, _) -> w
                | None -> fst (Cbat_runctx.call_facts_of_block b) in
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
              | None -> snd (Cbat_runctx.call_facts_of_block b) in
            if pushed then begin
              let abs =
                AI.add_word abs ~key:rsp
                  ~data:(WordSet.add (AI.find_word 64 abs rsp)
                           (WordSet.singleton (Cbat_word.of_int ~width:64 8))) in
              (* Relation restores RSP by +8. *)
              AI.set_frame abs (AI.frame_add_rsp (AI.frame_of abs))
            end else abs
          end in
    (* Per-jump transfer results. *)
    let env_res, rctx =
      match Jmp.kind jmp with
      | Int _ ->
        (* Traps are external callees. *)
        (AI.call_abstraction
           ~preserved:(Option.value ~default:Var.Set.empty preserved) env,
         rctx)
      | Call c -> (inspect_call c, rctx)
      | Goto (Direct tid)
      | Ret (Direct tid) ->
        ((if compare_tid target tid = 0 then env else AI.bottom), rctx)
      | Goto (Indirect _)
      | Ret (Indirect _) -> (env, rctx) in
    (AI.join acc env_res, rctx) in
  Seq.fold (reachable_jumps env (Term.enum jmp_t b))
    ~init:(AI.bottom, rctx)
    ~f:per_jump

(* Block denotation toward a target. *)




(* Stores-aware block denotation. *)
let denote_block_with_stores ?preserved ?defs ?stores
    ?(sub : sub term option = None)
    ?(edge_conds : exp Tid.Map.t Tid.Map.t option = None)
    ?(sol : (tid, AI.t) Solution.t option = None)
    ~(rctx : Cbat_runctx.refine_ctx)
    (ctx : program term) ~(source : tid) (env : AI.t)
    : target:tid -> AI.t * Cbat_runctx.refine_ctx =
 match (Program.lookup blk_t ctx source) with
   | Some b ->
     let postcond = denote_defs b env in
     (* Last understood flag-setting comparison. *)
     
     let flag_state, flag_group =
       match Core.Map.find rctx.rc_flag_states (Term.tid b) with
       | Some fs -> fs
       | None -> Cbat_runctx.flag_state_of_block b in
     fun ~target ->
       denote_jump ?preserved ?defs ?stores ~flag_state
         ~flag_group:(Some flag_group) ~sub ?edge_conds ?sol
         ~rctx
         b postcond ~target
   | None -> fun ~target ->
       ignore (invalid_arg "source tid does not represent block");
       (AI.bottom, rctx)
