(* Backward refinement: guard rows, pre-images, the deep walk, the
   inline edge refinement. Consumes the transfer (open, bodies
   untouched); cbat_forward's jump denotation drives the walk at each
   conditional edge. Trace-partitioning lives here (ADR-0002). *)

include Core
open Bap.Std
open Graphlib.Std
open Cbat_vsa_utils
module AI = Cbat_ai_representation
module WordSet = Cbat_clp_set_composite
module Mem = Cbat_ai_memmap
module Word_ops = Cbat_word

module Stages = Cbat_vsa_stages
open Cbat_transfer

(* Guard-op vocabulary of the comparison rows (the BIR cond's binop,
   its const-first flip, and its false-edge complement). *)
type guard_op = ULT | ULE | UGT | UGE | EQ | NEQ | SLT | SLE | SGT | SGE

(* The producer non-negativity proof: an expression's every possible
   value has its sign bit clear.  Literals, positive-preserving
   arithmetic, and — through unique defs — anchored loads whose cell is
   seeded with a non-negative constant and only ever written with
   non-negative data (the load closes the induction). *)
let prove_nonneg ~(defs : (def term * bool) Var.Map.t)
    ~(stores : def term list)
    ~(env : AI.t) (e : exp) : bool =
  let nonneg_word (n : Cbat_word.t) : bool =
    let w = Cbat_word.bitwidth n in
    w > 0
    && Cbat_word.(<) n (Word_ops.half w) in
  (* Anchored (ADR 0008): the address var's word IS a stack-symbolic
     value, so the cell is private to this sub's frame. *)
  let stack_anchor (v : var) : bool =
    match Var.typ v with
    | Type.Imm w ->
      Option.is_some (WordSet.stack_offsets (AI.find_word w env v))
    | Type.Mem _ | Type.Unk -> false in
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
        end
      in
      result
    | Bil.BinOp (Bil.PLUS, a, b) ->
      walk cells vars a && walk cells vars b
    | Bil.BinOp (Bil.MINUS, a, b) ->
      (match b with
       | Bil.Int z when Cbat_word.is_zero (Cbat_word.of_word z) ->
         walk cells vars a
       | _ -> false)
    | Bil.BinOp (Bil.RSHIFT, _, Bil.Int k) ->
      (match Cbat_word.to_int (Cbat_word.of_word k) with
       | Ok n when n > 0 -> true
       | _ -> false)
    | Bil.BinOp (Bil.ARSHIFT, a, Bil.Int k) ->
      (match Cbat_word.to_int (Cbat_word.of_word k) with
       | Ok n when n >= 0 -> walk cells vars a
       | _ -> false)
    | Bil.BinOp (Bil.TIMES, a, Bil.Int k) ->
      Cbat_word.is_zero (Cbat_word.of_word k) || walk cells vars a
    | Bil.BinOp (Bil.DIVIDE, a, Bil.Int k) ->
      (match Cbat_word.to_int (Cbat_word.of_word k) with
       | Ok n when n >= 2 -> true
       | Ok 1 -> walk cells vars a
       | _ -> false)
    | Bil.BinOp (Bil.AND, _, Bil.Int k) ->
      let k = Cbat_word.of_word k in
      let w = Cbat_word.bitwidth k in
      Cbat_word.(<) k (Word_ops.half w)
    | Bil.BinOp (Bil.OR, a, Bil.Int k)
      when Cbat_word.is_zero (Cbat_word.of_word k) -> walk cells vars a
    | Bil.BinOp (Bil.XOR, a, Bil.Int k)
      when Cbat_word.is_zero (Cbat_word.of_word k) -> walk cells vars a
    | Bil.Cast (Bil.HIGH, _, a) -> walk cells vars a
    | Bil.Load (_, addr, _, _) ->
      let anchored =
        not (Core.Set.is_empty (Exp.free_vars addr))
        && Core.Set.for_all (Exp.free_vars addr) ~f:stack_anchor in
      let reentry = Core.Set.mem cells addr in
      if not anchored then false
      else if reentry then true
      else
        let cells' = Core.Set.add cells addr in
        let matches = List.filter stores ~f:(fun d ->
            match Def.rhs d with
            | Bil.Store (_, addr', _, _, _) -> Exp.equal addr addr'
            | _ -> false) in
        let has_seed = List.exists matches ~f:(fun d ->
            match Def.rhs d with
            | Bil.Store (_, _, Bil.Int n, _, _) ->
              nonneg_word (Cbat_word.of_word n)
            | _ -> false) in
        let all_values = List.for_all matches ~f:(fun d ->
            match Def.rhs d with
            | Bil.Store (_, _, u, _, _) -> walk cells' vars u
            | _ -> false) in
        has_seed && all_values
    | _ -> false
  in
  walk Exp.Set.empty Exp.Set.empty e

(* Shared step-1 CLP interval. *)
let interval_clp_of ~(width : int) ~(cardn : Cbat_word.t) (base : Cbat_word.t)
    : wordset option =
  if Cbat_word.is_zero cardn then None
  else
    let ws = WordSet.of_clp
        (Cbat_clp.create ~width ~step:(Cbat_word.one width) ~cardn base) in
    if WordSet.is_top ws then None else Some ws

(* Backward guard refinement. *)

(* CLP interval hull, or [None] on doubt (a width mismatch or a TOP
   collapse).  Without [~wrapping] a lo>hi pair is doubt — the
   non-wrapping contract; the backward PLUS/MINUS/SDIVIDE rows pin
   wrapped hulls (a wrapped pair is the circular interval) and pass
   [~wrapping:true]. *)
let hull ~(wrapping : bool) (width : int) (lo : Cbat_word.t) (hi : Cbat_word.t)
    : wordset option =
  if Cbat_word.bitwidth lo <> width || Cbat_word.bitwidth hi <> width then None
  else if (not wrapping) && Cbat_word.(>) lo hi then None
  else
    let ws = WordSet.of_clp (Cbat_clp.interval ~width lo hi) in
    if WordSet.is_top ws then None else Some ws

(* TOP minus a point: the exact two-piece NEQ complement. *)
let neq_complement (c : Cbat_word.t) : wordset option =
  let cstr =
    WordSet.diff (WordSet.top (Cbat_word.bitwidth c)) (WordSet.singleton c) in
  if Cbat_clp_set_composite.is_bottom cstr then None else Some cstr

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
         let a' = Option.map2 (WordSet.min_elem b_ws) (WordSet.max_elem b_ws)
             ~f:(fun bmin bmax ->
               hull ~wrapping:true width (Cbat_word.sub vlo bmax) (Cbat_word.sub vhi bmin)) |> Option.join in
         let b' = Option.map2 (WordSet.min_elem a_ws) (WordSet.max_elem a_ws)
             ~f:(fun amin amax ->
               hull ~wrapping:true width (Cbat_word.sub vlo amax) (Cbat_word.sub vhi amin)) |> Option.join in
         a', b'
       | _ -> None, None)
    | Bil.MINUS ->
      (* Minus: shift intervals by the other operand. *)
      (match WordSet.min_elem cstr, WordSet.max_elem cstr with
       | Some vlo, Some vhi ->
         let a' = Option.map2 (WordSet.min_elem b_ws) (WordSet.max_elem b_ws)
             ~f:(fun bmin bmax ->
               hull ~wrapping:true width (Cbat_word.add vlo bmin) (Cbat_word.add vhi bmax)) |> Option.join in
         let b' = Option.map2 (WordSet.min_elem a_ws) (WordSet.max_elem a_ws)
             ~f:(fun amin amax ->
               hull ~wrapping:true width (Cbat_word.sub amin vhi) (Cbat_word.sub amax vlo)) |> Option.join in
         a', b'
       | _ -> None, None)
    | Bil.TIMES ->
      (* Times by literal. *)
      (match WordSet.min_elem cstr, WordSet.max_elem cstr,
             WordSet.min_elem b_ws, WordSet.max_elem b_ws with
       | Some vlo, Some vhi, Some k, Some k' when Cbat_word.(=) k k' ->
         (match Cbat_word.to_int k with
          | Ok kk when kk > 0 && operand_bounded (wrap_limit k) ->
            (match hull ~wrapping:false width (ceil_div k vlo)
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
            (match hull ~wrapping:false width lo_a hi_a with
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
              (match hull ~wrapping:false width lo_a hi_a with
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
              (match hull ~wrapping:false width lo_a hi_a with
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
               (match hull ~wrapping:true width
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

(* The bit-window pre-image: the constraint hull [vlo, vhi] placed at
   bit position [k], width [d], of the operand (width [w]) — the window's
   bits are the constraint's, every other bit free.  The min is the
   low endpoint shifted up, the max the shifted succ's pred closed by
   the free-above term (none when the window reaches the word top).
   Endpoints lift to width [ew]; a hull off [w] or a TOP collapse is
   the identity. *)
let shift_fill_preimage ~(w : int) ~(ew : int) (k : int) (d : int)
    (vlo : Cbat_word.t) (vhi : Cbat_word.t) : wordset option =
  let sh = Cbat_word.of_int ~width:w k in
  let lo_a = Cbat_word.lshift (Cbat_word.extract_exn ~hi:(ew - 1) vlo) sh in
  let hi_a =
    Cbat_word.pred
      (Cbat_word.lshift
         (Cbat_word.extract_exn ~hi:(ew - 1) (Cbat_word.succ vhi)) sh) in
  let top =
    if k + d >= w then Cbat_word.zero ew
    else
      Cbat_word.sub (Cbat_word.ones w)
        (Cbat_word.lshift (Cbat_word.one w)
           (Cbat_word.of_int ~width:w (k + d))) in
  hull ~wrapping:false w lo_a (Cbat_word.add hi_a top)

(* HIGH-cast pre-image: the constraint is the word's top [n] bits. *)
let high_cast_constraint (env : AI.t) (a : exp) (sz : int)
    (cstr : wordset) : wordset option =
  match denote_imm_exp a env with
  | Ok a_ws ->
    let w = WordSet.bitwidth a_ws in
    let n = WordSet.bitwidth cstr in
    if w <= n then None
    else
      (match WordSet.min_elem cstr, WordSet.max_elem cstr with
       | Some vlo, Some vhi ->
         (* An open-top constraint (the succ wraps) has no closed hull. *)
         if Cbat_word.is_zero (Cbat_word.succ vhi) then None
         else shift_fill_preimage ~w ~ew:w (w - n) n vlo vhi
       | _ -> None)
  | Error _ -> None

(* Genuine-subset meet into a var; gate-free (spec §2.1). *)
(* BIL op to guard op. *)
let guard_op_of_binop (op : Bil.binop) : guard_op = match op with
  | Bil.LT -> ULT
  | Bil.LE -> ULE
  | Bil.EQ -> EQ
  | Bil.NEQ -> NEQ
  | Bil.SLT -> SLT
  | Bil.SLE -> SLE
  | _ -> EQ

(* Const-first flip. *)
let flip_guard_op (op : guard_op) : guard_op = match op with
  | ULT -> UGT | UGT -> ULT
  | ULE -> UGE | UGE -> ULE
  | SLT -> SGT | SGT -> SLT
  | SLE -> SGE | SGE -> SLE
  | EQ -> EQ | NEQ -> NEQ


(* The ONE guard-row family: the set a true guard [x op c] admits on
   [x], at two precision tiers.  [constraint_row] is the evidence tier
   — the single-CLP-interval row the operand's own value [cur] and the
   producer non-negativity proof [known_nonneg] admit; [None] is the
   identity.  [total_row] is the always-sound row; [guard_row] composes
   the tiers, falling from the evidence row to the total row. *)
let constraint_row ?(cur : wordset option = None)
    ?(known_nonneg : bool = false)
    (op : guard_op) (c : Cbat_word.t) : wordset option =
  let width = Cbat_word.bitwidth c in
  let half = Word_ops.half width in
  let cardn_of_int (i : int) : Cbat_word.t option =
    if i < 0 then None else Some (Cbat_word.of_int ~width:(width + 1) i) in
  let int_of_word (v : Cbat_word.t) : int option =
    try Some (Cbat_word.to_int_exn v) with _ -> None in
  let provably_nonneg =
    known_nonneg
    || Option.value_map cur ~default:false ~f:(fun ws ->
        match WordSet.max_elem ws with
        | None -> false
        | Some m -> Cbat_word.(<) m half) in
  match op with
  | ULT ->
    Option.bind (int_of_word c) ~f:(fun i ->
        Option.bind (cardn_of_int i) ~f:(fun cardn ->
            interval_clp_of ~width ~cardn (Cbat_word.zero width)))
  | ULE ->
    Option.bind (int_of_word c) ~f:(fun i ->
        Option.bind (cardn_of_int (i + 1)) ~f:(fun cardn ->
            interval_clp_of ~width ~cardn (Cbat_word.zero width)))
  | EQ -> Some (WordSet.singleton c)
  | SLT ->
    if Cbat_word.(>=) c half
    then interval_clp_of ~width ~cardn:(Cbat_word.sub c half) half
    else if provably_nonneg
    then interval_clp_of ~width ~cardn:c (Cbat_word.zero width)
    else None
  | SLE ->
    if Cbat_word.(>=) c half
    then interval_clp_of ~width ~cardn:(Cbat_word.succ (Cbat_word.sub c half)) half
    else if provably_nonneg
    then interval_clp_of ~width ~cardn:(Cbat_word.succ c) (Cbat_word.zero width)
    else None
  | NEQ | UGT | UGE | SGT | SGE -> None

let total_row (op : guard_op) (c : Cbat_word.t) : wordset option =
  let width = Cbat_word.bitwidth c in
  let maxw = Cbat_word.ones width in
  let half = Word_ops.half width in
  let iv lo hi = hull ~wrapping:false width lo hi in
  match op with
  | EQ -> Some (WordSet.singleton c)
  | NEQ -> neq_complement c
  | ULT ->
    (if Cbat_word.is_zero c then None
     else iv (Cbat_word.zero width) (Cbat_word.pred c))
  | ULE -> iv (Cbat_word.zero width) c
  | UGT ->
    (if Cbat_word.(=) c maxw then None
     else iv (Cbat_word.succ c) maxw)
  | UGE -> iv c maxw
  | SLT ->
    let pos =
      if Cbat_word.is_zero c then None
      else iv (Cbat_word.zero width) (Cbat_word.pred c) in
    (match iv half maxw with
     | Some neg ->
       Some (match pos with
         | Some p -> WordSet.union p neg
         | None -> neg)
     | None -> pos)
  | SLE ->
    (match iv half maxw with
     | Some neg ->
       (match iv (Cbat_word.zero width) c with
        | Some lo -> Some (WordSet.union lo neg)
        | None -> Some neg)
     | None -> iv (Cbat_word.zero width) c)
  | SGT ->
    (if Cbat_word.(=) c (Cbat_word.pred half) then None
     else iv (Cbat_word.succ c) (Cbat_word.pred half))
  | SGE -> iv c (Cbat_word.pred half)

let guard_row ?(cur : wordset option = None)
    ?(known_nonneg : bool = false)
    (op : guard_op) (c : Cbat_word.t) : wordset option =
  match op with
  | ULT | ULE | EQ | SLT | SLE ->
    (match constraint_row ~cur ~known_nonneg op c with
     | Some row -> Some row
     | None -> total_row op c)
  | NEQ | UGT | UGE | SGT | SGE -> total_row op c


(* The var-var meet: EQ keeps the intersection, NEQ subtracts it —
   more precise than any extremum row. *)
let overlap_eq (op : Bil.binop) (a_ws : wordset) (b_ws : wordset)
    : wordset option * wordset option =
  let ov = WordSet.meet a_ws b_ws in
  if Cbat_word.is_zero (WordSet.cardinality ov)
  then
    (match op with
     | Bil.NEQ -> Some a_ws, Some b_ws
     | _ -> None, None)
  else
    (match op with
     | Bil.NEQ -> Some (WordSet.diff a_ws ov), Some (WordSet.diff b_ws ov)
     | _ -> Some ov, Some ov)

(* Var-var comparison: the const rows at the other operand's extrema —
   [x op y] admits total_row(op) on [x] at y's upper extremum and
   total_row(flip op) on [y] at x's lower extremum; the signed [x]
   rows take the evidence tier (constraint_row) so the identity None
   survives an unproven operand.  EQ/NEQ take the meet. *)
let overlap_constraints (op : Bil.binop) (a_ws : wordset) (b_ws : wordset)
    : wordset option * wordset option =
  let w = WordSet.bitwidth a_ws in
  if WordSet.bitwidth b_ws <> w then None, None
  else
    let half = Word_ops.half w in
    let signed =
      match op with Bil.SLT | Bil.SLE -> true | _ -> false in
    let mn s = if signed then WordSet.min_elem_signed s else WordSet.min_elem s in
    let mx s = if signed then WordSet.max_elem_signed s else WordSet.max_elem s in
    match mn a_ws, mx b_ws, mn b_ws, mx a_ws with
    | Some mn_x, Some mx_y, Some _, Some _ ->
      let nonneg_x =
        match WordSet.max_elem a_ws with
        | Some m -> Cbat_word.(<) m half
        | None -> false in
      (match op with
       | Bil.LT -> total_row ULT mx_y, total_row UGT mn_x
       | Bil.LE -> total_row ULE mx_y, total_row UGE mn_x
       | Bil.SLT ->
         constraint_row ~known_nonneg:nonneg_x SLT mx_y, total_row SGT mn_x
       | Bil.SLE ->
         constraint_row ~known_nonneg:nonneg_x SLE mx_y, total_row SGE mn_x
       | Bil.EQ | Bil.NEQ -> overlap_eq op a_ws b_ws
       | _ -> None, None)
    | _ -> None, None

(* The [Ok] payload, or [None]. *)
let or_opt : ('a, _) result -> 'a option = function
  | Ok v -> Some v
  | Error _ -> None

(* Constraint row on an operand.  The signed rows read the producer
   non-negativity proof; the family falls from the evidence tier to the
   total tier on its own. *)
let row_for ~(env : AI.t) ?(nonneg : exp -> bool = fun _ -> false)
    (e : exp) (op : guard_op) (c : Cbat_word.t)
    : wordset option =
  let cur = or_opt (denote_imm_exp e env) in
  match op with
  | SLT | SLE -> guard_row ~cur ~known_nonneg:(nonneg e) op c
  | ULT | ULE | EQ -> guard_row ~cur op c
  | NEQ | UGT | UGE | SGT | SGE -> guard_row op c

(* Leaf seeds of a guard. *)
let ext_cast_constraint ~(is_signed : bool) (env : AI.t) (a : exp)
    (cstr : wordset) : wordset option =
  match denote_imm_exp a env with
  | Ok a_ws ->
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
            hull ~wrapping:false n
              (Cbat_word.extract_exn ~hi:(n - 1) lo')
              (Cbat_word.extract_exn ~hi:(n - 1) hi'))
       | _ -> None)
  | Error _ -> None

(* Truncation pre-image. *)
let low_cast_constraint (env : AI.t) (a : exp) (cstr : wordset)
    : wordset option =
  match denote_imm_exp a env with
  | Ok a_ws ->
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
         hull ~wrapping:false w vlo_w hi_a
       | _ -> None)
  | Error _ -> None

(* Extract pre-image: the constraint is bits [lo, hi] of the operand;
   the window sits mid-word, so the endpoints compute at the constraint
   width and the hull gate stays at the operand width. *)
let extract_constraint (env : AI.t) (a : exp) (hi : int) (lo : int)
    (cstr : wordset) : wordset option =
  match denote_imm_exp a env with
  | Ok a_ws ->
    let w = WordSet.bitwidth a_ws in
    let n = WordSet.bitwidth cstr in
    if n <> hi - lo + 1 then None
    else
      (match WordSet.min_elem cstr, WordSet.max_elem cstr with
       | Some vlo, Some vhi -> shift_fill_preimage ~w ~ew:n lo n vlo vhi
       | _ -> None)
  | Error _ -> None



(* THE inverse denote: the per-node mirror of the forward transfer
   (cbat_transfer's [denote_exp]).  ONE backward rule per node kind, at
   this one site, phrased as that node's inverse: where the forward
   rule is [WordSet.add], the inverse is the subtraction pre-image;
   where it is a cast, the extent widening; a leaf var's inverse is the
   meet; a load's the cell meet into the env's memory; a comparison's
   the polarity windows of its ordering/equality decision.  A node
   whose forward rule has no closed-form inverse (MOD/SMOD) takes
   identity — no extra knowledge.  A genuinely empty pre-image is the
   empty state (the dead edge), sanctioned.  Both directions of the
   analysis read this one function: the edge step at the graph's
   completed cond constrained TRUE, and the walk's per-def step at each
   def's rhs under the producer subtraction. *)
(* A cell fact awaiting positional delivery to the same-block store
   that wrote it: the memory var, the key the load read, and the
   constraint its value must satisfy. *)
type pending_cell = var * Mem.Key.t * wordset * endian

(* The leaf var's inverse: the meet; an empty meet is observed (the
   widening landmark) and takes identity. *)
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
#ifdef VSA_DEBUG
        Format.eprintf "DBG OBSERVE-UNSAT var=%s cur=%a cstr=%a\n%!"
          (Var.name v) WordSet.pp cur WordSet.pp refined;
#endif
        Cbat_landmarks.observe_unsat_var v ~p:cur ~cstr:refined;
        env
      end else if not (WordSet.precedes m cur)
      then env
      else begin
#ifdef VSA_DEBUG
        (match WordSet.stack_offsets cur, WordSet.stack_offsets m with
         | Some _, None ->
           Format.eprintf "DBG SYMBOL-STRIP var=%s cur=%a refined=%a meet=%a\n%!"
             (Var.name v) WordSet.pp cur WordSet.pp refined WordSet.pp m
         | _ -> ());
#endif
        AI.add_word env ~key:v ~data:m
      end
  | Type.Mem _ | Type.Unk -> env

let rec inverse_denote ~(env : AI.t)
    ?(cells : pending_cell list ref = ref [])
    ?(nonneg : exp -> bool = fun _ -> false)
    (e : exp) (produced : wordset) : AI.t =
  match e with
  | Bil.Var v ->
    (* The leaf's inverse is the meet; an empty meet is observed (the
       widening landmark) and takes identity — the over-approximated
       state may simply not cover the excluded value yet. *)
    meet_var env v produced
  | Bil.Int c ->
    (* The forward rule always produces the same constant: a disjoint
       produced value is the genuinely empty pre-image. *)
    let cw = Cbat_word.bitwidth (Cbat_word.of_word c) in
    if WordSet.bitwidth produced = cw
       && not (WordSet.elem (Cbat_word.of_word c) produced)
    then begin
#ifdef VSA_DEBUG
      Format.eprintf "DBG INT-BOTTOM: const=%s produced=%a\n%!"
        (Cbat_word.to_string (Cbat_word.of_word c)) WordSet.pp produced;
#endif
      AI.bottom
    end
    else env
  | Bil.UnOp (Bil.NOT, a) ->
    inverse_denote ~env ~cells ~nonneg a (WordSet.lnot produced)
  | Bil.UnOp (Bil.NEG, a) ->
    inverse_denote ~env ~cells ~nonneg a (WordSet.neg produced)
  | Bil.Cast (Bil.HIGH, sz, a) ->
    (* The extent widening. *)
    Option.value_map (high_cast_constraint env a sz produced) ~default:env
      ~f:(fun a' -> inverse_denote ~env ~cells ~nonneg a a')
  | Bil.Cast (ct, _, a) ->
    (match ct with
     | Bil.SIGNED | Bil.UNSIGNED ->
       Option.value_map
         (ext_cast_constraint
            ~is_signed:(match ct with Bil.SIGNED -> true | _ -> false)
            env a produced) ~default:env
         ~f:(fun a' -> inverse_denote ~env ~cells ~nonneg a a')
     | _ ->
       Option.value_map (low_cast_constraint env a produced) ~default:env
         ~f:(fun a' -> inverse_denote ~env ~cells ~nonneg a a'))
  | Bil.Extract (hi, lo, a) ->
    Option.value_map (extract_constraint env a hi lo produced) ~default:env
      ~f:(fun a' -> inverse_denote ~env ~cells ~nonneg a a')
  | Bil.Concat (a, b) ->
    (* The forward concatenates; the inverse splits the window on the
       width boundary. *)
    (match denote_imm_exp b env with
     | Ok b_ws ->
       let bw = WordSet.bitwidth b_ws in
       let cw = WordSet.bitwidth produced in
       if bw >= cw then inverse_denote ~env ~cells ~nonneg a produced
       else
         let env = inverse_denote ~env ~cells ~nonneg a
             (WordSet.extract ~hi:(cw - 1) ~lo:bw produced) in
         inverse_denote ~env ~cells ~nonneg b
           (WordSet.extract ~hi:(bw - 1) ~lo:0 produced)
     | Error _ -> env)
  | Bil.Ite (_, t, f) ->
    (* The forward joins the branches; the inverse constrains both. *)
    let env = inverse_denote ~env ~cells ~nonneg t produced in
    inverse_denote ~env ~cells ~nonneg f produced
  | Bil.Let (_, _, body) -> inverse_denote ~env ~cells ~nonneg body produced
  | Bil.Load (m, a, en, s) ->
    (* The load's inverse: the cell fact meets the env's memory, and
       threads positionally to the same-block store that wrote it. *)
    let env = meet_cell ~env ~mem:m ~addr:a ~size:s ~endian:en produced in
    (match m with
     | Bil.Var mv ->
       Option.iter
         (Option.bind (or_opt (denote_imm_exp a env)) ~f:Mem.Key.of_wordset)
         ~f:(fun k -> cells := (mv, k, produced, en) :: !cells)
     | _ -> ());
    env
  | Bil.Store (m, a, u, _en, s) ->
    (* The store's inverse: the last writer carries the pending cell's
       constraint into its data (met against the store's own written
       value — the producer subtraction).  No pending cell for this
       key: the identity. *)
    (match m with
     | Bil.Var mv ->
       (match !cells with
        | [] -> env
        | pending ->
          let resSize = Size.in_bits s in
          let ks = Option.bind (or_opt (denote_imm_exp a env)) ~f:Mem.Key.of_wordset in
          (match ks with
           | None -> env
           | Some ks ->
             let rec take pending = match pending with
               | [] -> None
               | ((mv', kc, c, _en) as cell) :: rest ->
                 if Var.same mv' mv
                    && WordSet.bitwidth c = resSize
                    && Mem.Key.overlap ks kc
                 then Some (cell, rest)
                 else
                   match take rest with
                   | Some (cell', rest') -> Some (cell', cell :: rest')
                   | None -> None in
             (match take pending with
              | None -> env
              | Some ((_, _, cstr_cell, _), rest) ->
                cells := rest;
                let data_cstr =
                  Option.value_map (or_opt (denote_imm_exp u env))
                    ~default:cstr_cell ~f:(WordSet.meet cstr_cell) in
                if Cbat_word.is_zero (WordSet.cardinality data_cstr) then env
                else inverse_denote ~env ~cells ~nonneg u data_cstr)))
     | _ -> env)
  | Bil.BinOp (Bil.AND, a, b) when WordSet.bitwidth produced = 1 ->
    (* The forward AND of two booleans is true only when both are: the
       inverse composes both operands' rules with the produced bit. *)
    if WordSet.elem Cbat_word.b1 produced
       && not (WordSet.elem Cbat_word.b0 produced)
    then
      let env = inverse_denote ~env ~cells ~nonneg a produced in
      inverse_denote ~env ~cells ~nonneg b produced
    else if WordSet.elem Cbat_word.b0 produced
            && not (WordSet.elem Cbat_word.b1 produced)
    then
      (* AND = false: at least one operand false — the disjunction of
         the negated sides takes identity (no window without knowing
         which). *)
      env
    else env
  | Bil.BinOp (op, a, b) ->
    (match op with
     | Bil.EQ | Bil.NEQ | Bil.LT | Bil.LE | Bil.SLT | Bil.SLE
       when WordSet.bitwidth produced = 1 ->
       (* The comparison's inverse: the produced bit's polarity windows
          over the operands — the {1} slice through the comparison's
          true side, the {0} slice through the completed negation. *)
       let has1 = WordSet.elem Cbat_word.b1 produced in
       let has0 = WordSet.elem Cbat_word.b0 produced in
       if has1 && not has0 then cmp_inverse ~env ~cells ~nonneg op a b
       else if has0 && not has1 then
         (match complete_cond (Bil.UnOp (Bil.NOT, e)) with
          | Bil.BinOp (op', x, y) -> cmp_inverse ~env ~cells ~nonneg op' x y
          | _ -> env)
       else if has1 || has0 then env
       else AI.bottom
     | Bil.MOD | Bil.SMOD ->
       (* No closed-form inverse: identity, no extra knowledge. *)
       env
     | _ ->
       (* The subtraction pre-image: the operands' windows whose forward
          images land in the produced value.  A literal receives nothing
          (its window is a hull over-approximation with no env slot);
          a Let's binding is not part of the walked state. *)
       let deliver (e : exp) (c : wordset option) (env : AI.t) : AI.t =
         match e, c with
         | Bil.Int _, _ | Bil.Let _, _ -> env
         | _, Some c' -> inverse_denote ~env ~cells ~nonneg e c'
         | _ -> env in
       (match denote_imm_exp a env, denote_imm_exp b env with
        | Ok a_ws, Ok b_ws ->
          (match operand_constraints op produced a_ws b_ws with
           | a', b' ->
             let env = deliver a a' env in
             deliver b b' env)
        | _ -> env))
  | Bil.Unknown _ -> env

(* The comparison's true-side EXISTS projection: the produced {1}
   windows the operands by the ordering/equality decision. *)
and cmp_inverse ~(env : AI.t) ~(cells : pending_cell list ref)
    ~(nonneg : exp -> bool)
    (op : Bil.binop) (a : exp) (b : exp) : AI.t =
  let const_side (x : exp) (flip : bool) (op : Bil.binop) (c : word) : AI.t =
    let c0 = Cbat_word.of_word c in
    let row o = if flip then flip_guard_op o else o in
    let cstr_opt = match op with
      | Bil.NEQ -> neq_complement c0
      | _ -> row_for ~env ~nonneg x (row (guard_op_of_binop op)) c0 in
    match cstr_opt with
    | Some cstr -> inverse_denote ~env ~cells ~nonneg x cstr
    | None -> env in
  match a, b with
  | _, Bil.Int c0 -> const_side a false op c0
  | Bil.Int c0, e0 -> const_side e0 true op c0
  | _ ->
    (match denote_imm_exp a env, denote_imm_exp b env with
     | Ok a_ws, Ok b_ws ->
       let x_cstr, y_cstr = overlap_constraints op a_ws b_ws in
       let env = match x_cstr with
         | Some xc -> inverse_denote ~env ~cells ~nonneg a xc
         | None -> env in
       (match y_cstr with
        | Some yc -> inverse_denote ~env ~cells ~nonneg b yc
        | None -> env)
     | _ -> env)

(* The load's cell fact meets the env's memory at the address the env
   denotes: stack-symbolic addresses key by their segment offsets,
   foreign ones by their concrete hulls; identity on doubt. *)
and meet_cell ~(env : AI.t) ~(mem : exp) ~(addr : exp) ~(size : Size.t)
    ~(endian : endian) (produced : wordset) : AI.t =
  match mem with
  | Bil.Var m ->
    (match Var.typ m with
     | Type.Mem (addr_i, addressable_size) ->
       let k = mem_idx addr_i addressable_size in
       (match denote_imm_exp addr env with
        | Error _ ->
#ifdef VSA_DEBUG
          Format.eprintf "DBG MEET-CELL: addr denote ERROR\n%!";
#endif
          env
        | Ok addr_ws ->
          (match Mem.Key.of_wordset addr_ws with
           | None ->
#ifdef VSA_DEBUG
             Format.eprintf "DBG MEET-CELL: no key from %a\n%!"
               WordSet.pp addr_ws;
#endif
             env
           | Some key ->
             let resSize = Size.in_bits size in
             if WordSet.bitwidth produced <> resSize then env
             else
               let mv = AI.find_memory k env m in
               let data = Mem.Val.create produced endian in
#ifdef VSA_DEBUG
               Format.eprintf "DBG MEET-CELL: meet %a into key %s\n%!"
                 WordSet.pp produced
                 (Sexp.to_string (Mem.Key.sexp_of_t key));
#endif
               AI.add_memory env ~key:m
                 ~data:(Mem.meet_range mv ~key ~data)))
     | Type.Imm _ | Type.Unk -> env)
  | _ -> env

(* THE edge step: the graph's completed cond constrained TRUE — the {1}
   lives here and nowhere else (negation sits at the producer's
   completion).  No defs, no stores, no ctx: the cond's own expression
   is the whole fact. *)
let constrain_edge ~(env : AI.t) (cond : exp) : AI.t =
  inverse_denote ~env cond (WordSet.singleton Cbat_word.b1)

(* The walk's word-constraint carrier: a pure var→constraint map.
   Constraints are consumed (killed) at each def of their var, so a
   redefinition never carries a downstream constraint to the earlier
   def that produced the overwritten value. *)
type live_map = wordset Var.Map.t

(* The ONE walk entry: the seeds pushed through the block's defs one by
   one backwards.  Each def's incoming constraint is its var's live
   entry met with the def's own produced value (the producer
   subtraction; the prefix states make it same-iteration exact); the
   node's inverse rule derives the operands' constraints into [live]
   and the memory meets into the walked state.  Reads (operands,
   addresses) take the def's PREFIX state overlaid with [live] — the
   positional, same-iteration values.  Returns the walked edge state.
   [~raw] inverts each def with the constraint AS GIVEN, skipping the
   producer subtraction: the acquisition's hypothetical (the paper's
   observe_unsat asks what the disabled edge would require, even when
   the current state cannot produce it).  Raw walks write nothing —
   only the empty-meet observations fire. *)
let walk_block ?(raw : bool = false)
    ~(sol : (tid, AI.t) Solution.t)
    ~(witness : env:AI.t -> exp -> bool)
    ~(seeds : live_map)
    (env : AI.t) (blk : blk term) : AI.t =
  let env_out = ref env in
  let blk_state = Solution.get sol (Term.tid blk) in
  (* Prefix states, ONE forward fold: each def paired with the state
     before it and the state after it, positionally — same-iteration
     earlier defs included.  The list is the reverse def order. *)
  let prefixed =
    Term.enum def_t blk
    |> Seq.fold ~init:(blk_state, [])
      ~f:(fun (st, acc) d ->
          let post = denote_def d st in
          (post, (d, st, post) :: acc))
    |> snd in
  (* The block's mentioned vars: word vars are the delivery/kill
     domain; mem vars are where memory meets accumulate. *)
  let mem_vars_of (e : exp) (acc : var list) =
    Core.Set.fold (Exp.free_vars e) ~init:acc ~f:(fun acc v ->
        match Var.typ v with
        | Type.Mem _ -> if List.mem acc v ~equal:Var.equal then acc else v :: acc
        | _ -> acc) in
  let mem_vars, _word_mentions =
    List.fold prefixed ~init:([], Var.Set.empty)
      ~f:(fun (ms, ws) (d, _, _) ->
          let ms = mem_vars_of (Def.rhs d) ms in
          (match Var.typ (Def.lhs d) with
           | Type.Mem _ ->
             if List.mem ms (Def.lhs d) ~equal:Var.equal then ms
             else Def.lhs d :: ms
           | _ -> ms),
          Core.Set.union ws (Exp.free_vars (Def.rhs d))) in
  let mem_idx_of m =
    match Var.typ m with
    | Type.Mem (ai, asz) -> Some (mem_idx ai asz, m)
    | _ -> None in
  let cells = ref [] in
  let live = ref seeds in
  (* The vars whose last def has been processed: its confined value
     bounds the var's edge value (the target reads the final value). *)
  let confined = ref Var.Set.empty in
  (* The positional call env: the prefix state's words, the live
     constraints met in, and the accumulating edge memory. *)
  let call_env (pre : AI.t) : AI.t =
    let e = List.fold mem_vars ~init:pre ~f:(fun e m ->
        Option.value_map (mem_idx_of m) ~default:e ~f:(fun (k, m) ->
            AI.add_memory e ~key:m ~data:(AI.find_memory k !env_out m))) in
    Core.Map.fold !live ~init:e ~f:(fun ~key:v ~data:c acc ->
        match Var.typ v with
        | Type.Imm w when WordSet.bitwidth c = w ->
          AI.add_word acc ~key:v
            ~data:(WordSet.meet (AI.find_word w pre v) c)
        | _ -> acc) in
  (* The rule's deliveries: the rhs's free vars whose value the
     inversion narrowed.  A delivered constraint lives until its var's
     own (earlier) def consumes it. *)
  let harvest ~(base : AI.t) (env' : AI.t) (rhs : exp) =
    Core.Set.fold (Exp.free_vars rhs) ~init:() ~f:(fun () v ->
        match Var.typ v with
        | Type.Imm w ->
          let before = AI.find_word w base v in
          let after = AI.find_word w env' v in
          if (not (WordSet.is_bottom after)) && WordSet.precedes after before
          then live := Core.Map.set !live ~key:(Var.base v) ~data:after
        | _ -> ()) in
  let commit_memory (env' : AI.t) =
    List.iter mem_vars ~f:(fun m ->
        Option.iter (mem_idx_of m) ~f:(fun (k, m) ->
            env_out := AI.add_memory !env_out ~key:m
                ~data:(AI.find_memory k env' m))) in
  List.iter prefixed ~f:(fun (d, pre, post) ->
      let v = Def.lhs d in
      match Var.typ v with
      | Type.Imm w ->
        let cstr = Core.Map.find !live (Var.base v) in
        (* The def consumes its var's constraint, whatever it says. *)
        live := Core.Map.remove !live (Var.base v);
        (match cstr with
         | None -> ()
         | Some cstr ->
           let post_v = AI.find_word w post v in
           let cstr' =
             if raw then cstr else WordSet.meet cstr post_v in
           if (not raw)
              && Cbat_word.is_zero (WordSet.cardinality cstr') then
             (* The def's produced value cannot satisfy the constraint
                (a redefinition overwrote the var): the constraint does
                not hold before this def — dropped. *)
             ()
           else begin
             (* The first processing of a var is its LAST def: the
                confined value bounds the edge value the target reads. *)
             if not raw
                && not (Core.Set.mem !confined (Var.base v)) then begin
               confined := Core.Set.add !confined (Var.base v);
               let cur = AI.find_word w !env_out v in
               let m = WordSet.meet cur cstr' in
               if (not (Cbat_word.is_zero (WordSet.cardinality m)))
                  && WordSet.precedes m cur
               then env_out := AI.add_word !env_out ~key:v ~data:m
             end;
             if raw || WordSet.precedes cstr' post_v then begin
               let ce = call_env pre in
               let env' =
                 inverse_denote ~env:ce ~cells
                   ~nonneg:(fun e -> witness ~env:ce e)
                   (Def.rhs d) cstr' in
               if not raw then begin
                 commit_memory env';
                 harvest ~base:ce env' (Def.rhs d)
               end
             end
           end)
      | Type.Mem _ ->
        (* The store's inverse is driven by the pending cells the
           loads pushed. *)
        if not raw then
          (match !cells with
           | [] -> ()
           | _ ->
             let ce = call_env pre in
             let env' =
               inverse_denote ~env:ce ~cells
                 ~nonneg:(fun e -> witness ~env:ce e)
                 (Def.rhs d) (WordSet.bottom 8) in
             commit_memory env';
             harvest ~base:ce env' (Def.rhs d))
      | Type.Unk -> ());
  (* Constraints on vars the block never defines flow to the edge env
     (their value crosses the block unchanged). *)
  Core.Map.fold !live ~init:() ~f:(fun ~key:v ~data:c () ->
      if raw then () else
      match Var.typ v with
      | Type.Imm w when WordSet.bitwidth c = w ->
        let cur = AI.find_word w !env_out v in
        let m = WordSet.meet cur c in
        if (not (Cbat_word.is_zero (WordSet.cardinality m)))
           && WordSet.precedes m cur
        then env_out := AI.add_word !env_out ~key:v ~data:m
      | _ -> ());
  !env_out

(* The walk's seeds: the cond's OWN narrowings — the strict per-var diff
   of the constrained env against the pre-constrain state, over the
   cond's free vars.  A var whose value the cond did not strictly narrow
   carries no constraint; seeding the block's own denoted values would
   re-derive the whole exit state as if every edge required it (the
   state snapshot that dilutes loop cells with edge-independent rows). *)
let cond_seeds ~(base : AI.t) (env : AI.t) (cond : exp) : live_map =
  Core.Set.fold (Exp.free_vars cond) ~init:Var.Map.empty ~f:(fun acc v ->
      match Var.typ v with
      | Type.Imm w ->
        let before = AI.find_word w base v in
        let after = AI.find_word w env v in
        if (not (WordSet.is_bottom after))
           && WordSet.precedes after before
           && not (WordSet.equal after before)
        then Core.Map.set acc ~key:(Var.base v) ~data:after
        else acc
      | _ -> acc)

(* The deep walk: the guard block's defs, one by one backwards.  The
   derived constraints land on the block's live vars and memory; the
   leftover constraints and cell meets flow into the returned edge
   env.  The seeds are the cond's own narrowings ([cond_seeds] at the
   edge step; the unit seams pass the constraint they pre-applied).
   Every walk runs to its fixpoint over the block — there is no step
   cap. *)
let refine_edge ~(sol : (tid, AI.t) Solution.t)
    ~(rctx : Cbat_runctx.refine_ctx)
    ?(reads : Tid.Set.t ref option = None)
    ~(seeds : live_map)
    (env : AI.t) (blk : blk term) : AI.t =
  Option.iter reads ~f:(fun r -> r := Core.Set.add !r (Term.tid blk));
  let refined = walk_block ~sol ~witness:rctx.rc_nonneg ~seeds env blk in
  (* Commit walk metrics (debug-only; the production adapter drops them). *)
  Stages.bump_walk_pops
    ~pops:1
#ifdef VSA_DEBUG
    ~blocks:1
#else
    ~blocks:0
#endif
    ~truncated:false
    ();
  refined

(* The disabled continuation observed through the same rules, the
   result DISCARDED: [meet_var] records an observation at every empty
   meet — the excluded boundary + distance become the enclosing WTO
   cycle's widening landmark.  The observation runs the full walk so
   the cond's constraint reaches the producers (the counter behind the
   flag).  The continuation is observed at the REACHABLE jmp (a
   disabled edge's own iteration is pruned by the reachability
   filter).  Memory cells carry no landmarks (words lane only). *)
let acquire_unsat ~(sol : (tid, AI.t) Solution.t) ~(witness : env:AI.t -> exp -> bool)
    (env : AI.t) (blk : blk term) (disabled : exp) : unit =
  (* The leaf meets observe; the raw walk pushes the disabled cond's
     own constraints through the producers so the empty meets land on
     the counters (the words-lane landmarks). *)
  let constrained = constrain_edge ~env disabled in
  if not (AI.equal constrained AI.bottom) then begin
    let seeds = cond_seeds ~base:env constrained disabled in
    (* An empty leaf meet leaves the env unchanged: the constraint
       still exists — re-derive it as the raw seed of its var. *)
    let raw_seeds =
      if AI.equal constrained env then
        Core.Set.fold (Exp.free_vars disabled) ~init:seeds ~f:(fun acc v ->
            match Var.typ v with
            | Type.Imm 1 ->
              Core.Map.set acc ~key:(Var.base v)
                ~data:(WordSet.singleton Cbat_word.b1)
            | _ -> acc)
      else seeds in
    (* The raw walk's state is discarded; only its empty-meet
       observations persist. *)
    ignore (walk_block ~raw:true ~sol ~witness ~seeds:raw_seeds constrained blk)
  end

let refine_edge_inline
    ~(sol : (tid, AI.t) Solution.t)
    ~(rctx : Cbat_runctx.refine_ctx)
    ~(jt : Tid.t)
    ~(discarded : bool)
    (b : blk term) (env : AI.t) (acc_cond : exp)
    : AI.t * Cbat_runctx.refine_ctx =
  (* The edge's cond constrains the state; the walk delivers the
     constraint to the producers positionally. *)
  let env_in = env in
  let env = constrain_edge ~env acc_cond in
  (* No constraint derived: nothing to deliver to the producers (the
     unconditional conds). *)
  if discarded || AI.equal env env_in || AI.equal env AI.bottom then (env, rctx)
  else
    let bt = Term.tid b in
    (* Memo handles validity. *)
    let version = Cbat_runctx.ver_of rctx in
    (match Cbat_runctx.Walk_memo.find ~version rctx.rc_state.fs_cache bt jt with
     | Some refined -> (refined, rctx)
     | None ->
       let walk_reads = ref (Tid.Set.singleton bt) in
       let seeds = cond_seeds ~base:env_in env acc_cond in
       let refined =
         Stages.time `Walk (fun () ->
             refine_edge ~sol ~rctx
               ~reads:(Some walk_reads)
               ~seeds env b) in
       let rctx =
         Cbat_runctx.with_cache rctx
           (Cbat_runctx.Walk_memo.add ~version rctx.rc_state.fs_cache
              bt jt ~reads:!walk_reads refined) in
       (refined, rctx))
