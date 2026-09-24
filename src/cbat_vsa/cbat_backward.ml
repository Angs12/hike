(* Backward refinement: guard rows, pre-images, the deep walk, the
   inline edge refinement. *)

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

type guard_op = ULT | ULE | UGT | UGE | EQ | NEQ | SLT | SLE | SGT | SGE

(* Proves an expression's every possible value has its sign bit clear:
   literals, positive-preserving arithmetic, and — through unique defs —
   anchored loads seeded and written only with non-negative data. *)
let prove_nonneg ~(defs : (def term * bool) Var.Map.t)
    ~(stores : def term list)
    ~(env : AI.t) (e : exp) : bool =
  let nonneg_word (n : Cbat_word.t) : bool =
    let w = Cbat_word.bitwidth n in
    w > 0
    && Cbat_word.(<) n (Word_ops.half w) in
  (* Anchored: the address var's word is a stack-symbolic value, so the
     cell is private to this sub's frame. *)
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

let interval_clp_of ~(width : int) ~(cardn : Cbat_word.t) (base : Cbat_word.t)
    : wordset option =
  if Cbat_word.is_zero cardn then None
  else
    let ws = WordSet.of_clp
        (Cbat_clp.create ~width ~step:(Cbat_word.one width) ~cardn base) in
    if WordSet.is_top ws then None else Some ws

(* CLP interval hull; [None] on doubt — width mismatch, TOP collapse,
   or a lo>hi pair without [~wrapping] (the wrapped pair is the
   circular interval). *)
let hull ~(wrapping : bool) (width : int) (lo : Cbat_word.t) (hi : Cbat_word.t)
    : wordset option =
  if Cbat_word.bitwidth lo <> width || Cbat_word.bitwidth hi <> width then None
  else if (not wrapping) && Cbat_word.(>) lo hi then None
  else
    let ws = WordSet.of_clp (Cbat_clp.interval ~width lo hi) in
    if WordSet.is_top ws then None else Some ws

let neq_complement (c : Cbat_word.t) : wordset option =
#ifdef VSA_DEBUG
  Cbat_attr_census.bump "band.neq_complement";
#endif
  let cstr =
    WordSet.diff (WordSet.top (Cbat_word.bitwidth c)) (WordSet.singleton c) in
  if Cbat_clp_set_composite.is_bottom cstr then None else Some cstr

let operand_constraints (op : Bil.binop) (cstr : wordset)
    (a_ws : wordset) (b_ws : wordset) : wordset option * wordset option =
  let width = WordSet.bitwidth cstr in
  if WordSet.bitwidth a_ws <> width || WordSet.bitwidth b_ws <> width
  then None, None
  else
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
    | _ -> None, None

(* Bit-window pre-image: the constraint hull placed at bit position
   [k], width [d] — the window's bits are the constraint's, the rest
   free.  Identity on doubt. *)
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

(* The six comparisons, exhaustive: any other binop is not a guard
   op and fails loudly. *)
let guard_op_of_binop (op : Bil.binop) : guard_op = match op with
  | Bil.LT -> ULT
  | Bil.LE -> ULE
  | Bil.EQ -> EQ
  | Bil.NEQ -> NEQ
  | Bil.SLT -> SLT
  | Bil.SLE -> SLE
  | Bil.PLUS | Bil.MINUS | Bil.TIMES | Bil.DIVIDE | Bil.SDIVIDE
  | Bil.MOD | Bil.SMOD | Bil.LSHIFT | Bil.RSHIFT | Bil.ARSHIFT
  | Bil.AND | Bil.OR | Bil.XOR -> assert false

let flip_guard_op (op : guard_op) : guard_op = match op with
  | ULT -> UGT | UGT -> ULT
  | ULE -> UGE | UGE -> ULE
  | SLT -> SGT | SGT -> SLT
  | SLE -> SGE | SGE -> SLE
  | EQ -> EQ | NEQ -> NEQ


(* The row a true guard [x op c] admits on [x]: [constraint_row] is the
   CLP-interval evidence row ([None] = identity), [total_row] the
   always-sound row; [guard_row] falls from evidence to total. *)
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
#ifdef VSA_DEBUG
  Cbat_attr_census.bump
    (match op with
     | ULT -> "band.total.ult"
     | ULE -> "band.total.ule"
     | UGT -> "band.total.ugt"
     | UGE -> "band.total.uge"
     | EQ -> "band.total.eq"
     | NEQ -> "band.total.neq"
     | SLT -> "band.total.slt"
     | SLE -> "band.total.sle"
     | SGT -> "band.total.sgt"
     | SGE -> "band.total.sge");
#endif
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
     | Some row ->
#ifdef VSA_DEBUG
       Cbat_attr_census.bump "band.constraint.ok";
#endif
       Some row
     | None ->
#ifdef VSA_DEBUG
       Cbat_attr_census.bump "band.constraint.fallback";
#endif
       total_row op c)
  | NEQ | UGT | UGE | SGT | SGE -> total_row op c


(* The var-var meet: EQ keeps the intersection, NEQ subtracts it. *)
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
     | Bil.NEQ ->
       let da = WordSet.diff a_ws ov and db = WordSet.diff b_ws ov in
#ifdef VSA_DEBUG
       (if WordSet.equal da a_ws then
          Cbat_attr_census.bump "band.diff.identity"
        else Cbat_attr_census.bump "band.diff.exact");
#endif
       Some da, Some db
     | _ -> Some ov, Some ov)

(* [x op y]: const rows at the other operand's extrema; the signed [x]
   rows take the evidence tier so identity survives an unproven
   operand; EQ/NEQ take the meet. *)
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

(* The constraint row for an operand; signed rows consult the
   non-negativity proof. *)
let row_for ~(env : AI.t) ?(nonneg : exp -> bool = fun _ -> false)
    (e : exp) (op : guard_op) (c : Cbat_word.t)
    : wordset option =
  let cur = Base.Result.ok (denote_imm_exp e env) in
  match op with
  | SLT | SLE -> guard_row ~cur ~known_nonneg:(nonneg e) op c
  | ULT | ULE | EQ -> guard_row ~cur op c
  | NEQ | UGT | UGE | SGT | SGE -> guard_row op c

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
             if Cbat_word.(>) lo maxn then []
             else [ (lo, Cbat_word.min hi maxn) ]
           else begin
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
                 (* The negative half wraps above [two_n]. *)
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
            hull ~wrapping:false n
              (Cbat_word.extract_exn ~hi:(n - 1) lo')
              (Cbat_word.extract_exn ~hi:(n - 1) hi'))
       | _ -> None)
  | Error _ -> None

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
         let vlo_w = Cbat_word.extract_exn ~hi:(w - 1) vlo in
         let vhi_w = Cbat_word.extract_exn ~hi:(w - 1) vhi in
         let two_n =
           Cbat_word.lshift (Cbat_word.one w) (Cbat_word.of_int ~width:w n) in
         let hi_a = Cbat_word.add vhi_w (Cbat_word.sub (Cbat_word.ones w) two_n) in
         hull ~wrapping:false w vlo_w hi_a
       | _ -> None)
  | Error _ -> None

(* Extract pre-image: the constraint is bits [lo, hi] of the operand;
   the endpoints compute at the constraint width, the hull gate at the
   operand width. *)
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



(* THE inverse denote: the per-node mirror of the forward transfer,
   phrased as each node's inverse — a binop's subtraction pre-image, a
   cast's extent widening, a leaf var's meet, a comparison's polarity
   windows.  A node with no closed-form inverse takes identity; a
   genuinely empty pre-image is the dead edge. *)
(* A cell fact awaiting delivery to the same-block store that wrote
   it. *)
type pending_cell = {
  pc_mem : var;          (* the memory var *)
  pc_key : Mem.Key.t;    (* the key the load read *)
  pc_cstr : wordset;     (* the produced value's constraint *)
  pc_endian : endian;
}

(* The leaf var's inverse: the meet; an empty meet is observed as a
   widening landmark and takes identity. *)
let meet_var ~(landmarks : Cbat_landmarks.t) (env : AI.t)
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
        Cbat_landmarks.observe_unsat_var landmarks v ~p:cur ~cstr:refined;
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

#ifdef VSA_DEBUG
(* The cell-meet soundness differential: each narrowing cell meet is
   checked over its enumerable concrete points — every pre-meet element
   satisfying the produced constraint must survive the meet; a lost
   point is an unsound narrowing and fails the debug run.  Bounded:
   pre-values beyond the enumeration cap count as skipped. *)
let cell_meet_cap = 16
let cell_meet_seq = ref 0
let cell_meet_verified = ref 0
let cell_meet_skipped = ref 0
let cell_meet_violations = ref 0
let cell_meet_diff_dump () =
  Printf.printf "CELL-MEET-DIFF: verified=%d skipped=%d violations=%d\n%!"
    !cell_meet_verified !cell_meet_skipped !cell_meet_violations
let () = at_exit cell_meet_diff_dump
let cell_meet_diff ~(ckey : string) ~(pre : wordset) ~(cstr : wordset)
    ~(res : wordset) : unit =
  incr cell_meet_seq;
  match WordSet.enumerate ~cap:cell_meet_cap pre with
  | None -> incr cell_meet_skipped
  | Some elems ->
    (match List.find elems ~f:(fun v ->
         WordSet.elem v cstr && not (WordSet.elem v res)) with
     | None -> incr cell_meet_verified
     | Some v ->
       incr cell_meet_violations;
       failwith
         (Format.asprintf
            "CELL-MEET-DIFF VIOLATION cell %s: point %s satisfies the \
             constraint %a but is outside the meet %a (pre %a)"
            ckey (Cbat_word.to_string v) WordSet.pp cstr WordSet.pp res
            WordSet.pp pre))
#endif

(* The cell key a backward meet may name: only a bounded address set
   denotes the cell a trace reads.  An unbounded address names no cell,
   so its constraint must stay identity rather than narrow every cell. *)
let bounded_cell_key (ws : wordset) : Mem.Key.t option =
  if WordSet.is_top ws || WordSet.is_infinite ws then None
  else Mem.Key.of_wordset ws

let rec inverse_denote ~(env : AI.t)
    ?(cells : pending_cell list ref = ref [])
    ?(nonneg : exp -> bool = fun _ -> false)
    ~(landmarks : Cbat_landmarks.t)
    (e : exp) (produced : wordset) : AI.t =
  match e with
  | Bil.Var v ->
    meet_var ~landmarks env v produced
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
    inverse_denote ~env ~cells ~nonneg ~landmarks a (WordSet.lnot produced)
  | Bil.UnOp (Bil.NEG, a) ->
    inverse_denote ~env ~cells ~nonneg ~landmarks a (WordSet.neg produced)
  | Bil.Cast (Bil.HIGH, sz, a) ->
    Option.value_map (high_cast_constraint env a sz produced) ~default:env
      ~f:(fun a' -> inverse_denote ~env ~cells ~nonneg ~landmarks a a')
  | Bil.Cast (ct, _, a) ->
    (match ct with
     | Bil.SIGNED | Bil.UNSIGNED ->
       Option.value_map
         (ext_cast_constraint
            ~is_signed:(match ct with Bil.SIGNED -> true | _ -> false)
            env a produced) ~default:env
         ~f:(fun a' -> inverse_denote ~env ~cells ~nonneg ~landmarks a a')
     | _ ->
       Option.value_map (low_cast_constraint env a produced) ~default:env
         ~f:(fun a' -> inverse_denote ~env ~cells ~nonneg ~landmarks a a'))
  | Bil.Extract (hi, lo, a) ->
    Option.value_map (extract_constraint env a hi lo produced) ~default:env
      ~f:(fun a' -> inverse_denote ~env ~cells ~nonneg ~landmarks a a')
  | Bil.Concat (a, b) ->
    (* The inverse splits the window on the width boundary. *)
    (match denote_imm_exp b env with
     | Ok b_ws ->
       let bw = WordSet.bitwidth b_ws in
       let cw = WordSet.bitwidth produced in
       if bw >= cw then inverse_denote ~env ~cells ~nonneg ~landmarks a produced
       else
         let env = inverse_denote ~env ~cells ~nonneg ~landmarks a
             (WordSet.extract ~hi:(cw - 1) ~lo:bw produced) in
         inverse_denote ~env ~cells ~nonneg ~landmarks b
           (WordSet.extract ~hi:(bw - 1) ~lo:0 produced)
     | Error _ -> env)
  | Bil.Ite (_, t, f) ->
    (* The forward joins the branches; the inverse constrains both. *)
    let env = inverse_denote ~env ~cells ~nonneg ~landmarks t produced in
    inverse_denote ~env ~cells ~nonneg ~landmarks f produced
  | Bil.Let (_, _, body) -> inverse_denote ~env ~cells ~nonneg ~landmarks body produced
  | Bil.Load (m, a, en, s) ->
    (* The cell fact meets the env's memory and threads to the store
       that wrote it. *)
    let env = meet_cell ~landmarks ~env ~mem:m ~addr:a ~size:s ~endian:en produced in
    (match m with
     | Bil.Var mv ->
       (match denote_imm_exp a env with
        | Ok aws ->
          Option.iter (bounded_cell_key aws)
            ~f:(fun k ->
               cells := { pc_mem = mv; pc_key = k; pc_cstr = produced;
                          pc_endian = en } :: !cells)
        | Error _ -> ())
     | _ -> ());
    env
  | Bil.Store (m, a, u, _en, s) ->
    (* The store carries the pending cell's constraint into its data,
       met against the written value; no match: identity. *)
    (match m with
     | Bil.Var mv ->
       (match !cells with
        | [] -> env
        | pending ->
          let res_size = Size.in_bits s in
          let ks = Option.bind (Base.Result.ok (denote_imm_exp a env)) ~f:bounded_cell_key in
          (match ks with
           | None -> env
           | Some ks ->
             let rec take pending = match pending with
               | [] -> None
               | cell :: rest ->
                 if Var.same cell.pc_mem mv
                    && WordSet.bitwidth cell.pc_cstr = res_size
                    && Mem.Key.overlap ks cell.pc_key
                 then Some (cell, rest)
                 else
                   (match take rest with
                    | Some (cell', rest') -> Some (cell', cell :: rest')
                    | None -> None) in
             (match take pending with
              | None -> env
              | Some (cell, rest) ->
                cells := rest;
                let data_cstr =
                  Option.value_map (Base.Result.ok (denote_imm_exp u env))
                    ~default:cell.pc_cstr ~f:(WordSet.meet cell.pc_cstr) in
                if Cbat_word.is_zero (WordSet.cardinality data_cstr) then env
                else inverse_denote ~env ~cells ~nonneg ~landmarks u data_cstr)))
     | _ -> env)
  | Bil.BinOp (Bil.AND, a, b) when WordSet.bitwidth produced = 1 ->
    (* AND = true constrains both operands. *)
    if WordSet.elem Cbat_word.b1 produced
       && not (WordSet.elem Cbat_word.b0 produced)
    then
      let env = inverse_denote ~env ~cells ~nonneg ~landmarks a produced in
      inverse_denote ~env ~cells ~nonneg ~landmarks b produced
    else if WordSet.elem Cbat_word.b0 produced
            && not (WordSet.elem Cbat_word.b1 produced)
    then
      (* AND = false: which operand is false is unknown — identity. *)
      env
    else env
  | Bil.BinOp (op, a, b) ->
    (match op with
     | Bil.EQ | Bil.NEQ | Bil.LT | Bil.LE | Bil.SLT | Bil.SLE
       when WordSet.bitwidth produced = 1 ->
       (* The produced bit's polarity windows the operands: {1} through
          the true side, {0} through the completed negation. *)
       let has1 = WordSet.elem Cbat_word.b1 produced in
       let has0 = WordSet.elem Cbat_word.b0 produced in
       if has1 && not has0 then cmp_inverse ~env ~cells ~nonneg ~landmarks op a b
       else if has0 && not has1 then
         (match complete_cond (Bil.UnOp (Bil.NOT, e)) with
          | Bil.BinOp (op', x, y) -> cmp_inverse ~env ~cells ~nonneg ~landmarks op' x y
          | _ -> env)
       else if has1 || has0 then env
       else AI.bottom
     | Bil.MOD | Bil.SMOD ->
       (* No closed-form inverse: identity, no extra knowledge. *)
       env
     | _ ->
       (* The subtraction pre-image: the operands' windows whose forward
          images land in the produced value; literals and Let bindings
          receive nothing. *)
       let deliver (e : exp) (c : wordset option) (env : AI.t) : AI.t =
         match e, c with
         | Bil.Int _, _ | Bil.Let _, _ -> env
         | _, Some c' -> inverse_denote ~env ~cells ~nonneg ~landmarks e c'
         | _ -> env in
       (match denote_imm_exp a env, denote_imm_exp b env with
        | Ok a_ws, Ok b_ws ->
          (match operand_constraints op produced a_ws b_ws with
           | a', b' ->
             let env = deliver a a' env in
             deliver b b' env)
        | _ -> env))
  | Bil.Unknown _ -> env

(* The produced {1} windows the operands by the ordering decision. *)
and cmp_inverse ~(env : AI.t) ~(cells : pending_cell list ref)
    ~(landmarks : Cbat_landmarks.t)
    ~(nonneg : exp -> bool)
    (op : Bil.binop) (a : exp) (b : exp) : AI.t =
  let const_side (x : exp) (flip : bool) (op : Bil.binop) (c : word) : AI.t =
    let c0 = Cbat_word.of_word c in
    let row o = if flip then flip_guard_op o else o in
    let cstr_opt = match op with
      | Bil.NEQ -> neq_complement c0
      | _ -> row_for ~env ~nonneg x (row (guard_op_of_binop op)) c0 in
    match cstr_opt with
    | Some cstr -> inverse_denote ~env ~cells ~nonneg ~landmarks x cstr
    | None -> env in
  match a, b with
  | _, Bil.Int c0 -> const_side a false op c0
  | Bil.Int c0, e0 -> const_side e0 true op c0
  | _ ->
    (match denote_imm_exp a env, denote_imm_exp b env with
     | Ok a_ws, Ok b_ws ->
       let x_cstr, y_cstr = overlap_constraints op a_ws b_ws in
       let env = match x_cstr with
         | Some xc -> inverse_denote ~env ~cells ~nonneg ~landmarks a xc
         | None -> env in
       (match y_cstr with
        | Some yc -> inverse_denote ~env ~cells ~nonneg ~landmarks b yc
        | None -> env)
     | _ -> env)

(* The load's cell fact meets the env's memory at the denoted address:
   stack-symbolic addresses key by segment offsets, foreign by their
   concrete hulls; identity on doubt. *)
and meet_cell ~(landmarks : Cbat_landmarks.t) ~(env : AI.t) ~(mem : exp)
    ~(addr : exp) ~(size : Size.t) ~(endian : endian) (produced : wordset) : AI.t =
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
          (match bounded_cell_key addr_ws with
           | None ->
#ifdef VSA_DEBUG
             Format.eprintf "DBG MEET-CELL: no key from %a\n%!"
               WordSet.pp addr_ws;
#endif
             env
           | Some key ->
             let res_size = Size.in_bits size in
             if WordSet.bitwidth produced <> res_size then env
             else
               let mv = AI.find_memory k env m in
               let data = Mem.Val.create produced endian in
#ifdef VSA_DEBUG
               let pre = Mem.Val.data (Mem.find (res_size, endian) mv key) in
               if Cbat_landmarks.observe_unsat_cell landmarks
                    ~cell:(Mem.Key.cell_key key) ~p:pre ~cstr:produced
               then incr Stages.cell_lm_recorded;
               let res = WordSet.meet pre produced in
               if not (WordSet.equal res pre) then
                 cell_meet_diff
                   ~ckey:(Sexp.to_string (Mem.Key.sexp_of_t key))
                   ~pre ~cstr:produced ~res;
               Format.eprintf "DBG MEET-CELL: meet %a into key %s\n%!"
                 WordSet.pp produced
                 (Sexp.to_string (Mem.Key.sexp_of_t key));
#else
               ignore (Cbat_landmarks.observe_unsat_cell landmarks
                         ~cell:(Mem.Key.cell_key key)
                         ~p:(Mem.Val.data (Mem.find (res_size, endian) mv key))
                         ~cstr:produced);
#endif
               AI.add_memory env ~key:m
                 ~data:(Mem.meet_range mv ~key ~data)))
     | Type.Imm _ | Type.Unk -> env)
  | _ -> env

(* The edge step: the graph's completed cond constrained TRUE — the {1}
   lives here only. *)
let constrain_edge ~(env : AI.t) ~(landmarks : Cbat_landmarks.t)
    (cond : exp) : AI.t =
  inverse_denote ~landmarks ~env cond (WordSet.singleton Cbat_word.b1)

(* Var→constraint map; a constraint is consumed at its var's def. *)
type live_map = wordset Var.Map.t

(* The walk entry: the seeds pushed through the block's defs backwards.
   Each def's incoming constraint is its var's live entry met with the
   def's produced value; reads take the def's PREFIX state overlaid
   with [live].  [~raw] applies the constraint AS GIVEN, skipping the
   producer subtraction — the acquisition's hypothetical; raw walks
   write nothing, only the empty-meet observations fire. *)
(* Constraints on vars the block never defines cross unchanged. *)
let carry_undefined ~(raw : bool) (live : wordset Var.Map.t)
    (env : AI.t) : AI.t =
  Core.Map.fold live ~init:env ~f:(fun ~key:v ~data:c acc ->
      if raw then acc
      else
        match Var.typ v with
        | Type.Imm w when WordSet.bitwidth c = w ->
          let cur = AI.find_word w acc v in
          let m = WordSet.meet cur c in
          if (not (Cbat_word.is_zero (WordSet.cardinality m)))
             && WordSet.precedes m cur
          then AI.add_word acc ~key:v ~data:m
          else acc
        | _ -> acc)

(* A produced-width dummy for mem defs: their inverse reads ~cells,
   never the width. *)
let undefined_width = WordSet.bottom 8

let walk ?(raw : bool = false)
    ~(sol : (tid, AI.t) Solution.t)
    ~(landmarks : Cbat_landmarks.t)
    ~(witness : env:AI.t -> exp -> bool)
    ~(seeds : live_map)
    (env : AI.t) (blk : blk term) : AI.t =
  let env_out = ref env in
  let blk_state = Solution.get sol (Term.tid blk) in
  (* Each def paired with its pre- and post-state, positionally;
     reverse def order. *)
  let prefixed =
    Term.enum def_t blk
    |> Seq.fold ~init:(blk_state, [])
      ~f:(fun (st, acc) d ->
          let post = denote_def d st in
          (post, (d, st, post) :: acc))
    |> snd in
  (* Word vars are the delivery/kill domain; mem vars the meets. *)
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
  (* A var's last def confines its edge value. *)
  let confined = ref Var.Set.empty in
  (* The positional call env: the prefix state's words, the live
     constraints met in, the edge memory. *)
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
  (* Records the rhs's free vars the inversion narrowed; each lives
     until its var's def consumes it. *)
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
  let walk_word_def (d, pre, post) =
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
             (* The produced value cannot satisfy the constraint: it
                does not hold before this def — dropped. *)
             ()
           else begin
             (* The first processing of a var is its LAST def. *)
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
                 inverse_denote ~env:ce ~cells ~landmarks
                   ~nonneg:(fun e -> witness ~env:ce e)
                   (Def.rhs d) cstr' in
               if not raw then begin
                 commit_memory env';
                 harvest ~base:ce env' (Def.rhs d)
               end
             end
           end)
    | Type.Mem _ ->
      (* Driven by the pending cells the loads pushed. *)
      if not raw then
        (match !cells with
         | [] -> ()
         | _ ->
           let ce = call_env pre in
           let env' =
             inverse_denote ~env:ce ~cells ~landmarks
               ~nonneg:(fun e -> witness ~env:ce e)
               (Def.rhs d) undefined_width in
           commit_memory env';
           harvest ~base:ce env' (Def.rhs d))
    | Type.Unk -> ()
  in
  List.iter prefixed ~f:walk_word_def;
  env_out := carry_undefined ~raw !live !env_out;
  !env_out

(* The walk's seeds: the cond's OWN narrowings — the strict per-var
   diff of the constrained env against the pre-constrain state. *)
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

(* The refinement walk: the constraint meets the produced values (the
   producer subtraction). *)
let walk_block ~sol ~landmarks ~witness ~seeds env blk =
  walk ~raw:false ~sol ~landmarks ~witness ~seeds env blk

(* The acquisition's hypothetical: the constraint applies AS GIVEN,
   skipping the producer subtraction. *)
let walk_block_raw ~sol ~landmarks ~witness ~seeds env blk =
  walk ~raw:true ~sol ~landmarks ~witness ~seeds env blk

(* The deep walk: the guard block's defs backwards; leftover
   constraints and cell meets flow into the returned edge env. *)
let refine_edge ~(sol : (tid, AI.t) Solution.t)
    ~(rctx : Cbat_runctx.refine_ctx)
    ~(seeds : live_map)
    (env : AI.t) (blk : blk term) : AI.t =
  Stages.incr_walk ();
  walk_block ~sol ~landmarks:rctx.rc_landmarks ~witness:rctx.rc_nonneg ~seeds env blk

(* The disabled continuation observed through the same rules, the
   result DISCARDED: every empty meet records the excluded boundary +
   distance as the enclosing WTO cycle's widening landmark (words and
   memory cells alike). *)
let acquire_unsat ~(sol : (tid, AI.t) Solution.t) ~(landmarks : Cbat_landmarks.t)
    ~(witness : env:AI.t -> exp -> bool)
    (env : AI.t) (blk : blk term) (disabled : exp) : unit =
  (* The raw walk pushes the disabled cond's constraints through the
     producers so the empty meets land on the counters. *)
  let constrained = constrain_edge ~env ~landmarks disabled in
  if not (AI.equal constrained AI.bottom) then begin
    let seeds = cond_seeds ~base:env constrained disabled in
    (* An empty leaf meet leaves the env unchanged: re-derive the
       constraint as the raw seed of its var. *)
    let raw_seeds =
      if AI.equal constrained env then
        Core.Set.fold (Exp.free_vars disabled) ~init:seeds ~f:(fun acc v ->
            match Var.typ v with
            | Type.Imm 1 ->
              Core.Map.set acc ~key:(Var.base v)
                ~data:(WordSet.singleton Cbat_word.b1)
            | _ -> acc)
      else seeds in
    ignore (walk_block_raw ~sol ~landmarks ~witness ~seeds:raw_seeds constrained blk)
  end

let refine_edge_inline
    ~(sol : (tid, AI.t) Solution.t)
    ~(rctx : Cbat_runctx.refine_ctx)
    ~(discarded : bool)
    (b : blk term) (env : AI.t) (acc_cond : exp)
    : AI.t =
  let env_in = env in
  let env = constrain_edge ~env ~landmarks:rctx.rc_landmarks acc_cond in
  (* No constraint derived: nothing to deliver. *)
  if discarded || AI.equal env env_in || AI.equal env AI.bottom then env
  else
    let seeds = cond_seeds ~base:env_in env acc_cond in
    let refined =
      Stages.time `Walk (fun () ->
          refine_edge ~sol ~rctx ~seeds env b) in
    refined
