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
    ~(index : def term list Exp.Map.t)
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
      (match Core.Map.find defs (Var.base v) with
       | Some (d, true) when seen ->
         (* Loads may close the induction. *)
         (match Def.rhs d with
          | Bil.Load _ -> walk cells vars (Def.rhs d)
          | _ -> false)
       | Some (d, true) -> walk cells (Core.Set.add vars e) (Def.rhs d)
       | _ -> false)
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
      let k = Cbat_word.of_word k in
      nonneg_word k && (Cbat_word.is_zero k || walk cells vars a)
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
      let addr_vars = Exp.free_vars addr in
      let anchored =
        not (Core.Set.is_empty addr_vars)
        && Core.Set.for_all addr_vars ~f:stack_anchor in
      let reentry = Core.Set.mem cells addr in
      if not anchored then false
      else if reentry then true
      else
        let cells' = Core.Set.add cells addr in
        let matches =
          Core.Map.find index addr |> Option.value ~default:[]
        in
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

(* The largest submask of [k] that is at most [v], built greedily from
   the top bit: every [x] with [x land k <= v] has [x land k] at most
   it, so [x <= max_submask_le k v lor lnot k]. *)
let max_submask_le (k : Cbat_word.t) (v : Cbat_word.t) : Cbat_word.t =
  let w = Cbat_word.bitwidth k in
  let rec go i acc =
    if i < 0 then acc
    else
      let bit = Cbat_word.lshift (Cbat_word.one w) (Cbat_word.of_int ~width:w i) in
      let cand = Cbat_word.logor acc bit in
      if (not (Cbat_word.is_zero (Cbat_word.logand k bit))) && Cbat_word.(<=) cand v
      then go (i - 1) cand
      else go (i - 1) acc
  in
  go (w - 1) (Cbat_word.zero w)

let operand_constraints (op : Bil.binop) (cstr : wordset)
    (a_ws : wordset) (b_ws : wordset) : wordset option * wordset option =
  let width = WordSet.bitwidth cstr in
  if WordSet.bitwidth a_ws <> width || WordSet.bitwidth b_ws <> width
  then None, None
  else
    (* The extrema pairs, forced by the arms that read them. *)
    let v_extrema = lazy (WordSet.min_elem cstr, WordSet.max_elem cstr) in
    let a_extrema = lazy (WordSet.min_elem a_ws, WordSet.max_elem a_ws) in
    let b_extrema = lazy (WordSet.min_elem b_ws, WordSet.max_elem b_ws) in
    let b_single =
      lazy (match Lazy.force b_extrema with
          | Some k, Some k' when Cbat_word.(=) k k' -> Some k
          | _ -> None) in
    let wrap_limit (k : Cbat_word.t) : Cbat_word.t = Cbat_word.div (Cbat_word.ones width) k in
    let operand_bounded (limit : Cbat_word.t) : bool =
      match snd (Lazy.force a_extrema) with
      | Some m -> Cbat_word.(<=) m limit
      | None -> false in
    (* The wrapping hull of a bound pair mapped to the operand's range. *)
    let hull_by ((mn, mx) : Cbat_word.t option * Cbat_word.t option)
        ~(f : Cbat_word.t -> Cbat_word.t -> Cbat_word.t * Cbat_word.t)
      : wordset option =
      match mn, mx with
      | Some mn, Some mx ->
        let lo, hi = f mn mx in
        hull ~wrapping:true width lo hi
      | _ -> None in
    let ceil_div (k : Cbat_word.t) (x : Cbat_word.t) : Cbat_word.t =
      let q = Cbat_word.div x k in
      let r = Cbat_word.modulo x k in
      if Cbat_word.is_zero r then q else Cbat_word.succ q in
    match op with
    | Bil.PLUS ->
      (match Lazy.force v_extrema with
       | Some vlo, Some vhi ->
         hull_by (Lazy.force b_extrema) ~f:(fun bmin bmax ->
             Cbat_word.sub vlo bmax, Cbat_word.sub vhi bmin),
         hull_by (Lazy.force a_extrema) ~f:(fun amin amax ->
             Cbat_word.sub vlo amax, Cbat_word.sub vhi amin)
       | _ -> None, None)
    | Bil.MINUS ->
      (match Lazy.force v_extrema with
       | Some vlo, Some vhi ->
         hull_by (Lazy.force b_extrema) ~f:(fun bmin bmax ->
             Cbat_word.add vlo bmin, Cbat_word.add vhi bmax),
         hull_by (Lazy.force a_extrema) ~f:(fun amin amax ->
             Cbat_word.sub amin vhi, Cbat_word.sub amax vlo)
       | _ -> None, None)
    | Bil.TIMES ->
      (match Lazy.force v_extrema, Lazy.force b_single with
       | (Some vlo, Some vhi), Some k ->
         (match Cbat_word.to_int k with
          | Ok kk when kk > 0 && operand_bounded (wrap_limit k) ->
            (hull ~wrapping:false width (ceil_div k vlo) (Cbat_word.div vhi k), None)
          | _ -> None, None)
       | _ -> None, None)
    | Bil.LSHIFT ->
      (match Lazy.force v_extrema, Lazy.force b_extrema with
       | (Some vlo, Some vhi), (Some smin, Some smax) ->
         (match Cbat_word.to_int smin, Cbat_word.to_int smax with
          | Ok smin_i, Ok smax_i
            when smin_i >= 0 && smax_i < width && smin_i <= smax_i ->
            let lo_a = Cbat_word.rshift vlo smax in
            let hi_a = Cbat_word.rshift vhi smin in
            (hull ~wrapping:false width lo_a hi_a, None)
          | _ -> None, None)
       | _ -> None, None)
    | Bil.RSHIFT | Bil.ARSHIFT ->
      (match Lazy.force v_extrema, Lazy.force b_extrema with
       | (Some vlo, Some vhi), (Some smin, Some smax) ->
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
              (hull ~wrapping:false width lo_a hi_a, None)
          | _ -> None, None)
       | _ -> None, None)
    | Bil.DIVIDE ->
      (match Lazy.force v_extrema, Lazy.force b_extrema with
       | (Some vlo, Some vhi), (Some kmin, Some kmax) ->
         (match Cbat_word.to_int kmin, Cbat_word.to_int kmax with
          | Ok kmin_i, Ok kmax_i when kmin_i > 0 && kmin_i <= kmax_i ->
            let hi1 = Cbat_word.succ vhi in
            let kmax_w = Cbat_word.of_int ~width kmax_i in
            let limit = Cbat_word.div (Cbat_word.ones width) kmax_w in
            if Cbat_word.(>) hi1 limit then None, None
            else
              let lo_a = Cbat_word.mul vlo (Cbat_word.of_int ~width kmin_i) in
              let hi_a = Cbat_word.pred (Cbat_word.mul hi1 kmax_w) in
              (hull ~wrapping:false width lo_a hi_a, None)
          | _ -> None, None)
       | _ -> None, None)
    | Bil.SDIVIDE ->
      (match Lazy.force v_extrema, Lazy.force b_single with
       | (Some vlo, Some vhi), Some k when width <= 32 ->
         (match Cbat_word.to_int k with
          | Ok kk when kk > 0 ->
            (* Small widths avoid overflow. *)
            (match Cbat_word.to_int vlo, Cbat_word.to_int vhi with
             | Ok slo, Ok shi ->
               let lo' = slo * kk in
               let hi' = (shi + 1) * kk - 1 in
               (hull ~wrapping:true width (Cbat_word.of_int ~width lo') (Cbat_word.of_int ~width hi'), None)
             | _ -> None, None)
          | _ -> None, None)
       | _ -> None, None)
    | Bil.MOD | Bil.SMOD ->
      None, None
    | Bil.AND | Bil.OR | Bil.XOR ->
      (* Singleton masks constrain: XOR is a bitwise bijection, so its
         pre-image is exact; AND bounds the operand below by the
         constraint ([x >= x land k]) and above by the largest masked
         value the constraint admits with every unmasked bit set. *)
      (match Lazy.force b_single with
       | Some k ->
         if Cbat_word.is_zero k then
           (match op with
            | Bil.OR | Bil.XOR -> Some cstr, None
            | _ -> None, None)
         else if Cbat_word.(=) k (Cbat_word.ones width) then
           (match op with
            | Bil.AND -> Some cstr, None
            | Bil.XOR -> Some (WordSet.lnot cstr), None
            | _ -> None, None)
         else
           (match op with
            | Bil.XOR ->
              Some (WordSet.logxor cstr (WordSet.singleton k)), None
            | Bil.AND ->
              (match Lazy.force v_extrema with
               | Some vlo, Some vhi ->
                 hull ~wrapping:false width vlo
                   (Cbat_word.logor (max_submask_le k vhi) (Cbat_word.lnot k)),
                 None
               | _ -> None, None)
            | _ -> None, None)
       | _ -> None, None)
    | _ -> None, None

(* Operand constraints for a bit window: the result constraint's hull
   [vlo, vhi] placed at bit position [k], width [d], of the operand
   (width [w]) — the window's bits carry the constraint, every bit
   above the window free.  The endpoints lift to the operand width; a
   constraint whose successor wraps reaches the word top.  Identity on
   doubt. *)
let shift_fill_constraint ~(w : int) (k : int) (d : int)
    (vlo : Cbat_word.t) (vhi : Cbat_word.t) : wordset option =
  let sh = Cbat_word.of_int ~width:w k in
  let lo_a = Cbat_word.lshift (Cbat_word.extract_exn ~hi:(w - 1) vlo) sh in
  let hi_max =
    if Cbat_word.is_zero (Cbat_word.succ vhi) then Cbat_word.ones w
    else
      let hi_a =
        Cbat_word.pred
          (Cbat_word.lshift
             (Cbat_word.extract_exn ~hi:(w - 1) (Cbat_word.succ vhi)) sh) in
      let top =
        if k + d >= w then Cbat_word.zero w
        else
          Cbat_word.sub (Cbat_word.ones w)
            (Cbat_word.pred
               (Cbat_word.lshift (Cbat_word.one w)
                  (Cbat_word.of_int ~width:w (k + d)))) in
      Cbat_word.add hi_a top
  in
  hull ~wrapping:false w lo_a hi_max

(* The unsigned hull of a constraint; [None] when it has none. *)
let bounds (cstr : wordset) : (Cbat_word.t * Cbat_word.t) option =
  match WordSet.min_elem cstr, WordSet.max_elem cstr with
  | Some lo, Some hi -> Some (lo, hi)
  | _ -> None

(* HIGH-cast pre-image: the constraint is the word's top [n] bits. *)
let high_cast_constraint (env : AI.t) (a : exp) (sz : int)
    (cstr : wordset) : wordset option =
  match denote_imm_exp a env with
  | Ok a_ws ->
    let w = WordSet.bitwidth a_ws in
    let n = WordSet.bitwidth cstr in
    if w <= n then None
    else
      (match bounds cstr with
       | Some (vlo, vhi) ->
         (* An open-top constraint (the succ wraps) has no closed hull. *)
         if Cbat_word.is_zero (Cbat_word.succ vhi) then None
         else shift_fill_constraint ~w (w - n) n vlo vhi
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


(* The row a true guard [x op c] admits on [x]: [evidence_constraint] is the
   CLP-interval evidence row ([None] = identity), [total_constraint] the
   always-sound row; [guard_constraint] falls from evidence to total. *)
let evidence_constraint ?(cur : wordset option = None)
    ?(known_nonneg : bool = false)
    (op : guard_op) (c : Cbat_word.t) : wordset option =
  let width = Cbat_word.bitwidth c in
  let half = Word_ops.half width in
  let cardn_of_int (i : int) : Cbat_word.t option =
    if i < 0 then None else Some (Cbat_word.of_int ~width:(width + 1) i) in
  let int_of_word (v : Cbat_word.t) : int option =
    Cbat_word.to_int v |> Result.ok in
  (* The arms read the bound's payload: the sign flag a signed extremum
     carries is an annotation, not part of the value the comparison
     denotes, so the half tests run unsigned. *)
  let payload = Cbat_word.unsigned in
  let provably_nonneg =
    known_nonneg
    || Option.value_map cur ~default:false ~f:(fun ws ->
        match WordSet.max_elem ws with
        | None -> false
        | Some m -> Cbat_word.(<) (payload m) half) in
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
    if Cbat_word.(>=) (payload c) half
    then interval_clp_of ~width ~cardn:(Cbat_word.sub c half) half
    else if provably_nonneg
    then interval_clp_of ~width ~cardn:c (Cbat_word.zero width)
    else None
  | SLE ->
    if Cbat_word.(>=) (payload c) half
    then interval_clp_of ~width ~cardn:(Cbat_word.succ (Cbat_word.sub c half)) half
    else if provably_nonneg
    then interval_clp_of ~width ~cardn:(Cbat_word.succ c) (Cbat_word.zero width)
    else None
  | NEQ | UGT | UGE | SGT | SGE -> None

let total_constraint (op : guard_op) (c : Cbat_word.t) : wordset option =
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

let guard_constraint ?(cur : wordset option = None)
    ?(known_nonneg : bool = false)
    (op : guard_op) (c : Cbat_word.t) : wordset option =
  match op with
  | ULT | ULE | EQ | SLT | SLE ->
    (match evidence_constraint ~cur ~known_nonneg op c with
     | Some row ->
#ifdef VSA_DEBUG
       Cbat_attr_census.bump "band.constraint.ok";
#endif
       Some row
     | None ->
#ifdef VSA_DEBUG
       Cbat_attr_census.bump "band.constraint.fallback";
#endif
       total_constraint op c)
  | NEQ | UGT | UGE | SGT | SGE -> total_constraint op c


(* The var-var meet: EQ keeps the intersection; NEQ removes the other
   side's values exactly when that side is a singleton — with two or
   more partners every value keeps a differing one. *)
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
       let da =
         if Cbat_word.is_one (WordSet.cardinality b_ws) then WordSet.diff a_ws ov
         else a_ws
       in
       let db =
         if Cbat_word.is_one (WordSet.cardinality a_ws) then WordSet.diff b_ws ov
         else b_ws
       in
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
       | Bil.LT -> total_constraint ULT mx_y, total_constraint UGT mn_x
       | Bil.LE -> total_constraint ULE mx_y, total_constraint UGE mn_x
       | Bil.SLT ->
         evidence_constraint ~known_nonneg:nonneg_x SLT mx_y, total_constraint SGT mn_x
       | Bil.SLE ->
         evidence_constraint ~known_nonneg:nonneg_x SLE mx_y, total_constraint SGE mn_x
       | Bil.EQ | Bil.NEQ -> overlap_eq op a_ws b_ws
       | _ -> None, None)
    | _ -> None, None

(* The constraint row for an operand; signed rows consult the
   non-negativity proof. *)
let constraint_for_operand ~(env : AI.t) ?(nonneg : exp -> bool = fun _ -> false)
    (e : exp) (op : guard_op) (c : Cbat_word.t)
    : wordset option =
  let cur = Base.Result.ok (denote_imm_exp e env) in
  match op with
  | SLT | SLE -> guard_constraint ~cur ~known_nonneg:(nonneg e) op c
  | ULT | ULE | EQ -> guard_constraint ~cur op c
  | NEQ | UGT | UGE | SGT | SGE -> guard_constraint op c

let ext_cast_constraint ~(is_signed : bool) (env : AI.t) (a : exp)
    (cstr : wordset) : wordset option =
  match denote_imm_exp a env with
  | Ok a_ws ->
    let n = WordSet.bitwidth a_ws in
    let w = WordSet.bitwidth cstr in
    if w <= n then None
    else
      let zero = Cbat_word.zero w in
      let two_n = Cbat_word.pow2 ~width:w n in
      let half =
        Cbat_word.lshift (Cbat_word.one w) (Cbat_word.of_int ~width:w (n - 1)) in
      let maxn = Cbat_word.pred two_n in
      (match bounds cstr with
       | Some (lo, hi) ->
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

(* Low-cast pre-image: the constraint's window repeated at every
   multiple of [2^n] the operand can reach.  A zero-extension of an
   n-bit value reaches the first window only, so its pre-image is the
   constraint itself at the operand's width; a bounded operand reaches
   only the windows its own value set populates; an unbounded operand
   takes the wide hull. *)
let low_cast_constraint (env : AI.t) (a : exp) (cstr : wordset)
    : wordset option =
  match denote_imm_exp a env with
  | Error _ -> None
  | Ok a_ws ->
    let w = WordSet.bitwidth a_ws in
    let n = WordSet.bitwidth cstr in
    if n >= w then None
    else
      (* A zero-extension of an n-bit value keeps its low n bits, so the
         low cast is the identity there: the pre-image is the constraint
         itself at the operand's width, never the wide hull. *)
      let zero_extended_n =
        match a with
        | Bil.Cast (Bil.UNSIGNED, _, inner) ->
          (match denote_imm_exp inner env with
           | Ok inner_ws -> WordSet.bitwidth inner_ws = n
           | Error _ -> false)
        | _ -> false in
      match bounds cstr with
      | None -> None
      | Some (vlo, vhi) ->
        let vlo_w = Cbat_word.extract_exn ~hi:(w - 1) vlo in
        let vhi_w = Cbat_word.extract_exn ~hi:(w - 1) vhi in
        let wide_hull () =
          let two_n = Cbat_word.pow2 ~width:w n in
          hull ~wrapping:false w vlo_w
            (Cbat_word.add vhi_w (Cbat_word.sub (Cbat_word.ones w) two_n)) in
        if zero_extended_n then hull ~wrapping:false w vlo_w vhi_w
        else begin
          match bounds a_ws with
          | Some (alo, ahi)
            when (not (WordSet.is_infinite a_ws)) && Cbat_word.(<=) alo ahi ->
            (* The windows [k] the operand's reachable set populates:
               window [k·2^n, k·2^n + 2^n) can carry a concrete
               execution only when it meets [alo, ahi]; the others drop
               and the surviving windows' constraint pieces hull. *)
            (* The window index and the count word: rshift takes the
               count as a value, so the count rides a small literal
               ([n < w <= 64]) and the window base multiplies. *)
            let step = Cbat_word.pow2 ~width:w n in
            let cnt = Cbat_word.of_int ~width:w n in
            let k0 = Cbat_word.rshift alo cnt in
            let k1 = Cbat_word.rshift ahi cnt in
            begin match Cbat_word.to_int (Cbat_word.sub k1 k0) with
              | Ok span when span <= 64 ->
                (* One window's constraint pieces: a non-wrapping
                   constraint contributes [base+lo, base+hi]; a wrapping
                   one contributes its high half [base+lo, base+2^n-1]
                   and its low half [base, base+hi]. *)
                let piece k =
                  let base = Cbat_word.mul k step in
                  let ints =
                    if Cbat_word.(<=) vlo_w vhi_w then
                      [ (Cbat_word.add base vlo_w, Cbat_word.add base vhi_w) ]
                    else
                      [ (Cbat_word.add base vlo_w,
                         Cbat_word.add base (Cbat_word.ones n));
                        (base, Cbat_word.add base vhi_w) ] in
                  List.filter_map ints ~f:(fun (l, h) ->
                      let l = Cbat_word.max alo l in
                      let h = Cbat_word.min ahi h in
                      hull ~wrapping:false w l h) in
                let rec pieces k acc =
                  if Cbat_word.(<=) k k1 then
                    pieces (Cbat_word.add k (Cbat_word.one w))
                      (List.rev_append (piece k) acc)
                  else List.rev acc in
                List.reduce (pieces k0 []) ~f:WordSet.union
              | _ -> wide_hull ()
            end
          | _ -> wide_hull ()
        end

(* Operand constraints for an extract: the result constraint is the
   operand's bits [lo, hi]; the window sits mid-word, so the endpoints
   compute at the operand width with the free-above bits filled. *)
let extract_constraint (env : AI.t) (a : exp) (hi : int) (lo : int)
    (cstr : wordset) : wordset option =
  match denote_imm_exp a env with
  | Ok a_ws ->
    let w = WordSet.bitwidth a_ws in
    let n = WordSet.bitwidth cstr in
    if n <> hi - lo + 1 then None
    else
      (match bounds cstr with
       | Some (vlo, vhi) -> shift_fill_constraint ~w lo n vlo vhi
       | _ -> None)
  | Error _ -> None



(* The ONE pending-constraint map's entry: a constraint awaiting
   delivery to the producer that wrote it, keyed by what it constrains
   — a word var, or the byte range a load read.  A word entry dies at
   its var's def; a cell entry at the store that overwrites its range
   (a shape-matching one delivers, any overlapping one blocks the
   boundary carry).  An entry no def consumes crosses the block
   boundary into the edge state. *)
type pending =
  | PW of var * wordset
  | PC of {
      pm : var;              (* the memory var *)
      prange : Mem.Key.t;    (* the read's touched byte range *)
      pc : wordset;          (* the produced value's constraint *)
      pbits : int;           (* the read's width *)
      pendian : endian;      (* the read's endianness *)
    }

let pending_key (p : pending) : Cbat_landmarks.key =
  match p with
  | PW (v, _) -> Cbat_landmarks.Word v
  | PC { prange; _ } -> Cbat_landmarks.Cell (Mem.Key.cell_key prange)

(* The first entry [f] accepts, paired with the other entries in order. *)
let take_first ~(f : pending -> bool) (ps : pending list)
    : (pending * pending list) option =
  let rec go = function
    | [] -> None
    | p :: rest ->
      if f p then Some (p, rest)
      else
        match go rest with
        | Some (q, r) -> Some (q, p :: r)
        | None -> None
  in
  go ps

(* The first entry at [key], paired with the other entries. *)
let pending_take (key : Cbat_landmarks.key) (ps : pending list)
    : (pending * pending list) option =
  take_first ps ~f:(fun p -> Cbat_landmarks.equal_key (pending_key p) key)

(* THE one leaf meet, keyed by what it constrains (a variable, or a
   memory cell) — the policy both lanes share.  Every meet is acquired
   into the enclosing head's widening table (the excluded boundary when
   the meet empties, the trimmed piece when it narrows).  An empty meet
   is the excluded behavior: observed, the state unchanged — never the
   dead-path bottom.  A meet that does not narrow takes the identity.
   A real narrowing is written back. *)
let leaf_meet ~(landmarks : Cbat_landmarks.t) ~(key : Cbat_landmarks.key)
    ~(cur : wordset) ~(meet : wordset -> wordset -> wordset)
    ~(write : wordset -> 'st -> 'st) (cstr : wordset) (st : 'st) : 'st =
  if WordSet.bitwidth cur <> WordSet.bitwidth cstr then st
  else begin
    let m = meet cur cstr in
    ignore (Cbat_landmarks.observe_unsat landmarks ~key ~p:cur ~cstr ~m);
    if Cbat_word.is_zero (WordSet.cardinality m) then st
    else if (not (WordSet.precedes m cur)) || WordSet.equal m cur then st
    else write m st
  end

(* The leaf var's inverse: the meet, through the one leaf rule. *)
let meet_var ~(landmarks : Cbat_landmarks.t) (env : AI.t)
    (v : var) (refined : wordset) : AI.t =
  match Var.typ v with
  | Type.Imm w ->
    let cur = AI.find_word w env v in
    leaf_meet ~landmarks ~key:(Cbat_landmarks.Word v) ~cur ~meet:WordSet.meet
      ~write:(fun m env ->
#ifdef VSA_DEBUG
        (match WordSet.stack_offsets cur, WordSet.stack_offsets m with
         | Some _, None ->
           Format.eprintf "DBG SYMBOL-STRIP var=%s cur=%a refined=%a meet=%a\n%!"
             (Var.name v) WordSet.pp cur WordSet.pp refined WordSet.pp m
         | _ -> ());
#endif
        AI.add_word env ~key:v ~data:m)
      refined env
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
   so its constraint must stay identity rather than narrow every cell.
   The backward cell meet is sound only when every path reads the SAME
   cell: a single-point address, or a wider address set whose read bytes
   all lie inside one stored cell.  A read that can land on two cells
   reads a different one per path, so the read's value constraint is
   path-local.  ADR 0025's join argument covers the join (a load's value
   contains every contributing cell); it does not license the meet back
   into each cell. *)
let bounded_cell_key (ws : wordset) : Mem.Key.t list =
  if WordSet.is_top ws || WordSet.is_infinite ws then []
  else Mem.Key.of_wordset ws

(* A single-point key names one address (and so one cell on every path). *)
let key_is_point (k : Mem.Key.t) : bool =
  Mem.Key.step k = 1
  && (let lo, hi = Mem.Key.hull k in Cbat_word.equal lo hi)

(* The byte span a stored cell occupies: its key hull grown by its
   value's own width. *)
let cell_span ((k, v) : Mem.Key.t * Mem.Val.t) : Cbat_word.t * Cbat_word.t =
  Mem.Key.hull (Mem.Key.expand k ~bytes:(fst (Mem.Val.get_idx v) / 8))

(* The one stored cell the read's touched bytes all lie inside, when
   exactly one cell covers the read. *)
let covering_cell (mv : Mem.t) (key : Mem.Key.t) ~(bytes : int)
    : Mem.Key.t option =
  let origin = Mem.Key.origin key in
  let r_lo, r_hi = Mem.Key.hull (Mem.Key.expand key ~bytes) in
  let covers (c, v) =
    Hike_origin.equal (Mem.Key.origin c) origin
    && (let c_lo, c_hi = cell_span (c, v) in
        Cbat_word.(<=) c_lo r_lo && Cbat_word.(<=) r_hi c_hi)
  in
  match List.filter (Mem.cells mv) ~f:covers with
  | [ (c, _) ] -> Some c
  | _ -> None

(* The cell keys a backward meet may narrow: the read's own key when the
   read touches one cell on every path; [] otherwise (the meet stays the
   identity, and the address pre-image carries the sound narrowing). *)
let backward_cell_keys (mv : Mem.t) (addr_ws : wordset) ~(bytes : int)
    : Mem.Key.t list =
  match bounded_cell_key addr_ws with
  | [ k ] when key_is_point k -> [ k ]
  | [ k ] ->
    (match covering_cell mv k ~bytes with Some _ -> [ k ] | None -> [])
  | _ -> []

(* Whether a piece's elements fill its hull: its element count equals
   the hull's.  Every piece the address filter decides is finite and
   non-wrapped, so its min/max are its elements' bounds.  A step-1
   traversal (or a singleton) is dense by construction; the hull-count
   test is the general fallback. *)
let piece_dense (p : Cbat_clp.t) ~(lo : Cbat_word.t) ~(hi : Cbat_word.t) : bool =
  (not (Cbat_clp.is_infinite p))
  && (Cbat_word.is_one (Cbat_clp.cardinality p)
      || Cbat_word.is_one (Cbat_clp.step_of p)
      || (let w1 = Cbat_word.bitwidth hi + 1 in
          let hull_card =
            Cbat_word.add
              (Cbat_word.sub
                 (Cbat_word.cast Bil.UNSIGNED w1 hi)
                 (Cbat_word.cast Bil.UNSIGNED w1 lo))
              (Cbat_word.one w1) in
          Cbat_word.equal (Cbat_clp.cardinality p) hull_card))

(* Whether one of [p]'s elements is an address whose [bytes]-wide read
   can touch a stored cell on [line]: the read at [x] meets the cell
   hull [cl, ch] iff [x, x+bytes-1] meets [cl, ch] iff [x] lies in the
   (possibly wrapped) [cl-(bytes-1), ch].  The answer is definitive:
   [Pieces.overlap] never reports disjoint for a non-empty element
   intersection, so a piece it clears hides no read the singleton rule
   could drop.

   [has_cell_in] is the cheap necessary prefilter only: a false span
   answer clears every element; a true one hands the decision to the
   per-cell element test.  The cell's stride is not read: the forward
   load consults cells by hull overlap, and narrowing by the grid could
   clear a consulted read. *)
let piece_touches_cell_bounds ?cells (mv : Mem.t) ~(line : Hike_origin.t)
    ~(bytes : int) ~(lo : Cbat_word.t) ~(hi : Cbat_word.t)
    (p : Cbat_clp.t) : bool =
  let w = Cbat_word.bitwidth hi in
  let back = Cbat_word.of_int ~width:w (bytes - 1) in
  let last = Cbat_word.add hi back in
  (* A wrapped read can meet cells on either side of the modulus. *)
  Cbat_word.(<) last hi
  || (Mem.has_cell_in mv ~origin:line ~lo ~hi:last
      && (let qp = Cbat_clp.Pieces.of_progression p in
          let cells =
            match cells with Some c -> Lazy.force c | None -> Mem.cells mv in
          List.exists cells ~f:(fun (k, _) ->
              Hike_origin.equal (Mem.Key.origin k) line
              && (let cl, ch = Mem.Key.hull k in
                  Cbat_word.bitwidth cl <> w
                  || Cbat_word.bitwidth ch <> w
                  || Cbat_clp.Pieces.overlap qp
                       (Cbat_clp.Pieces.of_progression
                          (Cbat_clp.interval ~width:w
                             (Cbat_word.sub cl back) ch))))))

let piece_touches_cell (mv : Mem.t) ~(line : Hike_origin.t) ~(bytes : int)
    (p : Cbat_clp.t) : bool =
  match Cbat_clp.min_elem p, Cbat_clp.max_elem p with
  | Some lo, Some hi -> piece_touches_cell_bounds mv ~line ~bytes ~lo ~hi p
  | _ -> true

(* The read-start ranges of the threaded images that can hold a
   [bytes]-wide read: [img_lo, img_hi-(bytes-1)] — the forward image
   rule requires the whole read inside one image.  Images too short for
   the read drop out once here. *)
let image_read_starts ~(bytes : int) : (Stdlib.Int64.t * Stdlib.Int64.t) list =
  let back = Stdlib.Int64.of_int (bytes - 1) in
  List.filter_map !section_images_ref ~f:(fun { img_lo; img_hi; _ } ->
      if Stdlib.Int64.unsigned_compare (Stdlib.Int64.sub img_hi img_lo) back >= 0
      then Some (img_lo, Stdlib.Int64.sub img_hi back)
      else None)

(* Whether one of [p]'s elements is an address whose [bytes]-wide read
   fits inside one of the [fits] ranges: a dense piece tests the ranges
   directly, a strided piece intersects them exactly.  Images are the
   host's (64-bit) addresses; a narrower address width keeps the sound
   identity. *)
let piece_touches_image_bounds ~(fits : (Stdlib.Int64.t * Stdlib.Int64.t) list)
    ~(dense : bool) ~(lo : Cbat_word.t) ~(hi : Cbat_word.t)
    (p : Cbat_clp.t) : bool =
  let w = Cbat_word.bitwidth hi in
  if dense then
    (match Cbat_word.to_int64_opt lo, Cbat_word.to_int64_opt hi with
     | Some l, Some h ->
       List.exists fits ~f:(fun (fit_lo, fit_hi) ->
           Stdlib.Int64.unsigned_compare l fit_hi <= 0
           && Stdlib.Int64.unsigned_compare fit_lo h <= 0)
     | _ -> true)
  (* Non-64-bit: the int64-based reader cannot decide; sound identity. *)
  else if w <> 64 then true
  else
    let qp = Cbat_clp.Pieces.of_progression p in
    List.exists fits ~f:(fun (fit_lo, fit_hi) ->
        Cbat_clp.Pieces.overlap qp
          (Cbat_clp.Pieces.of_progression
             (Cbat_clp.interval ~width:w
                (Cbat_word.of_int64 ~width:w fit_lo)
                (Cbat_word.of_int64 ~width:w fit_hi))))

let piece_touches_image ~(bytes : int) (p : Cbat_clp.t) : bool =
  match Cbat_clp.min_elem p, Cbat_clp.max_elem p with
  | Some lo, Some hi ->
    piece_touches_image_bounds ~fits:(image_read_starts ~bytes)
      ~dense:(piece_dense p ~lo ~hi) ~lo ~hi p
  | _ -> true

(* The load's address pre-image: the addresses whose read can produce a
   value in [produced].  Only known memory — a stored cell or a section
   image — excludes an address: a range covering neither reads top and
   stays whole; a covered range is decided in bulk down to its covered
   elements, each read by the forward load and dropped iff its value, on
   the constraint's own origin, misses [produced].  [None] when nothing is
   excluded, or everything is (the leaf rule's identity). *)
let load_address_constraint ?denoted ~(env : AI.t) ~(mem : exp) ~(addr : exp)
    ~(endian : endian) ~(size : Size.t) (produced : wordset) : wordset option =
  let bits = Size.in_bits size in
  let denoted =
    match denoted with Some d -> d | None -> denote_imm_exp addr env in
  match mem, denoted with
  | Bil.Var m, Ok aws
    when bits mod 8 = 0 && WordSet.bitwidth produced = bits
         && not (WordSet.is_top aws || WordSet.is_infinite aws || WordSet.is_bottom aws) -> (
    match Var.typ m with
    | Type.Mem (addr_i, addressable_size) ->
      let mv = AI.find_memory (mem_idx addr_i addressable_size) env m in
      if Mem.is_bottom mv then None
      else
        let nb = bits / 8 in
        (* The threaded images' read-start ranges: constant across this
           constraint's decisions (one read width). *)
        let image_fits = image_read_starts ~bytes:nb in
        (* The memory's cells, materialized at most once per constraint. *)
        let cells = lazy (Mem.cells mv) in
        (* The singleton rule: the address value of the one-element
           piece [p]; a known read whose value, on this constraint's own
           origin, misses [produced], drops its address. *)
        let drops (v : wordset) : bool =
          Option.equal Hike_origin.equal (WordSet.origin v)
            (WordSet.origin produced)
          && Cbat_word.is_zero (WordSet.cardinality (WordSet.meet v produced)) in
        let read_image = image_point_reader ~endian ~bits mv in
        (* An image word's verdict depends on its value alone. *)
        let image_drops : (int64, bool) Hashtbl.t = Hashtbl.create (module Int64) in
        let image_keep (raw : int64) : bool =
          not
            (Hashtbl.find_or_add image_drops raw ~default:(fun () ->
                 drops
                   (WordSet.singleton
                      (Cbat_word.of_word (Word.of_int64 ~width:bits raw))))) in
        let general_keep line (p : Cbat_clp.t) : bool =
          let one =
            match line with
            | Hike_origin.Stack -> WordSet.stack_word p
            | _ -> WordSet.of_clp p in
          not (drops (load_value ~addr:one ~endian ~bits mv)) in
        let singleton_keep line (p : Cbat_clp.t) : bool =
          let point =
            match line, Cbat_clp.min_elem p with
            | Hike_origin.Stack, _ | _, None -> None
            | _, Some x when Cbat_word.bitwidth x <> 64 -> None
            | _, Some x ->
              Base.Option.bind (Cbat_word.to_int64_opt x)
                ~f:(read_image ~cell_free:false) in
          match point with
          | Some raw -> image_keep raw
          | None -> general_keep line p in
        (* The read-start ranges a covered element's read can touch, as
           the element-level tests build them: the same-line cell hulls
           each shifted back by the read width (the span prefilter is
           [has_cell_in]), and — on the Abs line — the images' read
           starts.  A cell hull whose width does not match the piece's
           cannot be intersected and keeps its addresses on the identity
           path.

           Each range carries whether its addresses may be kept
           wholesale.  A cell whose own hull is too wide to enumerate
           decides each address on its own read grid, repeated across
           the whole hull; walking that hull would enumerate the grid
           for no more knowledge than keeping it. *)
        let cell_enum_bound = 65536 in
        let covered_ranges (line : Hike_origin.t) ~(lo : Cbat_word.t)
            ~(hi : Cbat_word.t) ~(last : Cbat_word.t) :
            (Cbat_clp.t * bool) list =
          let w = Cbat_word.bitwidth hi in
          let back = Cbat_word.of_int ~width:w (nb - 1) in
          let image_ranges =
            match line with
            | Hike_origin.Abs ->
              List.map image_fits ~f:(fun (fit_lo, fit_hi) ->
                  (Cbat_clp.interval ~width:w
                     (Cbat_word.of_int64 ~width:w fit_lo)
                     (Cbat_word.of_int64 ~width:w fit_hi),
                   false))
            | _ -> [] in
          let cell_ranges =
            if Mem.has_cell_in mv ~origin:line ~lo ~hi:last then
              List.filter_map (Lazy.force cells) ~f:(fun (k, _) ->
                  if Hike_origin.equal (Mem.Key.origin k) line then
                    let cl, ch = Mem.Key.hull k in
                    if Cbat_word.bitwidth cl = w && Cbat_word.bitwidth ch = w
                    then
                      let keep_whole =
                        Cbat_word.gt_int
                          (Cbat_word.succ_exact (Cbat_word.sub ch cl))
                          cell_enum_bound in
                      Some (Cbat_clp.interval ~width:w (Cbat_word.sub cl back) ch,
                            keep_whole)
                    else None
                  else None)
            else [] in
          image_ranges @ cell_ranges in
        (* [q] minus one covered run [h] of [q]'s elements: the elements
           below [h]'s minimum and above its maximum.  [h] contains every
           element between its extrema (it is [q]'s grid intersected with
           an address interval, or that intersection hulled), so the
           dropped middle is exactly [h]'s own enumeration and never
           loses an element. *)
        let subtract_run (q : Cbat_clp.t) (h : Cbat_clp.t) : Cbat_clp.t list =
          match Cbat_clp.min_elem q, Cbat_clp.min_elem h, Cbat_clp.max_elem h with
          | Some q_lo, Some h_lo, Some h_hi ->
            let left, q =
              if Cbat_word.(<) q_lo h_lo then
                Cbat_clp.split_at_n q (Cbat_word.pred h_lo)
              else (Cbat_clp.bottom (Cbat_clp.bitwidth q), q) in
            let right =
              match Cbat_clp.min_elem q with
              | Some q_lo' when Cbat_word.(<=) q_lo' h_hi ->
                snd (Cbat_clp.split_at_n q h_hi)
              | _ -> q in
            [ left; right ]
          | _ -> [ q ] in
        (* The bulk partition: [hits] are the covered elements (each a
           contiguous run of [p]'s grid), [rest] keeps everything outside
           them wholesale.  Hits from a wholesale range (an oversized
           cell hull) are not enumerated: their elements stay in [rest]
           — keeping is always sound, and walking the hull would
           enumerate its whole read grid.  The other hits are enumerated
           and the singleton rule applies per element; one that exceeds
           [enum_bound] falls back to the [Split] bisection.  A piece
           whose coverage yields no ranges is kept whole ([`Keep`], the
           sound identity). *)
        let enum_bound = 4096 in
        (* The coverage runs as integer progressions (low, step, count,
           span free of stored cells), for 64-bit addresses below 2^61
           off the stack line; [None] sends the partition to the word
           path. *)
        let int_runs line (small : Cbat_clp.t list) ~(width : int) :
            (int * int * int * int * bool) list option =
          let limit = Stdlib.Int64.shift_left 1L 61 in
          let small_int w =
            match Cbat_word.to_int64_opt w with
            | Some v when Stdlib.Int64.compare v 0L >= 0
                          && Stdlib.Int64.compare v limit < 0 ->
              Some (Stdlib.Int64.to_int v)
            | _ -> None in
          let run piece =
            match
              Cbat_clp.min_elem piece, Cbat_clp.max_elem piece,
              small_int (Cbat_clp.cardinality piece)
            with
            | Some lo_w, Some hi_w, Some card ->
              (match small_int lo_w, small_int hi_w with
               | Some lo, Some hi ->
                 let step = if card = 1 then 1 else
                     Option.value (small_int (Cbat_clp.step_of piece)) ~default:0 in
                 if step > 0 && lo + (card - 1) * step = hi then
                   let last = Cbat_word.of_int ~width (hi + nb - 1) in
                   Some (lo, step, card, hi,
                         not (Mem.has_cell_in mv ~origin:Hike_origin.Abs
                                ~lo:lo_w ~hi:last))
                 else None
               | _ -> None)
            | _ -> None in
          match line with
          | Hike_origin.Stack -> None
          | _ when width <> 64 || bits > 64 -> None
          | _ ->
            let runs =
              List.concat_map small ~f:(fun h ->
                  List.map (Cbat_clp.split_wrapped h) ~f:run) in
            if List.for_all runs ~f:Option.is_some then
              Some (List.filter_map runs ~f:Fn.id)
            else None in
        (* The ordered union of the runs' addresses that survive the
           singleton rule, each read once. *)
        let sweep_runs line runs : Cbat_word.t list =
          let runs = Array.of_list runs in
          let k = Array.length runs in
          let idx = Array.create ~len:k 0 in
          let kept = Stdlib.ref [] in
          let continue = Stdlib.ref true in
          while !continue do
            let m = Stdlib.ref Stdlib.max_int in
            for j = 0 to k - 1 do
              let lo, step, card, _, _ = runs.(j) in
              if idx.(j) < card then m := Int.min !m (lo + idx.(j) * step)
            done;
            if !m = Stdlib.max_int then continue := false
            else begin
              let m = !m in
              let free = Stdlib.ref false in
              for j = 0 to k - 1 do
                let lo, step, card, hi, span_free = runs.(j) in
                if span_free && lo <= m && m <= hi then free := true;
                if idx.(j) < card && lo + idx.(j) * step = m then
                  idx.(j) <- idx.(j) + 1
              done;
              let keep =
                match read_image ~cell_free:!free (Stdlib.Int64.of_int m) with
                | Some raw -> image_keep raw
                | None ->
                  general_keep line
                    (Cbat_clp.singleton (Cbat_word.of_int ~width:64 m)) in
              if keep then kept := Cbat_word.of_int ~width:64 m :: !kept
            end
          done;
          List.rev !kept in
        let partition (line : Hike_origin.t) (p : Cbat_clp.t)
            ~(lo : Cbat_word.t) ~(hi : Cbat_word.t) ~(last : Cbat_word.t) =
          let hits =
            List.filter_map (covered_ranges line ~lo ~hi ~last)
              ~f:(fun (r, keep_whole) ->
                let h = Cbat_clp.intersection p r in
                if Cbat_clp.is_bottom h then None else Some (h, keep_whole)) in
          let small =
            List.filter_map hits ~f:(fun (h, keep_whole) ->
                if keep_whole then None else Some h) in
          match hits with
          | [] -> `Keep
          | _ when
              List.exists small ~f:(fun h ->
                  Cbat_clp.is_infinite h
                  || Cbat_word.gt_int (Cbat_clp.cardinality h) enum_bound) ->
            `Split
          | _ ->
            let rest =
              List.fold small ~init:[ p ] ~f:(fun qs h ->
                  List.concat_map qs ~f:(fun q ->
                      if Cbat_clp.is_bottom (Cbat_clp.intersection q h) then [ q ]
                      else subtract_run q h)) in
            let width = Cbat_word.bitwidth hi in
            let kept =
              match int_runs line small ~width with
              | Some runs -> sweep_runs line runs
              | None ->
                (* Coverage ranges may overlap: merge their ordered grids
                   before reading each covered address once. *)
                let covered =
                  List.concat_map small ~f:(fun h ->
                      List.map (Cbat_clp.split_wrapped h) ~f:Cbat_clp.iter)
                  |> Cbat_vsa_utils.merge_balanced
                       ~merge:(Cbat_vsa_utils.merge_dedup ~compare:Cbat_word.compare) in
                List.filter covered ~f:(fun x ->
                    singleton_keep line (Cbat_clp.singleton x)) in
            let kept_runs =
              Cbat_clp.Exact.to_pieces (Cbat_clp.Exact.of_sorted_list ~width kept) in
            let parts =
              Cbat_clp.Pieces.merge_progressions
                (List.filter rest ~f:(fun q -> not (Cbat_clp.is_bottom q)))
                kept_runs
              |> List.map ~f:(fun q -> (q, `Keep)) in
            `Parts parts in
        let decide line p =
          match Cbat_clp.min_elem p, Cbat_clp.max_elem p with
          | Some lo, Some hi ->
            let last = Cbat_word.add hi (Cbat_word.of_int ~width:(Cbat_word.bitwidth hi) (nb - 1)) in
            if Cbat_word.(<) last hi then `Keep
            else if
              not
                ((match line with
                  | Hike_origin.Abs ->
                    piece_touches_image_bounds ~fits:image_fits
                      ~dense:(piece_dense p ~lo ~hi) ~lo ~hi p
                  | _ -> false)
                 || piece_touches_cell_bounds ~cells mv ~line ~bytes:nb ~lo ~hi p)
            then `Keep
            else if Cbat_word.is_one (Cbat_clp.cardinality p) then
              (if singleton_keep line p then `Keep else `Drop)
            else partition line p ~lo ~hi ~last
          | _ -> `Keep in
        let kept = WordSet.filter_addresses aws ~decide in
        if WordSet.is_bottom kept || WordSet.equal kept aws then None else Some kept
    | Type.Imm _ | Type.Unk -> None)
  | _ -> None

(* Whether evaluating [e] reads memory (a load, or a memory-valued
   subterm). *)
let rec reads_memory (e : exp) : bool =
  match e with
  | Bil.Var v -> (match Var.typ v with Type.Mem _ -> true | _ -> false)
  | Bil.Int _ -> false
  | Bil.Load _ | Bil.Store _ | Bil.Unknown _ -> true
  | Bil.BinOp (_, a, b) | Bil.Concat (a, b) -> reads_memory a || reads_memory b
  | Bil.UnOp (_, a) | Bil.Cast (_, _, a) | Bil.Extract (_, _, a) -> reads_memory a
  | Bil.Ite (c, t, f) -> reads_memory c || reads_memory t || reads_memory f
  | Bil.Let (_, a, b) -> reads_memory a || reads_memory b

let rec constrain_operands ~(env : AI.t)
    ?(cells : pending list ref = ref [])
    ?(nonneg : exp -> bool = fun _ -> false)
    ~(landmarks : Cbat_landmarks.t)
    (e : exp) (produced : wordset) : AI.t =
  (* The recursive call on a sub-expression, in [env] unless given. *)
  let recur ?(env = env) e produced =
    constrain_operands ~env ~cells ~nonneg ~landmarks e produced in
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
    recur a (WordSet.lnot produced)
  | Bil.UnOp (Bil.NEG, a) ->
    recur a (WordSet.neg produced)
  | Bil.Cast (Bil.HIGH, sz, a) ->
    Option.value_map (high_cast_constraint env a sz produced) ~default:env
      ~f:(fun a' -> recur a a')
  | Bil.Cast (ct, _, a) ->
    (match ct with
     | Bil.SIGNED | Bil.UNSIGNED ->
       Option.value_map
         (ext_cast_constraint
            ~is_signed:(match ct with Bil.SIGNED -> true | _ -> false)
            env a produced) ~default:env
         ~f:(fun a' -> recur a a')
     | _ ->
       Option.value_map (low_cast_constraint env a produced) ~default:env
         ~f:(fun a' -> recur a a'))
  | Bil.Extract (hi, lo, a) ->
    Option.value_map (extract_constraint env a hi lo produced) ~default:env
      ~f:(fun a' -> recur a a')
  | Bil.Concat (a, b) ->
    (* The inverse splits the window on the width boundary. *)
    (match denote_imm_exp b env with
     | Ok b_ws ->
       let bw = WordSet.bitwidth b_ws in
       let cw = WordSet.bitwidth produced in
       if bw >= cw then recur a produced
       else
         let env = recur a
             (WordSet.extract ~hi:(cw - 1) ~lo:bw produced) in
         recur ~env b
           (WordSet.extract ~hi:(bw - 1) ~lo:0 produced)
     | Error _ -> env)
  | Bil.Ite (c, t, f) ->
    (* The branches are alternatives: a condition whose denotation names
       one branch constrains that branch; any other condition leaves the
       state unconstrained. *)
    (match denote_imm_exp c env with
     | Ok c_ws when Cbat_word.is_one (WordSet.cardinality c_ws) ->
       if WordSet.elem Cbat_word.b0 c_ws
       then recur f produced
       else recur t produced
     | Ok _ | Error _ -> env)
  | Bil.Let (_, _, body) -> recur body produced
  | Bil.Load (m, a, en, s) ->
    (* An address that reads no memory denotes the same before and after
       the cell step (which only writes the memory), so one denotation
       serves the whole arm. *)
    let denoted = denote_imm_exp a env in
    let stable = not (reads_memory a) in
    let addr_cstr =
      load_address_constraint ~denoted ~env ~mem:m ~addr:a ~endian:en ~size:s
        produced in
    (* The cell fact meets the env's memory and threads to the store
       that wrote it; the entry carries the touched byte range (the
       address denotation expanded by the read size) and the read's
       endianness, so the store match compares the read's whole
       shape. *)
    let env =
      constrain_cell_on_trace ~denoted ~landmarks ~env ~mem:m ~addr:a ~size:s
        ~endian:en produced in
    (match m with
     | Bil.Var mv ->
       (match Var.typ mv, if stable then denoted else denote_imm_exp a env with
        | Type.Mem (ai, asz), Ok aws ->
          let mv_mem = AI.find_memory (mem_idx ai asz) env mv in
          List.iter (backward_cell_keys mv_mem aws ~bytes:(Size.in_bytes s))
            ~f:(fun k ->
               cells := PC { pm = mv;
                             prange = Mem.Key.expand k ~bytes:(Size.in_bytes s);
                             pc = produced;
                             pbits = Size.in_bits s;
                             pendian = en }
                     :: !cells)
        | _ -> ())
     | _ -> ());
    Option.value_map addr_cstr ~default:env
      ~f:(fun a' -> recur ~env a a')
  | Bil.Store (m, a, u, en, s) ->
    (* The store consumes the first pending entry whose range it
       overwrites: the constraint speaks about the store's data or
       about nothing.  A shape-matching entry (same width, same
       endianness) delivers into the written value, met against the
       stored data's denotation; a shape-mismatched one is dropped —
       the written bytes reassembled under another shape bound no
       value.  The entry exists only for a read that touches one cell
       on every path (S6), so on the paths it speaks about the read
       reads exactly this store's bytes.  See
       docs/adr/0025-the-join-ruling.md. *)
    (match m with
     | Bil.Var mv ->
       (match !cells with
        | [] -> env
        | pending ->
          let ks =
            Base.Result.ok (denote_imm_exp a env)
            |> Base.Option.value_map ~default:[] ~f:bounded_cell_key in
          (match ks with
           | [] -> env
           | ks ->
             let overwrites (p : pending) : bool =
               match p with
               | PC { pm; prange; _ } ->
                 Var.same pm mv
                 && List.exists ks ~f:(fun k -> Mem.Key.overlap k prange)
               | PW _ -> false in
             (match take_first ~f:overwrites pending with
              | None -> env
              | Some (p, rest) ->
                cells := rest;
                match p with
                | PC c
                  when c.pbits = Size.in_bits s
                       && Bitvector.compare_endian c.pendian en = 0 ->
                  let data_cstr =
                    Option.value_map (Base.Result.ok (denote_imm_exp u env))
                      ~default:c.pc ~f:(WordSet.meet c.pc) in
                  if Cbat_word.is_zero (WordSet.cardinality data_cstr) then env
                  else recur u data_cstr
                | _ -> env)))
     | _ -> env)
  | Bil.BinOp (Bil.AND, a, b) when WordSet.bitwidth produced = 1 ->
    (* AND = true constrains both operands. *)
    if WordSet.elem Cbat_word.b1 produced
       && not (WordSet.elem Cbat_word.b0 produced)
    then
      let env = recur a produced in
      recur ~env b produced
    else
      (* AND = false: which operand is false is unknown — identity. *)
      env
  | Bil.BinOp (Bil.OR, a, b) when WordSet.bitwidth produced = 1 ->
    (* OR = false constrains both operands to false. *)
    if WordSet.elem Cbat_word.b0 produced
       && not (WordSet.elem Cbat_word.b1 produced)
    then
      let env = recur a produced in
      recur ~env b produced
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
         | _, Some c' -> recur ~env e c'
         | _ -> env in
       (match denote_imm_exp a env, denote_imm_exp b env with
        | Ok a_ws, Ok b_ws ->
          (let a', b' = operand_constraints op produced a_ws b_ws in
           let env = deliver a a' env in
           deliver b b' env)
        | _ -> env))
  | Bil.Unknown _ -> env

(* The produced {1} windows the operands by the ordering decision. *)
and cmp_inverse ~(env : AI.t) ~(cells : pending list ref)
    ~(landmarks : Cbat_landmarks.t)
    ~(nonneg : exp -> bool)
    (op : Bil.binop) (a : exp) (b : exp) : AI.t =
  let const_side (x : exp) (flip : bool) (op : Bil.binop) (c : word) : AI.t =
    let c0 = Cbat_word.of_word c in
    let row o = if flip then flip_guard_op o else o in
    let cstr_opt = match op with
      | Bil.NEQ -> neq_complement c0
      | _ -> constraint_for_operand ~env ~nonneg x (row (guard_op_of_binop op)) c0 in
    match cstr_opt with
    | Some cstr -> constrain_operands ~env ~cells ~nonneg ~landmarks x cstr
    | None -> env in
  match a, b with
  | _, Bil.Int c0 -> const_side a false op c0
  | Bil.Int c0, e0 -> const_side e0 true op c0
  | _ ->
    (match denote_imm_exp a env, denote_imm_exp b env with
     | Ok a_ws, Ok b_ws ->
       let x_cstr, y_cstr = overlap_constraints op a_ws b_ws in
       let env = match x_cstr with
         | Some xc -> constrain_operands ~env ~cells ~nonneg ~landmarks a xc
         | None -> env in
       (match y_cstr with
        | Some yc -> constrain_operands ~env ~cells ~nonneg ~landmarks b yc
        | None -> env)
     | _ -> env)

(* The load's cell fact meets the env's memory at the denoted address:
   stack-symbolic addresses key by segment offsets, foreign by their
   concrete hulls; identity on doubt.  Each fan-out key runs the one
   leaf rule; the write-back is the piecewise meet whose empty piece
   keeps its cell. *)
and constrain_cell_on_trace ?denoted ~(landmarks : Cbat_landmarks.t) ~(env : AI.t) ~(mem : exp)
    ~(addr : exp) ~(size : Size.t) ~(endian : endian) (produced : wordset) : AI.t =
  match mem with
  | Bil.Var m ->
    (match Var.typ m with
     | Type.Mem (addr_i, addressable_size) ->
       let k = mem_idx addr_i addressable_size in
       (match
          (match denoted with Some d -> d | None -> denote_imm_exp addr env)
        with
        | Error _ -> env
        | Ok addr_ws ->
          let res_size = Size.in_bits size in
          (* The cell world is byte-addressed: a sub-byte read's
             meet is unrepresentable — the identity (no meet) keeps
             the cell's pre. *)
          if res_size mod 8 <> 0 then env
          else if WordSet.bitwidth produced <> res_size then env
          else
            let mv = AI.find_memory k env m in
            (match backward_cell_keys mv addr_ws ~bytes:(Size.in_bytes size) with
             | [] -> env
             | keys ->
               List.fold keys ~init:env ~f:(fun env key ->
                   let cur = Mem.Val.data (Mem.find (res_size, endian) mv key) in
#ifdef VSA_DEBUG
                   let res = WordSet.meet cur produced in
                   if not (WordSet.equal res cur) then
                     cell_meet_diff
                       ~ckey:(Sexp.to_string (Mem.Key.sexp_of_t key))
                       ~pre:cur ~cstr:produced ~res;
                   Format.eprintf "DBG MEET-CELL: meet %a into key %s\n%!"
                     WordSet.pp produced
                     (Sexp.to_string (Mem.Key.sexp_of_t key));
#endif
                     leaf_meet ~landmarks
                     ~key:(Cbat_landmarks.Cell (Mem.Key.cell_key key))
                     ~cur ~meet:WordSet.meet
                     ~write:(fun mval mem ->
                         let mvk = AI.find_memory k mem m in
                         AI.add_memory mem ~key:m
                           ~data:(Mem.meet_range_keep mvk ~key
                                    ~data:(Mem.Val.create mval endian)))
                     produced env)))
     | Type.Imm _ | Type.Unk -> env)
  | _ -> env

(* The edge step: the graph's completed cond constrained TRUE — the {1}
   lives here only. *)
let constrain_edge ~(env : AI.t) ~(landmarks : Cbat_landmarks.t)
    (cond : exp) : AI.t =
  constrain_operands ~landmarks ~env cond (WordSet.singleton Cbat_word.b1)

(* A produced-width dummy for mem defs: their constraint derivation reads
   the pending map, never the width. *)
let undefined_width = WordSet.bottom 8

let strictly_precedes (narrow : wordset) (wide : wordset) : bool =
  WordSet.precedes narrow wide && not (WordSet.equal narrow wide)

(* The replay's write sites: a def's output fact, a block input fact. *)
type write_site = Output_write | Input_write

(* What the backward pass learned, by position: the constraint each
   def's output satisfies on the edge, and the cells each def's loads
   read under the edge.  The forward replay meets them in place. *)
type walk_state = {
  pending : pending list ref;
  outputs : wordset Tid.Map.t ref;
  reads : pending list Tid.Map.t ref;
  landmarks : Cbat_landmarks.t;
}

(* The walk's delivery locus: what the walk's facts become.  ONE walk
   serves both callers — the state-writer records every fact and
   replays the block forward from the refined inputs, so a fact reaches
   the edge exactly as far as the block's own transfer carries it; the
   observer keeps nothing: its walk exists for the leaf meets the seeds
   fire on the way, so its constraints apply as given and no path is
   claimed dead. *)
type locus = {
  at_def : post:(unit -> wordset) -> cstr:wordset -> wordset option;
  invert_mem : pending list -> bool;
  record_output : walk_state -> def term -> wordset -> unit;
  record_reads :
    walk_state -> def term -> before:pending list -> after:pending list -> unit;
  harvest : walk_state -> base:AI.t -> env:AI.t -> rhs:exp -> unit;
  replay :
    walk_state -> entry:AI.t -> prefix:(def term * AI.t * AI.t) list ->
    AI.t -> AI.t;
}

(* A word fact through the one leaf rule's write discipline: an empty
   meet keeps the state, an equal one writes nothing. *)
let meet_word ~(on_write : unit -> unit) (st : AI.t) (v : var) (c : wordset) :
    AI.t =
  match Var.typ v with
  | Type.Imm w when WordSet.bitwidth c = w ->
    let cur = AI.find_word w st v in
    let m = WordSet.meet cur c in
    if (not (Cbat_word.is_zero (WordSet.cardinality m)))
       && strictly_precedes m cur
    then begin on_write (); AI.add_word st ~key:v ~data:m end
    else st
  | _ -> st

(* A cell fact: the read's range meets the memory it names. *)
let meet_cell ~(landmarks : Cbat_landmarks.t option) (st : AI.t) (p : pending) :
    AI.t =
  match p with
  | PW _ -> st
  | PC c ->
    (match Var.typ c.pm with
     | Type.Mem (ai, asz) ->
       let k = mem_idx ai asz in
       let mv = AI.find_memory k st c.pm in
       let cur = Mem.Val.data (Mem.find (c.pbits, c.pendian) mv c.prange) in
       let write mval st =
         AI.add_memory st ~key:c.pm
           ~data:(Mem.meet_range_keep (AI.find_memory k st c.pm) ~key:c.prange
                    ~data:(Mem.Val.create mval c.pendian)) in
       (match landmarks with
        | Some landmarks ->
          leaf_meet ~landmarks
            ~key:(Cbat_landmarks.Cell (Mem.Key.cell_key c.prange))
            ~cur ~meet:WordSet.meet ~write c.pc st
        | None ->
          if WordSet.bitwidth cur <> WordSet.bitwidth c.pc then st
          else
            let m = WordSet.meet cur c.pc in
            if Cbat_word.is_zero (WordSet.cardinality m)
               || not (strictly_precedes m cur) then st
            else write m st)
     | _ -> st)

(* The state-writer: the edge state is the block replayed forward from
   its refined inputs, each def's facts met where they hold.  [on_write]
   names each actual write — an output fact at its def, an input fact at
   the entry; a fact equal to the replayed value writes nothing. *)
let writer_locus ~(on_write : write_site -> unit) : locus =
  let at_def ~post ~cstr =
    let m = WordSet.meet cstr (post ()) in
    if Cbat_word.is_zero (WordSet.cardinality m) then None else Some m
  in
  let invert_mem (ps : pending list) =
    List.exists ps ~f:(fun p ->
        match p with PC _ -> true | PW _ -> false)
  in
  let record_output (st : walk_state) (d : def term) (c : wordset) =
    st.outputs := Core.Map.set !(st.outputs) ~key:(Term.tid d) ~data:c
  in
  let record_reads (st : walk_state) (d : def term) ~(before : pending list)
      ~(after : pending list) =
    (* The cells this def's loads pushed. *)
    let ps =
      List.filter after ~f:(fun p ->
          match p with
          | PC _ -> not (List.exists before ~f:(phys_equal p))
          | PW _ -> false) in
    if not (List.is_empty ps) then
      st.reads := Core.Map.update !(st.reads) (Term.tid d)
          ~f:(fun old -> ps @ Option.value old ~default:[])
  in
  let harvest (st : walk_state) ~(base : AI.t) ~(env : AI.t) ~(rhs : exp) =
    Core.Set.fold (Exp.free_vars rhs) ~init:() ~f:(fun () v ->
        match Var.typ v with
        | Type.Imm w ->
          let before = AI.find_word w base v in
          let after = AI.find_word w env v in
          if (not (WordSet.is_bottom after)) && strictly_precedes after before
          then
            st.pending := PW (v, after)
                         :: List.filter !(st.pending) ~f:(fun p ->
                                match p with
                                | PW (v', _) -> not (Var.same v v')
                                | PC _ -> true)
        | _ -> ())
  in
  let replay (st : walk_state) ~(entry : AI.t)
      ~(prefix : (def term * AI.t * AI.t) list) (_edge : AI.t) =
    (* What no def consumed holds at the block's inputs. *)
    let inputs =
      List.fold !(st.pending) ~init:entry ~f:(fun acc p ->
          match p with
          | PW (v, c) -> meet_word ~on_write:(fun () -> on_write Input_write) acc v c
          | PC _ ->
#ifdef VSA_DEBUG
            Cbat_attr_census.bump "carry.cell.crossed";
#endif
            meet_cell ~landmarks:(Some st.landmarks) acc p)
    in
    (* A def entered in its cached pre-state keeps the cached post; the
       first state a meet changes is denoted afresh from there on. *)
    List.fold_right prefix ~init:inputs ~f:(fun (d, pre, post) acc ->
        let acc =
          List.fold (Core.Map.find_multi !(st.reads) (Term.tid d)) ~init:acc
            ~f:(meet_cell ~landmarks:None) in
        let acc = if phys_equal acc pre then post else denote_def d acc in
        match Core.Map.find !(st.outputs) (Term.tid d) with
        | Some c ->
          meet_word ~on_write:(fun () -> on_write Output_write) acc (Def.lhs d) c
        | None -> acc)
  in
  { at_def; invert_mem; record_output; record_reads; harvest; replay }

(* The observer: the walk's only product is the acquisitions. *)
let observer_locus : locus =
  { at_def = (fun ~post:_ ~cstr -> Some cstr);
    invert_mem = (fun _ -> false);
    record_output = (fun _ _ _ -> ());
    record_reads = (fun _ _ ~before:_ ~after:_ -> ());
    harvest = (fun _ ~base:_ ~env:_ ~rhs:_ -> ());
    replay = (fun _ ~entry:_ ~prefix:_ edge -> edge) }

(* A block's def chain with its pre/post states, positionally, in
   reverse def order.  It depends only on (block, entry state): the
   solve ctx caches the last denotation physically. *)
let cached_prefix
    (cache : (AI.t * (def term * AI.t * AI.t) list) Tid.Map.t ref option)
    (blk : blk term) (entry : AI.t) : (def term * AI.t * AI.t) list =
  let compute () =
    Term.enum def_t blk
    |> Seq.fold ~init:(entry, [])
      ~f:(fun (st, acc) d ->
          let post = denote_def d st in
          (post, (d, st, post) :: acc))
    |> snd
  in
  match cache with
  | Some c ->
    (match Core.Map.find !c (Term.tid blk) with
     | Some (e0, pref) when phys_equal e0 entry -> pref
     | _ ->
       let pref = compute () in
       c := Core.Map.set !c ~key:(Term.tid blk) ~data:(entry, pref);
       pref)
  | None -> compute ()

(* The block's postcondition from the same fold that fills the prefix
   cache, so the guard walk does not denote the chain again. *)
let denote_defs_cached
    (cache : (AI.t * (def term * AI.t * AI.t) list) Tid.Map.t ref)
    (blk : blk term) (entry : AI.t) : AI.t =
  match cached_prefix (Some cache) blk entry with
  | [] -> entry
  | (_, _, post) :: _ -> post

let walk ~(locus : locus)
    ?(cache : (AI.t * (def term * AI.t * AI.t) list) Tid.Map.t ref option)
    ~(entry : AI.t)
    ~(landmarks : Cbat_landmarks.t)
    ~(witness : env:AI.t -> exp -> bool)
    ~(seeds : Var.Set.t)
    (env : AI.t) (blk : blk term) : AI.t =
  (* The walked block's IN state, handed in by the caller — no
     solution lookup, no snapshot copy. *)
  let blk_state = entry in
  let prefixed = cached_prefix cache blk blk_state in
  (* The ONE pending map: the seeds are its word entries (each seed's
     constraint is the edge state's own value for the var); the loads
     push the cell entries. *)
  let cells =
    ref (Core.Set.fold seeds ~init:[] ~f:(fun acc v ->
            match Var.typ v with
            | Type.Imm w -> PW (v, AI.find_word w env v) :: acc
            | _ -> acc)) in
  let st = { pending = cells; outputs = ref Tid.Map.empty;
             reads = ref Tid.Map.empty; landmarks } in
  (* The positional call env: the def's own pre-state with the pending
     word constraints met in. *)
  let call_env (pre : AI.t) : AI.t =
    List.fold !cells ~init:pre ~f:(fun acc p ->
        match p with
        | PW (v, c) ->
          (match Var.typ v with
           | Type.Imm w when WordSet.bitwidth c = w ->
             AI.add_word acc ~key:v
               ~data:(WordSet.meet (AI.find_word w pre v) c)
           | _ -> acc)
        | PC _ -> acc) in
  let invert_def (d : def term) (pre : AI.t) (cstr' : wordset) =
    let ce = call_env pre in
    let before = !cells in
    let env' =
      constrain_operands ~env:ce ~cells ~landmarks
        ~nonneg:(fun e -> witness ~env:ce e)
        (Def.rhs d) cstr'
    in
    (* The cells this def's loads read hold the read constraint here. *)
    locus.record_reads st d ~before ~after:!cells;
    locus.harvest st ~base:ce ~env:env' ~rhs:(Def.rhs d)
  in
  let walk_word_def (d, pre, post) =
    let v = Def.lhs d in
    match Var.typ v with
    | Type.Imm w ->
      (match pending_take (Cbat_landmarks.Word v) !cells with
       | Some (PW (_, cstr), rest) ->
         (* The def consumes its var's constraint, whatever it says. *)
         cells := rest;
         (match locus.at_def ~post:(fun () -> AI.find_word w post v) ~cstr with
          | None ->
            (* The produced value cannot satisfy the constraint: it
               does not hold before this def. *)
            ()
          | Some cstr' ->
            locus.record_output st d cstr';
            invert_def d pre cstr')
       | _ -> ())
    | Type.Mem _ ->
      (* Driven by the pending cells the loads pushed. *)
      if locus.invert_mem !cells then invert_def d pre undefined_width
    | Type.Unk -> ()
  in
  List.iter prefixed ~f:walk_word_def;
  locus.replay st ~entry:blk_state ~prefix:prefixed env

(* The walk's seeds: the cond's own constrained vars — every free var
   the guard bounds.  A seed's constraint is the state's own value for
   the var, so the var names the delivery and the walk reads the value
   from the state it walks. *)
let cond_seeds ~(env : AI.t) (cond : exp) : Var.Set.t =
  Core.Set.fold (Exp.free_vars cond) ~init:Var.Set.empty ~f:(fun acc v ->
      match Var.typ v with
      | Type.Imm w ->
        let after = AI.find_word w env v in
        if (not (WordSet.is_bottom after))
           && (not (WordSet.is_top after))
           && not (WordSet.is_infinite after)
        then Core.Set.add acc (Var.base v)
        else acc
      | _ -> acc)

(* The refinement walk (the state-writer locus): the constraint meets
   the produced values (the producer subtraction). *)
let walk_block ?(on_write : write_site -> unit = ignore)
    ~(rctx : Cbat_runctx.refine_ctx) ~entry ~landmarks ~witness
    ~seeds env blk =
  walk ~locus:(writer_locus ~on_write)
    ~cache:rctx.Cbat_runctx.rc_prefix ~entry ~landmarks
    ~witness ~seeds env blk

(* The deep walk: the guard block's defs backwards; leftover
   constraints and cell meets flow into the returned edge env. *)
let refine_edge ?(on_write : write_site -> unit = ignore)
    ~(entry : AI.t)
    ~(rctx : Cbat_runctx.refine_ctx)
    ~(seeds : Var.Set.t)
    (env : AI.t) (blk : blk term) : AI.t =
  Stages.incr_walk ();
  walk_block ~on_write ~rctx ~entry ~landmarks:rctx.rc_landmarks
    ~witness:rctx.rc_nonneg ~seeds env blk

(* The disabled continuation observed through the same rules, the
   result DISCARDED: every empty meet records the excluded boundary +
   distance as the enclosing WTO cycle's widening landmark (words and
   memory cells alike). *)
let acquire_unsat ~(entry : AI.t) ~(landmarks : Cbat_landmarks.t)
    ~(cache : (AI.t * (def term * AI.t * AI.t) list) Tid.Map.t ref)
    ~(witness : env:AI.t -> exp -> bool)
    (env : AI.t) (blk : blk term) (disabled : exp) : unit =
  (* Outside a cycle no observation records, so the walk has no effect. *)
  if Cbat_landmarks.in_cycle landmarks then begin
    (* The raw walk pushes the disabled cond's constraints through the
       producers so the empty meets land on the counters. *)
    let constrained = constrain_edge ~env ~landmarks disabled in
    if not (AI.equal constrained AI.bottom) then begin
      let seeds = cond_seeds ~env:constrained disabled in
      (* Without seeds the observer, which never inverts memory defs,
         reaches no leaf meet: skip the walk and its prefix replay. *)
      if not (Core.Set.is_empty seeds) then
        ignore
          (walk ~locus:observer_locus ~cache ~entry ~landmarks ~witness ~seeds
             constrained blk)
    end
  end

let refine_edge_inline
    ~(entry : AI.t)
    ~(rctx : Cbat_runctx.refine_ctx)
    ~(discarded : bool)
    (b : blk term) (env : AI.t) (acc_cond : exp)
    : AI.t =
  let env_in = env in
  let env = constrain_edge ~env ~landmarks:rctx.rc_landmarks acc_cond in
  (* No constraint derived: nothing to deliver. *)
  if discarded then env_in
  else if AI.equal env AI.bottom then env
  else
    let seeds = cond_seeds ~env acc_cond in
    if Core.Set.is_empty seeds then env
    else
      Stages.time `Walk (fun () ->
          refine_edge ~entry ~rctx ~seeds env b)
