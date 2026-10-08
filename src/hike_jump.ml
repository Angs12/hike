(* The jump compiler: each jump's cond becomes the simplest equivalent
   expression over values.  A backward pass substitutes the defs it
   passes into the cond — a def replaces its var, so every var left
   reads the value at the walked position — and simplifies after each
   step; the walk continues into a unique goto predecessor.  The
   smallest flag-free form wins: inlined at the jump when its vars still
   hold those values there, else bound to a fresh comparison def at its
   own position.  No flag-free form keeps the cond. *)

open Bap.Std
open Bap_core_theory
open Core

(* The status flags, identified by the target's register roles. *)
let flag_vars (target : Theory.Target.t) : var list =
  let role r = Option.map ~f:Var.reify (Theory.Target.reg target r) in
  let open Theory.Role.Register in
  List.filter_opt
    [ role zero_flag; role carry_flag; role sign_flag; role overflow_flag;
      role parity_flag ]

let is_flag (flags : var list) (v : var) : bool = List.exists flags ~f:(Var.same v)

let rec size (e : exp) : int =
  match e with
  | Bil.Var _ | Bil.Int _ | Bil.Unknown _ -> 1
  | Bil.Load (m, a, _, _) -> 1 + size m + size a
  | Bil.Store (m, a, v, _, _) -> 1 + size m + size a + size v
  | Bil.BinOp (_, a, b) | Bil.Concat (a, b) | Bil.Let (_, a, b) -> 1 + size a + size b
  | Bil.UnOp (_, a) | Bil.Cast (_, _, a) | Bil.Extract (_, _, a) -> 1 + size a
  | Bil.Ite (c, a, b) -> 1 + size c + size a + size b

let rec has_unknown (e : exp) : bool =
  match e with
  | Bil.Unknown _ -> true
  | Bil.Var _ | Bil.Int _ -> false
  | Bil.Load (m, a, _, _) -> has_unknown m || has_unknown a
  | Bil.Store (m, a, v, _, _) -> has_unknown m || has_unknown a || has_unknown v
  | Bil.BinOp (_, a, b) | Bil.Concat (a, b) | Bil.Let (_, a, b) ->
    has_unknown a || has_unknown b
  | Bil.UnOp (_, a) | Bil.Cast (_, _, a) | Bil.Extract (_, _, a) -> has_unknown a
  | Bil.Ite (c, a, b) -> has_unknown c || has_unknown a || has_unknown b

(* [e] with [v] read as [r]; a Let binding [v] shadows it in its body. *)
let rec subst (v : var) (r : exp) (e : exp) : exp =
  let s = subst v r in
  match e with
  | Bil.Var x when Var.same x v -> r
  | Bil.Var _ | Bil.Int _ | Bil.Unknown _ -> e
  | Bil.Load (m, a, en, sz) -> Bil.Load (s m, s a, en, sz)
  | Bil.Store (m, a, x, en, sz) -> Bil.Store (s m, s a, s x, en, sz)
  | Bil.BinOp (op, a, b) -> Bil.BinOp (op, s a, s b)
  | Bil.UnOp (op, a) -> Bil.UnOp (op, s a)
  | Bil.Cast (c, n, a) -> Bil.Cast (c, n, s a)
  | Bil.Extract (hi, lo, a) -> Bil.Extract (hi, lo, s a)
  | Bil.Concat (a, b) -> Bil.Concat (s a, s b)
  | Bil.Ite (c, a, b) -> Bil.Ite (s c, s a, s b)
  | Bil.Let (x, a, b) -> Bil.Let (x, s a, if Var.same x v then b else s b)

(* The width of an immediate exp, by BAP's type inference. *)
let width_of_exp (e : exp) : int option =
  match Type.infer e with Ok (Type.Imm n) -> Some n | _ -> None

let zero_of (e : exp) : exp option =
  Option.map ~f:(fun n -> Bil.Int (Word.zero n)) (width_of_exp e)

let is_zero = function Bil.Int w -> Word.is_zero w | _ -> false

let is_ones = function
  | Bil.Int w -> Word.equal w (Word.ones (Word.bitwidth w))
  | _ -> false

let bool_exp (b : bool) : exp = Bil.Int (if b then Word.b1 else Word.b0)

(* The relation lattice: a relation admits a subset of the orderings over
   its operand pair; the complement and the connectives are
   componentwise. *)
type rel = LT | LE | EQ | NEQ | GT | GE

let rel_bits = function
  | LT -> (true, false, false) | LE -> (true, true, false)
  | EQ -> (false, true, false) | NEQ -> (true, false, true)
  | GT -> (false, false, true) | GE -> (false, true, true)

let rel_complement = function
  | LT -> GE | GE -> LT | LE -> GT | GT -> LE | EQ -> NEQ | NEQ -> EQ

let rel_flip = function
  | LT -> GT | GT -> LT | LE -> GE | GE -> LE | EQ -> EQ | NEQ -> NEQ

(* A relation over (a, b); [signed] is [None] for the equalities. *)
type atom = { r : rel; signed : bool option; a : exp; b : exp }

let atom_of (e : exp) : atom option =
  match e with
  | Bil.BinOp (Bil.LT, a, b) -> Some { r = LT; signed = Some false; a; b }
  | Bil.BinOp (Bil.LE, a, b) -> Some { r = LE; signed = Some false; a; b }
  | Bil.BinOp (Bil.SLT, a, b) -> Some { r = LT; signed = Some true; a; b }
  | Bil.BinOp (Bil.SLE, a, b) -> Some { r = LE; signed = Some true; a; b }
  | Bil.BinOp (Bil.EQ, a, b) -> Some { r = EQ; signed = None; a; b }
  | Bil.BinOp (Bil.NEQ, a, b) -> Some { r = NEQ; signed = None; a; b }
  | _ -> None

(* GT/GE render operand-swapped; signedness picks the operator. *)
let render (t : atom) : exp =
  let s = Option.value t.signed ~default:false in
  let op =
    match t.r with
    | LT | GT -> if s then Bil.SLT else Bil.LT
    | LE | GE -> if s then Bil.SLE else Bil.LE
    | EQ -> Bil.EQ
    | NEQ -> Bil.NEQ in
  let x, y = match t.r with GT | GE -> (t.b, t.a) | _ -> (t.a, t.b) in
  Bil.BinOp (op, x, y)

(* Two relations over one operand pair (either orientation, compatible
   signedness) meet or join componentwise. *)
let combine ~(or_ : bool) (u : atom) (v : atom) : exp option =
  let signed =
    match u.signed, v.signed with
    | Some x, Some y -> if Bool.equal x y then Some (Some x) else None
    | Some x, None | None, Some x -> Some (Some x)
    | None, None -> Some None in
  let v =
    if Exp.equal u.a v.a && Exp.equal u.b v.b then Some v
    else if Exp.equal u.a v.b && Exp.equal u.b v.a then
      Some { v with r = rel_flip v.r; a = v.b; b = v.a }
    else None in
  match signed, v with
  | Some signed, Some v ->
    let f = if or_ then ( || ) else ( && ) in
    let (b1, e1, g1) = rel_bits u.r and (b2, e2, g2) = rel_bits v.r in
    (match f b1 b2, f e1 e2, f g1 g2 with
     | true, true, true -> Some (bool_exp true)
     | false, false, false -> Some (bool_exp false)
     | true, false, false -> Some (render { u with r = LT; signed })
     | true, true, false -> Some (render { u with r = LE; signed })
     | false, true, false -> Some (render { u with r = EQ; signed })
     | true, false, true -> Some (render { u with r = NEQ; signed })
     | false, false, true -> Some (render { u with r = GT; signed })
     | false, true, true -> Some (render { u with r = GE; signed }))
  | _ -> None

let fold_binop op a b =
  match op, b with
  | (Bil.DIVIDE | Bil.SDIVIDE | Bil.MOD | Bil.SMOD), b when Word.is_zero b -> None
  | _ -> Option.try_with (fun () -> Bil.Apply.binop op a b)

(* The connective chain of one operator, flattened. *)
let rec chain (op : binop) (e : exp) : exp list =
  match e with
  | Bil.BinOp (op', a, b) when Poly.equal op op' -> chain op a @ chain op b
  | e -> [ e ]

(* [s] the sign of a - b and [o] its overflow, (a ^ b) & (a ^ (a - b)),
   each as the signed test against zero: their xor is a <s b. *)
let signed_borrow (s : exp) (o : exp) : exp option =
  match s, o with
  | Bil.BinOp (Bil.SLT, (Bil.BinOp (Bil.MINUS, a, b) as d), z1),
    Bil.BinOp
      ( Bil.SLT
      , Bil.BinOp (Bil.AND, Bil.BinOp (Bil.XOR, a1, b1), Bil.BinOp (Bil.XOR, a2, d'))
      , z2 )
    when is_zero z1 && is_zero z2 && Exp.equal a a1 && Exp.equal b b1
         && Exp.equal a a2 && Exp.equal d d' ->
    Some (Bil.BinOp (Bil.SLT, a, b))
  | _ -> None

(* One rewrite at the node; [None] when no rule applies.  Every rule is an
   exact equivalence. *)
let rewrite (e : exp) : exp option =
  match e with
  (* constants *)
  | Bil.BinOp (op, Bil.Int a, Bil.Int b) ->
    Option.map (fold_binop op a b) ~f:(fun w -> Bil.Int w)
  | Bil.UnOp (op, Bil.Int a) -> Some (Bil.Int (Bil.Apply.unop op a))
  | Bil.Cast (c, n, Bil.Int a) -> Some (Bil.Int (Bil.Apply.cast c n a))
  | Bil.Extract (hi, lo, Bil.Int a) -> Some (Bil.Int (Word.extract_exn ~hi ~lo a))
  | Bil.Concat (Bil.Int a, Bil.Int b) -> Some (Bil.Int (Word.concat a b))
  | Bil.Ite (Bil.Int c, a, b) -> Some (if Word.is_one c then a else b)
  (* the sign bit is the signed test against zero *)
  | Bil.Cast (Bil.HIGH, 1, a) when Option.exists (width_of_exp a) ~f:(fun n -> n > 1) ->
    Option.map (zero_of a) ~f:(fun z -> Bil.BinOp (Bil.SLT, a, z))
  (* integer identities *)
  | Bil.BinOp ((Bil.XOR | Bil.MINUS), a, b) when Exp.equal a b -> zero_of a
  | Bil.BinOp (Bil.AND, a, b) when is_zero a -> Some a
  | Bil.BinOp (Bil.AND, a, b) when is_zero b -> Some b
  | Bil.BinOp (Bil.AND, a, b) when is_ones a -> Some b
  | Bil.BinOp (Bil.AND, a, b) when is_ones b -> Some a
  | Bil.BinOp (Bil.OR, a, b) when is_ones a -> Some a
  | Bil.BinOp (Bil.OR, a, b) when is_ones b -> Some b
  | Bil.BinOp ((Bil.OR | Bil.XOR | Bil.PLUS), a, b) when is_zero a -> Some b
  | Bil.BinOp ((Bil.OR | Bil.XOR | Bil.PLUS | Bil.MINUS), a, b) when is_zero b -> Some a
  | Bil.BinOp ((Bil.AND | Bil.OR), a, b) when Exp.equal a b -> Some a
  | Bil.UnOp (Bil.NOT, Bil.UnOp (Bil.NOT, a)) -> Some a
  (* relations *)
  | Bil.BinOp ((Bil.EQ | Bil.LE | Bil.SLE), a, b) when Exp.equal a b -> Some (bool_exp true)
  | Bil.BinOp ((Bil.NEQ | Bil.LT | Bil.SLT), a, b) when Exp.equal a b -> Some (bool_exp false)
  | Bil.BinOp (((Bil.EQ | Bil.NEQ) as op), (Bil.Int _ as k), a) when
      (match a with Bil.Int _ -> false | _ -> true) ->
    Some (Bil.BinOp (op, a, k))
  | Bil.BinOp (((Bil.EQ | Bil.NEQ) as op), a, (Bil.Int k as z))
    when Word.is_zero k
         && not (Option.equal Int.equal (width_of_exp a) (Some (Word.bitwidth k))) ->
    Option.bind (zero_of a) ~f:(fun z' ->
        if Exp.equal z z' then None else Some (Bil.BinOp (op, a, z')))
  | Bil.BinOp (((Bil.EQ | Bil.NEQ) as op), Bil.BinOp (Bil.MINUS, a, b), z) when is_zero z ->
    Some (Bil.BinOp (op, a, b))
  | Bil.UnOp (Bil.NOT, r) ->
    Option.map (atom_of r) ~f:(fun t -> render { t with r = rel_complement t.r })
  (* the xor core: (p | q) & ~(p & q) *)
  | Bil.BinOp
      (Bil.AND, Bil.BinOp (Bil.OR, p, q), Bil.UnOp (Bil.NOT, Bil.BinOp (Bil.AND, p', q')))
    when (Exp.equal p p' && Exp.equal q q') || (Exp.equal p q' && Exp.equal q p') ->
    Some (Bil.BinOp (Bil.XOR, p, q))
  (* the signed borrow: sign(a - b) xor overflow(a - b) is a <s b *)
  | Bil.BinOp (Bil.XOR, p, q) when Option.is_some (signed_borrow p q) ->
    signed_borrow p q
  | Bil.BinOp (Bil.XOR, p, q) when Option.is_some (signed_borrow q p) ->
    signed_borrow q p
  (* connectives over relations *)
  | Bil.BinOp (((Bil.OR | Bil.AND) as op), _, _) ->
    let or_ = Poly.equal op Bil.OR in
    let terms = chain op e in
    let rec pair acc = function
      | [] -> None
      | x :: rest ->
        let hit =
          List.find_mapi rest ~f:(fun i y ->
              match atom_of x, atom_of y with
              | Some u, Some v ->
                Option.map (combine ~or_ u v) ~f:(fun c -> (i, c))
              | _ -> None) in
        (match hit with
         | Some (i, c) ->
           let rest = List.filteri rest ~f:(fun k _ -> k <> i) in
           Some (List.rev_append acc (c :: rest))
         | None -> pair (x :: acc) rest) in
    Option.map (pair [] terms) ~f:(fun ts ->
        List.reduce_exn ts ~f:(fun a b -> Bil.BinOp (op, a, b)))
  | _ -> None

let rec simplify (e : exp) : exp =
  let s = simplify in
  let e =
    match e with
    | Bil.Var _ | Bil.Int _ | Bil.Unknown _ -> e
    | Bil.Load (m, a, en, sz) -> Bil.Load (s m, s a, en, sz)
    | Bil.Store (m, a, x, en, sz) -> Bil.Store (s m, s a, s x, en, sz)
    | Bil.BinOp (op, a, b) -> Bil.BinOp (op, s a, s b)
    | Bil.UnOp (op, a) -> Bil.UnOp (op, s a)
    | Bil.Cast (c, n, a) -> Bil.Cast (c, n, s a)
    | Bil.Extract (hi, lo, a) -> Bil.Extract (hi, lo, s a)
    | Bil.Concat (a, b) -> Bil.Concat (s a, s b)
    | Bil.Ite (c, a, b) -> Bil.Ite (s c, s a, s b)
    | Bil.Let (x, a, b) -> Bil.Let (x, s a, s b) in
  match rewrite e with Some e' -> simplify e' | None -> e

(* A substituted cond past this size ends the walk. *)
let size_cap = 128

type edge = Goto_edge | Other_edge

(* Every block's incoming edges, by source block. *)
let preds_of (sub : sub term) : (tid * edge) list Tid.Map.t =
  Term.enum blk_t sub
  |> Seq.fold ~init:Tid.Map.empty ~f:(fun m b ->
      Term.enum jmp_t b
      |> Seq.fold ~init:m ~f:(fun m j ->
          let add t k = Core.Map.add_multi m ~key:t ~data:(Term.tid b, k) in
          match Jmp.kind j with
          | Goto (Direct t) -> add t Goto_edge
          | Call c ->
            (match Call.return c with Some (Direct t) -> add t Other_edge | _ -> m)
          | Ret (Direct t) | Int (_, t) -> add t Other_edge
          | Goto (Indirect _) | Ret (Indirect _) -> m))

(* A cond's form at one position: insert before [at] in [blk] (or inline
   at the jump); [hops] counts the blocks back from the jump. *)
type candidate = {
  cond : exp;
  blk : tid;
  at : tid option;
  hops : int;
  pos : int;
  inline : bool;
  consumed : Var.Set.t;
}

let order (c : candidate) = (size c.cond, (if c.inline then 0 else 1), c.hops, - c.pos)

let acceptable (flags : var list) (e : exp) : bool =
  (not (has_unknown e))
  && not (Core.Set.exists (Exp.free_vars e) ~f:(is_flag flags))

(* The backward walk over [j]'s block and its unique goto predecessors;
   the best candidate, if any improves on the cond. *)
let compile_jmp ~(flags : var list) ~(blocks : blk term Tid.Map.t)
    ~(preds : (tid * edge) list Tid.Map.t) ~(entry : tid option)
    (b0 : blk term) (j : jmp term) : candidate option =
  let orig = Jmp.cond j in
  if Core.Set.is_empty (Exp.free_vars orig) then None
  else
    let start =
      if acceptable flags orig then
        [ { cond = orig; blk = Term.tid b0; at = None; hops = 0; pos = Int.max_value;
            inline = true; consumed = Var.Set.empty } ]
      else [] in
    let unique_goto_pred (b : tid) : tid option =
      if Option.exists entry ~f:(Tid.equal b) then None
      else
        match Core.Map.find_multi preds b with
        | (p, Goto_edge) :: rest
          when List.for_all rest ~f:(fun (q, k) ->
              Tid.equal p q && (match k with Goto_edge -> true | Other_edge -> false)) ->
          Some p
        | _ -> None in
    (* [later]: the vars defined between this block's end and the jump. *)
    let rec walk e consumed (blk : blk term) hops later visited cands =
      let defs = Term.enum def_t blk |> Seq.to_list in
      let n = List.length defs in
      let e, consumed, cands, defined, stop =
        List.foldi (List.rev defs) ~init:(e, consumed, cands, later, false)
          ~f:(fun k (e, consumed, cands, defined, stop) d ->
              let lhs = Def.lhs d in
              let defined = Core.Set.add defined (Var.base lhs) in
              if stop || not (Core.Set.exists (Exp.free_vars e) ~f:(Var.same lhs))
              then (e, consumed, cands, defined, stop)
              else
                let e = simplify (subst lhs (Def.rhs d) e) in
                let consumed =
                  if is_flag flags lhs then Core.Set.add consumed lhs else consumed in
                if size e > size_cap then (e, consumed, cands, defined, true)
                else
                  let cands =
                    if acceptable flags e then
                      { cond = e; blk = Term.tid blk; at = Some (Term.tid d); hops;
                        pos = n - 1 - k;
                        inline =
                          not (Core.Set.exists (Exp.free_vars e) ~f:(fun v ->
                              Core.Set.mem defined (Var.base v)));
                        consumed } :: cands
                    else cands in
                  (e, consumed, cands, defined, false)) in
      if stop then cands
      else
        match unique_goto_pred (Term.tid blk) with
        | Some p when not (Core.Set.mem visited p) ->
          (match Core.Map.find blocks p with
           | Some pb -> walk e consumed pb (hops + 1) defined (Core.Set.add visited p) cands
           | None -> cands)
        | _ -> cands in
    let cands =
      walk orig Var.Set.empty b0 0 Var.Set.empty
        (Tid.Set.singleton (Term.tid b0)) start in
    match List.min_elt cands ~compare:(fun x y -> Poly.compare (order x) (order y)) with
    | Some c when not (Exp.equal c.cond orig) -> Some c
    | _ -> None

let uses_of ~(abi : Hike_abi.t) (s : sub term) : Var.Set.t =
  Hike_stack_model.sub_reads ~abi s

(* Compiles every jump's cond, then drops every def of a consumed flag var
   no read survives.  A compiled cond that reads memory, or whose vars are
   rewritten before the jump, is bound to a fresh 1-bit def at its own
   position — the VSA tags the def, and the tag licenses the emitter's
   frame addressing. *)
let compile_sub (target : Theory.Target.t) (sub : sub term) : sub term =
  let abi = Hike_abi.of_target target in
  let flags = flag_vars target in
  let preds = preds_of sub in
  let entry = Option.map (Term.first blk_t sub) ~f:Term.tid in
  let blocks =
    Term.enum blk_t sub
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m b -> Core.Map.set m ~key:(Term.tid b) ~data:b) in
  let plans =
    Term.enum blk_t sub
    |> Seq.concat_map ~f:(fun b ->
        Term.enum jmp_t b
        |> Seq.filter_map ~f:(fun j ->
            Option.map (compile_jmp ~flags ~blocks ~preds ~entry b j)
              ~f:(fun c -> (Term.tid j, c))))
    |> Seq.to_list in
  if List.is_empty plans then sub
  else
    let conds, inserts =
      List.fold plans ~init:(Tid.Map.empty, []) ~f:(fun (conds, ins) (jt, c) ->
          if c.inline && not (Hike_stack_model.reads_mem c.cond) then
            (Core.Map.set conds ~key:jt ~data:c.cond, ins)
          else
            let d = Def.create (Hike_synth.fresh ~bits:1 Hike_synth.Comparison) c.cond in
            (Core.Map.set conds ~key:jt ~data:(Bil.Var (Def.lhs d)), (c, d) :: ins)) in
    let consumed =
      List.fold plans ~init:Var.Set.empty ~f:(fun acc (_, c) -> Core.Set.union acc c.consumed) in
    let sub1 =
      Term.map blk_t sub ~f:(fun blk ->
          let blk =
            List.fold inserts ~init:blk ~f:(fun blk (c, d) ->
                if not (Tid.equal c.blk (Term.tid blk)) then blk
                else
                  match c.at with
                  | Some before -> Term.prepend def_t ~before blk d
                  | None -> Term.append def_t blk d) in
          Term.map jmp_t blk ~f:(fun j ->
              match Core.Map.find conds (Term.tid j) with
              | Some c -> Jmp.with_cond j c
              | None -> j)) in
    let dead = Core.Set.diff consumed (uses_of ~abi sub1) in
    if Core.Set.is_empty dead then sub1
    else
      Term.map blk_t sub1 ~f:(fun blk ->
          Term.filter def_t blk ~f:(fun d -> not (Core.Set.mem dead (Def.lhs d))))
