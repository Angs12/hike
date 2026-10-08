(* Backward substitution: an exp read at a block's end, re-read at each
   earlier position.  The walk passes the block's defs backward — and on
   into a unique goto predecessor — and substitutes each def into the
   exp, so every var left reads its value at the walked position; each
   step is simplified by exact rewrites.  The forms are the exp's
   equivalents, one per position, for a consumer to choose from. *)

open Bap.Std
open Core

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

(* Every block's incoming edges, by source block: the BIR's jumps.  An
   indirect transfer names none. *)
let preds_of (sub : sub term) : (tid * edge) list Tid.Map.t =
  Term.enum blk_t sub
  |> Seq.fold ~init:Tid.Map.empty ~f:(fun m b ->
      Term.enum jmp_t b
      |> Seq.fold ~init:m ~f:(fun m j ->
          let add m t k = Core.Map.add_multi m ~key:t ~data:(Term.tid b, k) in
          match Jmp.kind j with
          | Goto (Direct t) -> add m t Goto_edge
          | Call c ->
            (match Call.return c with Some (Direct t) -> add m t Other_edge | _ -> m)
          | Ret (Direct t) | Int (_, t) -> add m t Other_edge
          | Goto (Indirect _) | Ret (Indirect _) -> m))

(* The exp's value read at one position: before [at] in [blk], or at
   the block's end with no [at] (the start).  [hops] counts the blocks
   back from the start; [pos] orders positions within a block (later is
   larger); [written] are the vars defined between the position and the
   start; [substituted] are the vars whose defs the walk substituted. *)
type form = {
  exp : exp;
  blk : blk term;
  at : def term option;
  hops : int;
  pos : int;
  written : Var.Set.t;
  substituted : Var.Set.t;
}

(* [e], read at [f]'s position, reads the same value at the start: none
   of its vars is written in between. *)
let holds (f : form) (e : exp) : bool =
  not (Core.Set.exists (Exp.free_vars e) ~f:(fun v -> Core.Set.mem f.written (Var.base v)))

type graph = {
  blocks : blk term Tid.Map.t;
  preds : (tid * edge) list Tid.Map.t;
  entry : tid option;
}

let graph_of_sub (sub : sub term) : graph =
  { blocks =
      Term.enum blk_t sub
      |> Seq.fold ~init:Tid.Map.empty ~f:(fun m b ->
          Core.Map.set m ~key:(Term.tid b) ~data:b);
    preds = preds_of sub;
    entry = Option.map (Term.first blk_t sub) ~f:Term.tid }

let unique_goto_pred (g : graph) (b : tid) : tid option =
  if Option.exists g.entry ~f:(Tid.equal b) then None
  else
    match Core.Map.find_multi g.preds b with
    | (p, Goto_edge) :: rest
      when List.for_all rest ~f:(fun (q, k) ->
          Tid.equal p q && (match k with Goto_edge -> true | Other_edge -> false)) ->
      Some p
    | _ -> None

(* Every form of [e] read at the end of [b0], the start first, then one
   per substituting def, nearest first.  A form past [size_cap] ends the
   walk. *)
let forms (g : graph) (b0 : blk term) (e : exp) : form list =
  let start =
    { exp = e; blk = b0; at = None; hops = 0; pos = Int.max_value;
      written = Var.Set.empty; substituted = Var.Set.empty } in
  (* [later]: the vars defined between this block's end and the start. *)
  let rec walk e substituted (blk : blk term) hops later visited acc =
    let defs = Term.enum def_t blk |> Seq.to_list in
    let n = List.length defs in
    let e, substituted, acc, defined, stop =
      List.foldi (List.rev defs) ~init:(e, substituted, acc, later, false)
        ~f:(fun k (e, substituted, acc, defined, stop) d ->
            let lhs = Def.lhs d in
            let defined = Core.Set.add defined (Var.base lhs) in
            if stop || not (Core.Set.exists (Exp.free_vars e) ~f:(Var.same lhs))
            then (e, substituted, acc, defined, stop)
            else
              let e = simplify (subst lhs (Def.rhs d) e) in
              let substituted = Core.Set.add substituted lhs in
              if size e > size_cap then (e, substituted, acc, defined, true)
              else
                let f =
                  { exp = e; blk; at = Some d; hops; pos = n - 1 - k;
                    written = defined; substituted } in
                (e, substituted, f :: acc, defined, false)) in
    if stop then acc
    else
      match unique_goto_pred g (Term.tid blk) with
      | Some p when not (Core.Set.mem visited p) ->
        (match Core.Map.find g.blocks p with
         | Some pb -> walk e substituted pb (hops + 1) defined (Core.Set.add visited p) acc
         | None -> acc)
      | _ -> acc in
  if Core.Set.is_empty (Exp.free_vars e) then [ start ]
  else
    start :: List.rev
      (walk e Var.Set.empty b0 0 Var.Set.empty (Tid.Set.singleton (Term.tid b0)) [])

(* Binds each form's exp to its var by a def at the form's position:
   before [at], or appended at the block's end. *)
let bind (sub : sub term) (binds : (form * var) list) : sub term =
  if List.is_empty binds then sub
  else
    Term.map blk_t sub ~f:(fun blk ->
        List.fold binds ~init:blk ~f:(fun blk (f, v) ->
            if not (Tid.equal (Term.tid f.blk) (Term.tid blk)) then blk
            else
              let d = Def.create v f.exp in
              match f.at with
              | Some before -> Term.prepend def_t ~before:(Term.tid before) blk d
              | None -> Term.append def_t blk d))
