(* The jump compiler (construction): a BIR→BIR term transformation
   that REDESIGNS jcc flag idioms into the SIMPLEST equivalent value
   comparisons (never a relocation of the flag decoding).  The flag
   semantics lives HERE ONCE — the flag-effects table below.  Identity
   on the residual: a cond with no single reaching flag def, an
   unknown shape, or an inconsistent fact set keeps the current path
   unchanged (no gates, no fallbacks, no partial rewrites).  The pass
   runs FIRST in the analysis chain (after hike-filter, before
   hike-vsa), so every downstream consumer reads value comparisons
   where the rewrite fired. *)

open Bap.Std
open Bap_core_theory
open Core

(* The flag-effects table: the flag defs as the lifter emits them.
   ZF := 0 = d               ZF ⇔ d = 0      (also ZF := 1 / := 0)
   CF := a < b               CF ⇔ a <u b     (sub/cmp borrow)
   SF := high:1[e]           SF ⇔ sign bit of e
   OF := high:1[(x^y)&(x^d)] OF ⇔ signed overflow of x−y, d = x−y
   OF := 0                  the test/and group: OF ≡ 0, so the
                            signed families run on SF alone
   Anything else (add/imul/shift carries, PF/AF forms, unknown[bits])
   is NOT consumed — conds over those shapes stay residual. *)

(* Cond boolean structure over flag vars (BIR conds are pure AND/OR/NOT
   over 1-bit vars; anything else fails to parse and stays residual). *)
type bexp = V of var | N of bexp | A of bexp * bexp | O of bexp * bexp

(* The flags the compiler consumes, identified by the target's register
   roles (never a register name).  A flag the target does not register
   has no var — conds over it stay residual. *)
type flag = ZF | CF | SF | OF

type flag_vars = {
  zf : var option;
  cf : var option;
  sf : var option;
  of_ : var option;
}

let flag_vars (target : Theory.Target.t) : flag_vars =
  let role r = Option.map ~f:Var.reify (Theory.Target.reg target r) in
  let open Theory.Role.Register in
  {
    zf = role zero_flag;
    cf = role carry_flag;
    sf = role sign_flag;
    of_ = role overflow_flag;
  }

let is_flag (fv : flag_vars) (f : flag) (v : var) : bool =
  let same = Option.exists ~f:(Var.same v) in
  match f with
  | ZF -> same fv.zf
  | CF -> same fv.cf
  | SF -> same fv.sf
  | OF -> same fv.of_

let parse_bexp (e : exp) : bexp option =
  let rec go e =
    match e with
    | Bil.Var v -> (match Var.typ v with Type.Imm 1 -> Some (V v) | _ -> None)
    | Bil.UnOp (Bil.NOT, e) -> Option.map ~f:(fun b -> N b) (go e)
    | Bil.BinOp (Bil.AND, a, b) -> pair (fun x y -> A (x, y)) a b
    | Bil.BinOp (Bil.OR, a, b) -> pair (fun x y -> O (x, y)) a b
    | _ -> None
  and pair c a b =
    match (go a, go b) with
    | Some a, Some b -> Some (c a b)
    | _ -> None in
  go e

(* The signed xor core: (SF|OF) & ~(SF&OF) — OF xor SF. *)
let is_xor_core (fv : flag_vars) (b : bexp) : bool =
  match b with
  | A (O (V sf1, V of1), N (A (V sf2, V of2))) ->
      is_flag fv SF sf1 && is_flag fv OF of1
      && is_flag fv SF sf2 && is_flag fv OF of2
  | _ -> false

(* Per-block flag facts. *)

type zf_fact = Zero of exp | Zconst of bool

type cf_fact = Ult of exp * exp | Cconst of bool

type facts = {
  zf : zf_fact option; (* ZF ⇔ (d = 0) / constant *)
  cf : cf_fact option; (* CF ⇔ (a <u b) / constant *)
  sf : exp option; (* SF ⇔ sign bit of e *)
  ovf : (exp * exp * exp) option; (* OF ⇔ signed overflow of x−y, d = x−y *)
  and_form : bool; (* OF := 0 — the test/and group (OF identically 0) *)
}

let empty_facts = { zf = None; cf = None; sf = None; ovf = None; and_form = false }

(* Width of an exp: the width of its free vars (operands are
   width-uniform in BIR); a bare immediate is its own width. *)
let width_of_exp (e : exp) : int option =
  match e with
  | Bil.Int w -> Some (Word.bitwidth w)
  | _ -> (
      let vs = Exp.free_vars e in
      if Core.Set.is_empty vs then None
      else
        let v = Option.value_exn (Core.Set.min_elt vs) in
        match Var.typ v with Type.Imm n -> Some n | _ -> None)

let zero_exp (e : exp) : exp option =
  match width_of_exp e with Some n -> Some (Bil.Int (Word.zero n)) | None -> None

let is_zero_int = function Bil.Int w -> Word.is_zero w | _ -> false

let is_one_int = function Bil.Int w -> Word.is_one w | _ -> false

(* Fact extraction from one flag def rhs (the table above).  Called
   once per flag — on its single reaching def (the block's last def of
   the flag var); [None] when the shape is unknown (the flag gets no
   fact and conds over it stay residual). *)
let extract_facts (fl : flag) (rhs : exp) (f : facts) : facts option =
  match (fl, rhs) with
  | ZF, Bil.BinOp (Bil.EQ, a, b) when is_zero_int a -> (
      match f.zf with None -> Some { f with zf = Some (Zero b) } | _ -> None)
  | ZF, Bil.BinOp (Bil.EQ, a, b) when is_zero_int b -> (
      match f.zf with None -> Some { f with zf = Some (Zero a) } | _ -> None)
  | ZF, e when is_one_int e -> (
      match f.zf with None -> Some { f with zf = Some (Zconst true) } | _ -> None)
  | ZF, e when is_zero_int e -> (
      match f.zf with None -> Some { f with zf = Some (Zconst false) } | _ -> None)
  | CF, Bil.BinOp (Bil.LT, a, b) -> (
      match f.cf with None -> Some { f with cf = Some (Ult (a, b)) } | _ -> None)
  | CF, e when is_zero_int e -> (
      match f.cf with None -> Some { f with cf = Some (Cconst false) } | _ -> None)
  | SF, Bil.Cast (Bil.HIGH, 1, e) -> (
      match f.sf with None -> Some { f with sf = Some e } | _ -> None)
  | ( OF
    , Bil.Cast
        ( Bil.HIGH
        , 1
        , Bil.BinOp (Bil.AND, Bil.BinOp (Bil.XOR, x, y), Bil.BinOp (Bil.XOR, x2, d)) ) )
    when Exp.equal x x2 -> (
      match f.ovf with None -> Some { f with ovf = Some (x, y, d) } | _ -> None)
  (* test/and: OF is identically 0 — the group's signed identity is SF
     alone. *)
  | OF, e when is_zero_int e ->
    if f.and_form then None else Some { f with and_form = true }
  | _ -> None

(* Block context: single-def value rhs (for CONSISTENCY CHECKS only —
   the emitted comparison REUSES the var, never re-substitutes). *)

type ctx = { rhs : exp Var.Map.t; xrhs : exp Var.Map.t }

(* [rhs] keys the block's own single defs; [xrhs] keys (by base var)
   the unique reaching defs from predecessor blocks. *)
let resolve_exp (c : ctx) (e : exp) : exp =
  match e with
  | Bil.Var v -> (
      match Core.Map.find c.rhs v with
      | Some r -> r
      | None -> Option.value (Core.Map.find c.xrhs (Var.base v)) ~default:e)
  | _ -> e

let same_exp (c : ctx) (a : exp) (b : exp) : bool =
  Exp.equal (resolve_exp c a) (resolve_exp c b)

(* The overflow pattern is only the sub-overflow predicate when its
   diff exp IS (x − y) — resolved. *)
let is_minus_xy (c : ctx) (e : exp) (x : exp) (y : exp) : bool =
  match resolve_exp c e with
  | Bil.BinOp (Bil.MINUS, a, b) -> Exp.equal a x && Exp.equal b y
  | _ -> false

(* The rewrite. *)

let const_cond (b : bool) : exp = Bil.Int (if b then Word.one 1 else Word.zero 1)

(* The cond algebra: the parsed bexp compiles by SUBSTITUTION over the
   flag facts — each leaf becomes an atom, NOT is the complement, and
   AND/OR combine two relations when both range over the same two
   values.  Everything else stays residual (the identity). *)

(* The relation lattice: a relation admits a subset of the orderings
   less/equal/greater over its operand pair; the complement and the
   connectives are componentwise. *)
type rel = LT | LE | EQ | NEQ | GT | GE

let rel_bits = function
  | LT -> (true, false, false) | LE -> (true, true, false)
  | EQ -> (false, true, false) | NEQ -> (true, false, true)
  | GT -> (false, false, true) | GE -> (false, true, true)

let rel_complement = function
  | LT -> GE | GE -> LT | LE -> GT | GT -> LE | EQ -> NEQ | NEQ -> EQ

let rel_of_bits = function
  | true, false, false -> Some LT | true, true, false -> Some LE
  | false, true, false -> Some EQ | true, false, true -> Some NEQ
  | false, false, true -> Some GT | false, true, true -> Some GE
  | true, true, true | false, false, false -> None

(* An atom: a constant truth, or one relation over two values (the
   flag picks signed vs unsigned).  The pair is the two values the
   relation ranges over — the connectives' agreement key.  An emitted
   equality keeps the ZF var form (d = 0); its pair looks through the
   resolved subtraction (d = x − y makes the pair (x, y)). *)
type atom = Const of bool | Rel of rel * bool * exp * exp

type item = { atom : atom; pair : (exp * exp) option; flags : flag list }

let complement_item (i : item) : item =
  { i with
    atom =
      (match i.atom with
       | Const b -> Const (not b)
       | Rel (r, s, a, b) -> Rel (rel_complement r, s, a, b)) }

(* The emitted comparison: GT/GE render operand-swapped (never a
   NOT); signedness picks the operator. *)
let render_atom = function
  | Const b -> const_cond b
  | Rel (r, s, a, b) ->
      let op =
        match r with
        | LT | GT -> if s then Bil.SLT else Bil.LT
        | LE | GE -> if s then Bil.SLE else Bil.LE
        | EQ -> Bil.EQ
        | NEQ -> Bil.NEQ in
      let x, y = match r with GT | GE -> (b, a) | _ -> (a, b) in
      Bil.BinOp (op, x, y)

(* The atoms over the facts.  ZF ⇔ (d = 0): a subtraction compares its
   operands (a−a is constant, the constant stays right), any other d
   is compared to zero at d's own width — d is reused, never
   re-substituted.  CF ⇔ (a <u b) / constant.  SF under OF ≡ 0 is the
   sign alone, e <s 0. *)
let zf_item (c : ctx) (d : exp) : item option =
  let pair =
    match resolve_exp c d with
    | Bil.BinOp (Bil.MINUS, u, v) -> Some (u, v)
    | _ -> Option.map ~f:(fun z -> (d, z)) (zero_exp d) in
  let atom =
    match d with
    | Bil.BinOp (Bil.MINUS, x, y) ->
        if Exp.equal x y then Some (Const true)
        else if is_zero_int x then Some (Rel (EQ, false, y, x))
        else Some (Rel (EQ, false, x, y))
    | _ -> Option.map ~f:(fun z -> Rel (EQ, false, d, z)) (zero_exp d) in
  match (atom, pair) with
  | Some atom, Some pair -> Some { atom; pair = Some pair; flags = [ ZF ] }
  | _ -> None

let sign_item (e : exp) (flags : flag list) : item option =
  match zero_exp e with
  | Some z -> Some { atom = Rel (LT, true, e, z); pair = Some (e, z); flags }
  | None -> None

(* The atom a cond leaf reads over the facts. *)
let flag_item (fv : flag_vars) (c : ctx) (facts : facts) (v : var) : item option =
  if is_flag fv ZF v then
    match facts.zf with
    | Some (Zero d) -> zf_item c d
    | Some (Zconst b) -> Some { atom = Const b; pair = None; flags = [ ZF ] }
    | None -> None
  else if is_flag fv CF v then
    match facts.cf with
    | Some (Ult (a, b)) ->
        Some { atom = Rel (LT, false, a, b); pair = Some (a, b); flags = [ CF ] }
    | Some (Cconst b) -> Some { atom = Const b; pair = None; flags = [ CF ] }
    | None -> None
  else if is_flag fv SF v && facts.and_form then
    match facts.sf with Some e -> sign_item e [ SF ] | None -> None
  else None

(* The xor-core atom: x <s y when the overflow's diff resolves to
   (x − y) and the sign exp to the same diff; with OF ≡ 0 (the
   test/and group) the core is the sign alone. *)
let signed_item (c : ctx) (facts : facts) : item option =
  match (facts.sf, facts.ovf) with
  | Some e, Some (x, y, d) when is_minus_xy c d x y && same_exp c e d ->
      Some { atom = Rel (LT, true, x, y); pair = Some (x, y); flags = [ SF; OF ] }
  | Some e, None when facts.and_form -> sign_item e [ SF; OF ]
  | _ -> None

(* AND/OR over two compiled atoms: constants fold; relations combine
   on the lattice iff both range over the same two values (the pairs
   agree under the block's single-def resolution); an equality side
   carries no signed flavor — the ordering side's operands and
   signedness emit. *)
let combine (c : ctx) ~or_ (u : item) (v : item) : item option =
  let flags = List.append u.flags v.flags in
  let eq r = match r with EQ | NEQ -> true | _ -> false in
  let joined =
    match (u.atom, v.atom) with
    | Const p, Const q -> Some (Const (if or_ then p || q else p && q), None)
    | Const p, r | r, Const p ->
        if Bool.equal p or_ then Some (Const or_, None)
        else (
          let side = match u.atom with Const _ -> v | _ -> u in
          Some (r, side.pair))
    | Rel (r1, s1, x1, y1), Rel (r2, s2, x2, y2)
      when Bool.equal s1 s2 || eq r1 || eq r2 -> (
        match (u.pair, v.pair) with
        | Some (p1, q1), Some (p2, q2)
          when same_exp c p1 p2 && same_exp c q1 q2 -> (
            let f = if or_ then ( || ) else ( && ) in
            let (b1, e1, g1) = rel_bits r1 in
            let (b2, e2, g2) = rel_bits r2 in
            match rel_of_bits (f b1 b2, f e1 e2, f g1 g2) with
            | Some r ->
                let s, x, y, pair =
                  if eq r1 && not (eq r2) then (s2, x2, y2, v.pair)
                  else (s1, x1, y1, u.pair) in
                Some (Rel (r, s, x, y), pair)
            | None -> None)
        | _ -> None)
    | _ -> None in
  Option.map ~f:(fun (atom, pair) -> { atom; pair; flags }) joined

(* The cond's value: the bexp evaluated over the atoms. *)
let rec eval_bexp (fv : flag_vars) (c : ctx) (facts : facts) (b : bexp) :
    item option =
  match b with
  | b when is_xor_core fv b -> signed_item c facts
  | V v -> flag_item fv c facts v
  | N x -> Option.map ~f:complement_item (eval_bexp fv c facts x)
  | A (x, y) -> join fv c facts ~or_:false x y
  | O (x, y) -> join fv c facts ~or_:true x y

and join (fv : flag_vars) (c : ctx) (facts : facts) ~or_ (x : bexp) (y : bexp) :
    item option =
  match (eval_bexp fv c facts x, eval_bexp fv c facts y) with
  | Some x', Some y' -> combine c ~or_ x' y'
  | _ -> None

(* ------------------------------------------------------------------ *)
(* Cross-block reaching definitions                                    *)
(* ------------------------------------------------------------------ *)

type binfo = {
  idefs : (int * def term) list; (* defs in block order *)
  last_pos : int Var.Map.t; (* last def position per var *)
  defined : Var.Set.t; (* vars with a def or phi site here (entry kills) *)
}

(* Reaching state: the unique def site per BASE var, plus the vars
   whose entry value has no unique site (several reaching defs, or a
   phi).  A var absent from both reaches from no site — a live-in
   parameter, whose value is stable. *)
type rstate = { ru : def term Var.Map.t; rm : Var.Set.t }

let rstate_equal (a : rstate) (b : rstate) : bool =
  Var.Map.equal (fun d d' -> Tid.equal (Term.tid d) (Term.tid d')) a.ru b.ru
  && Var.Set.equal a.rm b.rm

let rjoin (a : rstate) (b : rstate) : rstate =
  let keys =
    List.fold_left (Core.Map.to_alist b.ru) ~init:
      (List.fold_left (Core.Map.to_alist a.ru) ~init:(Core.Set.union a.rm b.rm)
         ~f:(fun acc (v, _) -> Core.Set.add acc v))
      ~f:(fun acc (v, _) -> Core.Set.add acc v) in
  Core.Set.fold keys ~init:{ ru = Var.Map.empty; rm = Var.Set.empty }
    ~f:(fun st v ->
        if Core.Set.mem a.rm v || Core.Set.mem b.rm v then
          { st with rm = Core.Set.add st.rm v }
        else
          match (Core.Map.find a.ru v, Core.Map.find b.ru v) with
          | Some d, Some d' ->
              if Tid.equal (Term.tid d) (Term.tid d') then
                { st with ru = Core.Map.set st.ru ~key:v ~data:d }
              else { st with rm = Core.Set.add st.rm v }
          | Some d, None | None, Some d ->
              { st with ru = Core.Map.set st.ru ~key:v ~data:d }
          | None, None -> st)

let rtrans (bin : rstate) (bi : binfo) : rstate =
  let gen =
    List.fold_left bi.idefs ~init:Var.Map.empty
      ~f:(fun acc (_, d) ->
        Core.Map.set acc ~key:(Var.base (Def.lhs d)) ~data:d) in
  let ru =
    Core.Map.to_alist bin.ru
    |> List.filter ~f:(fun (k, _) -> not (Core.Set.mem bi.defined k))
    |> List.fold_left ~init:Var.Map.empty
         ~f:(fun acc (k, d) -> Core.Map.set acc ~key:k ~data:d) in
  let ru =
    Core.Map.to_alist gen
    |> List.fold_left ~init:ru
         ~f:(fun acc (k, d) -> Core.Map.set acc ~key:k ~data:d) in
  let rm =
    Core.Set.filter bin.rm ~f:(fun v -> not (Core.Set.mem bi.defined v)) in
  (* A phi defines its lhs at the entry with no def site — the var's
     entry value stays site-less (multi). *)
  let rm =
    Core.Set.fold bi.defined ~init:rm ~f:(fun s v ->
        if List.exists (Core.Map.to_alist gen) ~f:(fun (v', _) -> Var.equal v' v)
        then s
        else Core.Set.add s v) in
  { ru; rm }

(* The jump targets of a block that are blocks of the sub. *)
let blk_targets (b : blk term) : tid list =
  Term.enum jmp_t b
  |> Seq.fold ~init:[] ~f:(fun acc j ->
         match Jmp.kind j with
         | Goto (Direct t) | Ret (Direct t) -> t :: acc
         | Call c -> (
             match Call.return c with Some (Direct t) -> t :: acc | _ -> acc)
         | Goto (Indirect _) | Ret (Indirect _) | Int _ -> acc)

type xenv = {
  in_state : rstate Tid.Map.t; (* reaching defs at each block entry *)
  bins : binfo Tid.Map.t;
  site : (Tid.t * int) Tid.Map.t; (* def tid -> (block tid, position) *)
}

(* The reaching-defs fixpoint over the CFG (union dataflow; the unique
   site per var when every path agrees, ambiguity otherwise). *)
let reaching_defs (blocks : blk term list) : xenv =
  let all_tids = List.map blocks ~f:(fun b -> Term.tid b) in
  let bins =
    List.fold_left blocks ~init:Tid.Map.empty ~f:(fun m b ->
        let idefs =
          Term.enum def_t b |> Seq.to_list
          |> List.mapi ~f:(fun i d -> (i, d)) in
        let last_pos =
          List.fold_left idefs ~init:Var.Map.empty
            ~f:(fun acc (i, d) -> Core.Map.set acc ~key:(Def.lhs d) ~data:i) in
        let phis =
          Term.enum phi_t b
          |> Seq.fold ~init:Var.Set.empty ~f:(fun acc p ->
                 Core.Set.add acc (Var.base (Phi.lhs p))) in
        let defined =
          Core.Set.union
            (List.fold_left idefs ~init:Var.Set.empty
               ~f:(fun acc (_, d) -> Core.Set.add acc (Var.base (Def.lhs d))))
            phis in
        Core.Map.set m ~key:(Term.tid b) ~data:{ idefs; last_pos; defined }) in
  let preds =
    List.fold_left blocks ~init:Tid.Map.empty ~f:(fun m b ->
        List.fold_left (blk_targets b) ~init:m ~f:(fun m t ->
            if not (List.mem all_tids t ~equal:Tid.equal) then m
            else
              let ps =
                Option.value (Core.Map.find m t) ~default:Tid.Set.empty in
              Core.Map.set m ~key:t ~data:(Core.Set.add ps (Term.tid b)))) in
  let empty = { ru = Var.Map.empty; rm = Var.Set.empty } in
  let states =
    ref
      (List.fold_left blocks ~init:Tid.Map.empty ~f:(fun m b ->
           Core.Map.set m ~key:(Term.tid b) ~data:(empty, empty))) in
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter blocks ~f:(fun b ->
        let bt = Term.tid b in
        let inn =
          match Core.Map.find preds bt with
          | None -> empty
          | Some ps ->
              Core.Set.fold ps ~init:empty ~f:(fun acc p ->
                  match Core.Map.find !states p with
                  | Some (_, out) -> rjoin acc out
                  | None -> acc) in
        let out =
          match Core.Map.find bins bt with
          | Some bi -> rtrans inn bi
          | None -> inn in
        let (_, prev_out) = Option.value_exn (Core.Map.find !states bt) in
        if not (rstate_equal prev_out out) then begin
          states := Core.Map.set !states ~key:bt ~data:(inn, out);
          changed := true
        end);
  done;
  let site =
    List.fold_left blocks ~init:Tid.Map.empty ~f:(fun m b ->
        match Core.Map.find bins (Term.tid b) with
        | None -> m
        | Some bi ->
            List.fold_left bi.idefs ~init:m ~f:(fun m (i, d) ->
                Core.Map.set m ~key:(Term.tid d) ~data:(Term.tid b, i))) in
  { in_state =
      Core.Map.to_alist !states
      |> List.map ~f:(fun (k, (inn, _)) -> (k, inn))
      |> List.fold_left ~init:Tid.Map.empty
           ~f:(fun m (k, v) -> Core.Map.set m ~key:k ~data:v);
    bins;
    site }

(* The def of [v] the flag producer at [pos] in block [p] read: the
   last def of [v] in [p] before [pos], else [v]'s unique reaching
   def at [p]'s entry. *)
let read_def (xenv : xenv) (p : Tid.t) (pos : int) (v : var) : def term option =
  match Core.Map.find xenv.bins p with
  | None -> None
  | Some bi -> (
      let vb = Var.base v in
      let within =
        List.fold_left bi.idefs ~init:None ~f:(fun acc (i, d) ->
            if i < pos && Var.equal (Var.base (Def.lhs d)) vb then Some d else acc)
      in
      match within with
      | Some d -> Some d
      | None -> (
          match Core.Map.find xenv.in_state p with
          | Some st -> Core.Map.find st.ru vb
          | None -> None))

(* The inline guard: every var the emitted comparison reads must hold,
   at the jump, the value its flag producer read.  A var with a site in
   the branching block is readable only when every producer is local
   (the position guard); a var reaching from elsewhere is readable only
   when each cross-block producer read the same unique reaching def. *)
let cross_guard (xenv : xenv) (b : blk term) (bi : binfo) (in_st : rstate)
    (producers : (Tid.t * int) list) (e : exp) : bool =
  let b_tid = Term.tid b in
  let has_there =
    List.exists producers ~f:(fun (p, _) -> not (Tid.equal p b_tid)) in
  let produced_at =
    List.fold_left producers ~init:Int.max_value
      ~f:(fun acc (_, p) -> Int.min acc p) in
  Core.Set.for_all (Exp.free_vars e) ~f:(fun v ->
      let vb = Var.base v in
      if Core.Set.mem bi.defined vb then
        (not has_there)
        && (match Core.Map.find bi.last_pos v with
            | None -> true
            | Some p -> p <= produced_at)
      else if not has_there then true
      else
        match Core.Map.find in_st.ru vb with
        | Some d ->
            let dk = Term.tid d in
            List.for_all producers ~f:(fun (p, pos) ->
                Tid.equal p b_tid
                ||
                match read_def xenv p pos v with
                | Some d' -> Tid.equal (Term.tid d') dk
                | None -> false)
        | None -> not (Core.Set.mem in_st.rm vb))

(* Block analysis and the sub driver. *)

let all_flags = [ ZF; CF; SF; OF ]

(* True when the exp reads memory.  A comparison over a mem operand
   must live in a DEF, never inline in a jmp cond: the def is what the
   VSA tags (the access's frame-residency proof rides the def, exactly
   as it rode the flag defs), and the tag is what licenses the
   emitter's frame addressing. *)
let reads_mem (e : exp) : bool =
  let vis =
    object
      inherit [ bool ] Exp.visitor
      method! visit_load ~mem:_ ~addr _ _ acc = acc || true
      method! visit_store ~mem:_ ~addr ~exp:_ _ _ acc = acc || true
    end
  in
  vis#visit_exp e false

type block_plan = {
  changed : bool;
  (* consumed flag vars (their facts served the rewritten cond). *)
  consumed_vars : Var.Set.t;
}

(* One block: compile every jmp whose cond evaluates over the atoms.
   Each flag resolves to its single reaching def — the block's last
   def, or the unique reaching def at the block entry (the cross-block
   case).  A flag with no def in the block and no unique reaching def,
   or an ambiguous candidate, has no fact (conds over it stay
   residual).  Unchanged jmps (and whole unchanged blocks) keep the
   current path — the identity, never a partial rewrite. *)
let plan_block (xenv : xenv) (fv : flag_vars) (blk : blk term) :
    block_plan * (jmp term * exp option * item option) list =
  let bt = Term.tid blk in
  let bi =
    Option.value (Core.Map.find xenv.bins bt)
      ~default:{ idefs = []; last_pos = Var.Map.empty; defined = Var.Set.empty } in
  let in_st =
    Option.value (Core.Map.find xenv.in_state bt)
      ~default:{ ru = Var.Map.empty; rm = Var.Set.empty } in
  (* The block's own last def of each flag var. *)
  let flag_map =
    List.fold_left bi.idefs ~init:Var.Map.empty
      ~f:(fun acc (i, d) ->
        let lhs = Def.lhs d in
        if List.exists all_flags ~f:(fun fl -> is_flag fv fl lhs) then
          Core.Map.set acc ~key:lhs ~data:(i, Def.rhs d)
        else acc) in
  (* Block ctx: single-def value rhs (own defs, plus the unique
     reaching defs of vars with no site here — the cross-block temp
     chains the consistency checks resolve) + last def position per
     var. *)
  let ctx =
    let counts =
      List.fold_left bi.idefs ~init:Var.Map.empty
        ~f:(fun acc (_, d) ->
          Core.Map.update acc (Def.lhs d) ~f:(function
            | None -> 1
            | Some n -> n + 1)) in
    let rhs =
      List.fold_left bi.idefs ~init:Var.Map.empty
        ~f:(fun acc (i, d) ->
          let v = Def.lhs d in
          if
            (match Core.Map.find counts v with Some n -> Int.equal n 1 | None -> false)
          then Core.Map.set acc ~key:v ~data:(Def.rhs d)
          else acc) in
    let xrhs =
      Core.Map.to_alist in_st.ru
      |> List.fold_left ~init:Var.Map.empty
           ~f:(fun acc (key, data) ->
             if Core.Set.mem bi.defined key then acc
             else Core.Map.set acc ~key ~data:(Def.rhs data)) in
    { rhs; xrhs } in
  (* One candidate per flag: the within-block def when the block has
     one, else the unique reaching def.  Two distinct candidates are
     ambiguous — the flag gets no fact. *)
  let flag_def (fl : flag) : (var * (Tid.t * int) * exp) option =
    let within =
      Core.Map.to_alist flag_map
      |> List.filter_map ~f:(fun (v, (i, rhs)) ->
             if is_flag fv fl v then Some (v, (bt, i), rhs) else None) in
    match within with
    | [ cand ] -> Some cand
    | [] -> (
        let reaching =
          Core.Map.to_alist in_st.ru
          |> List.filter_map ~f:(fun (v, d) ->
                 if is_flag fv fl v then
                   match Core.Map.find xenv.site (Term.tid d) with
                   | Some site -> Some (v, site, Def.rhs d)
                   | None -> None
                 else None) in
        match reaching with [ cand ] -> Some cand | _ -> None)
    | _ -> None in
  let facts =
    List.fold_left all_flags ~init:empty_facts ~f:(fun acc fl ->
        match flag_def fl with
        | Some (_, _, rhs) -> (
            match extract_facts fl rhs acc with Some f -> f | None -> acc)
        | None -> acc) in
  let jmps = Term.enum jmp_t blk |> Seq.to_list in
  let compiled =
    List.map jmps ~f:(fun j ->
        let result =
          Option.bind (parse_bexp (Jmp.cond j)) ~f:(eval_bexp fv ctx facts) in
        let new_cond =
          match result with
          | Some i ->
              let producers =
                List.filter_map i.flags ~f:(fun fl ->
                    match flag_def fl with
                    | Some (_, site, _) -> Some site
                    | None -> None) in
              let guard = cross_guard xenv blk bi in_st producers in
              let cond = render_atom i.atom in
              if guard cond then Some cond else None
          | None -> None in
        (j, new_cond, result)) in
  let changed = List.exists compiled ~f:(fun (_, c, _) -> Option.is_some c) in
  let consumed_vars =
    if not changed then Var.Set.empty
    else
      (* for each rewritten jmp, the flag vars its atoms read. *)
      List.filter_map compiled ~f:(fun (_, c, r) ->
          match (c, r) with
          | Some _, Some i ->
              Some
                (List.filter_map i.flags ~f:(fun fl ->
                     match flag_def fl with
                     | Some (v, _, _) -> Some v
                     | None -> None))
          | _ -> None)
      |> List.concat |> Var.Set.of_list
  in
  ({ changed; consumed_vars }, compiled)

(* Sub-wide free-var uses (defs' rhs + jmps + phis). *)
let uses_of (s : sub term) : Var.Set.t =
  Term.enum blk_t s
  |> Seq.fold ~init:Var.Set.empty ~f:(fun acc blk ->
      let acc =
        Term.enum def_t blk
        |> Seq.fold ~init:acc ~f:(fun acc d ->
            Core.Set.union acc (Exp.free_vars (Def.rhs d)))
      in
      let acc =
        Term.enum jmp_t blk
        |> Seq.fold ~init:acc ~f:(fun acc j -> Core.Set.union acc (Jmp.free_vars j))
      in
      Term.enum phi_t blk
      |> Seq.fold ~init:acc ~f:(fun acc p -> Core.Set.union acc (Phi.free_vars p)))

(* The jump compiler over one sub: compiles every eligible cond (flag
   defs resolve through cross-block reaching definitions), then drops
   every def of a consumed flag var whose only use was the rewritten
   jump (the var is unused sub-wide, so all its defs are dead).  A
   compiled cond reading memory binds the comparison to a fresh 1-bit
   def (the VSA tags the def — the access proof the emitter's frame
   addressing consumes) and the cond reads the def.  Everything else is
   the identity. *)
let compile_sub (target : Theory.Target.t) (sub : sub term) : sub term =
  let fv = flag_vars target in
  let xenv = reaching_defs (Term.enum blk_t sub |> Seq.to_list) in
  let consumed = ref Var.Set.empty in
  let sub1 =
    Term.map blk_t sub ~f:(fun blk ->
        let plan, compiled = plan_block xenv fv blk in
        if not plan.changed then blk
        else begin
          consumed := Core.Set.union !consumed plan.consumed_vars;
          (* The mem-operand comparisons become defs (in jmp order, all
             after the block's own defs — the operands' values are the
             block-end values either way); the cond reads its def. *)
          let cmp_by_jmp =
            List.filter_map compiled ~f:(fun (j, c, _) ->
                match c with
                | Some c when reads_mem c ->
                    Some
                      (Term.tid j,
                       Def.create
                         (Var.create ~is_virtual:true ~fresh:true "hike_cmp"
                            (Type.Imm 1)) c)
                | _ -> None)
          in
          let blk =
            List.fold_left cmp_by_jmp ~init:blk ~f:(fun blk (_, d) ->
                Term.append def_t blk d) in
          Term.map jmp_t blk ~f:(fun j ->
              let cond =
                match
                  List.find cmp_by_jmp ~f:(fun (jt, _) ->
                      Tid.equal (Term.tid j) jt)
                with
                | Some (_, d) -> Bil.Var (Def.lhs d)
                | None -> Jmp.cond j in
              match
                List.find compiled ~f:(fun (j', _, _) ->
                    Tid.equal (Term.tid j) (Term.tid j'))
              with
              | Some (_, Some c, _) -> Jmp.with_cond j (if reads_mem c then cond else c)
              | _ -> j)
        end)
  in
  if Core.Set.is_empty !consumed then sub1
  else
    let used = uses_of sub1 in
    let dead = Core.Set.diff !consumed used in
    if Core.Set.is_empty dead then sub1
    else
      Term.map blk_t sub1 ~f:(fun blk ->
          if
            Term.enum def_t blk
            |> Seq.exists ~f:(fun d -> Core.Set.mem dead (Def.lhs d))
          then
            Term.filter def_t blk ~f:(fun d ->
                not (Core.Set.mem dead (Def.lhs d)))
          else blk)

