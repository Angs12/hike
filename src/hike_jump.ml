(* The jump compiler: rewrites jcc flag idioms into the simplest equivalent
   value comparisons.  Identity on the residual — a cond with no single
   reaching flag def, an unknown shape, or an inconsistent fact set keeps
   the current path unchanged. *)

open Bap.Std
open Bap_core_theory
open Core

(* The flag defs as the lifter emits them, and the facts they yield:
   ZF := 0 = d               ZF ⇔ d = 0      (also ZF := 1 / := 0)
   CF := a < b               CF ⇔ a <u b     (sub/cmp borrow)
   SF := high:1[e]           SF ⇔ sign bit of e
   OF := high:1[(x^y)&(x^d)] OF ⇔ signed overflow of x−y, d = x−y
   OF := 0                   the test/and group: OF ≡ 0, so the
                             signed families run on SF alone
   Anything else (add/imul/shift carries, PF/AF forms) is NOT consumed. *)

(* BIR conds are pure AND/OR/NOT over 1-bit vars. *)
type bexp = V of var | N of bexp | A of bexp * bexp | O of bexp * bexp

(* Flags identified by the target's register roles, never a name. *)
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
    Option.bind (go a) ~f:(fun a -> Option.map (go b) ~f:(c a)) in
  go e

(* The signed xor core: (SF|OF) & ~(SF&OF) — OF xor SF. *)
let is_xor_core (fv : flag_vars) (b : bexp) : bool =
  match b with
  | A (O (V sf1, V of1), N (A (V sf2, V of2))) ->
      is_flag fv SF sf1 && is_flag fv OF of1
      && is_flag fv SF sf2 && is_flag fv OF of2
  | _ -> false

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

(* Width of an exp: the width of its free vars (BIR is width-uniform); a
   bare immediate is its own width. *)
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
  Option.map ~f:(fun n -> Bil.Int (Word.zero n)) (width_of_exp e)

let is_zero_int = function Bil.Int w -> Word.is_zero w | _ -> false

let is_one_int = function Bil.Int w -> Word.is_one w | _ -> false

(* Fact extraction from one flag def rhs (the table above); [None] when the
   shape is unknown. *)
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
  (* test/and: OF is identically 0 — the group's signed identity is SF alone. *)
  | OF, e when is_zero_int e ->
    if f.and_form then None else Some { f with and_form = true }
  | _ -> None

(* Block context: single-def value rhs, for CONSISTENCY CHECKS only — the
   emitted comparison reuses the var, never re-substitutes. *)

type ctx = { rhs : exp Var.Map.t; xrhs : exp Var.Map.t }

(* [rhs] keys the block's own single defs; [xrhs] keys (by base var) the
   unique reaching defs from predecessor blocks. *)
let resolve_exp (c : ctx) (e : exp) : exp =
  match e with
  | Bil.Var v -> (
      match Core.Map.find c.rhs v with
      | Some r -> r
      | None -> Option.value (Core.Map.find c.xrhs (Var.base v)) ~default:e)
  | _ -> e

let same_exp (c : ctx) (a : exp) (b : exp) : bool =
  Exp.equal (resolve_exp c a) (resolve_exp c b)

(* The overflow pattern is only the sub-overflow predicate when its diff exp
   IS (x − y), resolved. *)
let is_minus_xy (c : ctx) (e : exp) (x : exp) (y : exp) : bool =
  match resolve_exp c e with
  | Bil.BinOp (Bil.MINUS, a, b) -> Exp.equal a x && Exp.equal b y
  | _ -> false

let const_cond (b : bool) : exp = Bil.Int (if b then Word.one 1 else Word.zero 1)

(* The cond algebra: each parsed leaf becomes an atom over the flag facts,
   NOT is the complement, and AND/OR combine two relations when both range
   over the same two values. *)

(* The relation lattice: a relation admits a subset of the orderings over its
   operand pair; the complement and the connectives are componentwise. *)
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

(* An atom: a constant truth, or one relation over two values (the bool picks
   signed vs unsigned).  The pair is the two values the relation ranges over —
   the connectives' agreement key; an emitted equality's pair looks through
   the resolved subtraction (d = x − y makes the pair (x, y)). *)
type atom = Const of bool | Rel of rel * bool * exp * exp

type item = { atom : atom; pair : (exp * exp) option; flags : flag list }

let complement_item (i : item) : item =
  { i with
    atom =
      (match i.atom with
       | Const b -> Const (not b)
       | Rel (r, s, a, b) -> Rel (rel_complement r, s, a, b)) }

(* GT/GE render operand-swapped (never a NOT); signedness picks the
   operator. *)
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

(* The atoms over the facts: a ZF subtraction compares its operands (d is
   reused, never re-substituted), any other d is compared to zero at d's own
   width; SF under OF ≡ 0 is the sign alone, e <s 0. *)
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
  Option.bind atom ~f:(fun atom ->
      Option.map pair ~f:(fun pair -> { atom; pair = Some pair; flags = [ ZF ] }))

let sign_item (e : exp) (flags : flag list) : item option =
  Option.map (zero_exp e) ~f:(fun z ->
      { atom = Rel (LT, true, e, z); pair = Some (e, z); flags })

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
    Option.bind facts.sf ~f:(fun e -> sign_item e [ SF ])
  else None

(* The xor-core atom: x <s y when the overflow's diff resolves to (x − y) and
   the sign exp to the same diff; with OF ≡ 0 the core is the sign alone. *)
let signed_item (c : ctx) (facts : facts) : item option =
  match (facts.sf, facts.ovf) with
  | Some e, Some (x, y, d) when is_minus_xy c d x y && same_exp c e d ->
      Some { atom = Rel (LT, true, x, y); pair = Some (x, y); flags = [ SF; OF ] }
  | Some e, None when facts.and_form -> sign_item e [ SF; OF ]
  | _ -> None

(* AND/OR over two compiled atoms: constants fold; relations combine on the
   lattice iff both range over the same two values; an equality side carries
   no signed flavor — the ordering side's operands and signedness emit. *)
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
  Option.bind (eval_bexp fv c facts x) ~f:(fun x' ->
      Option.bind (eval_bexp fv c facts y) ~f:(combine c ~or_ x'))

type binfo = {
  idefs : (int * def term) list; (* defs in block order *)
  last_pos : int Var.Map.t; (* last def position per var *)
  defined : Var.Set.t; (* vars with a def or phi site here (entry kills) *)
}

(* Reaching state: the unique def site per BASE var, plus the vars whose
   entry value has no unique site (several reaching defs, or a phi).  A var
   absent from both is a live-in parameter, whose value is stable. *)
type rstate = { unique_site : def term Var.Map.t; multi_site : Var.Set.t }

let rstate_equal (a : rstate) (b : rstate) : bool =
  Var.Map.equal (fun d d' -> Tid.equal (Term.tid d) (Term.tid d')) a.unique_site b.unique_site
  && Var.Set.equal a.multi_site b.multi_site

let rjoin (a : rstate) (b : rstate) : rstate =
  let key_set =
    Core.Map.merge a.unique_site b.unique_site
      ~f:(fun ~key:v -> function
        | `Both _ | `Left _ | `Right _ -> Some v)
    |> Core.Map.keys
    |> Core.Set.of_list (module Var)
  in
  let keys = Core.Set.union key_set (Core.Set.union a.multi_site b.multi_site) in
  Core.Set.fold keys ~init:{ unique_site = Var.Map.empty; multi_site = Var.Set.empty }
    ~f:(fun st v ->
        if Core.Set.mem a.multi_site v || Core.Set.mem b.multi_site v then
          { st with multi_site = Core.Set.add st.multi_site v }
        else
          match (Core.Map.find a.unique_site v, Core.Map.find b.unique_site v) with
          | Some d, Some d' ->
              if Tid.equal (Term.tid d) (Term.tid d') then
                { st with unique_site = Core.Map.set st.unique_site ~key:v ~data:d }
              else { st with multi_site = Core.Set.add st.multi_site v }
          | Some d, None | None, Some d ->
              { st with unique_site = Core.Map.set st.unique_site ~key:v ~data:d }
          | None, None -> st)

let rtrans (bin : rstate) (bi : binfo) : rstate =
  let gen =
    List.fold_left bi.idefs ~init:Var.Map.empty
      ~f:(fun acc (_, d) ->
        Core.Map.set acc ~key:(Var.base (Def.lhs d)) ~data:d) in
  let unique_site =
    Core.Map.filter_keys bin.unique_site ~f:(fun k -> not (Core.Set.mem bi.defined k))
  in
  let unique_site = Core.Map.merge unique_site gen
      ~f:(fun ~key:_ -> function
        | `Both (_, d) | `Left d | `Right d -> Some d) in
  let multi_site =
    Core.Set.filter bin.multi_site ~f:(fun v -> not (Core.Set.mem bi.defined v)) in
  (* A phi defines its lhs at the entry with no def site — the var's entry
     value stays site-less (multi). *)
  let multi_site =
    Core.Set.fold bi.defined ~init:multi_site ~f:(fun s v ->
        if Core.Map.mem gen v then s else Core.Set.add s v) in
  { unique_site; multi_site }

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

(* The reaching-defs fixpoint: the unique site per var when every path
   agrees, ambiguity otherwise. *)
let reaching_defs (blocks : blk term list) : xenv =
  let all_tids = Core.Set.of_list (module Tid) (List.map blocks ~f:(fun b -> Term.tid b)) in
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
            if not (Core.Set.mem all_tids t) then m
            else
              let ps =
                Option.value (Core.Map.find m t) ~default:Tid.Set.empty in
              Core.Map.set m ~key:t ~data:(Core.Set.add ps (Term.tid b)))) in
  let empty = { unique_site = Var.Map.empty; multi_site = Var.Set.empty } in
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
          Option.value
            (Option.map (Core.Map.find preds bt) ~f:(fun ps ->
                 Core.Set.fold ps ~init:empty ~f:(fun acc p ->
                     Option.value
                       (Option.map (Core.Map.find !states p)
                          ~f:(fun (_, out) -> rjoin acc out))
                       ~default:acc)))
            ~default:empty in
        let out =
          Option.value (Option.map (Core.Map.find bins bt) ~f:(rtrans inn))
            ~default:inn in
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

(* The def of [v] the flag producer at [pos] in block [p] read: the last def
   of [v] in [p] before [pos], else [v]'s unique reaching def at [p]'s
   entry. *)
let read_def (xenv : xenv) (p : Tid.t) (pos : int) (v : var) : def term option =
  Option.bind (Core.Map.find xenv.bins p) ~f:(fun bi ->
      let vb = Var.base v in
      let within =
        List.fold_left bi.idefs ~init:None ~f:(fun acc (i, d) ->
            if i < pos && Var.equal (Var.base (Def.lhs d)) vb then Some d else acc)
      in
      match within with
      | Some d -> Some d
      | None ->
          Option.bind (Core.Map.find xenv.in_state p) ~f:(fun st ->
              Core.Map.find st.unique_site vb))

(* The inline guard: every var the emitted comparison reads must hold, at the
   jump, the value its flag producer read — a var defined in the branching
   block only when every producer is local, a cross-block var only through
   one unique reaching def. *)
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
        match Core.Map.find in_st.unique_site vb with
        | Some d ->
            let dk = Term.tid d in
            List.for_all producers ~f:(fun (p, pos) ->
                Tid.equal p b_tid
                ||
                match read_def xenv p pos v with
                | Some d' -> Tid.equal (Term.tid d') dk
                | None -> false)
        | None -> not (Core.Set.mem in_st.multi_site vb))

let all_flags = [ ZF; CF; SF; OF ]

let reads_mem (e : exp) : bool = Hike_stack_model.reads_mem e

type block_plan = {
  changed : bool;
  (* consumed flag vars (their facts served the rewritten cond). *)
  consumed_vars : Var.Set.t;
}

(* One block: each flag resolves to its single reaching def — the block's
   last def or the unique reaching def at the block entry; an ambiguous
   candidate has no fact.  Unchanged jmps keep the current path. *)
let plan_block (xenv : xenv) (fv : flag_vars) (blk : blk term) :
    block_plan * (jmp term * exp option * item option) list =
  let bt = Term.tid blk in
  let bi =
    Option.value (Core.Map.find xenv.bins bt)
      ~default:{ idefs = []; last_pos = Var.Map.empty; defined = Var.Set.empty } in
  let in_st =
    Option.value (Core.Map.find xenv.in_state bt)
      ~default:{ unique_site = Var.Map.empty; multi_site = Var.Set.empty } in
  (* The block's own last def of each flag var. *)
  let flag_map =
    List.fold_left bi.idefs ~init:Var.Map.empty
      ~f:(fun acc (i, d) ->
        let lhs = Def.lhs d in
        if List.exists all_flags ~f:(fun fl -> is_flag fv fl lhs) then
          Core.Map.set acc ~key:lhs ~data:(i, Def.rhs d)
        else acc) in
  (* Block ctx: single-def value rhs — own defs, plus the unique reaching
     defs of vars with no site here — + last def position per var. *)
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
      Core.Map.to_alist in_st.unique_site
      |> List.fold_left ~init:Var.Map.empty
           ~f:(fun acc (key, data) ->
             if Core.Set.mem bi.defined key then acc
             else Core.Map.set acc ~key ~data:(Def.rhs data)) in
    { rhs; xrhs } in
  (* One reaching def per flag var: the block's last def (the fold
     keeps one def per var), else the reaching state's. *)
  (* Each flag's reaching def, computed once per block and reused by
     the facts fold and every jmp's compilation. *)
  let flag_def (fl : flag) : (var * (Tid.t * int) * exp) option =
    let within =
      Core.Map.to_alist flag_map
      |> List.filter_map ~f:(fun (v, (i, rhs)) ->
             if is_flag fv fl v then Some (v, (bt, i), rhs) else None) in
    match within with
    | cand :: _ -> Some cand
    | [] -> (
        let reaching =
          Core.Map.to_alist in_st.unique_site
          |> List.filter_map ~f:(fun (v, d) ->
                 if is_flag fv fl v then
                   match Core.Map.find xenv.site (Term.tid d) with
                   | Some site -> Some (v, site, Def.rhs d)
                   | None -> None
                 else None) in
        match reaching with [ cand ] -> Some cand | _ -> None)
  in
  let flag_defs =
    List.map all_flags ~f:(fun fl -> (fl, flag_def fl)) in
  let flag_def (fl : flag) =
    Option.join (Base.List.Assoc.find flag_defs fl ~equal:Stdlib.( = )) in
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
          Option.bind result ~f:(fun i ->
              let producers =
                List.filter_map i.flags ~f:(fun fl ->
                    Option.map (flag_def fl) ~f:(fun (_, site, _) -> site)) in
              let guard = cross_guard xenv blk bi in_st producers in
              let cond = render_atom i.atom in
              if guard cond then Some cond else None) in
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
                     Option.map (flag_def fl) ~f:(fun (v, _, _) -> v)))
          | _ -> None)
      |> List.concat |> Var.Set.of_list
  in
  ({ changed; consumed_vars }, compiled)

let uses_of (s : sub term) : Var.Set.t =
  Hike_stack_model.sub_reads s

(* Compiles every eligible cond, then drops every def of a consumed flag var
   whose only use was the rewritten jump.  A compiled cond reading memory
   binds the comparison to a fresh 1-bit def — the VSA tags the def, and the
   tag is what licenses the emitter's frame addressing. *)
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
                Option.value
                  (Option.map
                     (List.find cmp_by_jmp ~f:(fun (jt, _) ->
                          Tid.equal (Term.tid j) jt))
                     ~f:(fun (_, d) -> Bil.Var (Def.lhs d)))
                  ~default:(Jmp.cond j) in
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

