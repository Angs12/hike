(* T13 — the jump compiler (construction): a BIR→BIR term transformation
   that REDESIGNS jcc flag idioms into the SIMPLEST equivalent value
   comparisons (never a relocation of the flag decoding).  The flag
   semantics lives HERE ONCE — the flag-effects table below, the def-
   side twin of cbat_walk's decoder rows.  Identity on the residual: a
   cond with no dominating single flag def, an unknown shape, or an
   inconsistent fact set keeps the current path unchanged (no gates, no
   fallbacks, no partial rewrites).  Pipeline registration and the VSA
   decoder shrink are the slot-window phase. *)

open Bap.Std
open Core

(* ------------------------------------------------------------------ *)
(* The flag-effects table: the flag defs as the lifter emits them.     *)
(*                                                                     *)
(*   ZF := 0 = d               ZF ⇔ d = 0      (also ZF := 1 / := 0)   *)
(*   CF := a < b               CF ⇔ a <u b     (sub/cmp borrow)        *)
(*   SF := high:1[e]           SF ⇔ sign bit of e                      *)
(*   OF := high:1[(x^y)&(x^d)] OF ⇔ signed overflow of x−y, d = x−y    *)
(*                                                                     *)
(* Anything else (add/imul/shift carries, PF/AF forms, unknown[bits])  *)
(* is NOT consumed — conds over those shapes stay residual.            *)
(* ------------------------------------------------------------------ *)

(* The jcc families the pass compiles. *)
type jcc = JE | JNE | JLE | JL | JG | JGE | JA | JAE | JB | JBE

(* Cond boolean structure over flag vars (BIR conds are pure AND/OR/NOT
   over 1-bit vars; anything else fails to parse and stays residual). *)
type bexp = V of var | N of bexp | A of bexp * bexp | O of bexp * bexp

let is_flag (name : string) (v : var) : bool =
  String.equal (Var.name (Var.base v)) name

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
let is_xor_core (b : bexp) : bool =
  match b with
  | A (O (V sf1, V of1), N (A (V sf2, V of2))) ->
      is_flag "SF" sf1 && is_flag "OF" of1
      && is_flag "SF" sf2 && is_flag "OF" of2
  | _ -> false

let is_v f = function V v -> f v | _ -> false

(* The jcc family of a cond. *)
let classify (b : bexp) : jcc option =
  let zf x = is_v (is_flag "ZF") x in
  let cf x = is_v (is_flag "CF") x in
  match b with
  | b when zf b -> Some JE
  | N b when zf b -> Some JNE
  | b when is_xor_core b -> Some JL
  | O (a1, a2) when zf a1 && is_xor_core a2 -> Some JLE
  | O (a1, a2) when is_xor_core a1 && zf a2 -> Some JLE
  | O (a1, a2) when cf a1 && zf a2 -> Some JBE
  | O (a1, a2) when zf a1 && cf a2 -> Some JBE
  | N b when cf b -> Some JAE
  | b when cf b -> Some JB
  | N b -> (
      match b with
      | b when is_xor_core b -> Some JGE
      | O (a1, a2) when zf a1 && is_xor_core a2 -> Some JG
      | O (a1, a2) when is_xor_core a1 && zf a2 -> Some JG
      | O (a1, a2) when cf a1 && zf a2 -> Some JA
      | O (a1, a2) when zf a1 && cf a2 -> Some JA
      | _ -> None)
  | _ -> None

(* ------------------------------------------------------------------ *)
(* Per-block flag facts                                                *)
(* ------------------------------------------------------------------ *)

type zf_fact = Zero of exp | Zconst of bool

type cf_fact = Ult of exp * exp | Cconst of bool

type facts = {
  zf : zf_fact option; (* ZF ⇔ (d = 0) / constant *)
  cf : cf_fact option; (* CF ⇔ (a <u b) / constant *)
  sf : exp option; (* SF ⇔ sign bit of e *)
  ovf : (exp * exp * exp) option; (* OF ⇔ signed overflow of x−y, d = x−y *)
}

let empty_facts = { zf = None; cf = None; sf = None; ovf = None }

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

let is_one_int = function Bil.Int w -> Word.equal w (Word.one (Word.bitwidth w)) | _ -> false

(* Fact extraction from one flag def rhs (the table above).  Called
   once per flag — on its single reaching def (the block's last def of
   the flag var); [None] when the shape is unknown (the flag gets no
   fact and conds over it stay residual). *)
let extract_facts (name : string) (rhs : exp) (f : facts) : facts option =
  match (name, rhs) with
  | "ZF", Bil.BinOp (Bil.EQ, a, b) when is_zero_int a -> (
      match f.zf with None -> Some { f with zf = Some (Zero b) } | _ -> None)
  | "ZF", Bil.BinOp (Bil.EQ, a, b) when is_zero_int b -> (
      match f.zf with None -> Some { f with zf = Some (Zero a) } | _ -> None)
  | "ZF", e when is_one_int e -> (
      match f.zf with None -> Some { f with zf = Some (Zconst true) } | _ -> None)
  | "ZF", e when is_zero_int e -> (
      match f.zf with None -> Some { f with zf = Some (Zconst false) } | _ -> None)
  | "CF", Bil.BinOp (Bil.LT, a, b) -> (
      match f.cf with None -> Some { f with cf = Some (Ult (a, b)) } | _ -> None)
  | "CF", e when is_zero_int e -> (
      match f.cf with None -> Some { f with cf = Some (Cconst false) } | _ -> None)
  | "SF", Bil.Cast (Bil.HIGH, 1, e) -> (
      match f.sf with None -> Some { f with sf = Some e } | _ -> None)
  | ( "OF"
    , Bil.Cast
        ( Bil.HIGH
        , 1
        , Bil.BinOp (Bil.AND, Bil.BinOp (Bil.XOR, x, y), Bil.BinOp (Bil.XOR, x2, d)) ) )
    when Exp.equal x x2 -> (
      match f.ovf with None -> Some { f with ovf = Some (x, y, d) } | _ -> None)
  | _ -> None

(* ------------------------------------------------------------------ *)
(* Block context: single-def value rhs (for CONSISTENCY CHECKS only —  *)
(* the emitted comparison REUSES the var, never re-substitutes) and    *)
(* the last def position per var (the inline guard).                   *)
(* ------------------------------------------------------------------ *)

type ctx = { rhs : exp Var.Map.t; last_pos : int Var.Map.t }

let resolve_exp (c : ctx) (e : exp) : exp =
  match e with Bil.Var v -> Option.value (Core.Map.find c.rhs v) ~default:e | _ -> e

let same_exp (c : ctx) (a : exp) (b : exp) : bool =
  Exp.equal (resolve_exp c a) (resolve_exp c b)

(* The overflow pattern is only the sub-overflow predicate when its
   diff exp IS (x − y) — resolved. *)
let is_minus_xy (c : ctx) (e : exp) (x : exp) (y : exp) : bool =
  match resolve_exp c e with
  | Bil.BinOp (Bil.MINUS, a, b) -> Exp.equal a x && Exp.equal b y
  | _ -> false

(* Inline guard: no var read by the re-emitted comparison may be
   redefined after the producing def's position — the re-emission at
   the jump must read the same values the flag defs read. *)
let inline_guard (c : ctx) (inlined : Var.Set.t) ~(produced_at : int) : bool =
  Core.Set.for_all inlined ~f:(fun v ->
      match Core.Map.find c.last_pos v with
      | None -> true
      | Some p -> p <= produced_at)

(* ------------------------------------------------------------------ *)
(* The rewrite                                                         *)
(* ------------------------------------------------------------------ *)

let cmp op a b = Bil.BinOp (op, a, b)

let const_cond (b : bool) : exp = Bil.Int (if b then Word.one 1 else Word.zero 1)

(* The zero family with its folds: a−a resolves to a constant; the cmp
   x,0 shape folds ((x−0)=0 → x=0); (x−y)=0 → x=y (constant-right);
   test's (x&y) keeps the conjunction; anything else compares d to 0
   at the def's operand width.  A var d REUSES the var (rule 1) —
   never re-substituted. *)
let zero_family ~neg (d : exp) : exp option =
  let desired truth = if neg then not truth else truth in
  let eq_or_neq a b = if neg then cmp Bil.NEQ a b else cmp Bil.EQ a b in
  match d with
  | Bil.BinOp (Bil.MINUS, x, y) ->
      if Exp.equal x y then Some (const_cond (desired true))
      else if is_zero_int y then Some (eq_or_neq x y)
      else if is_zero_int x then Some (eq_or_neq y x)
      else Some (eq_or_neq x y)
  | _ -> (
      match zero_exp d with
      | None -> None
      | Some z -> Some (eq_or_neq d z))

(* The family comparisons.  Each row is the SIMPLEST equivalent: the
   complement pairs flip the operand order (a ≥u b ⇔ b ≤u a), never
   wrap in NOT; signed rows keep the def's original operand order
   where an operator exists (the flipped order is the complement row).
   The comparison runs at the def's operand width — the widths ride
   the inlined exps themselves. *)
let family_cond (facts : facts) (j : jcc) : exp option =
  let { zf; cf; sf; ovf } = facts in
  match (j, zf, cf, sf, ovf) with
  | JE, Some (Zero d), _, _, _ -> zero_family ~neg:false d
  | JNE, Some (Zero d), _, _, _ -> zero_family ~neg:true d
  | JE, Some (Zconst b), _, _, _ -> Some (const_cond b)
  | JNE, Some (Zconst b), _, _, _ -> Some (const_cond (not b))
  | JB, _, Some (Ult (a, b)), _, _ -> Some (cmp Bil.LT a b)
  | JAE, _, Some (Ult (a, b)), _, _ -> Some (cmp Bil.LE b a)
  | JBE, Some (Zero _), Some (Ult (a, b)), _, _ -> Some (cmp Bil.LE a b)
  | JA, Some (Zero _), Some (Ult (a, b)), _, _ -> Some (cmp Bil.LT b a)
  | JL, _, _, Some _, Some (x, y, _) -> Some (cmp Bil.SLT x y)
  | JGE, _, _, Some _, Some (x, y, _) -> Some (cmp Bil.SLE y x)
  | JLE, Some _, _, Some _, Some (x, y, _) -> Some (cmp Bil.SLE x y)
  | JG, Some _, _, Some _, Some (x, y, _) -> Some (cmp Bil.SLT y x)
  | _ -> None

let family_name (j : jcc) : string =
  match j with
  | JE -> "je" | JNE -> "jne" | JLE -> "jle" | JL -> "jl" | JG -> "jg"
  | JGE -> "jge" | JA -> "ja" | JAE -> "jae" | JB -> "jb" | JBE -> "jbe"

let family_of_cond (e : exp) : string option =
  match parse_bexp e with
  | Some b -> (
      match classify b with
      | Some j -> Some (family_name j)
      | None -> None)
  | None -> None

(* The flag vars a family consumes. *)
let family_flags (j : jcc) : string list =
  match j with
  | JE | JNE -> [ "ZF" ]
  | JB | JAE -> [ "CF" ]
  | JBE | JA -> [ "ZF"; "CF" ]
  | JL | JGE -> [ "SF"; "OF" ]
  | JLE | JG -> [ "SF"; "OF"; "ZF" ]

(* Compile one classified cond.  Besides the row lookup, the family
   collapses carry their consistency checks (the soundness of the
   collapse):
   - JBE/JA: the zero fact must be the SAME subtraction as the borrow
     (the compared d resolves to (a − b)) — then CF|ZF ⇔ a ≤u b.
   - Signed rows: the overflow pattern's diff resolves to (x − y) and
     SF's sign exp resolves to the same d (and, for JLE/JG, the zero
     fact's d to it too) — the standard signed identities.
   The vars the rewrite inlines must pass the inline guard. *)
let compile_jcc (c : ctx) (facts : facts) (flag_def : string -> (var * int) option)
    (j : jcc) : exp option =
  let zf_zero = match facts.zf with Some (Zero d) -> Some d | _ -> None in
  let consistent =
    match j with
    | JE | JNE | JB | JAE -> true
    | JBE | JA -> (
        match (zf_zero, facts.cf) with
        | Some d, Some (Ult (a, b)) -> is_minus_xy c d a b
        | _ -> false)
    | JL | JGE -> (
        match (facts.sf, facts.ovf) with
        | Some e, Some (x, y, d) -> is_minus_xy c d x y && same_exp c e d
        | _ -> false)
    | JLE | JG -> (
        match (zf_zero, facts.sf, facts.ovf) with
        | Some d0, Some e, Some (x, y, d) ->
            is_minus_xy c d x y && same_exp c e d && same_exp c d0 d
        | _ -> false)
  in
  if not consistent then None
  else
    match family_cond facts j with
    | None -> None
    | Some new_cond ->
        let wanted = family_flags j in
        let defs = List.filter_map wanted ~f:flag_def in
        if List.length defs <> List.length wanted then None
        else
          let produced_at =
            List.fold_left defs ~init:Int.max_value
              ~f:(fun acc (_, p) -> Int.min acc p) in
          if inline_guard c (Exp.free_vars new_cond) ~produced_at then
            Some new_cond
          else None

(* ------------------------------------------------------------------ *)
(* Block analysis and the sub driver                                   *)
(* ------------------------------------------------------------------ *)

let flag_names = [ "ZF"; "CF"; "SF"; "OF" ]

type block_plan = {
  changed : bool;
  (* consumed flag vars (their facts served the rewritten cond). *)
  consumed_vars : Var.Set.t;
}

(* One block: analyze the defs, compile every jmp whose cond
   classifies.  Unchanged jmps (and whole unchanged blocks) keep the
   current path — the identity, never a partial rewrite. *)
let plan_block (blk : blk term) : block_plan * (jmp term * exp option) list =
  let defs = Term.enum def_t blk |> Seq.to_list in
  let indexed = List.mapi defs ~f:(fun i d -> (i, d)) in
  (* The single REACHING def of each flag var: all defs precede all
     jmps of a block, so every cond reads the LAST def — earlier flag
     defs are dead writes.  Facts come only from that def; a flag with
     no def in the block has no fact (its conds stay residual). *)
  let flag_map =
    List.fold_left indexed ~init:Var.Map.empty
      ~f:(fun acc (i, d) ->
        let lhs = Def.lhs d in
        if List.exists flag_names ~f:(fun n -> is_flag n lhs) then
          Core.Map.set acc ~key:lhs ~data:(i, Def.rhs d)
        else acc) in
  (* Block ctx: single-def value rhs + last def position per var. *)
  let ctx =
    let counts =
      List.fold_left defs ~init:Var.Map.empty
        ~f:(fun acc d ->
          Core.Map.update acc (Def.lhs d) ~f:(function
            | None -> 1
            | Some n -> n + 1)) in
    let rhs, last_pos =
      List.fold_left indexed ~init:(Var.Map.empty, Var.Map.empty)
        ~f:(fun (rhs, last) (i, d) ->
          let v = Def.lhs d in
          let rhs =
            if
              (match Core.Map.find counts v with Some n -> Int.equal n 1 | None -> false)
            then
              Core.Map.set rhs ~key:v ~data:(Def.rhs d)
            else rhs in
          (rhs, Core.Map.set last ~key:v ~data:i)) in
    { rhs; last_pos } in
  (* By-name flag lookup; a name with two candidate vars is dropped —
     the flag is ambiguous and its facts stay absent. *)
  let flag_list =
    Core.Map.to_alist flag_map
    |> List.filter_map ~f:(fun (v, (i, _)) ->
        List.find_map flag_names ~f:(fun n ->
            if is_flag n v then Some (n, (v, i)) else None)) in
  let flag_list =
    List.filter flag_list ~f:(fun (n, _) ->
        Int.equal
          (List.length (List.filter flag_list ~f:(fun (n', _) -> String.equal n n')))
          1) in
  let flag_def name =
    List.find_map flag_list ~f:(fun (n, vi) ->
        if String.equal n name then Some vi else None) in
  let facts =
    List.fold_left flag_list ~init:empty_facts ~f:(fun acc (n, (v, _)) ->
        match Core.Map.find flag_map v with
        | Some (_, rhs) -> (
            match extract_facts n rhs acc with Some f -> f | None -> acc)
        | None -> acc) in
  let jmps = Term.enum jmp_t blk |> Seq.to_list in
  let compiled =
    List.map jmps ~f:(fun j ->
        let new_cond =
          match parse_bexp (Jmp.cond j) with
          | None -> None
          | Some b -> (
              match classify b with
              | None -> None
              | Some jcc -> compile_jcc ctx facts flag_def jcc)
        in
        (j, new_cond)) in
  let changed = List.exists compiled ~f:(fun (_, c) -> Option.is_some c) in
  let consumed_vars =
    if not changed then Var.Set.empty
    else
      (* for each rewritten jmp, the flag vars its family consumes. *)
      List.concat_map compiled ~f:(fun (j, c) ->
          match c with
          | None -> []
          | Some _ -> (
              match parse_bexp (Jmp.cond j) with
              | Some b -> (
                  match classify b with
                  | Some jcc ->
                      List.filter_map (family_flags jcc) ~f:(fun n ->
                          match flag_def n with
                          | Some (v, _) -> Some v
                          | None -> None)
                  | None -> [])
              | None -> []))
      |> Var.Set.of_list
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

(* The jump compiler over one sub: compiles every eligible cond, then
   drops every def of a consumed flag var whose only use was the
   rewritten jump (rule 5 — the var is unused sub-wide, so all its
   defs are dead).  Everything else is the identity. *)
let compile_sub (sub : sub term) : sub term =
  let consumed = ref Var.Set.empty in
  let sub1 =
    Term.map blk_t sub ~f:(fun blk ->
        let plan, compiled = plan_block blk in
        if not plan.changed then blk
        else begin
          consumed := Core.Set.union !consumed plan.consumed_vars;
          Term.map jmp_t blk ~f:(fun j ->
              match
                List.find compiled ~f:(fun (j', _) ->
                    Tid.equal (Term.tid j) (Term.tid j'))
              with
              | Some (_, Some c) -> Jmp.with_cond j c
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

let compile_program (prog : program term) : program term =
  Term.map sub_t prog ~f:compile_sub
