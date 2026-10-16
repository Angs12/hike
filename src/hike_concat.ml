(* Extract of a concat, once: a field read from [a.b] that lies inside one
   operand reads that operand.  The lifter builds a double-width temporary
   (x86 [div]: [t := rem.quot]) and extracts its halves in the same block;
   the domain's concat hulls the halves together, so the extract of a
   finite half would be TOP.  The temporary is looked through while
   nothing it was built from is redefined. *)

open Core
open Bap.Std

let width (e : exp) : int option =
  match Type.infer e with Ok (Type.Imm n) -> Some n | _ -> None

(* An exp whose value depends only on its vars. *)
let rec stable (e : exp) : bool =
  match e with
  | Bil.Var _ | Bil.Int _ -> true
  | Bil.Load _ | Bil.Store _ | Bil.Unknown _ | Bil.Let _ -> false
  | Bil.BinOp (_, a, b) | Bil.Concat (a, b) -> stable a && stable b
  | Bil.UnOp (_, a) | Bil.Cast (_, _, a) | Bil.Extract (_, _, a) -> stable a
  | Bil.Ite (c, a, b) -> stable c && stable a && stable b

(* The field [hi:lo] of [a.b] when it lies inside one operand; a field
   covering a whole operand is that operand. *)
let reduce ~hi ~lo (a : exp) (b : exp) : exp option =
  match width a, width b with
  | Some wa, Some wb ->
    let field ~hi ~lo x w =
      if lo = 0 && hi = w - 1 then x else Bil.Extract (hi, lo, x)
    in
    if hi < wb then Some (field ~hi ~lo b wb)
    else if lo >= wb then Some (field ~hi:(hi - wb) ~lo:(lo - wb) a wa)
    else None
  | _ -> None

let rewrite (env : (var * (exp * exp)) list) (rhs : exp) : exp =
  let m =
    object (self)
      inherit Exp.mapper as super
      method! map_extract ~hi ~lo e =
        let e = self#map_exp e in
        let operands =
          match e with
          | Bil.Concat (a, b) -> Some (a, b)
          | Bil.Var v ->
            List.find_map env ~f:(fun (t, ab) ->
                if Var.same t v then Some ab else None)
          | _ -> None
        in
        match Option.bind operands ~f:(fun (a, b) -> reduce ~hi ~lo a b) with
        | Some r -> r
        | None -> super#map_extract ~hi ~lo e
    end
  in
  m#map_exp rhs

let reads (e : exp) (v : var) : bool =
  Set.exists (Exp.free_vars e) ~f:(fun x -> Var.same (Var.base x) (Var.base v))

let normalize_block (blk : blk term) : blk term =
  Seq.fold (Term.enum def_t blk) ~init:(blk, [])
    ~f:(fun (blk, env) d ->
        let rhs = rewrite env (Def.rhs d) in
        let blk =
          if Exp.equal rhs (Def.rhs d) then blk
          else Term.update def_t blk (Def.with_rhs d rhs)
        in
        let v = Def.lhs d in
        let env =
          List.filter env ~f:(fun (t, (a, b)) ->
              not (Var.same (Var.base t) (Var.base v) || reads a v || reads b v))
        in
        let env =
          match rhs with
          | Bil.Concat (a, b)
            when stable a && stable b && not (reads a v || reads b v) ->
            (v, (a, b)) :: env
          | _ -> env
        in
        (blk, env))
  |> fst

let normalize (prog : program term) : program term =
  Term.map sub_t prog ~f:(fun sub -> Term.map blk_t sub ~f:normalize_block)
