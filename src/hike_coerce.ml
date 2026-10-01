(* Width coercion, once: every exp the later passes read is made
   width-honest in the BIR.  Binop operands are coerced to a common width
   (the signed ops sign-extend, every other op zero-extends), Ite branches
   to a common width, a store's data to its size, and a def/phi/Let to the
   declared width of its lhs — the emitter's def-birth rule (truncate a
   wider value, zero-extend a narrower one).  A literal retypes in place
   when the width change is exact; everything else casts. *)

open Bap.Std

(* A comparison's result is one bit, independent of its operands' width —
   the only binop whose result width does not become the common operand
   width. *)
let is_compare : Bil.binop -> bool = function
  | Bil.EQ | Bil.NEQ | Bil.LT | Bil.LE | Bil.SLT | Bil.SLE -> true
  | _ -> false

(* The exp's own width; 0 when undeterminable (then no coercion). *)
let exp_width (e : exp) : int =
  Hike_exp_fold.fold
    (fun e child ->
      match e with
      | Bil.Int w -> Word.bitwidth w
      | Bil.Var v -> (match Var.typ v with Type.Imm n -> n | _ -> 0)
      | Bil.Cast (_, n, _) -> n
      | Bil.Extract (hi, lo, _) -> Stdlib.max 0 (hi - lo + 1)
      | Bil.Concat (a, b) -> child a + child b
      | Bil.Load (_, _, _, s) -> Size.in_bits s
      | Bil.Store (_, _, data, _, _) -> child data
      | Bil.BinOp (op, a, b) ->
          if is_compare op then 1 else Stdlib.max (child a) (child b)
      | Bil.UnOp (_, a) -> child a
      | Bil.Ite (_, a, _) -> child a
      | Bil.Let (v, value, _) -> (
          match Var.typ v with Type.Imm n -> n | _ -> child value)
      | Bil.Unknown (_, t) -> (match t with Type.Imm n -> n | _ -> 0))
    e

(* The width a var declares; 0 when not an integer lane. *)
let var_width (v : var) : int =
  match Var.typ v with Type.Imm n -> n | _ -> 0

(* The cast kind for [op]: the signed ops sign-extend, the rest zero-extend. *)
let cast_kind (op : Bil.binop) : Bil.cast =
  match op with
  | Bil.SDIVIDE | Bil.SMOD | Bil.ARSHIFT | Bil.SLT | Bil.SLE -> Bil.SIGNED
  | _ -> Bil.UNSIGNED

(* The top bit of [lo] — the sign of the value.  BAP's [is_negative] is
   tag-dependent and false on the lifter's untagged words, so tag first. *)
let negative (lo : word) : bool = Word.is_negative (Word.signed lo)

(* The sign/zero filler bit that re-extending a [wo]-bit word to [wi]
   prepends under [c]. *)
let filler_bit (c : Bil.cast) (wi : int) (lo : word) : word =
  match c with
  | Bil.SIGNED when negative lo -> Word.ones (wi - Word.bitwidth lo)
  | _ -> Word.zero (wi - Word.bitwidth lo)

(* Widen [e] from [we] to [w].  A literal retypes its word (no node); every
   other operand casts. *)
let widen (c : Bil.cast) (w : int) (we : int) (e : exp) : exp =
  if we >= w then e
  else
    match e with
    | Bil.Int word -> Bil.Int (Word.concat (filler_bit c w word) word)
    | _ -> Bil.Cast (c, w, e)

(* The literal [e]'s [to_]-bit word when re-extending it under [c]
   reproduces [e] exactly; [None] for a non-literal or a lossy
   truncation. *)
let narrow_literal (c : Bil.cast) (w : int) (to_ : int) (e : exp) : exp option =
  if w <= to_ then None
  else
    match e with
    | Bil.Int imm ->
        let lo = Word.extract_exn ~hi:(to_ - 1) imm in
        if Word.equal (Word.concat (filler_bit c w lo) lo) imm then
          Some (Bil.Int lo)
        else None
    | _ -> None

(* Coerce [e] to width [w] with the emitter's def-birth rule. *)
let coerce_to (w : int) (e : exp) : exp =
  let we = exp_width e in
  if we = 0 || we = w then e
  else if we > w then
    match narrow_literal Bil.UNSIGNED we w e with
    | Some lit -> lit
    | None -> Bil.Cast (Bil.UNSIGNED, w, e)
  else widen Bil.UNSIGNED w we e

let coerce_to_known (w : int) (e : exp) : exp =
  if w = 0 then e else coerce_to w e

(* The exp coercer: widths the tree fixes must agree. *)
class coercer = object(self)
  inherit Exp.mapper

  method! map_binop op e1 e2 =
    let e1 = self#map_exp e1 in
    let e2 = self#map_exp e2 in
    let w1 = exp_width e1 and w2 = exp_width e2 in
    if w1 = 0 || w2 = 0 || w1 = w2 then Bil.BinOp (op, e1, e2)
    else
      let c = cast_kind op in
      (* A comparison of an exactly-representable wider literal retypes the
         literal down instead of casting the other operand; for every other
         op the result carries the common width, so only widening
         preserves it. *)
      match
        ( (if is_compare op then narrow_literal c w1 w2 e1 else None),
          (if is_compare op then narrow_literal c w2 w1 e2 else None) )
      with
      | Some lit1, _ -> Bil.BinOp (op, lit1, e2)
      | _, Some lit2 -> Bil.BinOp (op, e1, lit2)
      | None, None ->
          let w = Stdlib.max w1 w2 in
          Bil.BinOp (op, widen c w w1 e1, widen c w w2 e2)

  method! map_ite ~cond ~yes ~no =
    let cond = self#map_exp cond in
    let yes = self#map_exp yes in
    let no = self#map_exp no in
    let wy = exp_width yes and wn = exp_width no in
    if wy = 0 || wn = 0 || wy = wn then Bil.Ite (cond, yes, no)
    else
      let w = Stdlib.max wy wn in
      Bil.Ite (cond, widen Bil.UNSIGNED w wy yes, widen Bil.UNSIGNED w wn no)

  (* A zero-width operand contributes no bits: the concat is the other
     operand. *)
  method! map_concat e1 e2 =
    let e1 = self#map_exp e1 in
    let e2 = self#map_exp e2 in
    if exp_width e1 = 0 then e2
    else if exp_width e2 = 0 then e1
    else Bil.Concat (e1, e2)

  method! map_store ~mem ~addr ~exp:data e s =
    let mem = self#map_exp mem in
    let addr = self#map_exp addr in
    let data = coerce_to (Size.in_bits s) (self#map_exp data) in
    Bil.Store (mem, addr, data, e, s)

  method! map_let var ~exp:value ~body =
    let value = self#map_exp value in
    let w = var_width var in
    let value = coerce_to_known w value in
    let body = self#map_exp body in
    Bil.Let (var, value, body)
end

let coerce_exp (e : exp) : exp = (new coercer)#map_exp e

(* A def's value is born at its lhs's declared width; a phi's values at
   the phi's. *)
let coerce_to_lhs (v : var) (e : exp) : exp =
  coerce_to_known (var_width v) e

let coerce_def (d : def term) : def term =
  Def.map_exp d ~f:(fun rhs -> coerce_to_lhs (Def.lhs d) (coerce_exp rhs))

let coerce_phi (p : phi term) : phi term =
  Phi.map_exp p ~f:(fun v -> coerce_to_lhs (Phi.lhs p) (coerce_exp v))

(* Every rhs, cond and phi of the block. *)
let coerce_block (blk : blk term) : blk term =
  Blk.map_elts ~def:coerce_def
    ~jmp:(fun j -> Jmp.map_exp j ~f:coerce_exp)
    ~phi:coerce_phi blk

let coerce_sub (sub : sub term) : sub term =
  Term.map blk_t sub ~f:coerce_block

let coerce_program (prog : program term) : program term =
  Term.map sub_t prog ~f:coerce_sub
