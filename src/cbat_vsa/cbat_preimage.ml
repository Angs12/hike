(* Pure inverse operators. Representations own their kernels; the lift
   joins alternatives before any caller writes analysis state. *)
open Core
open Bap.Std
module W = Cbat_word

type unop = Lnot | Neg | Extract of int option * int | Cast of Bil.cast * int
type binop = Op of Bil.binop | Concat

let valid1 op ~arg ~result =
  match op with
  | Lnot | Neg -> arg = result
  | Cast (Bil.HIGH, n) -> n > 0 && n <= arg && result = n
  | Cast (_, n) -> n > 0 && result = n
  | Extract (hi, lo) ->
      let hi = Option.value hi ~default:(arg - 1) in
      lo >= 0 && hi >= lo && hi < arg && result = hi - lo + 1

let valid2 op ~left ~right ~result =
  match op with
  | Concat -> result = left + right
  | Op (Bil.EQ | Bil.NEQ | Bil.LT | Bil.LE | Bil.SLT | Bil.SLE) ->
      left = right && result = 1
  | Op (Bil.LSHIFT | Bil.RSHIFT | Bil.ARSHIFT) -> result = left
  | Op _ -> left = right && result = left

let word1 op x =
  match op with
  | Lnot -> W.lnot x
  | Neg -> W.neg x
  | Cast (c, n) -> W.cast c n x
  | Extract (hi, lo) -> W.extract_exn ?hi ~lo x

(* A constant's only possible value is itself: it is admitted unless a
   result of its own width excludes it.  Another width supplies no
   evidence. *)
let admits ~(value : W.t) ~(result_width : int) ~(result_has : W.t -> bool) :
    bool =
  result_width <> W.bitwidth value || result_has value

(* Undefined arithmetic supplies no evidence for excluding an input. *)
let word2 op x y =
  let bool b = if b then W.b1 else W.b0 in
  match op with
  | Concat -> Some (W.concat x y)
  | Op (Bil.DIVIDE | Bil.SDIVIDE | Bil.MOD | Bil.SMOD) when W.is_zero y -> None
  | Op op ->
      Some
        (match op with
        | Bil.PLUS -> W.add x y
        | Bil.MINUS -> W.sub x y
        | Bil.TIMES -> W.mul x y
        | Bil.DIVIDE -> W.div x y
        | Bil.SDIVIDE -> W.div (W.signed x) (W.signed y)
        | Bil.MOD -> W.modulo x y
        | Bil.SMOD -> W.modulo (W.signed x) (W.signed y)
        | Bil.LSHIFT -> W.lshift x y
        | Bil.RSHIFT -> W.rshift x y
        | Bil.ARSHIFT -> W.arshift x y
        | Bil.AND -> W.logand x y
        | Bil.OR -> W.logor x y
        | Bil.XOR -> W.logxor x y
        | Bil.EQ -> bool (W.equal (W.unsigned x) (W.unsigned y))
        | Bil.NEQ -> bool (not (W.equal (W.unsigned x) (W.unsigned y)))
        | Bil.LT -> bool W.(unsigned x < unsigned y)
        | Bil.LE -> bool W.(unsigned x <= unsigned y)
        | Bil.SLT -> bool W.(signed x < signed y)
        | Bil.SLE -> bool W.(signed x <= signed y))

module type Representation = sig
  type t

  val bitwidth : t -> int
  val parts : t -> t list
  val assemble : width:int -> t list -> t
  val intersection : t -> t -> t
  val is_bottom : t -> bool
  val unary : unop -> arg:t -> result:t -> t
  val binary : binop -> left:t -> right:t -> result:t -> t * t
end

module Make (R : Representation) = struct
  let backward1 op ~arg ~result =
    if R.is_bottom arg || R.is_bottom result then
      R.assemble ~width:(R.bitwidth arg) []
    else if not (valid1 op ~arg:(R.bitwidth arg) ~result:(R.bitwidth result))
    then arg
    else
      R.assemble ~width:(R.bitwidth arg)
        (List.concat_map (R.parts arg) ~f:(fun a ->
             List.map (R.parts result) ~f:(fun r ->
                 R.intersection a (R.unary op ~arg:a ~result:r))))

  let backward2 op ~left ~right ~result =
    if R.is_bottom left || R.is_bottom right || R.is_bottom result then
      ( R.assemble ~width:(R.bitwidth left) [],
        R.assemble ~width:(R.bitwidth right) [] )
    else if
      not
        (valid2 op ~left:(R.bitwidth left) ~right:(R.bitwidth right)
           ~result:(R.bitwidth result))
    then (left, right)
    else
      let pairs =
        List.concat_map (R.parts left) ~f:(fun a ->
            List.concat_map (R.parts right) ~f:(fun b ->
                List.filter_map (R.parts result) ~f:(fun r ->
                    let x, y = R.binary op ~left:a ~right:b ~result:r in
                    let x = R.intersection a x and y = R.intersection b y in
                    if R.is_bottom x || R.is_bottom y then None else Some (x, y))))
      in
      ( R.assemble ~width:(R.bitwidth left) (List.map pairs ~f:fst),
        R.assemble ~width:(R.bitwidth right) (List.map pairs ~f:snd) )
end
