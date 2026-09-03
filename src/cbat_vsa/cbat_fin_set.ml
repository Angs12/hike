(* ************************************************************************* *)
(*  *)
(* Copyright (C) Draper Laboratory. Licensed under project LICENSE. *)
(*  *)
(* This file is provided under the license found in the LICENSE file in *)
(* the top-level directory of this project. *)
(*  *)
(* This work is funded in part by ONR/NAWC Contract N6833518C0107. Its *)
(* content does not necessarily reflect the position or policy of the US *)
(* Government and no official endorsement should be inferred. *)
(*  *)
(* ************************************************************************* *)

open !Core_kernel
open Bap.Std


module WordSet = Cbat_wordset_intf
module WSet = Set.Make_binable(Word)

type t =  WSet.t * int [@@deriving bin_io, sexp]
type idx = int



let of_list ~width l = WSet.of_list l, width
let singleton w =
  let bw = Word.bitwidth w in
  WSet.singleton w, bw

let bitwidth (_, bw) : int = bw

(* Element count wrapped at the bitwidth. *)
let cardinality (s, width) : word =
  Core.Set.length s
  |> Word.of_int ~width:(width + 1)

let signed (s, bw) =
  let signed_s = WSet.map s ~f:Word.signed in
  (signed_s, bw)

let min_elem = Fn.compose Core.Set.min_elt fst
let max_elem = Fn.compose Core.Set.max_elt fst

let max_elem_signed t = max_elem (signed t)
let min_elem_signed t = min_elem (signed t)

let elem w (s, bw) : bool =
  (* Different widths never match. *)
  if Word.bitwidth w <> bw then false
  else Core.Set.mem s w

let iter = Fn.compose Core.Set.elements fst

let lift ?(width=fun x->x) (f : WSet.t -> WSet.t) (s, bw : t) : t = (f s, width bw)

(* Mixed widths coerce to the max. *)
let lift2 ?(width=fun w1 w2 -> Stdlib.max w1 w2)
    (f : WSet.t -> WSet.t -> WSet.t)
    (s1, bw) (s2, bw') : t =
  f s1 s2, width bw bw'

let lift2_pred (f : WSet.t -> WSet.t -> bool)
    (s1, bw) (s2, bw') : bool =
  (* Different widths compare false. *)
  if bw <> bw' then false
  else f s1 s2

let lift_unop (op : word -> word) : WSet.t -> WSet.t = WSet.map ~f:op

(* Cartesian fold of [elem_op]. *)
let lift_binop' (elem_op : word -> word -> word) s1 s2 : WSet.t =
  Core.Set.fold_right s1 ~init:WSet.empty ~f:begin fun w1 init ->
    Core.Set.fold_right s2 ~init ~f:begin fun w2 s ->
      Core.Set.add s (elem_op w1 w2)
    end
  end

let lift_binop (op : word -> word -> word)
    s1 s2 : WSet.t =
  lift_binop' op s1 s2

let lift_binop_signed (op : word -> word -> word)
    s1 s2 : WSet.t =
  lift_binop' (fun w1 w2 -> op (Word.signed w1) (Word.signed w2)) s1 s2

let equal = lift2_pred WSet.equal

let overlap (s1, bw) (s2, bw') : bool =
  (* Different widths never overlap. *)
  if bw <> bw' then false
  else Core.Set.exists s1 ~f:(fun w -> Core.Set.mem s2 w)

let union = lift2 Core.Set.union
let intersection = lift2 Core.Set.inter

(* Exact difference; width mismatch keeps the left set. *)
let diff (s1, bw) (s2, bw') : t =
  if bw <> bw' then (s1, bw)
  else Core.Set.diff s1 s2, bw

let add = lift2 (lift_binop Word.add)
let sub = lift2 (lift_binop Word.sub)
let mul = lift2 (lift_binop Word.mul)

let div = lift2 (lift_binop Word.div)
let sdiv = lift2 (lift_binop_signed Word.div)
let modulo = lift2 (lift_binop Word.modulo)
let smodulo = lift2 (lift_binop_signed Word.modulo)

let arshift = lift2 ~width:Fn.const (lift_binop Word.arshift)
let rshift  = lift2 ~width:Fn.const (lift_binop Word.rshift)
let lshift = lift2 ~width:Fn.const (lift_binop Word.lshift)

let logand : t -> t -> t = lift2 (lift_binop Word.logand)
let logor : t -> t -> t = lift2 (lift_binop Word.logor)
let logxor : t -> t -> t = lift2 (lift_binop Word.logxor)

let lnot = lift (lift_unop Word.lnot)
let neg = lift (lift_unop Word.neg)

let nearest_pred w (s, bw) : word option =
  (* Different widths have no predecessor. *)
  if Word.bitwidth w <> bw then None
  else Core.Set.fold s ~init:None ~f:(fun mmin w' ->
      let diff = Word.sub w w' in
      Option.value_map mmin ~default:(Some diff) ~f:(fun m ->
          if Word.(<=) m diff then Some m else Some diff))

let nearest_succ (i : word) (s : t) : word option =
  Option.map ~f:Word.lnot (nearest_pred (Word.lnot i) (lnot s))

(* True when elements are spaced by a multiple of [w]. *)
let splits_by (s, _ : t) (w : word) : bool =
  (* Local pairwise fold. *)
  let rec map2_shortest ~f l1 l2 = match l1,l2 with
    | [], _
    | _, [] -> []
    | e1::l1', e2::l2' -> f e1 e2 :: (map2_shortest ~f l1' l2') in
  let elems = Core.Set.elements s
              |> List.sort ~compare:Word.compare in
  let open Monads.Std.Monad.Option.Syntax in
  Option.value ~default:true begin
    List.tl elems >>| fun tl ->
    map2_shortest tl elems ~f:Word.sub
    |> List.for_all ~f:(fun diff -> Word.is_zero (Word.modulo diff w))
  end


let extract ?hi ?(lo=0) ((s, bw) : t) : t =
  let new_bw w =
    let hi = Option.value ~default:(w-1) hi in
    hi - lo + 1 in
  if new_bw bw <= 0 then (s, bw)
  else lift ~width:new_bw (lift_unop (Word.extract_exn ?hi ~lo)) (s, bw)

let cast ct (sz : int) ((s, bw) : t) : t =
  if sz <= 0 then (s, bw)
  else lift ~width:(Fn.const sz) (lift_unop (Bil.Apply.cast ct sz)) (s, bw)

let concat = lift2 ~width:(fun w1 w2 -> w1 + w2) (lift_binop Word.concat)

(* Lattice. *)
let precedes = lift2_pred (fun s1 s2 -> Core.Set.is_subset s1 ~of_:s2)
(* Interface stub; unreachable via the composite. *)
let widen_join _ _ = failwith "widen not implemented; usually impractical"
let join = union
let meet = intersection
let bottom bw = WSet.empty, bw

(* Interface stub; unreachable via the composite. *)
let top _ = failwith "top not implemented; usually impractical"
let get_idx = snd

let pp ppf (s, _) =
  Format.fprintf ppf "@[{@ ";
  Set.iter s ~f:(Format.fprintf ppf "%a@ " Word.pp);
  Format.fprintf ppf "}@]"

let compare (s1, bw1) (s2, bw2) =
  if bw1 < bw2 then -1
  else if bw1 > bw2 then 1
  else WSet.compare s1 s2

(* Generic word-set actions. *)

let intersect_generic (type ws) (module WS : WordSet.S with type t = ws)
    (s, bw : t) (s' : ws) : t =
  (* Width mismatch keeps the input. *)
  if WS.bitwidth s' <> bw then (s, bw)
  else
    let keep_set = Core.Set.filter s ~f:(fun w -> WS.elem w s') in
    keep_set, bw

let overlap_generic (type ws) (module WS : WordSet.S with type t = ws)
    (s, bw : t) (s' : ws) : bool =
  (* Width mismatch answers may-overlap. *)
  if WS.bitwidth s' <> bw then not (Core.Set.is_empty s)
  else Core.Set.exists s ~f:(fun w -> WS.elem w s')
