(* The stack-scope bounds and the escape hulls shared by the sections
   model and the call abstraction.  A position is the model's absolute
   segment line (the entry RSP is [stack_base]); a cell key is
   segment-relative for a stack-symbolic denotation and the value's own
   words otherwise. *)

open Core

module Ws = Cbat_clp_set_composite
module Clp = Cbat_clp

(* Ceiling division of sizes: an empty size spans no elements. *)
let cdiv (x : int) (y : int) : int = (x + y - 1) / y

let position_pair (lo : Cbat_word.t) (hi : Cbat_word.t)
    : (int64 * int64) option =
  let open Base.Option in
  Cbat_word.int64_pair lo hi >>= fun (lo, hi) ->
  Cbat_clp_set_composite.position_of_offset lo >>= fun lo ->
  Cbat_clp_set_composite.position_of_offset hi >>= fun hi ->
  Some (lo, hi)

let stack_floor ~(entry : int64) : int64 =
  Stdlib.Int64.add entry Stdlib.Int64.min_int

let args_ceiling : int64 = Stdlib.Int64.max_int

(* A stack-symbolic set's offset extrema on the position line. *)
let positions_of_offsets (ws : Ws.t) : (int64 * int64) option =
  Option.bind (Ws.offset_extrema ws) ~f:(fun (lo, hi) -> position_pair lo hi)

(* A plain set's unsigned extrema; None when not representable. *)
let unsigned_bounds (ws : Ws.t) : (int64 * int64) option =
  let open Base.Option in
  Ws.min_elem ws >>= fun lo ->
  Ws.max_elem ws >>= fun hi ->
  Cbat_word.int64_pair lo hi

(* An unbounded direction extends to the scope bound; a wrapped or
   circular hull covers the whole scope. *)
let full_bounds (ws : Ws.t) ~(flo : int64) ~(cei : int64) (lo : int64)
    (hi : int64) : int64 * int64 =
  if Stdlib.Int64.compare lo hi > 0 then (flo, cei)
  else if Ws.is_ascending ws then (lo, cei)
  else if Ws.is_descending ws then (flo, hi)
  else (flo, cei)

(* A stack-symbolic value's escape extent on the position line: its
   positions, with the unbounded directions reaching the scope bound. *)
let escape_extent ~(entry : int64) (ws : Ws.t) : (int64 * int64) option =
  match Ws.stack_offsets ws with
  | None -> None
  | Some _ -> (
      let floor = stack_floor ~entry in
      match positions_of_offsets ws with
      | None -> Some (floor, args_ceiling)
      | Some (lo, hi) ->
          if Ws.is_infinite ws || Stdlib.Int64.compare lo hi > 0 then
            Some (full_bounds ws ~flo:floor ~cei:args_ceiling lo hi)
          else Some (lo, hi))

(* The escape clamp in the cell-key space: offsets for a stack-symbolic
   value (the shape a memory cell keys by), the value's own words
   otherwise.  A true unsigned superset — ascending reaches the ceiling,
   descending reaches the floor, a finite set keeps its extrema, and a
   wrapped, circular, or top set spans the whole line, never a swapped
   hull. *)
let key_extent (ws : Ws.t) : (Cbat_word.t * Cbat_word.t) option =
  let zero = Cbat_word.zero 64 and ones = Cbat_word.ones 64 in
  let clamp lo hi =
    if not Cbat_word.(lo <= hi) then (zero, ones)
    else if Ws.is_ascending ws then (lo, ones)
    else if Ws.is_descending ws then (zero, hi)
    else if Ws.is_circular ws then (zero, ones)
    else (lo, hi)
  in
  match Ws.stack_offsets ws with
  | Some offs -> (
      match Clp.min_elem offs, Clp.max_elem offs with
      | Some lo, Some hi -> Some (clamp lo hi)
      | _ -> Some (zero, ones))
  | None -> (
      match Ws.stack_bounds ws with
      | Some (lo, hi) ->
          Some
            (clamp
               (Cbat_word.of_int64 ~width:64 lo)
               (Cbat_word.of_int64 ~width:64 hi))
      | None -> (
          match Ws.min_elem ws, Ws.max_elem ws with
          | Some lo, Some hi -> Some (clamp lo hi)
          | _ -> None))

(* The window extension's capacity; a real SysV window never needs more. *)
let caller_window_bytes : int64 = 65536L

(* The directionless stack top's below-entry clamp: a TOP stack offset
   claims [entry - stack_max, entry). *)
let stack_max : int64 = 65536L
