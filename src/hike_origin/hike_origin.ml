(* The runtime origin of a relative value: the concrete pointer the
   offsets are measured from.  One origin per value; the algebra's
   cross-origin rule materialises a mixed computation to [Abs]. *)

open Bap.Std

type t =
  | Abs  (* no origin: the absolute piece union *)
  | Stack  (* the sub's entry SP *)
  | Vla of Tid.t  (* the SP after that def's dynamic decrement *)
  | Window  (* the caller's frame (the call boundary) *)
  | Rip  (* the module base (BAP's rip_relative_addr slot) *)
[@@deriving bin_io, sexp, compare]

(* Core's [(=)] is int equality; origins compare structurally. *)
let equal (a : t) (b : t) : bool = Int.equal (compare a b) 0

(* The per-op table's result row: [Wrap o] = the offsets stay relative
   at [o]; [Materialise] = the bases do not survive the op — both
   hulls, the plain op; [Top] = the op keeps unknown base bits. *)
type rel_row = Wrap of t | Materialise | Top

(* The unary table's row: [Wrap] = the identity; [Image] = the
   certified image of the offsets into the plain tier; [Top]. *)
type un_row = Wrap | Image | Top

(* The per-origin facts on the shared offset line: [base] is the
   constant the offsets add to, [certified] the count of low base bits
   that are facts (ops confined to them compute), [lo]/[hi] the
   materialisation clamps — a hull endpoint with no concrete offset
   clamps to its side's bound, else materialises to top. *)
type facts = {
  base : int64;
  certified : int;
  lo : int64;
  hi : int64;
}

(* The segment base (2^62 + 8): the +8 is the ABI entry residue — a
   call-entered RSP is 8 (mod 16). *)
let segment_base = Stdlib.Int64.add (Stdlib.Int64.shift_left 1L 62) 8L

(* The symbolic stack segment spans 8 MiB around the base. *)
let stack_span = Stdlib.Int64.shift_left 1L 23

(* The window side of the entry line: every positive offset is the
   caller's world; the model layer's args band (which knows the target
   word) starts above the return-address slot. *)
let window_floor = 1L

(* A VLA frame's base is runtime-dependent, so its materialisation
   clamps are the segment's own — the allocation lives on the frame
   line, inside the symbolic span. *)
let facts (t : t) : facts =
  match t with
  | Abs -> { base = 0L; certified = 64; lo = 0L; hi = 0L }
  | Stack | Vla _ ->
    { base = segment_base;
      certified = 4;
      lo = Stdlib.Int64.neg stack_span;
      hi = stack_span }
  | Window ->
    { base = segment_base;
      certified = 4;
      lo = window_floor;
      hi = Stdlib.Int64.max_int }
  | Rip -> { base = 0L; certified = 0; lo = Stdlib.Int64.min_int; hi = Stdlib.Int64.max_int }

let name (t : t) : string =
  match t with
  | Abs -> "abs"
  | Stack -> "stack"
  | Vla _ -> "vla"
  | Window -> "window"
  | Rip -> "rip"

(* The run's VLA extents: the allocation's byte range on the segment
   line (absolute, inclusive), keyed by the decrement def's tid — the
   seed records, the boundary refinement and the attribution read.  The
   one mutable cell of the origin algebra; [take] drains at the facts
   boundary so nothing crosses a program run. *)
module Vla_seed = struct
  let empty : (int64 * int64) Tid.Map.t = Tid.Map.empty

  let extents : (int64 * int64) Tid.Map.t ref = ref empty

  let record (t : Tid.t) (ext : int64 * int64) : unit =
    extents := Core.Map.set !extents ~key:t ~data:ext

  let extent (t : Tid.t) : (int64 * int64) option =
    Core.Map.find !extents t

  let take () : (int64 * int64) Tid.Map.t =
    let e = !extents in
    extents := empty;
    e
end
