(* The runtime origin of a relative value: the concrete pointer the
   offsets are measured from.  One origin per value; the algebra's
   cross-origin rule materialises a mixed computation to [Abs]. *)

type t =
  | Abs  (* no origin: the absolute piece union *)
  | Stack  (* the sub's entry SP *)
  | Vla  (* the VLA-rebased SP (the dynamic SP decrement) *)
  | Window  (* the caller's frame (the call boundary) *)
  | Rip  (* the module base (BAP's rip_relative_addr slot) *)
[@@deriving bin_io, sexp, compare]

(* Core's [(=)] is int equality; origins compare structurally. *)
let equal (a : t) (b : t) : bool = Int.equal (compare a b) 0

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

(* The VLA band: a runtime-sized allocation relocates its SP to
   [base + anchor] minus the size, so its claims live in
   [floor, anchor) — disjoint from the frame line by construction. *)
let vla_anchor = Stdlib.Int64.shift_left 1L 21
let vla_span = Stdlib.Int64.shift_left 1L 20
let vla_floor = Stdlib.Int64.sub vla_anchor vla_span

(* The window side of the entry line: every positive offset is the
   caller's world; the model layer's args band (which knows the target
   word) starts above the return-address slot. *)
let window_floor = 1L

let facts (t : t) : facts =
  match t with
  | Abs -> { base = 0L; certified = 64; lo = 0L; hi = 0L }
  | Stack ->
    { base = segment_base;
      certified = 4;
      lo = Stdlib.Int64.neg stack_span;
      hi = stack_span }
  | Vla ->
    { base = segment_base;
      certified = 4;
      lo = vla_floor;
      hi = Stdlib.Int64.pred vla_anchor }
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
  | Vla -> "vla"
  | Window -> "window"
  | Rip -> "rip"
