(* The runtime origin of a relative value: the concrete pointer the
   offsets are measured from.  One origin per value; the algebra's
   cross-origin rule materialises a mixed computation to [Abs]. *)

open Bap.Std

type t =
  | Abs  (* no origin: the absolute piece union *)
  | Stack  (* the sub's entry SP — the caller's frame is Stack at/above the entry word *)
  | Fs  (* the ABI thread pointer; offsets are signed TLS/TCB byte offsets *)
  | Rip of Hike_section.t
  (* a module address into that section: offsets are link-time words *)
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

let facts (t : t) : facts =
  match t with
  | Abs -> { base = 0L; certified = 64; lo = 0L; hi = 0L }
  | Stack ->
    { base = segment_base;
      certified = 4;
      lo = Stdlib.Int64.neg stack_span;
      hi = stack_span }
  | Rip _ -> { base = 0L; certified = 64; lo = 0L; hi = 0L }
  | Fs -> { base = 0L; certified = 0;
            lo = Stdlib.Int64.min_int; hi = Stdlib.Int64.max_int }

let name (t : t) : string =
  match t with
  | Abs -> "abs"
  | Stack -> "stack"
  | Fs -> "fs"
  | Rip _ -> "rip"

(* The D10 namespace test: does an origin name the model's stack line.
   An absolute or module-relative origin names no stack cell. *)
let names_stack_line (t : t) : bool =
  match t with
  | Stack -> true
  | Abs | Rip _ | Fs -> false

(* The program's section map: the section each module address lies in.
   Installed once per program from the loaded image. *)
module Regions = struct
  let spans : (Hike_section.t * int64 * int64) list ref = ref []

  let install (rs : (Hike_section.t * int64 * int64) list) : unit = spans := rs

  let of_address (a : int64) : Hike_section.t option =
    Base.List.find_map !spans ~f:(fun (r, lo, hi) ->
        Base.Option.some_if
          (Stdlib.Int64.unsigned_compare lo a <= 0
           && Stdlib.Int64.unsigned_compare a hi <= 0)
          r)
end
