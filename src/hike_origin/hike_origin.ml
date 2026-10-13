(* The runtime origin of a relative value: the concrete pointer the
   offsets are measured from.  One origin per value; the algebra's
   cross-origin rule materialises a mixed computation to [Abs]. *)

open Bap.Std

type t =
  | Abs  (* no origin: the absolute piece union *)
  | Stack  (* the sub's entry SP *)
  | Vla of Tid.t  (* the SP after that def's dynamic decrement *)
  | Window  (* the caller's frame (the call boundary) *)
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

(* The window side of the entry line: every positive offset is the
   caller's world; the model layer's args band (which knows the target
   word) starts above the return-address slot. *)
let window_floor = 1L

(* VLA bases have no unconditional alignment fact. Their clamps stay
   on the stack line; allocation-specific facts live in Vla_seed. *)
let facts (t : t) : facts =
  match t with
  | Abs -> { base = 0L; certified = 64; lo = 0L; hi = 0L }
  | Stack ->
    { base = segment_base;
      certified = 4;
      lo = Stdlib.Int64.neg stack_span;
      hi = stack_span }
  | Vla _ ->
    { base = segment_base; certified = 0;
      lo = Stdlib.Int64.neg stack_span; hi = stack_span }
  | Window ->
    { base = segment_base;
      certified = 4;
      lo = window_floor;
      hi = Stdlib.Int64.max_int }
  | Rip _ -> { base = 0L; certified = 64; lo = 0L; hi = 0L }

let name (t : t) : string =
  match t with
  | Abs -> "abs"
  | Stack -> "stack"
  | Vla _ -> "vla"
  | Window -> "window"
  | Rip _ -> "rip"

(* The D10 namespace test: does an origin name the model's stack line.
   [Stack], [Window] and a [Vla] frame share the entry-relative line; an
   absolute or module-relative origin names no stack cell. *)
let names_stack_line (t : t) : bool =
  match t with
  | Stack | Window | Vla _ -> true
  | Abs | Rip _ -> false

(* A VLA allocation's fact in the allocation's own frame: the routable
   offsets are frame-relative (0 = the allocation base = the post-move
   SP).  [off_hi] bounds routing below the base (None = unbounded size);
   [base_lo]/[base_hi] are the base's entry-line (segment-relative)
   range, known when the base is bounded — they materialise a
   frame-relative value back to the entry line. *)
type vla_extent = {
  off_lo : int64;
  off_hi : int64 option;
  base_lo : int64 option;
  base_hi : int64 option;
}

(* The run's VLA allocations, keyed by the def that computes each
   allocation's base — the seed records; the boundary refinement, the
   materialiser and the call keep read.  A recorded allocation is a
   candidate until SP takes a value in its frame (or in a frame nested
   below it): an unconfirmed candidate is a pointer below SP, not an
   allocation.  [floors] is the lowest offset SP or a round-down takes
   in each frame; [parents] names the pending frame a nested allocation
   descends from.
   The one mutable cell of the origin algebra; [take] drains at the
   facts boundary so nothing crosses a program run. *)
module Vla_seed = struct
  let extents : vla_extent Tid.Map.t ref = ref Tid.Map.empty
  let floors : int64 Tid.Map.t ref = ref Tid.Map.empty
  let parents : Tid.t Tid.Map.t ref = ref Tid.Map.empty
  let confirmed : Tid.Set.t ref = ref Tid.Set.empty

  let floor_of (t : Tid.t) (lo : int64) : int64 =
    match Core.Map.find !floors t with
    | Some f when Stdlib.Int64.compare f lo < 0 -> f
    | _ -> lo

  (* A re-record keeps the floor already seen for the allocation. *)
  let record ?parent (t : Tid.t) (ext : vla_extent) : unit =
    extents :=
      Core.Map.set !extents ~key:t ~data:{ ext with off_lo = floor_of t ext.off_lo };
    Base.Option.iter parent ~f:(fun p -> parents := Core.Map.set !parents ~key:t ~data:p)

  let extent (t : Tid.t) : vla_extent option = Core.Map.find !extents t

  let parent (t : Tid.t) : Tid.t option = Core.Map.find !parents t

  (* Lower the frame's floor: a round-down's slack, or an SP position
     below the base. *)
  let widen_off_lo (t : Tid.t) (lo : int64) : unit =
    let lo = floor_of t lo in
    floors := Core.Map.set !floors ~key:t ~data:lo;
    match Core.Map.find !extents t with
    | Some e when Stdlib.Int64.compare lo e.off_lo < 0 ->
      extents := Core.Map.set !extents ~key:t ~data:{ e with off_lo = lo }
    | _ -> ()

  let confirm (t : Tid.t) : unit = confirmed := Core.Set.add !confirmed t

  (* The allocations: the confirmed frames and every frame they nest
     below. *)
  let allocations () : Tid.Set.t =
    let rec up acc t =
      if Core.Set.mem acc t then acc
      else
        let acc = Core.Set.add acc t in
        match parent t with Some p -> up acc p | None -> acc
    in
    Core.Set.fold !confirmed ~init:Tid.Set.empty ~f:up
    |> Core.Set.filter ~f:(Core.Map.mem !extents)

  (* Keep only the frames [keep] accepts — the boundary sweep clears a
     sub's own before its authoritative replay. *)
  let filter (keep : Tid.t -> bool) : unit =
    extents := Core.Map.filter_keys !extents ~f:keep;
    floors := Core.Map.filter_keys !floors ~f:keep;
    parents := Core.Map.filter_keys !parents ~f:keep;
    confirmed := Core.Set.filter !confirmed ~f:keep

  let keys () : Tid.Set.t = Core.Map.key_set !extents

  let reset () : unit =
    extents := Tid.Map.empty;
    floors := Tid.Map.empty;
    parents := Tid.Map.empty;
    confirmed := Tid.Set.empty

  (* The run's allocations and their parents, and every candidate's
     extent (a frame that is no allocation still names its stack
     positions); the table is drained. *)
  let take () :
      vla_extent Tid.Map.t * Tid.t Tid.Map.t * vla_extent Tid.Map.t =
    let allocs = allocations () in
    let keep t = Core.Set.mem allocs t in
    let all = !extents in
    let e = Core.Map.filter_keys all ~f:keep in
    let p = Core.Map.filter_keys !parents ~f:keep in
    reset ();
    (e, p, all)
end

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
