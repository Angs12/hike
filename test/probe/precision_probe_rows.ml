(* The precision probe's classification: the per-sub statistics record and
   the bucket, shape and window rules.  Shared by the probe and its pins. *)

module Ws = Cbat_clp_set_composite
module Origin = Ws.Origin

(* Classification buckets. *)

(* Bottom bucket split by the block's entry state. *)
type def_bucket =
  [ `Exact | `B2_3 | `B4_8 | `B9_64 | `B65p | `Top
  | `Bottom_live | `Bottom_dead ]

(* Bottom bucket split by the block's input state (L1). *)
type ld_bucket =
  [ `Exact | `Bounded | `Top | `Bottom_live | `Bottom_dead ]

(* Window buckets over stack-flagged finite non-top addresses. *)
type win_bucket = [ `W_b64 | `W_4k | `W_2m | `W_big ]

(* The address's shape: the symbolic arm carries its runtime origin; a
   plain value that lands in the segment has lost it. *)
type shape = [ `Stack | `Vla | `Window | `Other | `Lost ]

let classify_shape (ws : Ws.t) : shape =
  match Ws.origin ws with
  | Some Origin.Stack -> `Stack
  | Some (Origin.Vla _) -> `Vla
  | Some Origin.Window -> `Window
  | Some (Origin.Abs | Origin.Rip) -> `Other
  | None -> `Lost

(* Per-sub statistics record. *)

module Sub_stats = struct
  type t = {
    sname : string;
    mutable sub_ms : int;
    (* all-defs series (8 buckets) *)
    mutable def_exact : int;
    mutable def_b2_3 : int;
    mutable def_b4_8 : int;
    mutable def_b9_64 : int;
    mutable def_b65p : int;
    mutable def_top : int;
    mutable def_bottom_live : int;
    mutable def_bottom_dead : int;
    (* load/store address series (6) *)
    mutable ld_exact : int;
    mutable ld_bounded : int;
    mutable ld_top : int;
    mutable ld_bottom_live : int;
    mutable ld_bottom_dead : int;
    mutable ld_denote_err : int;
    (* stack-flagged address subset (5) *)
    mutable ldstk_exact : int;
    mutable ldstk_bounded : int;
    mutable ldstk_top : int;
    mutable ldstk_bottom_live : int;
    mutable ldstk_bottom_dead : int;
    (* window-size buckets (5) *)
    mutable ldstk_w_b64 : int;
    mutable ldstk_w_4k : int;
    mutable ldstk_w_2m : int;
    mutable ldstk_w_big : int;
    mutable ldstk_w_max : int64;
    (* stack-flagged access shape (5) *)
    mutable ldstk_sh_stack : int;
    mutable ldstk_sh_vla : int;
    mutable ldstk_sh_window : int;
    mutable ldstk_sh_other : int;
    mutable ldstk_sh_lost : int;
    (* stack-flagged def shape (5) *)
    mutable defstk_sh_stack : int;
    mutable defstk_sh_vla : int;
    mutable defstk_sh_window : int;
    mutable defstk_sh_other : int;
    mutable defstk_sh_lost : int;
  }

  let create (name : string) : t =
    { sname = name; sub_ms = 0;
      def_exact = 0; def_b2_3 = 0; def_b4_8 = 0; def_b9_64 = 0;
      def_b65p = 0; def_top = 0; def_bottom_live = 0;
      def_bottom_dead = 0;
      ld_exact = 0; ld_bounded = 0; ld_top = 0; ld_bottom_live = 0;
      ld_bottom_dead = 0; ld_denote_err = 0;
      ldstk_exact = 0; ldstk_bounded = 0; ldstk_top = 0;
      ldstk_bottom_live = 0; ldstk_bottom_dead = 0;
      ldstk_w_b64 = 0; ldstk_w_4k = 0; ldstk_w_2m = 0; ldstk_w_big = 0;
      ldstk_w_max = 0L;
      ldstk_sh_stack = 0; ldstk_sh_vla = 0; ldstk_sh_window = 0;
      ldstk_sh_other = 0; ldstk_sh_lost = 0;
      defstk_sh_stack = 0; defstk_sh_vla = 0; defstk_sh_window = 0;
      defstk_sh_other = 0; defstk_sh_lost = 0 }

  (* The shape of one stack-flagged access. *)
  let add_ld_shape (s : t) (sh : shape) : unit =
    match sh with
    | `Stack -> s.ldstk_sh_stack <- s.ldstk_sh_stack + 1
    | `Vla -> s.ldstk_sh_vla <- s.ldstk_sh_vla + 1
    | `Window -> s.ldstk_sh_window <- s.ldstk_sh_window + 1
    | `Other -> s.ldstk_sh_other <- s.ldstk_sh_other + 1
    | `Lost -> s.ldstk_sh_lost <- s.ldstk_sh_lost + 1

  (* The shape of one stack-flagged def. *)
  let add_def_shape (s : t) (sh : shape) : unit =
    match sh with
    | `Stack -> s.defstk_sh_stack <- s.defstk_sh_stack + 1
    | `Vla -> s.defstk_sh_vla <- s.defstk_sh_vla + 1
    | `Window -> s.defstk_sh_window <- s.defstk_sh_window + 1
    | `Other -> s.defstk_sh_other <- s.defstk_sh_other + 1
    | `Lost -> s.defstk_sh_lost <- s.defstk_sh_lost + 1

  (* Count a word def into the series; a stack-flagged def also counts its
     shape. *)
  let add_def (s : t) ~(stack : bool) ~(shape : shape) (b : def_bucket) : unit =
    (match b with
     | `Exact -> s.def_exact <- s.def_exact + 1
     | `B2_3 -> s.def_b2_3 <- s.def_b2_3 + 1
     | `B4_8 -> s.def_b4_8 <- s.def_b4_8 + 1
     | `B9_64 -> s.def_b9_64 <- s.def_b9_64 + 1
     | `B65p -> s.def_b65p <- s.def_b65p + 1
     | `Top -> s.def_top <- s.def_top + 1
     | `Bottom_live -> s.def_bottom_live <- s.def_bottom_live + 1
     | `Bottom_dead -> s.def_bottom_dead <- s.def_bottom_dead + 1);
    if stack then add_def_shape s shape

  let add_ld (s : t) ~(stack : bool) ~(shape : shape) (b : ld_bucket) : unit =
    (match b with
     | `Exact ->
       s.ld_exact <- s.ld_exact + 1;
       if stack then s.ldstk_exact <- s.ldstk_exact + 1
     | `Bounded ->
       s.ld_bounded <- s.ld_bounded + 1;
       if stack then s.ldstk_bounded <- s.ldstk_bounded + 1
     | `Top ->
       s.ld_top <- s.ld_top + 1;
       if stack then s.ldstk_top <- s.ldstk_top + 1
     | `Bottom_live ->
       s.ld_bottom_live <- s.ld_bottom_live + 1;
       if stack then s.ldstk_bottom_live <- s.ldstk_bottom_live + 1
     | `Bottom_dead ->
       s.ld_bottom_dead <- s.ld_bottom_dead + 1;
       if stack then s.ldstk_bottom_dead <- s.ldstk_bottom_dead + 1);
    if stack then add_ld_shape s shape

  let add_window (s : t) (b : win_bucket) : unit =
    match b with
    | `W_b64 -> s.ldstk_w_b64 <- s.ldstk_w_b64 + 1
    | `W_4k -> s.ldstk_w_4k <- s.ldstk_w_4k + 1
    | `W_2m -> s.ldstk_w_2m <- s.ldstk_w_2m + 1
    | `W_big -> s.ldstk_w_big <- s.ldstk_w_big + 1

  (* Accumulate one sub into the BIN sum (w_max takes max). *)
  let add_sum (dst : t) (src : t) : unit =
    dst.sub_ms <- dst.sub_ms + src.sub_ms;
    dst.def_exact <- dst.def_exact + src.def_exact;
    dst.def_b2_3 <- dst.def_b2_3 + src.def_b2_3;
    dst.def_b4_8 <- dst.def_b4_8 + src.def_b4_8;
    dst.def_b9_64 <- dst.def_b9_64 + src.def_b9_64;
    dst.def_b65p <- dst.def_b65p + src.def_b65p;
    dst.def_top <- dst.def_top + src.def_top;
    dst.def_bottom_live <- dst.def_bottom_live + src.def_bottom_live;
    dst.def_bottom_dead <- dst.def_bottom_dead + src.def_bottom_dead;
    dst.ld_exact <- dst.ld_exact + src.ld_exact;
    dst.ld_bounded <- dst.ld_bounded + src.ld_bounded;
    dst.ld_top <- dst.ld_top + src.ld_top;
    dst.ld_bottom_live <- dst.ld_bottom_live + src.ld_bottom_live;
    dst.ld_bottom_dead <- dst.ld_bottom_dead + src.ld_bottom_dead;
    dst.ld_denote_err <- dst.ld_denote_err + src.ld_denote_err;
    dst.ldstk_exact <- dst.ldstk_exact + src.ldstk_exact;
    dst.ldstk_bounded <- dst.ldstk_bounded + src.ldstk_bounded;
    dst.ldstk_top <- dst.ldstk_top + src.ldstk_top;
    dst.ldstk_bottom_live <- dst.ldstk_bottom_live + src.ldstk_bottom_live;
    dst.ldstk_bottom_dead <- dst.ldstk_bottom_dead + src.ldstk_bottom_dead;
    dst.ldstk_w_b64 <- dst.ldstk_w_b64 + src.ldstk_w_b64;
    dst.ldstk_w_4k <- dst.ldstk_w_4k + src.ldstk_w_4k;
    dst.ldstk_w_2m <- dst.ldstk_w_2m + src.ldstk_w_2m;
    dst.ldstk_w_big <- dst.ldstk_w_big + src.ldstk_w_big;
    if Int64.compare src.ldstk_w_max dst.ldstk_w_max > 0 then
      dst.ldstk_w_max <- src.ldstk_w_max;
    dst.ldstk_sh_stack <- dst.ldstk_sh_stack + src.ldstk_sh_stack;
    dst.ldstk_sh_vla <- dst.ldstk_sh_vla + src.ldstk_sh_vla;
    dst.ldstk_sh_window <- dst.ldstk_sh_window + src.ldstk_sh_window;
    dst.ldstk_sh_other <- dst.ldstk_sh_other + src.ldstk_sh_other;
    dst.ldstk_sh_lost <- dst.ldstk_sh_lost + src.ldstk_sh_lost;
    dst.defstk_sh_stack <- dst.defstk_sh_stack + src.defstk_sh_stack;
    dst.defstk_sh_vla <- dst.defstk_sh_vla + src.defstk_sh_vla;
    dst.defstk_sh_window <- dst.defstk_sh_window + src.defstk_sh_window;
    dst.defstk_sh_other <- dst.defstk_sh_other + src.defstk_sh_other;
    dst.defstk_sh_lost <- dst.defstk_sh_lost + src.defstk_sh_lost
end

(* Classification. *)

(* TOP/BOTTOM first; cardn buckets by size; unconvertible is b65p. *)
let classify_def (ws : Ws.t) :
    [ `Exact | `B2_3 | `B4_8 | `B9_64 | `B65p | `Top | `Bottom ] =
  if Ws.is_top ws then `Top
  else if Ws.is_bottom ws then `Bottom
  else
    match Probe_common.cardn_bucket_of_ws ws with
    | Some b -> b
    | None -> `B65p

(* Bottom first; exact/bounded/top/split-bottom. *)
let classify_ld (ws : Ws.t) (input_bottom : bool) : ld_bucket =
  if Ws.is_bottom ws then
    (if input_bottom then `Bottom_dead else `Bottom_live)
  else if Ws.is_top ws then `Top
  else
    match Cbat_word.to_int (Ws.cardinality ws) with
    | Ok 1 -> `Exact
    | _ -> `Bounded

(* Operand class: empty/exact/fin:k/big/top. *)
let classify_operand (ws : Ws.t) : string =
  if Ws.is_top ws then "top"
  else if Ws.is_bottom ws then "empty"
  else
    match Cbat_word.to_int (Ws.cardinality ws) with
    | Error _ -> "big"
    | Ok 0 -> "empty"
    | Ok 1 -> "exact"
    | Ok k when k <= 64 -> Printf.sprintf "fin:%d" k
    | Ok _ -> "big"

(* Signed-span window bucket + int64 value for w_max. *)
let window_metric_of (ws : Ws.t) : win_bucket * int64 option =
  if Ws.bitwidth ws > 64 then (`W_big, None)
  else
    match Ws.min_elem_signed ws, Ws.max_elem_signed ws with
    | Some mn, Some mx ->
      let w = Ws.bitwidth ws in
      let win = Cbat_word.add (Cbat_word.sub mx mn) (Cbat_word.one w) in
      (match Cbat_word.to_int64 win with
       | Ok v when v < 0L -> (`W_big, Some Int64.max_int)
       | Ok 0L -> (`W_big, Some Int64.max_int)
       | Ok v ->
         (if v <= 64L then `W_b64
          else if v <= 4096L then `W_4k
          else if v <= 1048576L then `W_2m
          else `W_big), Some v
       | Error _ -> (`W_big, Some Int64.max_int))
    | _ -> (`W_big, None)
