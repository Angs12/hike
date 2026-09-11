(* Pure stack model: the overlap partition and the region facts.

   THE MODEL IS THE TAG (ADR 0008): the VSA tags every frame-resident access
   with its proven offset span.  This module merges overlapping spans into
   regions and derives each region's facts from those tags alone (T4: the
   denotations left with the T3c servability clause — the SP Slot anchor
   is the privacy mechanism, so the partition is purely geometric).
   An oversized region joins to Frame with a diagnostic naming it —
   never a gate. *)

open Bap.Std
open Bap.Std.Bil.Types
open Bap_core_theory
module Abi = Hike_abi

(* Stack pointer only: the one register granted stack semantics by fiat
   (ADR 0008).  There is no frame-pointer fact here — fp is an ordinary
   callee-saved GPR whose stack-ness, like any register's, is proven by
   the VSA (its frame term), never by name. *)

(* The Vsa record (S10b): the producer/emitter contract point.  The
   producer (hike_vsa) builds it, the KB (hike_kb) stores it, the model
   and the emitter consume it — one home at the contract point. *)
module Vsa = struct
  open Core_kernel[@@warning "-D"]

  (* Alias of the kind enum in [Cbat_extraction]. *)
  type vsa_kind = Cbat_vsa.Cbat_extraction.kind =
    | Range of int64 * int64
    | Infinite of int64 * int64
    | Caller of int64 * int64
    | Mixed of int64 * int64
    | Unbounded
    | Dead
    | VLA of Tid.t
  (* Aliases [equal_kind] for [@@deriving equal]. *)
  let equal_vsa_kind = Cbat_vsa.Cbat_extraction.equal_kind

  type region = {
    id : int;
    span : int64 * int64;
    members : (Tid.t * (int64 * int64)) list;
    convertible : bool;
    max_width : int;
  }
  [@@deriving equal]

  (* [plan <> []] splits into [stack_rN] allocas; [[]] uses one [%frame]. *)
  type split_plan = region list [@@deriving equal]

  (* One call site's outgoing slot facts (T4): which slot index each of
     the block's outgoing stores feeds.  The structured fact IS the
     provability — presence of slot i in the map = the site's store
     feeds promoted slot i; absence = the store stays on the window
     path (the identity). *)
  type call_site = {
    site_slots : (int * Tid.t) list; (* slot index -> storing def *)
  } [@@deriving equal]

  (* Per-def index map: [offsets] — the possible range of each access.
     This is the VSA's entire tag product. *)
  type vsa_info = {
    offsets : vsa_kind Tid.Map.t;
    regions : region list;
    stack_plan : split_plan;
    degraded : bool;
    (* Dynamic-allocation defs (spec §2.3); the producer's one detection,
       read by the emitter instead of re-detecting. *)
    vla_alloc_tids : Tid.Set.t;
    (* T4 stack-arg promotion. [prom_slots]: def tid -> promoted incoming
       slot index (the callee's proven singleton slot reads).
       [prom_arity]: the positional slot count (max index + 1).
       [prom_window]: the sub needs the Caller-Window Parameter (mixed /
       spanned / storing / wide window traffic — the unproven remainder).
       [prom_retaddr]: return-address slot reads (they die with the real
       LLVM ret and must not force a window parameter).
       [prom_sites]: per call block, the outgoing slot stores.
       [prom_resolved]: per indirect call, the singleton lifted target. *)
    prom_slots : int Tid.Map.t;
    prom_arity : int;
    prom_window : bool;
    prom_retaddr : Tid.Set.t;
    prom_sites : call_site Tid.Map.t;
    prom_resolved : Tid.t option Tid.Map.t;
    (* T4: the extents of every stack-symbolic VALUE the sub forms
       (SP-derived addresses computed into non-memory defs — sret
       pointers, escaped cell addresses).  Two consumers: the precise
       decision (a value outside the convertible regions joins the sub
       to Frame — the storage lattice) and the frame sizing (the frame
       covers the formed extents). *)
    sp_extents : (int64 * int64) list;
  }

  (* Hand-written equality over maps. *)
  let equal_vsa_info (i1 : vsa_info) (i2 : vsa_info) : bool =
    Core.Map.equal equal_vsa_kind i1.offsets i2.offsets
    && Base.List.equal equal_region i1.regions i2.regions
    && Base.List.equal equal_region i1.stack_plan i2.stack_plan
    && Bool.equal i1.degraded i2.degraded
    && Core.Set.equal i1.vla_alloc_tids i2.vla_alloc_tids
    && Core.Map.equal Int.equal i1.prom_slots i2.prom_slots
    && Int.equal i1.prom_arity i2.prom_arity
    && Bool.equal i1.prom_window i2.prom_window
    && Core.Set.equal i1.prom_retaddr i2.prom_retaddr
    && Core.Map.equal equal_call_site i1.prom_sites i2.prom_sites
    && Core.Map.equal (Base.Option.equal Tid.equal) i1.prom_resolved
         i2.prom_resolved
    && Base.List.equal
         (fun (a,b) (c,d) -> Int64.equal a c && Int64.equal b d)
         i1.sp_extents i2.sp_extents

  (* Builds info from maps. The promotion fields are optional (empty =
     no promotion) so the fixture grammar stays stable; the trailing
     unit closes the application. *)
  let mk_vsa_info_maps
      ?(prom_slots = Tid.Map.empty)
      ?(prom_arity = 0)
      ?(prom_window = false)
      ?(prom_retaddr = Tid.Set.empty)
      ?(prom_sites = Tid.Map.empty)
      ?(prom_resolved = Tid.Map.empty)
      ?(sp_extents = [])
      ~offsets ~regions ~stack_plan ~degraded
      ~vla_alloc_tids () : vsa_info =
    { offsets; regions; stack_plan; degraded; vla_alloc_tids; prom_slots;
      prom_arity; prom_window; prom_retaddr; prom_sites; prom_resolved;
      sp_extents }

  (* Builds info from lists. *)
  let mk_vsa_info
      ?prom_slots ?prom_arity ?prom_window ?prom_retaddr ?prom_sites
      ?prom_resolved ?sp_extents
      ~offsets ~regions ~stack_plan ~degraded
      ~vla_alloc_tids () : vsa_info =
    mk_vsa_info_maps
      ?prom_slots ?prom_arity ?prom_window ?prom_retaddr ?prom_sites
      ?prom_resolved ?sp_extents
      ~offsets:
        (Base.List.fold_left offsets ~init:Tid.Map.empty
           ~f:(fun m (tid, kind) -> Core.Map.set m ~key:tid ~data:kind))
      ~regions ~stack_plan ~degraded ~vla_alloc_tids ()

  (* Info with no tags. *)
  let empty_vsa_info : vsa_info =
    mk_vsa_info_maps ~offsets:Tid.Map.empty
      ~regions:[] ~stack_plan:[] ~degraded:false
      ~vla_alloc_tids:Tid.Set.empty ()
end
include Vsa



let addr_of_rhs (e : exp) : (exp * Size.t) option =
  let vis =
    object
      inherit [ (exp * Size.t) option ] Exp.visitor
      method! visit_load ~mem:_ ~addr _ s acc =
        Base.Option.first_some acc (Some (addr, s))
      method! visit_store ~mem:_ ~addr ~exp:_ _ s acc =
        Base.Option.first_some acc (Some (addr, s))
    end
  in
  vis#visit_exp e None

(* Splits a store rhs into data and cast wrapper using visitor/mapper. *)
let store_data_of_rhs (e : exp) : (exp * (exp -> exp)) option =
  let vis =
    object
      inherit [ exp option ] Exp.visitor
      method! visit_store ~mem:_ ~addr:_ ~exp:data _ _ acc =
        Base.Option.first_some acc (Some data)
    end
  in
  match vis#visit_exp e None with
  | None -> None
  | Some data ->
      let wrap x =
        let mapper =
          object
            inherit Exp.mapper
            method! map_store ~mem:_ ~addr:_ ~exp:_ _ _ = x
          end
        in
        mapper#map_exp e
      in
      Some (data, wrap)

let slot_of (lo : int64) (bits : int) : var =
  Var.create ~is_virtual:false ~fresh:false
    (Printf.sprintf "slot_%Ld" (Int64.abs lo))
    (Type.Imm bits)

(* The promoted incoming stack-slot parameter of index [i] (T4): the
   callee's own signature fact, minted deterministically so the
   signature and the body agree on the same var. *)
let arg_slot (i : int) : var =
  Var.create ~is_virtual:false ~fresh:false
    (Printf.sprintf "hike_slot%d" i)
    (Type.Imm 64)

(* The call-argument temp of slot [i] (T10): the BIR def a call site
   binds the promoted argument to (the promotion rewrite creates it
   right after the site's outgoing store; the call's emission passes its
   bound value).  Deterministically minted like the slots. *)
let call_arg (i : int) : var =
  Var.create ~is_virtual:false ~fresh:false
    (Printf.sprintf "hike_arg%d" i)
    (Type.Imm 64)

(* Tests for the call-argument temps (the DCE rule: they survive — they
   are the call's arguments, consumed by the emission). *)
let is_call_arg (v : var) : bool =
  Base.String.is_prefix (Var.name v) ~prefix:"hike_arg"

(* The Caller-Window Parameter: the caller-window base, not SP — the
   residual window-base argument of variadic/mixed subs (the bridge) and
   of the memory-convention thunks.  The model owns the var grammar:
   window, slots, and regions all mint here. *)
let hike_window_var : var =
  Var.create ~is_virtual:false ~fresh:false "hike_window" (Type.Imm 64)

(* Region memory and base vars; the alloca's emitted name. *)
let region_name (id : int) : string = Printf.sprintf "stack_r%d" id

let region_mem (id : int) : var =
  Var.create ~is_virtual:false ~fresh:false
    (region_name id ^ "_mem")
    (Type.Mem (Size.addr_of_int_exn 64, Size.of_int_exn 8))

let region_base (id : int) : var =
  Var.create ~is_virtual:false ~fresh:false
    (region_name id ^ "_base") (Type.Imm 64)

(* Memory-var test (the BAP var-kind predicate; the var grammar lives
   here with the fission-var tests). *)
let is_mem var = match Var.typ var with Mem _ -> true | _ -> false

(* Tests for fission var names. *)
let is_region_mem (v : var) : bool =
  Base.String.is_prefix (Var.name v) ~prefix:"stack_r"
  && Base.String.is_suffix (Var.name v) ~suffix:"_mem"

let is_region_base (v : var) : bool =
  Base.String.is_prefix (Var.name v) ~prefix:"stack_r"
  && Base.String.is_suffix (Var.name v) ~suffix:"_base"

(* The region partition's storage rule (T4): a region converts when
   every member is a NEGATIVE singleton `Range` tag — the sub's own
   proven-constant cells.  T3c's servability clause (the whole-sub
   traffic test) is DELETED here: the SP Slot anchor (T4) makes every
   sub's SP neighborhood private, so traffic outside the regions flows
   through the SP-relative lane over the sub's own storage and no
   longer forces the frame model. *)

(* Merges overlapping ranges into regions; the partition decides from
   the tags and the promotion record (T4). *)
let regions_of_sub (sub : sub term) (info : vsa_info) :
    region list =
  (* The ranges ARE the tags: singleton-span Range members at negative
     offsets are this sub's own proven-constant cells. *)
  let ranges : (int64 * int64) Tid.Map.t =
    Core.Map.filter_map info.offsets
      ~f:(fun (kind : vsa_kind) ->
        match kind with
        | Range (lo, hi) -> Some (lo, hi)
        | Infinite _ | Caller _ | Mixed _
        | Unbounded | Dead | VLA _ -> None)
  in
  let facts =
    (* One walk for the widths (the only per-def BIL fact still needed). *)
    Term.enum blk_t sub
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m blk ->
           Term.enum def_t blk
           |> Seq.fold ~init:m ~f:(fun m d ->
                  match addr_of_rhs (Def.rhs d) with
                  | Some (_, s) ->
                      Core.Map.set m ~key:(Term.tid d)
                        ~data:(Size.in_bits s)
                  | None -> m))
  in
  let def_width_of (mtid : tid) : int =
    match Core.Map.find facts mtid with Some w -> w | None -> 64
  in
  (* Connected components of the interval-overlap graph, by sort-and-sweep:
     sort ascending on (lo, hi, tid); a range joins the current component
     when its lo <= the component's max hi — it then overlaps the member
     holding that max (lo_m <= lo_j holds for all earlier members by the
     sort). The (lo, hi, tid) order fixes member and component order. *)
  let merge_components
      (items : (tid * (int64 * int64)) list)
      : (tid * (int64 * int64)) list list =
    let sorted =
      Base.List.sort items
        ~compare:(fun (t1, (lo1, hi1)) (t2, (lo2, hi2)) ->
          let c = Int64.compare lo1 lo2 in
          if c <> 0 then c
          else
            let c = Int64.compare hi1 hi2 in
            if c <> 0 then c else Tid.compare t1 t2)
    in
    let rec sweep cur max_hi rest =
      match rest with
      | [] -> [ Base.List.rev cur ]
      | ((_, (lo, hi)) as x) :: tl ->
          if Int64.compare lo max_hi <= 0 then
            sweep (x :: cur) (if Int64.compare hi max_hi > 0 then hi else max_hi) tl
          else
            Base.List.rev cur :: sweep [ x ] hi tl
    in
    match sorted with
    | [] -> []
    | ((_, (_, hi0)) as x0) :: tl -> sweep [ x0 ] hi0 tl
  in
  let components : (tid * (int64 * int64)) list list =
    merge_components (Core.Map.to_alist ranges)
  in
  (* T4: a cell some call site stores into as its outgoing window slot
     must remain a REAL memory store — the callee's Thunk and the
     Caller-Window Parameter lane read the window memory.  The
     write-closed join: a region holding such a member keeps Frame
     storage (a member that stays memory blocks the region). *)
  let site_stores =
    Core.Map.fold info.prom_sites ~init:Tid.Set.empty
      ~f:(fun ~key:_ ~data:site acc ->
        Base.List.fold site.site_slots ~init:acc
          ~f:(fun acc (_, dtid) -> Core.Set.add acc dtid))
  in
  Base.List.foldi components ~init:[] ~f:(fun i acc members ->
      let span =
        match members with
        | [] -> (0L, 0L)
        | (_, (lo0, hi0)) :: rest ->
            Base.List.fold_left rest ~init:(lo0, hi0)
              ~f:(fun (l, h) (_, (lo, hi)) ->
                (Int64.min l lo, Int64.max h hi))
      in
      (* Storage class, from the tags + the promotion record: every
         member at a NEGATIVE offset (this sub owns the cell) and a
         SINGLETON span (the proven offset is constant) -> Static;
         anything else (mixed ownership, a widened span) -> Frame. *)
      let convertible =
        match members with
        | [] -> false
        | _ ->
            Base.List.for_all members ~f:(fun (mtid, (lo, hi)) ->
                (not (Core.Set.mem site_stores mtid))
                && Int64.compare lo 0L < 0
                && Int64.equal lo hi)
      in
      let max_width =
        Base.List.fold_left members ~init:0 ~f:(fun m (mtid, _) ->
            Int.max m (def_width_of mtid))
      in
      {
        id = i;
        span = span;
        members = members;
        convertible = convertible;
        max_width = max_width;
      }
      :: acc)
  |> Base.List.rev

(* Tests for caller-visible storage: the producer's [Caller] lane
  split (incoming-arg / return-slot denotations at/above entry RSP). *)
let is_abi_visible ~(tag_of : vsa_kind Tid.Map.t) (d : def term) : bool =
  match Core.Map.find tag_of (Term.tid d) with
  | Some (Caller _) -> true
  | _ -> false

(* Stack model decision. *)

(* Returns the region alloca size. *)
let region_bytes (r : region) : int64 =
  let lo, hi = r.span in
  let span_len = Int64.add (Int64.sub hi lo) 1L in
  let raw = Int64.div (Int64.mul span_len (Int64.of_int r.max_width)) 8L in
  let raw = if Int64.compare raw 0L <= 0 then 1L else raw in
  let r = Int64.rem raw 16L in
  if Int64.equal r 0L then raw else Int64.add raw (Int64.sub 16L r)

(* A region whose alloca would exceed the cap joins to Frame (the sound
   fallback storage — Static ⊔ Frame = Frame, per the storage-class
   lattice); the diagnostic names it.  A rule, never a gate: the OTHER
   regions still convert. *)
let region_max_bytes : int64 = 67108864L

(* Rounds a frame size up to 16-byte alignment. *)
let align16_up n =
  let r = Int64.rem n 16L in
  if Int64.equal r 0L then n else Int64.add n (Int64.sub 16L r)

(* Frame-geometry facts for the degraded lane: deepest SP decrement (the
   granted fact: catches rsp-sub prologues and VLAs) and the deepest
   negative access extent.  Extents come from the TAGS (ADR 0008): a
   tagged access's proven offset span IS its extent; an untagged access
   never touches the fallback frame (it emits through the real-address
   lane). *)
let degraded_geometry (sub : sub term) ~(abi : Abi.t)
    (info : vsa_info) : int64 * int64 * bool =
  let is_sp v = Abi.is_sp abi (Var.base v) in
  let max_dec =
    Term.enum blk_t sub
    |> Seq.fold ~init:0L ~f:(fun acc blk ->
           Term.enum def_t blk
           |> Seq.fold ~init:acc ~f:(fun acc d ->
                 match Def.rhs d with
                 | Bil.BinOp (Bil.MINUS, Bil.Var r, Bil.Int w)
                   when is_sp r ->
                     Int64.max acc (Word.to_int64_exn w)
                 | _ -> acc))
  in
  (* Tagged extents: Range/Infinite spans, Unbounded = the whole frame. *)
  let max_neg, has_unbounded =
    Core.Map.fold info.offsets
      ~init:(0L, false)
      ~f:(fun ~key:_ ~data:(kind : vsa_kind) (neg, unb) ->
        match kind with
        | Range (lo, _) | Infinite (lo, _) ->
            let neg =
              if Int64.compare lo 0L < 0 then
                Int64.max neg (Int64.neg (Int64.min lo 0L))
              else neg
            in
            (neg, unb)
        | Mixed (lo, _) ->
            (* The mixed class's frame arm indexes the frame for the
               below-entry truths: the negative extent sizes it. *)
            let neg =
              if Int64.compare lo 0L < 0 then
                Int64.max neg (Int64.neg (Int64.min lo 0L))
              else neg
            in
            (neg, unb)
        | Caller _ -> (neg, unb)
        | Unbounded -> (neg, true)
        | Dead -> (neg, unb)
        | VLA _ -> (neg, true))
  in
  (max_dec, max_neg, has_unbounded)

(* An extent the frame cannot bound: an unordered (wrapped) pair, or a
   span at/above the alloca machinery's 32-bit element boundary (2^31 —
   beyond it the array-type count loses bits, and no real frame lives
   there).  The sound reading of an unboundable extent is UNBOUNDED —
   the extent joins the unbounded classification and the frame takes
   the bounded arm (the 64K window), never a multi-exabyte request
   (T14: spill_many's fake extents folded into a 4-EB span here). *)
let extent_absurd (l : int64) (h : int64) : bool =
  let lo = Int64.min l h and hi = Int64.max l h in
  (* hi - lo >= 2^31 - 1, overflow-safe (a wrapped add reads absurd). *)
  Int64.compare hi (Int64.add lo 0x7fff_ffffL) >= 0

(* The fallback frame's geometry: (alloca bytes, anchor byte index).
   The frame covers every owned-storage fact the record carries — the
   tagged access extents AND the formed stack-value extents (T4: the
   SP-derived addresses the sub computes, e.g. an sret pointer) — the
   SP-decrement walk sizes the no-facts degraded arm, widened to the
   64K caller-arg window on unbounded and floored at the 8192-byte
   degraded minimum. *)
let frame_dims (sub : sub term) ~(abi : Abi.t)
    (info : vsa_info) : int64 * int64 =
  let tags = info.offsets in
  let absurd, min_lo, max_hi, unbounded =
    Core.Map.fold tags ~init:([], 0L, 0L, false)
      ~f:(fun ~key:_ ~data:(kind : vsa_kind) (abs, lo, hi, unb) ->
        match kind with
        | Range (l, h) | Infinite (l, h) ->
            (* Post-split Range/Infinite always reach below the entry
               RSP; the caller window never sizes the frame. *)
            if extent_absurd l h then ((l, h) :: abs, lo, hi, true)
            else (abs, Int64.min lo l, Int64.max hi h, unb)
        | Mixed (l, h) ->
            (* Two-sided: the below-entry side sizes the frame; the
               span may be wrapped, so fold both extrema. *)
            if extent_absurd l h then ((l, h) :: abs, lo, hi, true)
            else
              (abs, Int64.min lo (Int64.min l h), Int64.max hi (Int64.max l h),
               unb)
        | Unbounded | VLA _ -> (abs, lo, hi, true)
        | Caller _ | Dead -> (abs, lo, hi, unb))
  in
  (* The formed stack-value extents (T4), under the same absurd rule. *)
  let absurd, min_lo, max_hi, unbounded =
    Base.List.fold_left info.sp_extents
      ~init:(absurd, min_lo, max_hi, unbounded)
      ~f:(fun (abs, lo, hi, unb) (l, h) ->
        if extent_absurd l h then ((l, h) :: abs, lo, hi, true)
        else (abs, Int64.min lo l, Int64.max hi h, unb))
  in
  Base.List.iter absurd ~f:(fun (l, h) ->
      Hike_diag.warn
        "frame: sub %s: extent span (%Ld,%Ld) is absurd — the frame degrades to the bounded arm"
        (Sub.name sub) l h);
  if Core.Map.is_empty tags && Base.List.is_empty info.sp_extents
  then begin
    let max_dec, max_neg, unbounded = degraded_geometry sub ~abi info in
    let max_neg = if unbounded then Int64.max max_neg 65536L else max_neg in
    let deepest = Int64.max (Int64.max max_dec max_neg) 8L in
    let n = Int64.max (align16_up (Int64.add deepest 8L)) 8192L in
    (n, Int64.sub n 8L)
  end
  else begin
    let max_hi = if unbounded then Int64.max max_hi 65536L else max_hi in
    let span = Int64.sub max_hi min_lo in
    let need = Int64.max (Int64.sub 8L min_lo) (Int64.add span 1L) in
    let n = Int64.max (align16_up need) 8L in
    (n, Int64.sub n 8L)
  end
let is_precise (info : vsa_info) : bool =
  info.stack_plan <> []
  &&
  Base.List.for_all info.regions ~f:(fun r ->
      let lo, _ = r.span in
      if Int64.compare lo 0L >= 0 then true
      else r.convertible)

(* The stack plan IS the convertible regions.  No refusals, no
   recomputation: the record's regions are authoritative (the producer
   built them).  A sub with no convertible regions has an empty plan and
   emits one %frame.  An oversized region joins to Frame storage with a
   diagnostic naming it (the sanctioned channel; the corpus table greps
   these). *)
let split_plan (sub : sub term) (info : vsa_info) :
    split_plan =
  Base.List.filter info.regions ~f:(fun r ->
      r.convertible
      &&
      let b = region_bytes r in
      if Int64.compare b region_max_bytes > 0 then begin
        Hike_diag.warn
          "region: sub %s: region %d span=(%Ld,%Ld) implies %Ld-byte alloca (cap %Ld) — storage Frame"
          (Sub.name sub) r.id
          (fst r.span) (snd r.span)
          b region_max_bytes;
        false
      end
      else true)

(* ------------------------------------------------------------------ *)
(* T10: the emitter's per-sub inputs.  The emitter consumes NO analysis *)
(* record — everything it needs is either STRUCTURE (the promotion's    *)
(* BIR args / arg defs / direct targets, the def-kind slots below) or   *)
(* this narrow LAYOUT fact: the alloca-construction inputs alone (the   *)
(* fallback frame's bytes and the split regions' geometry).  No         *)
(* offsets, no promotion facts, no kinds in it.                         *)
(* ------------------------------------------------------------------ *)

module Sub_layout = struct
  open Core_kernel[@@warning "-D"]

  type t = {
    (* Some n = one %frame alloca of n bytes, anchor at byte n-8 (the
       fallback storage).  None = no fallback frame. *)
    frame_bytes : int64 option;
    (* The split regions: (id, span, alloca bytes) — one [stack_rN]
       alloca each, the GEP offsets relative to [span]. *)
    regions : (int * (int64 * int64) * int64) list;
  }

  (* (id, span, bytes) structural equality/order. *)
  let equal_region (i1, (l1, h1), b1) (i2, (l2, h2), b2) =
    Int.equal i1 i2 && Int64.equal l1 l2 && Int64.equal h1 h2
    && Int64.equal b1 b2

  let compare_region (i1, (l1, h1), b1) (i2, (l2, h2), b2) =
    match Int.compare i1 i2 with
    | 0 -> (
        match Int64.compare l1 l2 with
        | 0 -> (
            match Int64.compare h1 h2 with
            | 0 -> Int64.compare b1 b2
            | c -> c)
        | c -> c)
    | c -> c

  let equal (a : t) (b : t) =
    Base.Option.equal Int64.equal a.frame_bytes b.frame_bytes
    && Base.List.equal equal_region a.regions b.regions

  let compare (a : t) (b : t) : int =
    let frame =
      match (a.frame_bytes, b.frame_bytes) with
      | None, None -> 0
      | None, Some _ -> -1
      | Some _, None -> 1
      | Some x, Some y -> Int64.compare x y
    in
    if frame <> 0 then frame
    else Base.List.compare compare_region a.regions b.regions

  let pp fmt { frame_bytes; regions } =
    Format.fprintf fmt "frame=%s;regions=%d"
      (match frame_bytes with Some n -> Int64.to_string n | None -> "none")
      (Base.List.length regions)

  let empty = { frame_bytes = None; regions = [] }

  let sexp_of_t (t : t) : Sexp.t =
    Sexp.List
      (Sexp.Atom
         (match t.frame_bytes with
          | Some n -> Int64.to_string n
          | None -> "none")
       ::
       Base.List.map t.regions ~f:(fun (id, (lo, hi), b) ->
           Sexp.Atom (Printf.sprintf "%d:%Ld:%Ld:%Ld" id lo hi b)))

  let t_of_sexp (s : Sexp.t) : t =
    let atom_or_fail ~what = function
      | Sexp.Atom a -> a
      | _ -> failwith ("hike-layout: bad " ^ what ^ " sexp")
    in
    match s with
    | Sexp.List (frame :: rs) ->
        let frame_bytes =
          match atom_or_fail ~what:"frame" frame with
          | "none" -> None
          | n -> Some (Int64.of_string n)
        in
        let region_atom a =
          match
            Stdlib.String.split_on_char ':' (atom_or_fail ~what:"region" a)
          with
          | [ id; lo; hi; b ] ->
              (int_of_string id,
               (Int64.of_string lo, Int64.of_string hi),
               Int64.of_string b)
          | _ -> failwith "hike-layout: bad region sexp"
        in
        { frame_bytes; regions = Base.List.map rs ~f:region_atom }
    | _ -> failwith "hike-layout: bad sexp"

  module Stringable = struct
    type nonrec t = t
    let to_string t = Sexp.to_string (sexp_of_t t)
    let of_string s = t_of_sexp (Sexp.of_string s)
  end

  include Core_kernel.Binable.Of_stringable_without_uuid (Stringable)
      [@@warning "-D"]
end

(* Top-level aliases (the mli's re-export shape). *)
type sub_layout = Sub_layout.t = {
  frame_bytes : int64 option;
  regions : (int * (int64 * int64) * int64) list;
}

let empty_layout = Sub_layout.empty

(* The layout rides the SUB TERM (the one tag): the producer computes it
   once; the emitter reads it off the term. *)
let layout_tag : Sub_layout.t Value.Tag.t =
  Value.Tag.register ~package:"hike" ~name:"hike-layout"
    ~uuid:"3f5e1c2a-9b47-4d60-8a15-c4d9e07b2f11"
    (module Sub_layout)

(* Computes the alloca-construction inputs from the record (the exact
   replication of the emitter's former frame decision): precise subs
   carry their split regions; a non-degraded sub with no tags owns no
   stack storage; everything else falls back to one frame sized by
   [frame_dims]. *)
let layout_of_sub (sub : sub term) ~(abi : Abi.t) (info : vsa_info) :
    Sub_layout.t =
  if is_precise info then
    { frame_bytes = None;
      regions =
        Base.List.map info.stack_plan ~f:(fun r ->
            (r.id, r.span, region_bytes r)) }
  else if Core.Map.is_empty info.offsets && not info.degraded then
    Sub_layout.empty
  else
    let n, _ = frame_dims sub ~abi info in
    { frame_bytes = Some n; regions = [] }

let set_layout (l : Sub_layout.t) (sub : sub term) : sub term =
  Term.set_attr sub layout_tag l

(* ------------------------------------------------------------------ *)
(* T10: the per-def tags ride the DEF'S VALUE (the rip_relative_addr   *)
(* precedent): the producer stamps the kind (the 100% Tagging          *)
(* Invariant's tag, plus the VLA marker for the dynamic-allocation      *)
(* defs) onto each def; the emitter reads them off the term — never    *)
(* via a per-sub record.                                                *)
(* ------------------------------------------------------------------ *)

module KB = Bap_knowledge.Knowledge

(* Conflicting kinds for one def (two different classifications were
   stamped — the analyses disagree). *)
type KB.conflict += Def_kind_conflict

let () =
  KB.Conflict.register_printer (function
    | Def_kind_conflict ->
        Some
          "hike: def-kind conflict: two different VSA classifications were stamped for one def (the analyses disagree)"
    | _ -> None)

let kind_domain : vsa_kind option KB.Domain.t =
  KB.Domain.define
    ~inspect:(fun _ -> Base.Sexp.Atom "hike:def-kind")
    ~join:(fun a b ->
      match (a, b) with
      | None, x | x, None -> Ok (if Base.Option.is_none a then b else a)
      | Some a, Some b ->
          if equal_vsa_kind a b then Ok (Some a)
          else Error Def_kind_conflict)
    ~order:(fun a b ->
      match (a, b) with
      | None, None -> KB.Order.EQ
      | None, Some _ -> KB.Order.LT
      | Some _, None -> KB.Order.GT
      | Some a, Some b ->
          if Base.phys_equal a b || equal_vsa_kind a b then KB.Order.EQ
          else KB.Order.NC)
    ~empty:None "hike:def-kind"

(* The def's VSA kind: the producer's classification, read by the
   emitter's tag dispatch and the frame-wrap license. *)
let def_kind_slot : (Theory.Value.cls, vsa_kind option) KB.slot =
  KB.Class.property ~package:"hike" Theory.Value.cls "hike-vsa-kind"
    kind_domain

let def_kind (d : def term) : vsa_kind option =
  KB.Value.get def_kind_slot (Def.value d)

(* Stamps the record's per-def facts onto the sub's defs: the kind tag
   for every tagged def, and the VLA kind for the dynamic-allocation
   defs (whose rhs is a SP decrement — no memory node, hence no tag —
   so the marker travels in the same slot). *)
let stamp_def_kinds (info : vsa_info) (sub : sub term) : sub term =
  Term.map blk_t sub ~f:(fun blk ->
      Term.map def_t blk ~f:(fun d ->
          match
            match Core.Map.find info.offsets (Term.tid d) with
            | Some k -> Some k
            | None ->
                if Core.Set.mem info.vla_alloc_tids (Term.tid d) then
                  Some (VLA (Term.tid d))
                else None
          with
          | None -> d
          | Some k ->
              Def.with_value d
                (KB.Value.put def_kind_slot (Def.value d) (Some k))))
