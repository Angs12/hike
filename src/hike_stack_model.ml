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
module Abi = Hike_abi

(* Stack pointer only: the one register granted stack semantics by fiat
   (ADR 0008).  There is no frame-pointer fact here — fp is an ordinary
   callee-saved GPR whose stack-ness, like any register's, is proven by the
   VSA (its frame term), never by name. *)


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
let regions_of_sub (sub : sub term) (info : Convutils.vsa_info) :
    Convutils.region list =
  (* The ranges ARE the tags: singleton-span Range members at negative
     offsets are this sub's own proven-constant cells. *)
  let ranges : (int64 * int64) Tid.Map.t =
    Core.Map.filter_map info.Convutils.offsets
      ~f:(fun (kind : Convutils.vsa_kind) ->
        match kind with
        | Convutils.Range (lo, hi) -> Some (lo, hi)
        | Convutils.Infinite _ | Convutils.Caller _ | Convutils.Mixed _
        | Convutils.Unbounded | Convutils.Dead | Convutils.VLA _ -> None)
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
    Core.Map.fold info.Convutils.prom_sites ~init:Tid.Set.empty
      ~f:(fun ~key:_ ~data:site acc ->
        Base.List.fold site.Convutils.site_slots ~init:acc
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
        Convutils.id = i;
        Convutils.span = span;
        Convutils.members = members;
        Convutils.convertible = convertible;
        Convutils.max_width = max_width;
      }
      :: acc)
  |> Base.List.rev

(* Tests for caller-visible storage: the producer's [Caller] lane
  split (incoming-arg / return-slot denotations at/above entry RSP). *)
let is_abi_visible ~(tag_of : Convutils.vsa_kind Tid.Map.t) (d : def term) : bool =
  match Core.Map.find tag_of (Term.tid d) with
  | Some (Convutils.Caller _) -> true
  | _ -> false

(* Stack model decision. *)

(* Returns the region alloca size. *)
let region_bytes (r : Convutils.region) : int64 =
  let lo, hi = r.Convutils.span in
  let span_len = Int64.add (Int64.sub hi lo) 1L in
  let raw = Int64.div (Int64.mul span_len (Int64.of_int r.Convutils.max_width)) 8L in
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
    (info : Convutils.vsa_info) : int64 * int64 * bool =
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
    Core.Map.fold info.Convutils.offsets
      ~init:(0L, false)
      ~f:(fun ~key:_ ~data:(kind : Convutils.vsa_kind) (neg, unb) ->
        match kind with
        | Convutils.Range (lo, _) | Convutils.Infinite (lo, _) ->
            let neg =
              if Int64.compare lo 0L < 0 then
                Int64.max neg (Int64.neg (Int64.min lo 0L))
              else neg
            in
            (neg, unb)
        | Convutils.Mixed (lo, _) ->
            (* The mixed class's frame arm indexes the frame for the
               below-entry truths: the negative extent sizes it. *)
            let neg =
              if Int64.compare lo 0L < 0 then
                Int64.max neg (Int64.neg (Int64.min lo 0L))
              else neg
            in
            (neg, unb)
        | Convutils.Caller _ -> (neg, unb)
        | Convutils.Unbounded -> (neg, true)
        | Convutils.Dead -> (neg, unb)
        | Convutils.VLA _ -> (neg, true))
  in
  (max_dec, max_neg, has_unbounded)

(* The fallback frame's geometry: (alloca bytes, anchor byte index).
   The frame covers every owned-storage fact the record carries — the
   tagged access extents AND the formed stack-value extents (T4: the
   SP-derived addresses the sub computes, e.g. an sret pointer) — the
   SP-decrement walk sizes the no-facts degraded arm, widened to the
   64K caller-arg window on unbounded and floored at the 8192-byte
   degraded minimum. *)
let frame_dims (sub : sub term) ~(abi : Abi.t)
    (info : Convutils.vsa_info) : int64 * int64 =
  let tags = info.Convutils.offsets in
  let min_lo, max_hi, unbounded =
    Core.Map.fold tags ~init:(0L, 0L, false)
      ~f:(fun ~key:_ ~data:(kind : Convutils.vsa_kind) (lo, hi, unb) ->
        match kind with
        | Convutils.Range (l, h) | Convutils.Infinite (l, h) ->
            (* Post-split Range/Infinite always reach below the entry
               RSP; the caller window never sizes the frame. *)
            (Int64.min lo l, Int64.max hi h, unb)
        | Convutils.Mixed (l, h) ->
            (* Two-sided: the below-entry side sizes the frame; the
               span may be wrapped, so fold both extrema. *)
            (Int64.min lo (Int64.min l h), Int64.max hi (Int64.max l h), unb)
        | Convutils.Unbounded | Convutils.VLA _ -> (lo, hi, true)
        | Convutils.Caller _ | Convutils.Dead -> (lo, hi, unb))
  in
  (* The formed stack-value extents (T4). *)
  let min_lo, max_hi =
    Base.List.fold_left info.Convutils.sp_extents
      ~init:(min_lo, max_hi)
      ~f:(fun (lo, hi) (l, h) -> (Int64.min lo l, Int64.max hi h))
  in
  if Core.Map.is_empty tags && Base.List.is_empty info.Convutils.sp_extents
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
let is_precise (info : Convutils.vsa_info) : bool =
  info.Convutils.stack_plan <> []
  &&
  Base.List.for_all info.Convutils.regions ~f:(fun r ->
      let lo, _ = r.Convutils.span in
      if Int64.compare lo 0L >= 0 then true
      else r.Convutils.convertible)

(* The stack plan IS the convertible regions.  No refusals, no
   recomputation: the record's regions are authoritative (the producer
   built them).  A sub with no convertible regions has an empty plan and
   emits one %frame.  An oversized region joins to Frame storage with a
   diagnostic naming it (the sanctioned channel; the corpus table greps
   these). *)
let split_plan (sub : sub term) (info : Convutils.vsa_info) :
    Convutils.split_plan =
  Base.List.filter info.Convutils.regions ~f:(fun r ->
      r.Convutils.convertible
      &&
      let b = region_bytes r in
      if Int64.compare b region_max_bytes > 0 then begin
        Hike_diag.warn
          "region: sub %s: region %d span=(%Ld,%Ld) implies %Ld-byte alloca (cap %Ld) — storage Frame"
          (Sub.name sub) r.Convutils.id
          (fst r.Convutils.span) (snd r.Convutils.span)
          b region_max_bytes;
        false
      end
      else true)
