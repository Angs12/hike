(* Pure stack model: the overlap partition and the region facts.

   THE MODEL IS THE TAG (ADR 0008): the VSA tags every frame-resident access
   with its proven offset span.  This module merges overlapping spans into
   regions and derives each region's facts from those tags and the solution's
   denotations alone (T3c: the escape fact is deleted — the segment universe
   answers the storage question; see the region partition's servability
   rule).  An oversized region joins to Frame with a diagnostic naming it —
   never a gate. *)

open Bap.Std
open Bap.Std.Bil.Types
module Abi = Hike_abi
module Vsa = Cbat_vsa

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

(* Stored data of a store rhs (no wrapper closure; the model never
   rewrites, only tests). *)
let store_data_exp_of_rhs (e : exp) : exp option =
  let vis =
    object
      inherit [ exp option ] Exp.visitor
      method! visit_store ~mem:_ ~addr:_ ~exp:data _ _ acc =
        Base.Option.first_some acc (Some data)
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

(* The region partition's storage-servability rule (T3c): a region
   converts only when the sub's stack traffic is entirely region-
   servable — every stack access a convertible singleton serves.  The
   segment universe makes all stack memory one address space, but the
   SP-relative lane's neighborhood is private only under the sub's own
   anchor; an access the region lanes cannot serve (any tag but a
   convertible singleton) with a stack-symbolic address operand keeps
   the frame model.  Stack-reachability is DENOTATIONAL:
   [is_stack_access] applied to the operand's value at the def — the
   ONE predicate family, reading the solution's denotations directly.
   There is NO escape fact and no var closure. *)
let unservable_stack_traffic ~(sol : Vsa.vsa_sol)
    ~(offsets : Convutils.vsa_kind Tid.Map.t) (sub : sub term) : bool =
  Term.enum blk_t sub
  |> Seq.exists ~f:(fun blk ->
      let st0 = Graphlib.Std.Solution.get sol (Term.tid blk) in
      let _, found =
        Base.List.fold_left (Term.enum def_t blk |> Seq.to_list)
          ~init:(st0, false)
          ~f:(fun (st, found) d ->
            let st_before = st in
            let st = Vsa.denote_def d st in
            if found then (st, true)
            else
              match Vsa.Cbat_extraction.stack_address_of_rhs (Def.rhs d) with
              | Some addr ->
                let reachable =
                  Exp.free_vars addr
                  |> Core.Set.exists ~f:(fun v ->
                      Vsa.Cbat_extraction.is_stack_access st_before
                        (Bil.Var v))
                in
                let servable =
                  match Core.Map.find offsets (Term.tid d) with
                  | Some (Convutils.Range (lo, hi)) -> Int64.equal lo hi
                  | _ -> false
                in
                (st, reachable && not servable)
              | None -> (st, found))
      in
      found)

(* Merges overlapping ranges into regions; the partition decides from
   the tags and the solution's denotations alone. *)
let regions_of_sub ~(sol : Vsa.vsa_sol) (sub : sub term)
    (info : Convutils.vsa_info) : Convutils.region list =
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
  Base.List.foldi components ~init:[] ~f:(fun i acc members ->
      let span =
        match members with
        | [] -> (0L, 0L)
        | (_, (lo0, hi0)) :: rest ->
            Base.List.fold_left rest ~init:(lo0, hi0)
              ~f:(fun (l, h) (_, (lo, hi)) ->
                (Int64.min l lo, Int64.max h hi))
      in
      (* Storage class, from the tags + the denotations alone:
         - every member at a NEGATIVE offset (this sub owns the cell) and a
           SINGLETON span (the proven offset is constant) → Static;
         - anything else (mixed ownership, a widened span) → Frame.
         The servability rule: if ANY stack access of the sub is not
         region-servable, no region converts — the SP-relative lane's
         neighborhood must stay private (see the T3c verdict,
         BLOCKED-BY-T4: the entry-block alloca anchor removes this). *)
      let convertible =
        if unservable_stack_traffic ~sol ~offsets:info.Convutils.offsets sub
        then false
        else
          match members with
          | [] -> false
          | _ ->
              Base.List.for_all members ~f:(fun (_mtid, (lo, hi)) ->
                  Int64.compare lo 0L < 0
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

(* [abi_visibility_of] over one sub. *)
let abi_visibility_of (info : Convutils.vsa_info) : def term -> bool =
  is_abi_visible ~tag_of:info.Convutils.offsets


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

(* The fallback frame's geometry: (alloca bytes, anchor byte index) for
   every non-precise lane.  With tags, the tagged extents ARE the frame
   extents; with no tags (the degraded arm) the extents come from the
   SP-decrement walk, widened to the 64K caller-arg window on unbounded
   and floored at the 8192-byte degraded minimum. *)
let frame_dims (sub : sub term) ~(abi : Abi.t)
    (info : Convutils.vsa_info) : int64 * int64 =
  let tags = info.Convutils.offsets in
  if Core.Map.is_empty tags then begin
    let max_dec, max_neg, unbounded = degraded_geometry sub ~abi info in
    let max_neg = if unbounded then Int64.max max_neg 65536L else max_neg in
    let deepest = Int64.max (Int64.max max_dec max_neg) 8L in
    let n = Int64.max (align16_up (Int64.add deepest 8L)) 8192L in
    (n, Int64.sub n 8L)
  end
  else begin
    let min_lo, max_hi =
      Core.Map.fold tags ~init:(0L, 0L)
        ~f:(fun ~key:_ ~data:(kind : Convutils.vsa_kind) (lo, hi) ->
          match kind with
          | Convutils.Range (l, h) | Convutils.Infinite (l, h) ->
              (* Post-split Range/Infinite always reach below the entry
                 RSP; the caller window ([Caller]) never sizes the frame. *)
              (Int64.min lo l, Int64.max hi h)
          | Convutils.Mixed (l, h) ->
              (* Two-sided: the below-entry side sizes the frame (the
                 select routes above-entry words to hike_stack); the
                 span may be wrapped, so fold both extrema. *)
              (Int64.min lo (Int64.min l h), Int64.max hi (Int64.max l h))
          | Convutils.Caller _ | Convutils.Unbounded | Convutils.Dead
          | Convutils.VLA _ -> (lo, hi))
    in
    let span = Int64.sub max_hi min_lo in
    let need = Int64.max (Int64.sub 8L min_lo) (Int64.add span 1L) in
    let n = align16_up need in
    (n, Int64.sub n 8L)
  end

(* The emission-shape switch: does this sub split into region allocas
   (plan non-empty) or emit one %frame?  A derived view of the record —
   consumed by the emitter (region-allocas vs %frame, SP erase/keep,
   call-restore suppression) and DCE's precise sweep.  Write-closed:
   for the sub to omit the frame and erase SP, every negative-offset
   region must be convertible. *)
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
