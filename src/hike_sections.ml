(* The section home: the data-section facts of a binary (its images,
   the bss copy-reloc slots), and the ownership pass —
   [range_of_denotation] is the ONE mechanism turning an address
   denotation into occupied-byte portions in the represented spaces;
   the immutable visitor collects members into the two collection
   trees; finalization decides each merged range's storage and numbers
   it.  The finalized trees are the authoritative ownership
   representation — no parallel decisions list, no owner cache, no
   query-time rebuild. *)

open! Core
open Bap.Std
module Model = Hike_stack_model
module Vsa = Cbat_vsa

(* ------------------------------------------------------------------ *)
(* Section prep: the project's native data-section bytes, the bss      *)
(* copy-reloc slots, and the named regions.                            *)
(* ------------------------------------------------------------------ *)

type 'a region = { addr : int64; size : int64; info : 'a }

let get_section_mem name proj =
  Project.memory proj |> Memmap.to_sequence
  |> Seq.find ~f:(fun (_, v) ->
      Base.Option.value_map (Value.get Image.section v) ~default:false
        ~f:(fun n -> String.equal n name))

(* Eta-expanded so the weak type variable of the point-free spelling
   resolves here, not at a use site. *)
let get_section_data x =
  Base.Option.map x ~f:(fun (mem, _) ->
      let length = Memory.length mem in
      let min_addr = Memory.min_addr mem in
      let arr = Base.Array.init length ~f:(fun _ -> 0) in
      Memory.iteri ~word_size:`r8 mem ~f:(fun index v ->
          arr.(Word.to_int_exn (Word.( - ) index min_addr)) <- Word.to_int_exn v);
      (arr, Memory.min_addr mem, Memory.max_addr mem))

(* Collects copy-relocated bss slots. *)
let get_copy_relocations proj ~bss_addr ~bss_size =
  let rows =
    let open Ogre in
    let at = Type.("at" %: int) in
    let name = Type.("name" %: str) in
    let nr_tbl = Type.(scheme at $ name) in
    let name_ref () =
      Ogre.declare ~name:"llvm:name-reference" nr_tbl (fun a n -> (a, n))
    in
    let c = Ogre.collect Query.(select (from name_ref)) in
    fst (Ogre.run c (Project.specification proj) |> Core.Or_error.ok_exn)
  in
  Base.Sequence.to_list rows
  |> Base.List.filter_map ~f:(fun (fixup, name) ->
         let off = Stdlib.Int64.sub fixup bss_addr in
         if
           Int64.compare off 0L >= 0
           && Int64.compare off bss_size < 0
         then Some (Int64.to_int_exn off, name)
         else None)
  |> Base.List.dedup_and_sort ~compare:(fun (a, _) (b, _) ->
         Int64.compare (Int64.of_int a) (Int64.of_int b))

let get_named_region_info proj =
  let query =
    let open Ogre in
    let region addr size info = { addr; size; info } in
    let addr = Type.("addr" %: int) in
    let size = Type.("size" %: int) in
    let name = Type.("name" %: str) in
    let table_type = Type.(scheme addr $ size $ name) in
    let named_region () = Ogre.declare ~name:"named-region" table_type region in
    Query.(select (from named_region))
  in
  let regions = Ogre.collect query in
  fst (Ogre.run regions (Project.specification proj) |> Core.Or_error.ok_exn)

type sec = Hike_stack_model.sec [@@deriving equal, compare, sexp]

type data_span = {
  ds_sec : sec;
  ds_lo : int64;
  ds_hi : int64;
  ds_slots : int64 list;
}
[@@deriving equal, compare, sexp]

type point = { p_sec : sec; p_pos : int64 } [@@deriving sexp]
type range = { lo : point; hi : point } [@@deriving sexp]

(* The endpoint seam: the section orders first (declaration order),
   then the domain's numeric order — the signed segment line for the
   sub-local sections, unsigned addresses for the data sections. *)
let compare_point (a : point) (b : point) : int =
  let c = compare_sec a.p_sec b.p_sec in
  if c <> 0 then c
  else
    match a.p_sec with
    | Stack | Args -> Stdlib.Int64.compare a.p_pos b.p_pos
    | _ -> Stdlib.Int64.unsigned_compare a.p_pos b.p_pos

let compare (r1 : range) (r2 : range) : int =
  let c = compare_point r1.lo r2.lo in
  if c <> 0 then c else compare_point r1.hi r2.hi

let equal_point (a : point) (b : point) : bool =
  equal_sec a.p_sec b.p_sec && Stdlib.Int64.equal a.p_pos b.p_pos

let equal (a : range) (b : range) : bool =
  equal_point a.lo b.lo && equal_point a.hi b.hi

let point (s : sec) (pos : int64) : point = { p_sec = s; p_pos = pos }
let range (s : sec) (lo : int64) (hi : int64) : range = { lo = point s lo; hi = point s hi }

type member = {
  m_sec : sec;
  m_lo : int64;
  m_hi : int64;
  m_sub : Tid.t;
  m_def : Tid.t option;
  m_width : int;
  m_store : bool;
  m_identity : bool;
}
[@@deriving equal, compare, sexp]

(* D2: the storage model collapses to regions.  A stack region's id
   keys a per-sub alloca; a data region's id keys a module-wide
   global — a whole span is one data region whose extent is the span,
   served by the section's own image global.  The residue id 0 is the
   stack's fallback alloca (the anchor and the caller window).
   Arg_slot is the promoted incoming register (no alloca). *)
type storage =
  | Stack_region of int
  | Stack_residue
  | Data_region of int
  | Arg_slot of int
  [@@deriving equal, compare, sexp]

type range_storage = { storage : storage; members : member list }
[@@deriving equal, compare, sexp]

module Range_key = struct
  type nonrec t = range
  type nonrec point = point
  let lower r = r.lo
  let upper r = r.hi
  let compare = compare
  let compare_point = compare_point
  let sexp_of_t = sexp_of_range
  let sexp_of_point = sexp_of_point
  let equal = equal
  let equal_point = equal_point
end

module Tree = Bap.Std.Interval_tree.Make (Range_key)

type sub_tree = range_storage Tree.t
type data_tree = range_storage Tree.t

module Tag = Hike_stack_model.Tag

type sec_tag = Hike_stack_model.sec_tag

type ctx = { sub_trees : sub_tree Tid.Map.t; data_tree : data_tree; tags : sec_tag Tid.Map.t }

type portion = {
  pt_sec : sec;
  pt_lo : int64;
  pt_hi : int64;
  pt_elig : bool;
}
[@@deriving equal, compare, sexp]

(* ------------------------------------------------------------------ *)
(* The scope geometry (S01-S03).  The sub-local position line: the     *)
(* entry RSP at [entry], positions signed; the supported line spans    *)
(* [entry + min_int, max_int].  The return-address bytes are           *)
(* [entry, entry+word-1]; Args begins at entry+word.                   *)
(* ------------------------------------------------------------------ *)

let stack_floor ~(entry : int64) : int64 = Stdlib.Int64.add entry Stdlib.Int64.min_int
let args_ceiling : int64 = Stdlib.Int64.max_int

let args_base ~(entry : int64) ~(word : int) : int64 =
  Stdlib.Int64.add entry (Stdlib.Int64.of_int word)

let stack_top ~(entry : int64) ~(word : int) : int64 =
  Stdlib.Int64.pred (args_base ~entry ~word)

(* [hi + n - 1] in signed position arithmetic, saturating at the
   ceiling — the sound full interval, never a wrapped short one. *)
let expand_hi ~(cap : int64) (hi : int64) (n : int) : int64 =
  let w = Stdlib.Int64.of_int (n - 1) in
  let r = Stdlib.Int64.add hi w in
  if Stdlib.Int64.compare r hi < 0 || Stdlib.Int64.compare r cap > 0 then cap else r

(* [hi + n - 1] in unsigned address arithmetic; wrapping past the
   domain's top saturates at the top (2^64-1). *)
let expand_hi_unsigned (hi : int64) (n : int) : int64 =
  let w = Stdlib.Int64.of_int (n - 1) in
  let r = Stdlib.Int64.add hi w in
  if Stdlib.Int64.unsigned_compare r hi < 0 then -1L else r

(* The intersection of [lo, hi] (ordered by [cmp]) with [slo, shi]. *)
let clip ~(cmp : int64 -> int64 -> int) (lo : int64) (hi : int64)
    (slo : int64) (shi : int64) : (int64 * int64) option =
  let lo = if cmp lo slo >= 0 then lo else slo in
  let hi = if cmp hi shi <= 0 then hi else shi in
  if cmp lo hi <= 0 then Some (lo, hi) else None

(* A stack-symbolic set's offset extrema lifted onto the position
   line; None when not representable. *)
let positions_of_offsets (ws : Vsa.WordSet.t) : (int64 * int64) option =
  match Vsa.WordSet.offset_extrema ws with
  | None -> None
  | Some (lo, hi) -> (
      match Cbat_word.to_int64 lo, Cbat_word.to_int64 hi with
      | Ok lo, Ok hi -> (
          match
            ( Vsa.Cbat_extraction.position_of_offset lo,
              Vsa.Cbat_extraction.position_of_offset hi )
          with
          | Some lo, Some hi -> Some (lo, hi)
          | _ -> None)
      | _ -> None)

(* A plain set's unsigned extrema; None when not representable. *)
let unsigned_bounds (ws : Vsa.WordSet.t) : (int64 * int64) option =
  match Vsa.WordSet.min_elem ws, Vsa.WordSet.max_elem ws with
  | Some lo, Some hi -> (
      match Cbat_word.to_int64 lo, Cbat_word.to_int64 hi with
      | Ok lo, Ok hi -> Some (lo, hi)
      | _ -> None)
  | _ -> None

(* The domain bounds of a possibly-infinite set over [flo, cei]: an
   unbounded direction extends to the scope bound; a wrapped or
   circular hull covers the whole scope. *)
let full_bounds (ws : Vsa.WordSet.t) ~(flo : int64) ~(cei : int64)
    (lo : int64) (hi : int64) : int64 * int64 =
  if Stdlib.Int64.compare lo hi > 0 then (flo, cei)
  else if Vsa.WordSet.is_ascending ws then (lo, cei)
  else if Vsa.WordSet.is_descending ws then (flo, hi)
  else (flo, cei)

(* ------------------------------------------------------------------ *)
(* range_of_denotation: the ONE mechanism (S09).  Bottom yields no     *)
(* portion; every reachable unknown address contributes its full       *)
(* possible range to each space it may intersect.                     *)
(* ------------------------------------------------------------------ *)

let range_of_denotation ~(word : int) ~(entry : int64)
    ~(spans : data_span list) ~(rip : bool) ~(width : int)
    (ws : Vsa.WordSet.t) : sec_tag option * portion list =
  let floor = stack_floor ~entry in
  let cei = args_ceiling in
  let a_base = args_base ~entry ~word in
  let s_top = stack_top ~entry ~word in
  (* The Stack/Args portions of an OCCUPIED position interval
     [lo,hi]; the tag carries the ADDRESS bounds [alo,ahi]. *)
  let sub_portions ~(elig : bool) ~(alo : int64) ~(ahi : int64)
      (lo : int64) (hi : int64) : sec_tag option * portion list =
    let tag l h =
      if Stdlib.Int64.compare l a_base >= 0 then Tag.Args (l, h)
      else Tag.Stack (l, h)
    in
    let portion s part =
      Base.Option.map part ~f:(fun (plo, phi) ->
          { pt_sec = s; pt_lo = plo; pt_hi = phi; pt_elig = elig })
    in
    let parts =
      Base.List.filter_map
        [ portion Stack (clip ~cmp:Stdlib.Int64.compare lo hi floor s_top);
          portion Args (clip ~cmp:Stdlib.Int64.compare lo hi a_base cei) ]
        ~f:(fun x -> x)
    in
    ( Option.map
        (clip ~cmp:Stdlib.Int64.compare lo hi floor cei)
        ~f:(fun _ -> tag alo ahi),
      parts )
  in
  (* The directionless stack top's claim (N7): below-entry only,
     clamped by [stack_max] — imprecision never poisons the Args
     slots.  The residue serves the clamped claim; the access itself
     converts to the residue, byte-identical to the raw lane (both
     resolve to the same alloca position). *)
  let clamped_top_sub : sec_tag option * portion list =
    let lo = Stdlib.Int64.sub entry Hike_stack_model.stack_max in
    ( Some Tag.Stack_unbounded,
      snd (sub_portions ~elig:false ~alo:lo
             ~ahi:(Stdlib.Int64.pred entry) lo (Stdlib.Int64.pred entry)) )
  in
  (* N5: a plain top renders through its own address value and claims
     no DATA span (imprecision never poisons the spans).  It still
     claims the sub-local spaces' full range — the residue's identity
     member that keeps a proof-lost stack address's raw lane and the
     carved cells on one storage (write closure). *)
  let plain_top : sec_tag option * portion list =
    (None, snd (sub_portions ~elig:false ~alo:floor ~ahi:cei floor cei))
  in
  if Vsa.WordSet.is_bottom ws then (Some Tag.Dead, [])
  else if Vsa.WordSet.is_top ws then (
    (* A stack-symbolic top is the clamped below-entry claim; a plain
       top is the heap — unless the access carries a proof: a
       rip-relative address is a link-time constant, and top there
       means the analysis lost it. *)
    if Option.is_some (Vsa.WordSet.stack_offsets ws) then clamped_top_sub
    else if rip then
      failwith "hike-sections: a rip-relative access denotated plain top"
    else plain_top)
  else
    match Vsa.WordSet.stack_offsets ws with
    | Some _ -> (
        (* Stack-symbolic: the offset proof lifts onto the line. *)
        match positions_of_offsets ws with
        | None -> clamped_top_sub
        | Some (lo, hi) ->
            let occ_hi = expand_hi ~cap:cei hi width in
            if Vsa.WordSet.is_infinite ws || Stdlib.Int64.compare lo hi > 0 then
              (* An unbounded direction: the full supported bounds of the
                 side the interval reaches, identity. *)
              let nlo, nhi = full_bounds ws ~flo:floor ~cei:cei lo hi in
              let t =
                if Stdlib.Int64.compare nlo a_base >= 0 then Tag.Args_unbounded
                else Tag.Stack (nlo, nhi)
              in
              (Some t, snd (sub_portions ~elig:false ~alo:nlo ~ahi:nhi nlo nhi))
            else
              (* Bounded symbolic: the ONE Stack/Args conversion proof —
                 but only when the occupied bytes stay in one space. *)
              let single =
                Stdlib.Int64.compare occ_hi a_base < 0
                || Stdlib.Int64.compare lo a_base >= 0
              in
              sub_portions ~elig:single ~alo:lo ~ahi:hi lo occ_hi)
    | None -> (
        let in_band = Vsa.WordSet.in_stack_segment ws in
        match (if in_band then unsigned_bounds ws else None) with
        | Some (lo, hi) ->
            (* A plain band hull: its own positions on the line; no
               conversion proof (identity). *)
            sub_portions ~elig:false ~alo:lo ~ahi:hi lo
              (expand_hi ~cap:cei hi width)
        | None -> (
            (* A plain data/foreign address: project into every span by
               intersection. *)
            match unsigned_bounds ws with
            | None ->
                (* The values are provably stack (in the band) but no
                   bound survives: Args vs Locals is lost — a loud
                   failure, never the heap claim. *)
                if in_band then
                  failwith "hike-sections: a stack-band access lost all bounds"
                else plain_top
            | Some (lo, hi) ->
              if
                Vsa.WordSet.is_infinite ws
                && Vsa.WordSet.is_ascending ws
              then
                (* The section axiom: accesses never cross sections, so
                   an unbounded ascending access's minimum names its
                   section; the claim clamps into it.  A rip-relative
                   address carries the proof in its encoding; a
                   non-rip address outside every span is the heap. *)
                if rip then
                  match
                    Base.List.find spans ~f:(fun d ->
                        Stdlib.Int64.unsigned_compare lo d.ds_lo >= 0
                        && Stdlib.Int64.unsigned_compare lo d.ds_hi <= 0)
                  with
                  | Some d ->
                      ( None,
                        [ { pt_sec = d.ds_sec;
                            pt_lo = Stdlib.Int64.max lo d.ds_lo;
                            pt_hi = d.ds_hi;
                            pt_elig = false } ] )
                  | None -> plain_top
                else plain_top
              else
                let occ_hi = expand_hi_unsigned hi width in
                let parts =
                  Base.List.filter_map spans ~f:(fun d ->
                      Base.Option.map
                        (clip ~cmp:Stdlib.Int64.unsigned_compare lo occ_hi d.ds_lo d.ds_hi)
                        ~f:(fun (plo, phi) -> (d, plo, phi)))
                in
                let whole_in_one =
                  match parts with
                  | [ (d, _, _) ] ->
                      Stdlib.Int64.unsigned_compare lo d.ds_lo >= 0
                      && Stdlib.Int64.unsigned_compare occ_hi d.ds_hi <= 0
                  | _ -> false
                in
                (* A copy-relocated slot's bytes are the linker's — an
                   access reaching one has no conversion proof and keeps
                   the through lane. *)
                let at_slot (d, plo, phi) =
                  Base.List.exists d.ds_slots ~f:(fun s ->
                      Stdlib.Int64.unsigned_compare plo s <= 0
                      && Stdlib.Int64.unsigned_compare s phi <= 0)
                in
                let elig =
                  rip && whole_in_one
                  && not (Base.List.exists parts ~f:at_slot)
                in
                let tag =
                  match (parts, elig) with
                  | [ (d, _, _) ], true -> Some (Tag.Sec (d.ds_sec, lo, occ_hi))
                  | _ -> None
                in
                ( tag,
                  Base.List.map parts ~f:(fun (d, plo, phi) ->
                      { pt_sec = d.ds_sec; pt_lo = plo; pt_hi = phi;
                        pt_elig = elig } ))))

(* ------------------------------------------------------------------ *)
(* Collection: the immutable visitor (S10-S11).                        *)
(* ------------------------------------------------------------------ *)

type env = {
  word : int;
  entry : int64;
  spans : data_span list;
  params : var list;
  sp : var;
  denote : blk:blk term -> ?def:def term -> exp ->
           (Vsa.WordSet.t, Type.error) Result.t;
}

(* The escape extent of a denotation: a StackOff proof's positions
   (the full supported bounds when unbounded); None otherwise. *)
let escape_extent ~(entry : int64) (ws : Vsa.WordSet.t) : (int64 * int64) option =
  match Vsa.WordSet.stack_offsets ws with
  | None -> None
  | Some _ -> (
      let floor = stack_floor ~entry in
      match positions_of_offsets ws with
      | None -> Some (floor, args_ceiling)
      | Some (lo, hi) ->
          if Vsa.WordSet.is_infinite ws || Stdlib.Int64.compare lo hi > 0 then
            Some (full_bounds ws ~flo:floor ~cei:args_ceiling lo hi)
          else Some (lo, hi))

type collecting = {
  sub : Tid.t;                        (* the current sub *)
  blk : blk term;                     (* the current blk *)
  tree : member list Tree.t;          (* the current sub's tree *)
  data : member list Tree.t;          (* the program data tree *)
  subs : (member list Tree.t) Tid.Map.t;
  tags : sec_tag Tid.Map.t;
}

(* Inserts a member: the intersecting bindings merge with it into one
   — the inclusive hull, the members joined newest-first. *)
let insert (tree : member list Tree.t) (m : member) : member list Tree.t =
  let key = range m.m_sec m.m_lo m.m_hi in
  let hits = Tree.intersections tree key |> Seq.to_list in
  let rest = Tree.remove_intersections tree key in
  let hull =
    Base.List.fold hits ~init:key ~f:(fun acc (k, _) ->
        { lo = (if compare_point k.lo acc.lo < 0 then k.lo else acc.lo);
          hi = (if compare_point k.hi acc.hi > 0 then k.hi else acc.hi) })
  in
  Tree.add rest hull (Base.List.fold hits ~init:[ m ] ~f:(fun acc (_, ms) -> acc @ ms))

(* The word hull of a data position interval inside its span: the
   words the bytes touch, capped at the span's end (the emitter's
   tiles are word-granular and byte-exact). *)
let word_hull ~(word : int) (d : data_span) (lo : int64) (hi : int64) :
    int64 * int64 =
  let w = Stdlib.Int64.of_int word in
  let off_lo = Stdlib.Int64.sub lo d.ds_lo in
  let idx_lo = Stdlib.Int64.div off_lo w in
  let idx_hi = Stdlib.Int64.div (Stdlib.Int64.sub hi d.ds_lo) w in
  let hull_lo = Stdlib.Int64.add d.ds_lo (Stdlib.Int64.mul w idx_lo) in
  let hull_hi =
    Stdlib.Int64.min d.ds_hi
      (Stdlib.Int64.pred
         (Stdlib.Int64.add d.ds_lo (Stdlib.Int64.mul w (Stdlib.Int64.succ idx_hi))))
  in
  (hull_lo, Stdlib.Int64.max hull_hi hull_lo)

let member_of ~(sub : Tid.t) ~(def : Tid.t option) ~(width : int) ~(store : bool)
    ~(word : int) ~(spans : data_span list) (p : portion) : member =
  let lo, hi =
    match p.pt_sec with
    | Stack | Args -> (p.pt_lo, p.pt_hi)
    | _ -> (
        (* The data side owns the emitter's word grid: a member's
           extent is its occupied bytes snapped OUT to the owning
           span's word hull. *)
        match Base.List.find spans ~f:(fun d -> equal_sec d.ds_sec p.pt_sec) with
        | Some d -> word_hull ~word d p.pt_lo p.pt_hi
        | None -> (p.pt_lo, p.pt_hi))
  in
  { m_sec = p.pt_sec; m_lo = lo; m_hi = hi; m_sub = sub;
    m_def = def; m_width = width; m_store = store;
    m_identity = not p.pt_elig }

(* The identity members of an escape extent, projected into the
   sub-local spaces; no def. *)
let escape_members ~(sub : Tid.t) ~(env : env) (ext : int64 * int64) :
    member list =
  let lo, hi = ext in
  let floor = stack_floor ~entry:env.entry in
  let s_top = stack_top ~entry:env.entry ~word:env.word in
  let a_base = args_base ~entry:env.entry ~word:env.word in
  let member_of_sec s part =
    Base.Option.map part ~f:(fun (plo, phi) ->
        { m_sec = s; m_lo = plo; m_hi = phi; m_sub = sub; m_def = None;
          m_width = 0; m_store = false; m_identity = true })
  in
  Base.List.filter_map
    [ member_of_sec Stack (clip ~cmp:Stdlib.Int64.compare lo hi floor s_top);
      member_of_sec Args (clip ~cmp:Stdlib.Int64.compare lo hi a_base args_ceiling) ]
    ~f:(fun x -> x)

let is_rip_relative (d : def term) : bool =
  Bap_knowledge.Knowledge.Value.get Bap.Std.rip_relative_addr (Def.value d)

(* Pure constant arithmetic: the address shape whose emission evaluates
   to the exact native bits (the sec_comp lane's contract — the
   immediates lane leaves section constants unrendered). *)
let rec is_const_chain (e : exp) : bool =
  match e with
  | Bil.Int _ -> true
  | Bil.BinOp ((Bil.PLUS | Bil.MINUS), e1, e2) ->
    is_const_chain e1 && is_const_chain e2
  | _ -> false

(* The def's memory access: (address, width in bytes, stores). *)
let access_of (d : def term) : (exp * int * bool) option =
  match Model.addr_of_rhs (Def.rhs d) with
  | None -> None
  | Some (addr, size) ->
      Some
        ( addr,
          Size.in_bytes size,
          Option.is_some (Model.store_data_of_rhs (Def.rhs d)) )

let collect (env : env) (prog : program term) : collecting =
  let v =
    object
      inherit [ collecting ] Term.visitor

      method! enter_sub s acc = { acc with sub = Term.tid s; tree = Tree.empty }

      method! leave_sub s acc =
        { acc with subs = Core.Map.set acc.subs ~key:(Term.tid s) ~data:acc.tree }

      method! enter_blk b acc = { acc with blk = b }

      method! leave_blk _ acc =
        (* Parameter registers at the block's post-state: a stack value
           handed to a call escapes (its extent joins the identity
           members). *)
        let acc =
          Base.List.fold env.params ~init:acc ~f:(fun acc v ->
              match env.denote ~blk:acc.blk (Bil.Var v) with
              | Error _ -> acc
              | Ok ws -> (
                  match escape_extent ~entry:env.entry ws with
                  | None -> acc
                  | Some ext ->
                      Base.List.fold (escape_members ~sub:acc.sub ~env ext)
                        ~init:acc
                        ~f:(fun acc m -> { acc with tree = insert acc.tree m })))
        in
        (* The call window: a block that calls has an outgoing-window
           extent the callee (the memory-convention thunk) reads
           through the caller's window integer — the bytes must live
           in the residue region, never a carved one.  One identity
           member spanning the whole call window forces the residue
           and grows its window extent. *)
        let has_call =
          Term.enum jmp_t acc.blk
          |> Seq.exists ~f:(fun j -> Hike_stack_model.call_pushes j)
        in
        if not has_call then acc
        else
          match env.denote ~blk:acc.blk (Bil.Var env.sp) with
          | Error _ -> acc
          | Ok ws -> (
              match positions_of_offsets ws with
              | Some (lo, hi) when Stdlib.Int64.equal lo hi ->
                let sp_abs = lo in
                let win_lo =
                  Stdlib.Int64.sub sp_abs (Stdlib.Int64.of_int env.word) in
                let win_hi =
                  Stdlib.Int64.add
                    (Stdlib.Int64.add sp_abs
                       (Stdlib.Int64.of_int (8 * env.word)))
                    Hike_stack_model.caller_window_bytes
                in
                Base.List.fold (escape_members ~sub:acc.sub ~env (win_lo, win_hi))
                  ~init:acc
                  ~f:(fun acc m -> { acc with tree = insert acc.tree m })
              | _ -> acc)

      method! enter_def d acc =
        let dtid = Term.tid d in
        match access_of d with
        | None -> acc
        | Some (addr, width, store) -> (
            let tag, portions =
              match env.denote ~blk:acc.blk ~def:d addr with
              | Error _ ->
                  (* A failed query keeps the access: the unknown
                     identity contributes full members. *)
                  range_of_denotation ~word:env.word ~entry:env.entry
                    ~spans:env.spans ~rip:false ~width (Vsa.WordSet.top 64)
              | Ok ws ->
                  range_of_denotation ~word:env.word ~entry:env.entry
                    ~spans:env.spans ~rip:(is_rip_relative d) ~width ws
            in
            let acc =
              match tag with
              | Some t -> { acc with tags = Core.Map.set acc.tags ~key:dtid ~data:t }
              | None -> acc
            in
            Base.List.fold portions ~init:acc ~f:(fun acc p ->
                let m =
                  member_of ~sub:acc.sub ~def:(Some dtid) ~width ~store
                    ~word:env.word ~spans:env.spans p
                in
                let sub_local =
                  match p.pt_sec with Stack | Args -> true | _ -> false
                in
                if sub_local then { acc with tree = insert acc.tree m }
                else { acc with data = insert acc.data m })
            |> fun acc ->
            (* A stored stack-symbolic value escapes into memory: its
               reloaded copies deref through the raw lane. *)
            match Model.store_data_of_rhs (Def.rhs d) with
            | None -> acc
            | Some (data, _) -> (
                match env.denote ~blk:acc.blk ~def:d data with
                | Error _ -> acc
                | Ok ws -> (
                    match escape_extent ~entry:env.entry ws with
                    | None -> acc
                    | Some ext ->
                        Base.List.fold (escape_members ~sub:acc.sub ~env ext)
                          ~init:acc
                          ~f:(fun acc m -> { acc with tree = insert acc.tree m }))))
    end
  in
  v#run prog
    { sub = Tid.create ();
      blk = Blk.Builder.result (Blk.Builder.create ());
      tree = Tree.empty;
      data = Tree.empty; subs = Tid.Map.empty; tags = Tid.Map.empty }

(* ------------------------------------------------------------------ *)
(* Finalization: the storage rule and the deterministic numbering      *)
(* (S13, S07).                                                         *)
(* ------------------------------------------------------------------ *)

let align16_up n =
  let r = Stdlib.Int64.rem n 16L in
  if Stdlib.Int64.equal r 0L then n else Stdlib.Int64.add n (Stdlib.Int64.sub 16L r)

let region_max_bytes : int64 = 67108864L

let is_data_sec (s : sec) : bool =
  match s with Stack | Args -> false | _ -> true

(* The data spans served whole (identity): a span with any identity
   binding, or with copy-relocated slots (externally-owned bytes). *)
let whole_spans_of (spans : data_span list) (bindings : (range * member list) list) :
    data_span list =
  let tainted =
    Base.List.filter_map bindings ~f:(fun (k, ms) ->
        if is_data_sec k.lo.p_sec && Base.List.exists ms ~f:(fun m -> m.m_identity)
        then
          Base.List.find spans ~f:(fun d ->
              equal_sec d.ds_sec k.lo.p_sec
              && Stdlib.Int64.unsigned_compare k.lo.p_pos d.ds_lo >= 0
              && Stdlib.Int64.unsigned_compare k.lo.p_pos d.ds_hi <= 0)
        else None)
  in
  Base.List.filter spans ~f:(fun d ->
      (not (Base.List.is_empty d.ds_slots)) || Base.List.mem tainted d ~equal:equal_data_span)

let finalize_tree ~(word : int) ~(entry : int64) ~(spans : data_span list)
    ~(kind : [ `Sub | `Data ]) (tree : member list Tree.t) : range_storage Tree.t =
  let bindings = Tree.to_sequence tree |> Seq.to_list in
  let sorted = Base.List.sort bindings ~compare:(fun (k1, _) (k2, _) -> compare k1 k2) in
  let whole =
    match kind with `Data -> whole_spans_of spans sorted | `Sub -> []
  in
  let in_whole_span (s : sec) (pos : int64) : bool =
    Base.List.exists whole ~f:(fun d ->
        equal_sec d.ds_sec s
        && Stdlib.Int64.unsigned_compare pos d.ds_lo >= 0
        && Stdlib.Int64.unsigned_compare pos d.ds_hi <= 0)
  in
  let ret_lo = entry in
  let ret_hi = Stdlib.Int64.pred (Stdlib.Int64.add entry (Stdlib.Int64.of_int word)) in
  (* D2: the storage rule.  The residue (id 0) is the stack's
     fallback region — the anchor and the caller window.  A whole
     span is ONE data region: every range in it shares the span's id,
     and carved ranges mint ids per range, module-wide (data) / per
     sub (stack). *)
  let regions = ref 0 in
  let globals = ref (-1) in
  let span_ids = ref [] in
  let decide (k : range) (ms : member list) : range_storage =
    let any_identity = Base.List.exists ms ~f:(fun m -> m.m_identity) in
    match k.lo.p_sec with
    | Stack ->
        let overlaps_ret =
          Stdlib.Int64.compare k.hi.p_pos ret_lo >= 0
          && Stdlib.Int64.compare k.lo.p_pos ret_hi <= 0
        in
        let bytes =
          align16_up (Stdlib.Int64.add (Stdlib.Int64.sub k.hi.p_pos k.lo.p_pos) 1L) in
        if overlaps_ret || any_identity || Stdlib.Int64.compare bytes region_max_bytes > 0
        then { storage = Stack_residue; members = ms }
        else (
          incr regions;
          { storage = Stack_region !regions; members = ms })
    | Args -> (
        let base = args_base ~entry ~word in
        let w64 = Stdlib.Int64.of_int word in
        let same_cell lo hi =
          Stdlib.Int64.compare lo base >= 0
          && Stdlib.Int64.equal
               (Stdlib.Int64.div (Stdlib.Int64.sub lo base) w64)
               (Stdlib.Int64.div (Stdlib.Int64.sub hi base) w64)
        in
        if
          (not any_identity)
          && same_cell k.lo.p_pos k.hi.p_pos
          && Base.List.for_all ms ~f:(fun m ->
                 (not m.m_store) && 0 < m.m_width && m.m_width <= word)
        then
          { storage =
              Arg_slot
                (Stdlib.Int64.to_int (Stdlib.Int64.div (Stdlib.Int64.sub k.lo.p_pos base) w64));
            members = ms }
        else { storage = Stack_residue; members = ms })
    | sec ->
        if in_whole_span sec k.lo.p_pos then
      let id =
        match Base.List.Assoc.find !span_ids sec ~equal:equal_sec with
        | Some id -> id
            | None ->
                incr globals;
                span_ids := (sec, !globals) :: !span_ids;
                !globals
          in
          { storage = Data_region id; members = ms }
        else (
          incr globals;
          { storage = Data_region !globals; members = ms })
  in
  Base.List.fold sorted ~init:Tree.empty ~f:(fun t (k, ms) ->
      Tree.add t k (decide k ms))

(* ------------------------------------------------------------------ *)
(* The entries.                                                        *)
(* ------------------------------------------------------------------ *)

let attribute ~(word : int) ~(entry : int64) ~(abi : Hike_abi.t)
    ~(spans : data_span list)
    ~(denote : blk:blk term -> ?def:def term -> exp ->
                (Vsa.WordSet.t, Type.error) Result.t)
    (prog : program term) : ctx =
  let env =
    { word; entry; spans; params = Hike_abi.param_regs abi;
      sp = abi.Hike_abi.sp; denote }
  in
  let collected = collect env prog in
  let sub_trees =
    Core.Map.map collected.subs ~f:(fun tree ->
        finalize_tree ~word ~entry ~spans ~kind:`Sub tree)
  in
  let data_tree = finalize_tree ~word ~entry ~spans ~kind:`Data collected.data in
  { sub_trees; data_tree; tags = collected.tags }

(* The ownership query is the tree's own point-containment lookup: the
   collection invariant (merged bindings do not overlap) makes the
   binding containing the range's least point THE owner. *)
let storage_of_range (tree : range_storage Tree.t) (r : range) :
    range_storage option =
  match Tree.lookup tree r.lo |> Seq.to_list with
  | (_, v) :: _ -> Some v
  | [] -> None

(* The escape-root mem vars: every storage whose range carries identity
   members — bytes an escaped address reaches through another world (a
   callee reading the raw pointer, the window integer).  Their stores'
   reader is never a def of this sub, so the sweep keeps them as
   roots.  Arg_slot ranges carry no storage of their own. *)
let escape_roots_of_tree (tree : sub_tree) : Var.Set.t =
  Tree.to_sequence tree
  |> Seq.fold ~init:Var.Set.empty ~f:(fun acc (_, rs) ->
         if not (Base.List.exists rs.members ~f:(fun m -> m.m_identity)) then acc
         else
           let mem_var = function
             | Stack_region id -> Some (Model.region_mem id)
             | Stack_residue -> Some (Model.region_mem 0)
             | Data_region id -> Some (Model.sec_comp_mem id)
             | Arg_slot _ -> None
           in
           match mem_var rs.storage with
           | Some v -> Core.Set.add acc v
           | None -> acc)

(* The spans served whole, as ONE component covering the span: every
   range in it shares the span's id, and the section's own image
   global is the component's storage (the emitter wires the id to it).
   A span goes whole by [whole_spans_of]: copy-relocated slots, or any
   identity member — a span a computed address walks cannot be carved
   into separate globals. *)
let whole_comps_of ~(word : int) ~(spans : data_span list)
    (ctx : ctx) : (int * int64 * int64) list =
  let bindings = Tree.to_sequence ctx.data_tree |> Seq.to_list in
  let whole =
    whole_spans_of spans
      (Base.List.map bindings ~f:(fun (k, rs) -> (k, rs.members)))
  in
  Base.List.filter_map whole ~f:(fun d ->
      match
        Base.List.find bindings ~f:(fun (k, rs) ->
            equal_sec k.lo.p_sec d.ds_sec
            && (match rs.storage with Data_region _ -> true | _ -> false))
      with
      | Some (_, rs) -> (
          match rs.storage with
          | Data_region id -> Some (id, d.ds_lo, d.ds_hi)
          | _ -> None)
      | None -> None)

(* The emitter spec's Global components from the finalized data tree
   (S24): each CARVED range's word-grid tile and typed-width decision.
   Whole-span ranges contribute nothing here — their span serves whole
   through [whole_comps_of]. *)
let global_comps_of ~(word : int) ~(spans : data_span list)
    (ctx : ctx) : Model.sec_comp list =
  let w = Stdlib.Int64.of_int word in
  let bindings = Tree.to_sequence ctx.data_tree |> Seq.to_list in
  let whole =
    whole_spans_of spans
      (Base.List.map bindings ~f:(fun (k, rs) -> (k, rs.members)))
  in
  let in_whole (s : sec) (pos : int64) =
    Base.List.exists whole ~f:(fun d ->
        equal_sec d.ds_sec s
        && Stdlib.Int64.unsigned_compare pos d.ds_lo >= 0
        && Stdlib.Int64.unsigned_compare pos d.ds_hi <= 0)
  in
  let comps =
    bindings
    |> Base.List.filter_map ~f:(fun (k, rs) ->
        if in_whole k.lo.p_sec k.lo.p_pos then None
        else
          match rs.storage with
          | Data_region id -> (
              match
                Base.List.find spans ~f:(fun d ->
                    equal_sec d.ds_sec k.lo.p_sec)
              with
              | None -> None
              | Some d ->
                  let lo_w =
                    Int64.to_int_exn
                      (Stdlib.Int64.div (Stdlib.Int64.sub k.lo.p_pos d.ds_lo) w)
                  in
                  let hi_w =
                    Int64.to_int_exn
                      (Stdlib.Int64.div (Stdlib.Int64.sub k.hi.p_pos d.ds_lo) w)
                  in
                  let widths =
                    Base.List.filter_map rs.members ~f:(fun m ->
                        if m.m_width > 0 then Some m.m_width else None)
                  in
                  let tile_bytes = ((hi_w - lo_w + 1)) * word in
                  let typed_w =
                    match widths with
                    | w0 :: tl when tile_bytes mod w0 = 0
                                    && Base.List.for_all tl ~f:(Int.equal w0) ->
                      w0
                    | _ -> 1
                  in
                  Some
                    { Model.comp_id = id;
                      Model.sec_lo = d.ds_lo;
                      Model.sec_hi = d.ds_hi;
                      Model.lo_w = lo_w;
                      Model.hi_w = hi_w;
                      Model.typed_w = typed_w })
          | _ -> None)
  in
  Base.List.iter spans ~f:(fun d ->
      let n =
        Base.List.count comps ~f:(fun c ->
            Int64.equal c.Model.sec_lo d.ds_lo
            && Int64.equal c.Model.sec_hi d.ds_hi)
      in
      if n > 0 then
        Hike_diag.warn "sec: span %.8Lx..%.8Lx: %d component(s)" d.ds_lo d.ds_hi n);
  comps

(* The slim tag slot lives in the shared model ([Hike_stack_model]) —
   the attribution stamps it, the emitter reads it. *)
let sec_tag (d : def term) : sec_tag option = Hike_stack_model.sec_tag d

let set_sec_tag (t : sec_tag) (d : def term) : def term =
  Hike_stack_model.set_sec_tag t d

let stamp_tags (c : ctx) (sub : sub term) : sub term =
  Term.map blk_t sub ~f:(fun blk ->
      Term.map def_t blk ~f:(fun d ->
          match Core.Map.find c.tags (Term.tid d) with
          | Some t -> set_sec_tag t d
          | None -> d))

(* ------------------------------------------------------------------ *)
(* The Stack/Args rewrite surface (D1-D4: the range architecture).     *)
(* ------------------------------------------------------------------ *)

(* The layout IS the fold of the finalized tree (D3): every binding
   contributes exactly its obligation, and a member the fold cannot
   serve fails loudly here.  The Stack residue (id 0) is the
   section's fallback alloca — its extent is the below-entry depth of
   every residue member (the push slot and the unbounded 64K floor
   included) plus the caller window; the anchor (the entry RSP's
   runtime position) sits inside it.  Carved regions contribute their
   own align16 allocas.  The Arg_slot rows contribute nothing (a
   promoted register, no alloca). *)
let layout_of_tree ~(word : int) ~(entry : int64) ~(abi : Hike_abi.t)
    ~(sub : sub term) (tree : sub_tree) : Hike_stack_model.sub_layout =
  let w64 = Stdlib.Int64.of_int word in
  let fail_unserved what k =
    failwith
      (Printf.sprintf "hike-layout: unserved %s at %s .. %s" what
         (Base.Sexp.to_string (sexp_of_point k.lo))
         (Base.Sexp.to_string (sexp_of_point k.hi)))
  in
  let bindings = Tree.to_sequence tree |> Seq.to_list in
  (* The residue's below-entry depth and window extent, and the carved
     regions, in one fold. *)
  let ( below, window, carved ), residue_seen =
    Base.List.fold bindings
      ~init:
        ( ( Stdlib.Int64.max (Hike_stack_model.deepest_sp_decrement sub ~abi) w64,
            0L,
            [] ),
          false )
      ~f:(fun ((below, window, carved), residue_seen) (k, rs) ->
        match rs.storage with
        | Arg_slot _ -> ((below, window, carved), residue_seen)
        | Stack_residue ->
            let below =
              if
                Stdlib.Int64.equal k.lo.p_pos (stack_floor ~entry)
                || Stdlib.Int64.compare (Stdlib.Int64.sub entry k.lo.p_pos) 65536L > 0
              then Stdlib.Int64.max below 65536L
              else Stdlib.Int64.max below (Stdlib.Int64.sub entry k.lo.p_pos)
            in
            ((below, window, carved), true)
        | Stack_region id ->
            let bytes =
              align16_up (Stdlib.Int64.add (Stdlib.Int64.sub k.hi.p_pos k.lo.p_pos) 1L)
            in
            if Stdlib.Int64.compare bytes region_max_bytes > 0 then
              fail_unserved "oversized region" k;
            (( below,
               window,
               (id, (k.lo.p_pos, k.hi.p_pos), bytes) :: carved ),
             residue_seen)
        | Data_region _ -> fail_unserved "data binding in a sub tree" k)
  in
  let pushes = Hike_stack_model.has_call_push sub in
  let below = if pushes then Stdlib.Int64.add below w64 else below in
  let below = Stdlib.Int64.max below 8192L in
  let below = if residue_seen then below else Stdlib.Int64.add below w64 in
  (* The window is the constant SysV extent (never smaller in
     practice); a wider reach reads past it the way an unproven
     address always has — the established sound over-approximation. *)
  let window =
    let any_args =
      Base.List.exists bindings ~f:(fun (k, rs) ->
          match rs.storage with
          | Stack_residue -> equal_sec k.lo.p_sec Args
          | _ -> false)
    in
    if any_args || residue_seen then Hike_stack_model.caller_window_bytes
    else 0L
  in
  (* The anchor sits at the entry position inside the residue alloca,
     at the SysV entry-SP residue: idx ≡ 16 − word (mod 16) — the
     lifted word arithmetic (an SSE #GP guard tests (stack_0 + k) &
     15) must evaluate the residue the native does. *)
  let residue_mod = Stdlib.Int64.sub 16L (Stdlib.Int64.rem w64 16L) in
  let anchor_idx =
    Stdlib.Int64.add below
      (Stdlib.Int64.logand
         (Stdlib.Int64.sub residue_mod
            (Stdlib.Int64.rem below 16L))
         15L)
  in
  let residue_bytes =
    align16_up (Stdlib.Int64.add anchor_idx window) in
  let rlo = Stdlib.Int64.sub entry anchor_idx in
  let rhi = Stdlib.Int64.pred (Stdlib.Int64.add entry window) in
  let regions =
    if residue_seen || Stdlib.Int64.compare window 0L > 0 then
      (0, (rlo, rhi), residue_bytes) :: Base.List.rev carved
    else Base.List.rev carved
  in
  let anchor =
    if residue_seen || Stdlib.Int64.compare window 0L > 0 then Some (0, anchor_idx)
    else
      match regions with
      | (id, _, _) :: _ -> Some (id, residue_mod)
      | [] -> None
  in
  (* Any Args-position residue member reads the CALLER's window: the
     direct-call signature carries the hike_window parameter. *)
  let window_param =
    Base.List.exists bindings ~f:(fun (k, rs) ->
        match rs.storage with
        | Stack_residue -> equal_sec k.lo.p_sec Args
        | Arg_slot _ -> false
        | _ -> false)
  in
  { Hike_stack_model.regions; anchor; window_param }

(* Stage A (S16): the call-site correspondence.  At each call block,
   the store START addresses read at their original def positions, the
   call-time SP at the block's post-state: a singleton aligned start
   [a] corresponds to slot [(a - d_sp - word) / word].  Call data for
   the binding rewrite, never an ownership cache. *)
type site_binding = {
  sb_slot : int;                 (* the outgoing slot index *)
  sb_def : def term;             (* the storing def *)
  sb_full : bool;                (* the final store covers the whole cell *)
}

let stage_a ~(word : int) ~(abi : Hike_abi.t) ~(sp : var)
    ~(denote : blk:blk term -> ?def:def term -> exp ->
                (Vsa.WordSet.t, Type.error) Result.t)
    (sub : sub term) : site_binding list Tid.Map.t =
  let w64 = Stdlib.Int64.of_int word in
  let singleton_at ?(def : def term option) ~(blk : blk term) (e : exp) :
      int64 option =
    match denote ~blk ?def e with
    | Error _ -> None
    | Ok ws -> (
        match Vsa.WordSet.stack_offsets ws with
        | Some _ -> (
            match positions_of_offsets ws with
            | Some (lo, hi) when Stdlib.Int64.equal lo hi -> Some lo
            | _ -> None)
        | None ->
            if Vsa.WordSet.in_stack_segment ws then Hike_resolve.singleton_i64 ws
            else None)
  in
  let slot_of_start (a : int64) (d_sp : int64) : int option =
    let rel = Stdlib.Int64.sub a d_sp in
    if
      Stdlib.Int64.compare rel w64 >= 0
      && Stdlib.Int64.equal (Stdlib.Int64.rem rel w64) 0L
    then
      Some
        (Stdlib.Int64.to_int
           (Stdlib.Int64.div (Stdlib.Int64.sub rel w64) w64))
    else None
  in
  Term.enum blk_t sub
  |> Seq.fold ~init:Tid.Map.empty ~f:(fun sites blk ->
         let btid = Term.tid blk in
         let has_call =
           Term.enum jmp_t blk
           |> Seq.exists ~f:(fun j ->
                  match Jmp.kind j with Call _ -> true | _ -> false)
         in
         if not has_call then sites
         else
           match singleton_at ~blk (Bil.Var sp) with
           | None -> Core.Map.set sites ~key:btid ~data:[]
           | Some d_sp ->
               let bindings =
                 Term.enum def_t blk
                 |> Seq.fold ~init:[] ~f:(fun acc d ->
                        match
                          ( Model.addr_of_rhs (Def.rhs d),
                            Model.store_data_of_rhs (Def.rhs d) )
                        with
                        | Some (addr, size), Some _ -> (
                            match singleton_at ~def:d ~blk addr with
                            | Some a -> (
                                match slot_of_start a d_sp with
                                | Some i ->
                                    let cell_lo =
                                      Stdlib.Int64.add
                                        (Stdlib.Int64.add d_sp w64)
                                        (Stdlib.Int64.mul w64
                                           (Stdlib.Int64.of_int i))
                                    in
                                    let occ_hi =
                                      Stdlib.Int64.add a
                                        (Stdlib.Int64.of_int
                                           (Size.in_bytes size - 1))
                                    in
                                    let full =
                                      Stdlib.Int64.equal a cell_lo
                                      && Stdlib.Int64.equal occ_hi
                                           (Stdlib.Int64.add cell_lo
                                              (Stdlib.Int64.pred w64))
                                    in
                                    { sb_slot = i; sb_def = d; sb_full = full }
                                    :: Base.List.filter acc ~f:(fun b ->
                                           not (Int.equal b.sb_slot i))
                                | None -> acc)
                            | None -> acc)
                        | _ -> acc)
               in
               Core.Map.set sites ~key:btid
                 ~data:(Base.List.sort bindings ~compare:(fun a b ->
                      Int.compare a.sb_slot b.sb_slot)))

(* The per-def conversion decision (Stage B steps 1-3): the def's own
   portions at its original position, the owning finalized storage. *)
let region_id_of_storage (s : storage) : int =
  match s with
  | Stack_region n | Data_region n -> n
  | Stack_residue | Arg_slot _ -> 0

type conv =
  | Conv_region of int * (int64 * int64)  (* the region id and span *)
  | Conv_window                           (* the incoming window: the caller's world *)
  | Conv_slot of int * int                (* slot index, intra-slot byte *)
  | Conv_global of int                    (* the component id *)
  | Keep

let conversion_of ~(word : int) ~(entry : int64) ~(spans : data_span list)
    ~(denote : blk:blk term -> ?def:def term -> exp ->
                (Vsa.WordSet.t, Type.error) Result.t)
    ~(tree : sub_tree) ~(data : data_tree)
    ~(blk : blk term) ~(d : def term)
    ~(demoted : int list) : conv * Tag.t option =
  match access_of d with
  | None -> (Keep, None)
  | Some (addr, width, _) -> (
      match denote ~blk ~def:d addr with
      | Error _ -> (Keep, None)
      | Ok ws -> (
          let tag, portions =
            range_of_denotation ~word ~entry ~spans
              ~rip:(is_rip_relative d) ~width ws
          in
          (* An unbounded address keeps the raw lane: its value may live
             in another world's arithmetic (an escaped pointer), and the
             address value itself is the exact fact — the GEP form would
             re-anchor it into THIS sub's storage. *)
          match tag with
          | Some (Tag.Stack_unbounded | Tag.Args_unbounded) ->
              (Keep, tag)
          | _ ->
          (* D1: the retaddr contract keeps its die-with-ret rendering
             (the tag drives the emitter's arm). *)
          let retaddr_cell =
            match tag with
            | Some Tag.Stack (lo, hi) ->
              Stdlib.Int64.equal lo entry && Stdlib.Int64.equal hi entry
            | _ -> false
          in
          let owned =
            Base.List.filter portions ~f:(fun p ->
                match p.pt_sec with
                | Stack | Args -> not retaddr_cell
                | _ -> p.pt_elig && is_const_chain addr)
          in
          match owned with
          | [ p ] -> (
              let owner =
                match p.pt_sec with
                | Stack | Args -> storage_of_range tree (range p.pt_sec p.pt_lo p.pt_hi)
                | _ -> storage_of_range data (range p.pt_sec p.pt_lo p.pt_hi)
              in
              match owner with
              | Some rs -> (
                  match (p.pt_sec, rs.storage) with
                  | (Stack, (Stack_region _ | Stack_residue)) ->
                    (Conv_region (region_id_of_storage rs.storage, (p.pt_lo, p.pt_hi)), tag)
                  | (Args, Stack_residue) -> (Conv_window, tag)
                  | Args, Arg_slot i -> (
                      let d_in =
                        Stdlib.Int64.to_int
                          (Stdlib.Int64.rem
                             (Stdlib.Int64.sub p.pt_lo (args_base ~entry ~word))
                             (Stdlib.Int64.of_int word))
                      in
                      if Base.List.mem demoted i ~equal:Int.equal then
                        (Keep, tag)
                      else (Conv_slot (i, d_in), tag))
                  | _, Data_region id -> (Conv_global id, tag)
                  | _ -> (Keep, tag))
              | None -> (Keep, tag))
          | _ -> (Keep, tag)))

(* Stage B step 4-6 (S18-S20): the memory-node rewrite under the
   def's conversion.  Region accesses keep their model address
   arithmetic — the emitter GEPs the owning region's alloca at
   (position - region_lo), the same relative byte, exact for dynamic
   indices; Arg_slot reads select the cell's bytes at the access's
   intra-slot offset with the BIL endianness rule; everything else
   keeps its lane and its tag. *)
let rewrite_load_node ~(dst : exp) (e : exp) : exp =
  let v =
    object
      inherit Exp.mapper
      method! map_load ~mem ~addr rest s =
        ignore mem;
        ignore addr;
        ignore rest;
        ignore s;
        dst
      method! map_store ~mem ~addr ~exp rest s =
        ignore mem; ignore addr; ignore exp; ignore rest; ignore s;
        dst
    end
  in
  v#map_exp e

(* The Arg_slot byte selection (S20): a read of [n] bytes beginning
   [d] bytes into the word cell selects bits [8d, 8d+8n) little
   endian, [8(W-d-n), 8(W-d-n)+8n) big endian; widths coerce only
   after the selection. *)
let slot_read ~(word : int) (i : int) (d : int) (bits : int) : exp =
  let slot = Bil.Var (Model.arg_slot ~word i) in
  let wbits = word * 8 in
  if d = 0 then
    if Int.equal bits wbits then slot
    else Bil.Cast (Bil.LOW, bits, slot)
  else if Int.equal bits wbits then slot
  else Bil.Extract (8 * d + bits - 1, 8 * d, slot)

(* The total re-point mapper: EVERY memory node of the expression —
   the root and the ones nested in store data or load addresses —
   re-points at [mem_var] (per-cell world consistency: a converted def
   keeps no raw-model node).  The children arrive unmapped at the
   override, so the address and the store data are mapped explicitly. *)
let repoint_mapper (mem_var : var) =
  object
    inherit Exp.mapper as super
    method! map_load ~mem:_ ~addr rest s =
      Bil.Load (Bil.Var mem_var, super#map_exp addr, rest, s)
    method! map_store ~mem:_ ~addr ~exp rest s =
      Bil.Store
        (Bil.Var mem_var, super#map_exp addr, super#map_exp exp, rest, s)
  end

(* One def's rewrite: the memory node re-points at the owning
   storage's mem var (the address keeps its arithmetic); the Arg_slot
   load reads the parameter's selected bytes. *)
let rewrite_def ~(word : int) ~(conv : conv) ~(bits : int) (d : def term) :
    def term =
  match conv with
  | Keep -> d
  | Conv_region (id, _) ->
      let mem_var = Model.region_mem id in
      let d =
        Def.map_exp d ~f:(fun e -> (repoint_mapper mem_var)#map_exp e)
      in
      if Model.is_mem (Def.lhs d) then Def.with_lhs d mem_var else d
  | Conv_window ->
      let mem_var = Model.window_mem in
      let d =
        Def.map_exp d ~f:(fun e -> (repoint_mapper mem_var)#map_exp e)
      in
      if Model.is_mem (Def.lhs d) then Def.with_lhs d mem_var else d
  | Conv_global id ->
      let mem_var = Model.sec_comp_mem id in
      Def.map_exp d ~f:(fun e -> (repoint_mapper mem_var)#map_exp e)
  | Conv_slot (i, din) ->
      let read = slot_read ~word i din bits in
      Def.map_exp d ~f:(fun e -> rewrite_load_node ~dst:read e)

(* Stage C (S21): the call-argument bindings.  Each site's full-cell
   store gains its [hike_argN] def at the storing def's point, binding
   the STORING DEF's own value — the bytes actually written, never a
   later state.  Partial final stores bind nothing: the slot takes the
   Window rule on both sides. *)
let bind_site_args ~(word : int) (bindings : site_binding list)
    (blk : blk term) : blk term =
  Base.List.fold bindings ~init:blk ~f:(fun blk b ->
      if not b.sb_full then blk
      else
        (* S21: the parameter binds the bytes the store WROTE — the
           store's data expression, never the def's lhs (a memory-
           typed model var when the store went through the model's
           memory). *)
        let data =
          match Model.store_data_of_rhs (Def.rhs b.sb_def) with
          | Some (data, _) -> data
          | None -> Bil.Var (Def.lhs b.sb_def)
        in
        let arg = Def.create (Model.call_arg ~word b.sb_slot) data in
        match Term.next def_t blk (Term.tid b.sb_def) with
        | Some next -> Term.prepend def_t blk ~before:(Term.tid next) arg
        | None -> Term.append def_t blk arg)

(* ------------------------------------------------------------------ *)
(* The promotion: the callee-side window-traffic classification, the   *)
(* caller-side resolution, and the BIR rewrite (moved to the section   *)
(* home).                                                              *)
(* ------------------------------------------------------------------ *)

(* The VLA event's shape (mechanism 1): the def moves SP by a runtime
   size — the direct [SP +/- X] whose X the code never fixes (it is no
   literal and resolves through no def chain to one), or a copy chain
   reaching such a form.  Pure BIR shape: no denotation is read. *)
let dynamic_alloc_tids_of ~(sp : var)
    ~(denote : blk:blk term -> ?def:def term -> exp ->
                (Vsa.WordSet.t, Type.error) Result.t)
    (sub : sub term) : Tid.Set.t =
  let sp_base = Var.base sp in
  let is_sp v = Var.equal (Var.base v) sp_base in
  (* N6: the shape seeds the candidate; the SIZE's own denotation at
     the def confirms — a SINGLETON displacement is a proven-constant
     frame adjust (no alloca), a non-singleton or unknown displacement
     is the runtime move (the VLA event).  Exact where the shape test
     alone false-positives (the in-corpus {32} displacement). *)
  let runtime_at ~blk ~def d sz =
    match denote ~blk ~def:d sz with
    | Error _ -> true
    | Ok ws ->
      not (Cbat_vsa.WordSet.is_top ws)
      && (match Cbat_vsa.WordSet.min_elem ws, Cbat_vsa.WordSet.max_elem ws with
          | Some lo, Some hi -> not (Cbat_word.equal lo hi)
          | _ -> true)
  in
  (* One-line contract: the size the code does not fix - a literal is
     fixed, a var defers to its def, a def cycle or any other exp is
     runtime. *)
  let rec runtime_size chain seen sz =
    match sz with
    | Bil.Int _ -> false
    | Bil.Var v -> var_size chain seen v
    | _ -> true
  and var_size chain seen v =
    let b = Var.base v in
    if Core.Set.mem seen b then true
    else
      let next d = runtime_size chain (Core.Set.add seen b) (Def.rhs d) in
      Option.value ~default:true (Option.map ~f:next (Core.Map.find chain b))
  in
  (* N6's direction fact: the def's VALUE (the rhs denoted at the def)
     lands strictly below the old SP — the VLA is a decrement.  An
     unrepresentable value or an unknown old SP keeps the seed's
     verdict (unknown = the runtime move). *)
  let descends ~blk ~def d =
    match
      (denote ~blk ~def:d (Bil.Var sp_base), denote ~blk ~def:d (Def.rhs d))
    with
    | Ok old, Ok neu when not (Vsa.WordSet.is_top neu) -> (
      match (Vsa.WordSet.stack_offsets old, Vsa.WordSet.stack_offsets neu) with
      | Some old_offs, Some neu_offs -> (
        match Model.singleton_offset old_offs with
        | Some old_off -> (
          match Vsa.WordSet.Clp.max_elem neu_offs with
          | Some nhi -> (
            match Cbat_word.to_int64 nhi with
            | Ok hi -> Stdlib.Int64.compare hi old_off < 0
            | Error _ -> true)
          | None -> true)
        | None -> true)
      | _ -> true)
    | _ -> true
  in
  (* One-line contract: the rhs that moves SP by a runtime size - the
     direct [SP +/- X] form or the copy chain reaching it. *)
  let rec event_rhs chain seen rhs =
    match rhs with
    | Bil.BinOp ((Bil.PLUS | Bil.MINUS), Bil.Var a, sz) when is_sp a ->
      runtime_size chain seen sz
    | Bil.Var v ->
      let b = Var.base v in
      if Core.Set.mem seen b then false
      else
        let next d = event_rhs chain (Core.Set.add seen b) (Def.rhs d) in
        Option.value ~default:false
          (Option.map ~f:next (Core.Map.find chain b))
    | _ -> false
  in
  (* The sequential walk: the chain holds the defs seen so far, in
     block/def order. *)
  Term.enum blk_t sub
  |> Seq.fold ~init:(Tid.Set.empty, Var.Map.empty)
       ~f:(fun (events, chain) blk ->
         Seq.fold (Term.enum def_t blk) ~init:(events, chain)
           ~f:(fun (events, chain) d ->
             if is_sp (Def.lhs d) then
               (match Model.addr_of_rhs (Def.rhs d) with
                | Some (sz, _) ->
                  if event_rhs chain Var.Set.empty (Def.rhs d)
                     && runtime_at ~blk ~def:d d sz
                     && descends ~blk ~def:d d
                  then (Core.Set.add events (Term.tid d), chain)
                  else (events, chain)
                | None ->
                  if event_rhs chain Var.Set.empty (Def.rhs d)
                     && descends ~blk ~def:d d
                  then (Core.Set.add events (Term.tid d), chain)
                  else (events, chain))
             else
               (events,
                Core.Map.set chain ~key:(Var.base (Def.lhs d)) ~data:d)))
       |> fst

(* The producer's per-sub facts: the promotion lanes, the formed
   SP-extents, the dynamic-allocation events, and the window class.
   The fixpoint fold computes them in scope; the stamp/promote fold
   consumes them in scope — never KB-stored. *)
type facts = {
  prom_arity : int;
  prom_sites : Model.call_site Tid.Map.t;
  prom_resolved : Tid.t option Tid.Map.t;
}

(* The offset set's hull lifted onto the segment line: the extrema
   through to_int64 and position_of_offset; [None] when any step
   fails (an extremum outside the word or past the base sum). *)
let hull_positions (offs : Vsa.WordSet.Clp.t) : (int64 * int64) option =
  match Vsa.WordSet.Clp.min_elem offs, Vsa.WordSet.Clp.max_elem offs with
  | Some mn, Some mx -> (
      match Cbat_word.to_int64 mn, Cbat_word.to_int64 mx with
      | Ok lo, Ok hi -> (
          match
            Vsa.Cbat_extraction.position_of_offset lo,
            Vsa.Cbat_extraction.position_of_offset hi
          with
          | Some lo, Some hi -> Some (lo, hi)
          | _ -> None)
      | _ -> None)
  | _ -> None

(* The def's memory node is a LOAD of (addr, size); stores are not. *)
let load_of_rhs (e : exp) : (exp * Size.t) option =
  match Model.addr_of_rhs e with
  | Some (addr, size) ->
      if Option.is_some (Model.store_data_of_rhs e) then None
      else Some (addr, size)
  | None -> None

(* The SysV slot index of a callee-side incoming offset (the callee's
   slots sit at [entry_rsp + word + word*i]; entry_rsp is the window
   base the caller passes = its SP at the call). *)
let slot_index_of ~(word : int) (k : int64) : int option =
  let w = Stdlib.Int64.of_int word in
  if Stdlib.Int64.compare k w >= 0 && Stdlib.Int64.equal (Stdlib.Int64.rem k w) 0L
  then
    Some
      (Stdlib.Int64.to_int
         (Stdlib.Int64.div (Stdlib.Int64.sub k w) w))
  else None

(* The CALLEE side of the promotion: per-def classification of this
   sub's window traffic from its tags and rhs shapes.
   - a LOAD at the singleton offset 0 is the return-address cell — it
     dies with the real LLVM ret;
   - a LOAD at a singleton SysV slot offset, width within the cell,
     promotes to slot [(k-word)/word];
   - a STORE at a singleton slot offset writes the caller's window
     cell: the slot it touches DEMOTES — the parameter is only the
     initialization of a read-only slot, and a read after the write
     must observe the write — so every access to that slot takes the
     window;
   - everything else (a spanned or mixed set, a wider read, a storing
     def — writes land in real caller memory) stays window memory. *)
let caller_side ~(denote : blk:blk term -> ?def:def term -> exp ->
                  (Vsa.WordSet.t, Type.error) Result.t)
    ~(symtab : Symtab.t option) ~(name_tid : (string * Tid.t) list)
    ~(abi : Hike_abi.t)
    (sub : sub term) :
    Tid.t option Tid.Map.t * (int64 * int64) list =
  let resolved = ref Tid.Map.empty in
  let exts = ref [] in
  let note_escape ~(blk : blk term) ?def (e : exp) =
    match denote ~blk ?def e with
    | Error _ -> ()
    | Ok ws -> (
        match Vsa.WordSet.stack_offsets ws with
        | None -> ()
        | Some offs ->
            let ext =
              Base.Option.value (hull_positions offs)
                ~default:(Stdlib.Int64.min_int, Stdlib.Int64.max_int)
            in
            exts := ext :: !exts)
  in
  let lookup = Hike_resolve.symtab_lookup ~symtab ~name_tid in
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun blk ->
      (* An SP-derived value the sub STORES escapes into memory: its
         reloaded copies deref through the raw-address lane.  Each
         store's data denotes at the def's own before-env; the
         parameter registers at the block's end state. *)
      Term.enum def_t blk
      |> Seq.iter ~f:(fun d ->
          match Model.store_data_of_rhs (Def.rhs d) with
          | None -> ()
          | Some (data, _) -> note_escape ~blk ~def:d data);
      Term.enum jmp_t blk
      |> Seq.iter ~f:(fun j ->
          match Jmp.kind j with
          | Call c -> (
              match Call.target c with
              | Indirect texp -> (
                  match denote ~blk texp with
                  | Error _ ->
                      resolved :=
                        Core.Map.set !resolved ~key:(Term.tid j) ~data:None
                  | Ok ws ->
                      resolved :=
                        Core.Map.set !resolved ~key:(Term.tid j)
                          ~data:(Hike_resolve.resolve_target ~lookup ws))
              | Direct _ -> ())
          | _ -> ());
      Core.List.iter (Hike_abi.param_regs abi)
        ~f:(fun v -> note_escape ~blk (Bil.Var v)));
  (!resolved, !exts)

(* The resolution product alone (the driver's call_resolution). *)
let call_resolution ~(denote : blk:blk term -> ?def:def term -> exp ->
                      (Vsa.WordSet.t, Type.error) Result.t)
    ~(symtab : Symtab.t option) ~(name_tid : (string * Tid.t) list)
    ~(abi : Hike_abi.t)
    (sub : sub term) : Tid.t option Tid.Map.t =
  fst (caller_side ~denote ~symtab ~name_tid ~abi sub)

(* Replaces the Load node matching (addr,size) with [x] (the BIR twin
   of the emitter's node rewrite). *)
let rewrite_load_to (e : exp) (addr : exp) (size : Size.t) (x : exp) : exp =
  let v =
    object
      inherit Exp.mapper
      method! map_load ~mem ~addr:a rest s =
        if Exp.equal a addr && Size.equal s size then x
        else Bil.Load (mem, a, rest, s)
    end
  in
  v#map_exp e

(* The promotion rewrite: the promotion facts become BIR structure at
   rewrite time — the sub gains its promoted parameters as real BIR
   args (slots 0..arity-1, the window class's hull slots included);
   each proven incoming-slot load reads its parameter, truncated to the
   node's own width for narrower reads; each site's outgoing store gains
   a call-arg def binding the store def's own value ([hike_argN :=
   lhs]); singleton-resolved indirect targets become DIRECT call
   targets.  The emitter transcribes what the term already carries and
   reads no record; written slots never enter [prom_slots], so their
   loads are never rewritten and take the window.  Exact-carry
   exemptions (CALLEE side only): the emittable intrinsics and @main
   gain no BIR args and no parameter reads — their Caller traffic keeps
   the window/raw lanes.  The CALLER side (arg defs + direct targets)
   runs for every sub. *)
let promote_sub ~(abi : Hike_abi.t) (facts : facts)
    (sub : sub term) : sub term =
  (* The callee-side rewrite is skipped for the emittable intrinsics
     (the soft-float bodies — their signature branch is the free-var
     projection) and @main (its signature branch is fixed rdi/rsi): no
     BIR args, no parameter reads — exactly what their signature
     branches served before.  The CALLER side (the call-arg defs and
     the direct targets) applies to EVERY sub: any sub's call sites
     pass promoted arguments and resolve through the denotations. *)
  let callee_exempt = Bil2llvm.fixed_signature sub in
  let word = abi.Hike_abi.word in
  let sub =
    if callee_exempt then sub
    else
      (* 1. The sub gains its promoted parameters as real BIR args, in
         signature order: slots 0..arity-1 (the window class's hull
         slots included — the window storage consumes them at entry).
         Promotion defines the sub's whole argument convention — any
         pre-existing args (lifter-synthesized result slots) are not
         part of it and are stripped first. *)
      let sub = Term.filter arg_t sub ~f:(Fun.const false) in
      Base.List.init facts.prom_arity ~f:(fun i ->
          Arg.create ~intent:In (Model.arg_slot ~word i)
            (Bil.Var (Model.arg_slot ~word i)))
      |> Base.List.fold ~init:sub ~f:(fun sub a -> Term.append arg_t sub a)
  in
    (* 2 + 3. Per block: rewrite the proven slot loads to parameter
       reads; insert the call-arg defs; resolve the indirect targets.
       (The slot-load rewrite is callee-side — a non-exempt sub's own
       proven reads.) *)
    Term.map blk_t sub ~f:(fun blk ->
        (* 3a. A resolved singleton target becomes a direct one — the
           jmp keeps its tid (the record keys on it), its guard, and
           its tag. *)
        let blk =
          Term.map jmp_t blk ~f:(fun j ->
              match Core.Map.find facts.prom_resolved (Term.tid j) with
              | Some (Some t) -> (
                  match Jmp.kind j with
                  | Call c ->
                      Jmp.with_kind j (Call (Call.with_target c (Direct t)))
                  | _ -> j)
              | _ -> j)
        in
        (* 3b died with the duplicated recipe: bind_site_args (Stage
           C) is the ONE insertion site for the call-arg defs. *)
        blk)


(* The sub's promoted-slot facts from its tree: the Arg_slot
   components' member defs (the reads), minus the demoted slots. *)
let slot_defs_of ~(demoted : int list) (tree : sub_tree) :
    int Tid.Map.t * int =
  let bindings = Tree.to_sequence tree |> Seq.to_list in
  let slots, arity =
    Base.List.fold bindings ~init:(Tid.Map.empty, -1) ~f:(fun (m, mx) (_, rs) ->
        match rs.storage with
        | Arg_slot i when not (Base.List.mem demoted i ~equal:Int.equal) ->
            Base.List.fold rs.members ~init:(m, mx) ~f:(fun (m, mx) mm ->
                match mm.m_def with
                | Some dtid -> (Core.Map.set m ~key:dtid ~data:i, Int.max mx i)
                | None -> (m, mx))
        | _ -> (m, mx))
  in
  (slots, if arity < 0 then 0 else arity + 1)

(* The rewrite driver: the promotion (Stage A2/C via the existing
   promote rewrite over the tree-derived facts) then Stage B's storage
   rewrite and the layout stamp.  [sites] and [resolved] are the
   Stage-A and call-resolution products of the seam; [arity_of] the
   per-callee promoted arity (for the site bindings' slot filter). *)
let rewrite_sub ~(word : int) ~(entry : int64) ~(abi : Hike_abi.t)
    ~(spans : data_span list)
    ~(denote : blk:blk term -> ?def:def term -> exp ->
                (Vsa.WordSet.t, Type.error) Result.t)
    ~(ctx : ctx)
    ~(sites : site_binding list Tid.Map.t)
    ~(resolved : Tid.t option Tid.Map.t)
    ~(arity_of : Tid.t -> int)
    ~(demoted : int list)
    ~(callee_exempt : bool)
    (sub : sub term) : sub term =
  let tree =
    Core.Map.find ctx.sub_trees (Term.tid sub)
    |> Option.value ~default:Tree.empty
  in
  let slots, arity = slot_defs_of ~demoted tree in
  let arity = if callee_exempt then 0 else arity in
  (* The site bindings: full-cell stores only, filtered to the callee's
     promoted arity. *)
  let site_slots btid callee =
    let arity = arity_of callee in
    match Core.Map.find sites btid with
    | None -> []
    | Some bs ->
        Base.List.filter_map bs ~f:(fun b ->
            if b.sb_full && b.sb_slot < arity then
              Some (b.sb_slot, Term.tid b.sb_def)
            else None)
  in
  let prom_sites =
    Core.Map.mapi sites ~f:(fun ~key:btid ~data:_ ->
        match Term.find blk_t sub btid with
        | None -> { Model.site_slots = [] }
        | Some blk -> (
            match
              Term.enum jmp_t blk
              |> Seq.fold ~init:None ~f:(fun acc j ->
                     match Core.Map.find resolved (Term.tid j) with
                     | Some (Some t) -> Some t
                     | _ -> acc)
            with
            | Some callee -> { Model.site_slots = site_slots btid callee }
            | None -> { Model.site_slots = [] }))
  in
  let facts = { prom_arity = arity; prom_sites; prom_resolved = resolved } in
  let sub = promote_sub ~abi facts sub in
  (* The window-value facts (D4b): a def with no memory node whose
     value denotes bounded-stack-symbolic wholly at/above the entry
     line computes an address in the CALLER's window world — its
     emitted integer re-bases to the hike_window parameter at the
     emitter. *)
  let window_values =
    Term.enum blk_t sub
    |> Seq.fold ~init:Tid.Set.empty ~f:(fun acc blk ->
        Term.enum def_t blk
        |> Seq.fold ~init:acc ~f:(fun acc d ->
            if Option.is_some (Model.addr_of_rhs (Def.rhs d)) then acc
            else
              match denote ~blk ~def:d (Def.rhs d) with
              | Error _ -> acc
              | Ok ws -> (
                  match Vsa.WordSet.stack_offsets ws with
                  | None -> acc
                  | Some _ -> (
                      let a_base = args_base ~entry ~word in
                      match positions_of_offsets ws with
                      | Some (lo, hi)
                        when Stdlib.Int64.compare lo a_base >= 0
                             && Stdlib.Int64.compare hi a_base >= 0
                             && Stdlib.Int64.compare lo hi <= 0 ->
                        Core.Set.add acc (Term.tid d)
                      | _ -> acc))))
  in
  let sub = Hike_stack_model.stamp_window_values ~window_values sub in
  (* Stage B: the storage rewrite per def, at its original block. *)
  let sub =
    Term.map blk_t sub ~f:(fun blk ->
        let blk =
          Term.map def_t blk ~f:(fun d ->
              let bits =
                match access_of d with
                | Some (_, w, _) -> 8 * w
                | None -> 0
              in
              let conv, _tag =
                conversion_of ~word ~entry ~spans ~denote ~tree
                  ~data:ctx.data_tree ~blk ~d ~demoted
              in
              let d' = rewrite_def ~word ~conv ~bits d in
              match conv with
              | Keep -> d'
              | Conv_region _ | Conv_slot _ | Conv_global _ | Conv_window ->
                  (* Conversion supersedes the tag: the memory node's
                     region var names the storage, and the emitter's
                     dispatch reads the tag only for defs still on the
                     raw lanes (the Dead and return-address arms). *)
                  d')
        in
        (* Stage C: the argument bindings at the storing defs. *)
        match Core.Map.find sites (Term.tid blk) with
        | Some bs -> bind_site_args ~word bs blk
        | None -> blk)
  in
  (* A window-VALUE def reads the hike_window parameter (D4b): the
     signature carries it whenever such a def exists, tree or no tree
     member. *)
  let layout = layout_of_tree ~word ~entry ~abi ~sub tree in
  let layout =
    if Core.Set.is_empty window_values then layout
    else { layout with Hike_stack_model.window_param = true }
  in
  Hike_stack_model.set_layout layout sub

(* The program driver: the per-sub seam products (Stage A sites, the
   call resolution), the cross-sub demotion (S21), the rewrite. *)
let rewrite_program ~(word : int) ~(entry : int64) ~(abi : Hike_abi.t)
    ~(sp : var) ~(symtab : Symtab.t option)
    ~(spans : data_span list)
    ~(denote : blk:blk term -> ?def:def term -> exp ->
                (Vsa.WordSet.t, Type.error) Result.t)
    ~(ctx : ctx)
    (prog : program term) : program term =
  let sanitize (name : string) =
    String.filter name ~f:(fun c ->
        match c with '#' | '.' | '%' | '\\' | '@' -> false | _ -> true)
  in
  let name_tid =
    Term.enum sub_t prog
    |> Seq.fold ~init:[] ~f:(fun acc s ->
           (sanitize (Tid.name (Term.tid s)), Term.tid s) :: acc)
  in
  let callee_exempt (sub : sub term) : bool =
    (Term.has_attr sub Sub.intrinsic
     && not (Seq.is_empty (Term.enum blk_t sub)))
    || String.equal (Tid.name (Term.tid sub)) "@main"
  in
  let exempt =
    Term.enum sub_t prog
    |> Seq.fold ~init:Tid.Set.empty ~f:(fun acc s ->
           if callee_exempt s then Core.Set.add acc (Term.tid s) else acc)
  in
  let sides =
    Term.enum sub_t prog
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun acc sub ->
           let sites = stage_a ~word ~abi ~sp ~denote sub in
           let resolved =
             call_resolution ~denote ~symtab ~name_tid ~abi sub
           in
           Core.Map.set acc ~key:(Term.tid sub) ~data:(sites, resolved))
  in
  (* The callee arity map (pre-demotion slots; the demotion only
     shrinks it). *)
  let slots_of sub =
    let tree =
      Core.Map.find ctx.sub_trees (Term.tid sub)
      |> Option.value ~default:Tree.empty
    in
    Base.List.concat_map (Tree.to_sequence tree |> Seq.to_list)
      ~f:(fun (_, rs) ->
        match rs.storage with Arg_slot i -> [ i ] | _ -> [])
  in
  let arity_of (t : Tid.t) : int =
    if Core.Set.mem exempt t then 0
    else
      match Term.find sub_t prog t with
      | Some sub -> (
          match slots_of sub with [] -> 0 | is -> 1 + Base.List.fold is ~init:0 ~f:Int.max)
      | None -> 0
  in
  (* The cross-sub demotion (S21): an Arg_slot slot a resolved site
     cannot bind with its full final bytes takes the Window rule on
     both sides. *)
  let demotion =
    Term.enum sub_t prog
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun acc caller ->
        let sites, resolved =
          Core.Map.find sides (Term.tid caller)
          |> Option.value ~default:(Tid.Map.empty, Tid.Map.empty)
        in
        Core.Map.fold sites ~init:acc ~f:(fun ~key:btid ~data:bs acc ->
            let callees =
              match Term.find blk_t caller btid with
              | Some blk ->
                  Term.enum jmp_t blk
                  |> Seq.filter_map ~f:(fun j ->
                         match Core.Map.find resolved (Term.tid j) with
                         | Some (Some t) -> Some t
                         | _ -> None)
                  |> Seq.to_list
              | None -> []
            in
            Base.List.fold callees ~init:acc ~f:(fun acc callee ->
                Base.List.fold bs ~init:acc ~f:(fun acc b ->
                    if b.sb_full then acc
                    else
                      Core.Map.update acc callee ~f:(function
                          | None -> [ b.sb_slot ]
                          | Some ds ->
                              if Base.List.mem ds b.sb_slot ~equal:Int.equal then ds
                              else b.sb_slot :: ds)))))
  in
  Term.map sub_t prog ~f:(fun sub ->
      let sites, resolved =
        Core.Map.find sides (Term.tid sub)
        |> Option.value ~default:(Tid.Map.empty, Tid.Map.empty)
      in
      rewrite_sub ~word ~entry ~abi ~spans ~denote ~ctx ~sites ~resolved
        ~arity_of
        ~demoted:(Core.Map.find demotion (Term.tid sub) |> Option.value ~default:[])
        ~callee_exempt:(Core.Set.mem exempt (Term.tid sub))
        sub)

