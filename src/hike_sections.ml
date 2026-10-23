(* The ownership pass: [range_of_denotation] projects an address
   denotation into occupied-byte portions, collection builds the two
   interval trees, finalization decides each merged range's storage —
   the finalized trees are the authoritative ownership representation. *)

open! Core
open Bap.Std
module Model = Hike_stack_model
module Vsa = Cbat_vsa

type sec = Hike_stack_model.sec

let equal_sec = Hike_stack_model.equal_sec
let compare_sec = Hike_stack_model.compare_sec
let sexp_of_sec = Hike_stack_model.sexp_of_sec
let sec_of_sexp = Hike_stack_model.sec_of_sexp

type data_span = {
  ds_sec : sec;
  ds_lo : int64;
  ds_hi : int64;
  ds_slots : int64 list;
}
[@@deriving equal, compare, sexp]

(* The section metadata rows, in the fixed table order; the spans,
   emitter spec, and copy-reloc slots all project from this builder. *)
type sec_meta = Model.sec_meta = {
  sm_type : sec;
  sm_access : Hike_section.access;
  sm_lo : int64;
  sm_hi : int64;
  sm_words : int;
  sm_image : Bytes.t option;  (* None = the bss region *)
  sm_copy_relocs : (int * string) list;  (* bss: (byte offset, symbol) *)
}

let bss_region proj =
  let regions = Hike_image.get_named_region_info proj in
  Base.Option.map
    (Seq.find regions ~f:(fun { name; _ } ->
         String.equal name ("." ^ Model.sec_name Bss)))
    ~f:(fun { addr; size; _ } ->
      (addr, size, Hike_image.get_copy_relocations proj ~bss_addr:addr ~bss_size:size))

let sec_meta ~(word : int) (proj : Project.t) : sec_meta option list =
  let prot =
    Hike_image.protections proj
      ~page:(Hike_abi.of_target (Project.target proj)).Hike_abi.page_size
  in
  let byte_row (sm_type : sec) =
    let llvm_name = Model.sec_name sm_type in
    Hike_image.get_section_mem ("." ^ llvm_name) proj |> Hike_image.get_section_data
    |> Base.Option.map ~f:(fun (arr, min_addr, max_addr) ->
        { sm_type;
          sm_access = Hike_image.section_access prot proj sm_type;
          sm_lo = Word.to_int64_exn min_addr;
          sm_hi = Word.to_int64_exn max_addr;
          sm_words = Hike_stack_bounds.cdiv (Bytes.length arr) word;
          sm_image = Some arr;
          sm_copy_relocs = [] })
  in
  let bss_row =
    Base.Option.map (bss_region proj) ~f:(fun (addr, size, copy_relocs) ->
        { sm_type = Bss;
          sm_access = Hike_image.section_access prot proj Bss;
          sm_lo = addr;
          sm_hi = Stdlib.Int64.sub (Stdlib.Int64.add addr size) 1L;
          sm_words = Hike_stack_bounds.cdiv (Stdlib.Int64.to_int size) word;
          sm_image = None;
          sm_copy_relocs = copy_relocs })
  in
  [ byte_row Data;
    byte_row Rodata;
    bss_row;
    byte_row Got;
    byte_row Gotplt;
    byte_row Datarelro;
    byte_row Text ]

(* Every copy-relocated slot address (absolute): loads and stores at a
   slot go through the slot's relocated pointer. *)
let slot_addrs_of (m : sec_meta) : int64 list =
  Base.List.map m.sm_copy_relocs
    ~f:(fun (off, _) -> Stdlib.Int64.add m.sm_lo (Stdlib.Int64.of_int off))

let attrib_spans ~(meta : sec_meta option list) : data_span list =
  Base.List.filter_map meta
    ~f:(Base.Option.map ~f:(fun m ->
            { ds_sec = m.sm_type;
              ds_lo = m.sm_lo;
              ds_hi = m.sm_hi;
              ds_slots = slot_addrs_of m }))

(* The emitter's section spec; a [whole] entry (id, lo, hi) is a span
   served whole — the section's own image global is the id's storage.
   [relative] and [externals] are the loader's relocation facts the
   initializer consults. *)
let section_spec_of ~(word : int) ~(comps : Model.sec_comp list)
    ~(whole : (int * int64 * int64) list) ~(meta : sec_meta option list)
    ~(tls : Bil2llvm_env.tls_spec option) ~(relative : (int64 * int64) list)
    ~(externals : (int64 * string) list) : Bil2llvm_env.section_spec =
  let open Bil2llvm_env in
  { spec_comps = comps;
    spec_whole = whole;
    spec_word = word;
    spec_sections = meta;
    spec_tls = tls;
    spec_relative = relative;
    spec_externals = externals }

type point = { p_sec : sec; p_pos : int64 } [@@deriving sexp]
type range = { lo : point; hi : point } [@@deriving sexp]

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

(* A stack region id keys a per-sub alloca, a data region id a
   module-wide global (a whole span is one data region served by the
   section's image global); the residue is the stack's fallback storage
   (a bounded alloca or the runtime stack). *)
type storage =
  | Stack_region of int
  | Stack_residue
  | Data_region of int
  | Arg_slot
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

type portion = {
  pt_sec : sec;
  pt_lo : int64;
  pt_hi : int64;
  pt_elig : bool;
}
[@@deriving equal, compare, sexp]

(* The def's projection: the reduced tag, the address denotation's
   runtime origin (the analysis's own fact — the rewrite consumes it;
   no band re-derivation), and the portions. *)
type projection = {
  tag : sec_tag option;
  origin : Hike_origin.t option;
  portions : portion list;
  (* The access's stack-offset hull, when the denotation names one:
     promotion's extent admissibility reads it instead of re-denoting. *)
  offsets : (int64 * int64) option;
}

type conv = Hike_synth_addr.conv =
  | Conv_region of int                    (* the region id *)
  | Conv_window                           (* the incoming window: the caller's world *)
  | Conv_slot of int * int                (* slot index, intra-slot byte *)
  | Conv_global of int                    (* the component id *)
  | Keep

type ctx = {
  sub_trees : sub_tree Tid.Map.t;
  data_tree : data_tree;
  tags : sec_tag Tid.Map.t;
  (* Each access def's projection; [None] = the attribution's query
     failed and the rewrite keeps the memory form. *)
  projections : projection option Tid.Map.t;
  (* Each access def's storage conversion, decided once from the
     projections and the finalized trees. *)
  conversions : conv Tid.Map.t;
  (* The data spans served whole, computed once by [attribute] and
     shared by the finalize and both spec projections. *)
  whole : data_span list;
}


(* Why an address denotated TOP: the denotation query itself failed, a
   stack-symbolic set with no surviving bounds, or a plain top — no
   stack basis and no rip proof (the heap). *)
type top_cause = Query_failed | Unbounded_stack | Foreign

(* Portions of the occupied interval [lo,hi]; the tag carries the
   ADDRESS bounds [alo,ahi].  The sub-local line's spaces are the
   frame [floor, s_top] and the args [a_base, ceiling]. *)
let sub_portions ~(entry : int64)
    ~(word : int) ~(elig : bool) ~(alo : int64) ~(ahi : int64)
    (lo : int64) (hi : int64) : sec_tag option * portion list =
  let floor = Model.stack_floor ~entry in
  let cei = Model.args_ceiling in
  let a_base = Model.args_base ~entry ~word in
  let s_top = Model.stack_top ~entry ~word in
  let portion s part elig =
    Base.Option.map part ~f:(fun (plo, phi) ->
        { pt_sec = s; pt_lo = plo; pt_hi = phi; pt_elig = elig })
  in
  let parts =
    Base.List.filter_map
      [ portion Stack (Model.clip ~cmp:Stdlib.Int64.compare lo hi floor s_top)
          elig;
        portion Args (Model.clip ~cmp:Stdlib.Int64.compare lo hi a_base cei)
          elig ]
      ~f:(fun x -> x)
  in
  ( (if Option.is_some (Model.clip ~cmp:Stdlib.Int64.compare lo hi floor cei)
     then Some (Tag.Range (alo, ahi))
     else None),
    parts )

(* The full-span claim for a TOP address: a stack-symbolic top claims
   below-entry down to the floor; imprecision never reaches the Args
   slots; any other top claims the sub-local spaces' full range — the
   identity member forcing write closure with the carved cells. *)
let top_claim ~(cause : top_cause)
    ~(entry : int64) ~(word : int) : sec_tag option * portion list =
  match cause with
  | Unbounded_stack ->
    ( Some Tag.Unbounded,
      snd (sub_portions ~entry ~word ~elig:false
             ~alo:(Model.stack_floor ~entry) ~ahi:Model.args_ceiling
             (Model.stack_floor ~entry)
             (Stdlib.Int64.pred entry)) )
  | Query_failed | Foreign ->
    (None,
     snd (sub_portions ~entry ~word ~elig:false
            ~alo:(Model.stack_floor ~entry) ~ahi:Model.args_ceiling
            (Model.stack_floor ~entry) Model.args_ceiling))

(* Case 1: the address carries stack offsets.  Bounded positions carve;
   an unbounded direction takes the full supported bounds of the side
   it reaches.  The bounded case clips PER RUN: a disjoint-run address
   (the va_arg reg-save/overflow join) keeps both bands instead of
   hulling across the entry line. *)
let stack_offset_portions ~(word : int)
    ~(entry : int64) ~(width : int) (ws : Vsa.WordSet.t) :
    sec_tag option * portion list =
  let cei = Model.args_ceiling in
  let a_base = Model.args_base ~entry ~word in
  let sub_portions = sub_portions ~entry ~word in
  match Model.positions_of_offsets ws with
  | None -> top_claim ~cause:Unbounded_stack ~entry ~word
  | Some (lo, hi) -> (
      let occ_hi = Model.expand_hi ~cap:cei hi width in
      if Vsa.WordSet.is_infinite ws || Stdlib.Int64.compare lo hi > 0 then
        let nlo, nhi =
          Model.full_bounds ws ~flo:(Model.stack_floor ~entry) ~cei lo hi
        in
        (Some Tag.Unbounded,
         snd (sub_portions ~elig:false ~alo:nlo ~ahi:nhi nlo nhi))
      else
        let runs = Vsa.WordSet.offset_runs ws in
        let single =
          Stdlib.Int64.compare occ_hi a_base < 0
          || Stdlib.Int64.compare lo a_base >= 0
        in
        (match runs with
         | [ (rlo, rhi) ] ->
           let occ = Model.expand_hi ~cap:cei rhi width in
           sub_portions ~elig:single ~alo:lo ~ahi:hi rlo occ
         | [] -> sub_portions ~elig:single ~alo:lo ~ahi:hi lo occ_hi
         | _ ->
           let parts =
             Base.List.concat_map runs ~f:(fun (rlo, rhi) ->
                 let occ = Model.expand_hi ~cap:cei rhi width in
                 snd (sub_portions ~elig:false ~alo:lo ~ahi:hi rlo occ))
           in
           (Some (Tag.Range (lo, occ_hi)), parts)))

(* Case 2: a plain address. An unbounded ascending set's minimum names its
   section; the remaining bounded sets split across the data spans,
   with a resolved address basis where one span owns the occupied extent. *)
(* [x] lies in the unsigned span [lo, hi]. *)
let in_span ~(lo : int64) ~(hi : int64) (x : int64) : bool =
  Stdlib.Int64.unsigned_compare lo x <= 0
  && Stdlib.Int64.unsigned_compare x hi <= 0

let plain_portions ~(word : int)
    ~(entry : int64) ~(spans : data_span list) ~(basis : int64 option) ~(width : int)
    (ws : Vsa.WordSet.t) : sec_tag option * portion list =
  match Model.unsigned_bounds ws with
    | None ->
      (* No surviving bound: the identity claim, never the heap claim. *)
      top_claim ~cause:Foreign ~entry ~word
    | Some (lo, hi) ->
      if Vsa.WordSet.is_infinite ws && Vsa.WordSet.is_ascending ws then begin
        (* Accesses never cross sections, so an unbounded ascending
           access's minimum names its section; the claim clamps into
           it.  An address without a section basis keeps the identity claim. *)
        if Option.is_some basis then
          match
            Base.List.find spans ~f:(fun d ->
                in_span ~lo:d.ds_lo ~hi:d.ds_hi lo)
          with
          | Some d ->
            ( None,
              [ { pt_sec = d.ds_sec;
                  pt_lo = Stdlib.Int64.max lo d.ds_lo;
                  pt_hi = d.ds_hi;
                  pt_elig = false } ] )
          | None -> top_claim ~cause:Foreign ~entry ~word
        else top_claim ~cause:Foreign ~entry ~word
      end
      else
        let occ_hi = Model.expand_hi_unsigned hi width in
        let parts =
          Base.List.filter_map spans ~f:(fun d ->
              Base.Option.map
                (Model.clip ~cmp:Stdlib.Int64.unsigned_compare lo occ_hi d.ds_lo d.ds_hi)
                ~f:(fun (plo, phi) -> (d, plo, phi)))
        in
        let whole_in_one =
          match parts with
          | [ (d, _, _) ] ->
            Stdlib.Int64.unsigned_compare lo d.ds_lo >= 0
            && Stdlib.Int64.unsigned_compare occ_hi d.ds_hi <= 0
          | _ -> false
        in
        (* A copy-relocated slot's bytes are externally owned —
           an access reaching one has no conversion proof. *)
        let at_slot (d, plo, phi) =
          Base.List.exists d.ds_slots ~f:(fun s ->
              in_span ~lo:plo ~hi:phi s)
        in
        let elig =
          Option.is_some basis && whole_in_one
          && not (Base.List.exists parts ~f:at_slot)
        in
        ( None,
          Base.List.map parts ~f:(fun (d, plo, phi) ->
              { pt_sec = d.ds_sec; pt_lo = plo; pt_hi = phi;
                pt_elig = elig } ))

(* The def's address claim: the sections each reachable position may
   touch, and whether conversion is proven. *)
let range_of_denotation ~(word : int)
    ~(entry : int64) ~(spans : data_span list) ~(synth : Hike_synth.table)
    ~(address : exp) ~(width : int)
    (ws : Vsa.WordSet.t) : sec_tag option * portion list =
  let regions = Base.List.mapi spans ~f:(fun id span ->
      { Hike_synth_addr.id; lo = span.ds_lo; hi = span.ds_hi }) in
  let basis = Base.Option.bind (Hike_synth_addr.address_basis synth address)
      ~f:(fun a -> Base.Option.map
          (Hike_synth_addr.region_index ~addr_bits:(Model.word_bits word) ~regions a)
          ~f:(fun _ -> a)) in
  if Base.Option.equal Hike_origin.equal (Vsa.WordSet.origin ws)
       (Some Hike_origin.Fs) then
    (* TLS/TCB bytes live on their own origin line, outside these storages. *)
    None, []
  else if Vsa.WordSet.is_bottom ws then
    (* A def-anchored bottom is the refinement's empty meet, not a
       reachability proof — the def's block is CFG-reachable.  The
       access keeps its memory form: the raw-address emission is
       exact. *)
    top_claim ~cause:Query_failed ~entry ~word
  else if Vsa.WordSet.is_top ws then
    (* A plain top claims the sub-local spaces' full range — the
       identity member forcing write closure; a resolved address
       that loses its bounds receives the same conservative claim. *)
    if Option.is_some (Vsa.WordSet.stack_offsets ws) then
      top_claim ~cause:Unbounded_stack ~entry ~word
    else top_claim ~cause:Foreign ~entry ~word
  else
    match Vsa.WordSet.stack_offsets ws with
    | Some _ -> stack_offset_portions ~word ~entry ~width ws
    | None -> plain_portions ~word ~entry ~spans ~basis ~width ws

type env = {
  word : int;
  entry : int64;
  spans : data_span list;
  synth : Hike_synth.table;
  params : var list;
  sp : var;
  denote : blk:blk term -> ?def:def term -> exp ->
           (Vsa.WordSet.t, Type.error) Result.t;
}

type collecting = {
  sub : Tid.t;
  blk : blk term;
  tree : member list Tree.t;
  data : member list Tree.t;
  subs : (member list Tree.t) Tid.Map.t;
  tags : sec_tag Tid.Map.t;
  (* The projection the rewrite consumes: [None] = the query failed
     (the collect path claims the full span; the rewrite keeps the
     memory form). *)
  projections : projection option Tid.Map.t;
}

(* The intersecting bindings merge into one: the inclusive hull, the
   members joined newest-first. *)
let insert (tree : member list Tree.t) (m : member) : member list Tree.t =
  let key = range m.m_sec m.m_lo m.m_hi in
  let hits = Tree.intersections tree key |> Seq.to_list in
  let rest = Tree.remove_intersections tree key in
  let hull =
    Base.List.fold hits ~init:key ~f:(fun acc (k, _) ->
        { lo = (if compare_point k.lo acc.lo < 0 then k.lo else acc.lo);
          hi = (if compare_point k.hi acc.hi > 0 then k.hi else acc.hi) })
  in
  Tree.add rest hull (m :: Base.List.concat_map hits ~f:(fun (_, ms) -> ms))

(* The words the bytes touch, capped at the span's end — the emitter's
   tiles are word-granular. *)
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

let is_data_sec (s : sec) : bool =
  match s with Stack | Args -> false | _ -> true

(* The sub-local spaces: the stack frame and the caller window's arg
   slots — everything a per-sub alloca serves. *)
let is_sub_local (s : sec) : bool = not (is_data_sec s)

(* The span owning [s] — one row per section, so the find is total. *)
let span_of (spans : data_span list) (s : sec) : data_span option =
  Base.List.find spans ~f:(fun d -> equal_sec d.ds_sec s)

let member_of ~(sub : Tid.t) ~(def : Tid.t option) ~(width : int) ~(store : bool)
    ~(word : int) ~(spans : data_span list) (p : portion) : member =
  let lo, hi =
    if is_sub_local p.pt_sec then (p.pt_lo, p.pt_hi)
    else
        (* The data side owns the emitter's word grid: a member's
           extent is its occupied bytes snapped OUT to the owning
           span's word hull. *)
        Option.value_map (span_of spans p.pt_sec)
          ~default:(p.pt_lo, p.pt_hi)
          ~f:(fun d -> word_hull ~word d p.pt_lo p.pt_hi)
  in
  { m_sec = p.pt_sec; m_lo = lo; m_hi = hi; m_sub = sub;
    m_def = def; m_width = width; m_store = store;
    m_identity = not p.pt_elig }

(* The word cell of a promotable Args member: a def-backed, non-identity
   access wholly inside one word cell at/above the args base.  [None] for
   any other member — an identity claim (a TOP access) converts to its
   own memory form and never names a slot. *)
let args_member_cell ~(word : int) ~(entry : int64) (m : member) : int option =
  if m.m_identity then None
  else Model.args_cell_of_span ~word ~entry m.m_lo m.m_hi

(* A stack pointer may be dereferenced at any offset in the escaped
   caller frame. Keep that frame in one storage so pointer arithmetic
   remains contiguous; def-backed accesses still size the allocation. *)
let escape_members ~(sub : Tid.t) ~(env : env)
    (ext : int64 * int64) : member list =
  let lo, hi = ext in
  let _, parts =
    sub_portions ~entry:env.entry ~word:env.word
      ~elig:false ~alo:lo ~ahi:hi lo hi
  in
  if Base.List.exists parts ~f:(fun p -> equal_sec p.pt_sec Stack) then
    [ { m_sec = Stack;
        m_lo = Model.stack_floor ~entry:env.entry;
        m_hi = Model.stack_top ~entry:env.entry ~word:env.word;
        m_sub = sub; m_def = None; m_width = 0; m_store = false;
        m_identity = true } ]
  else []

(* The exact outgoing argument stores of a call, shared with the
   promotion's slot binding rule, are the caller-window member.  Each
   store comes with the block that holds it: a store in a predecessor
   block of the call fills a slot as well as one in the call's block. *)
let call_window_members ~(sub : Tid.t) ~(env : env)
    (stores : (blk term * def term) list) : member list =
  let extents =
    Base.List.filter_map stores ~f:(fun (blk, def) ->
        match Model.addr_of_rhs (Def.rhs def) with
        | None -> None
        | Some (addr, size) ->
          (match env.denote ~blk ~def addr with
           | Error _ -> None
           | Ok ws ->
             Option.map (Model.singleton_stack_position ws) ~f:(fun lo ->
                 (lo, Model.expand_hi ~cap:Model.args_ceiling lo
                        (Size.in_bytes size)))))
  in
  match extents with
  | [] -> []
  | (lo, hi) :: rest ->
    let lo, hi =
      Base.List.fold rest ~init:(lo, hi) ~f:(fun (lo, hi) (lo', hi') ->
          (Stdlib.Int64.min lo lo', Stdlib.Int64.max hi hi'))
    in
    let _, portions =
      sub_portions ~entry:env.entry ~word:env.word ~elig:false
        ~alo:lo ~ahi:hi lo hi
    in
    Base.List.map portions ~f:(fun p ->
        { m_sec = p.pt_sec; m_lo = p.pt_lo; m_hi = p.pt_hi; m_sub = sub;
          m_def = None; m_width = 0; m_store = false; m_identity = true })

(* The def's memory access: (address, width in bytes, stores). *)
let access_of (d : def term) : (exp * int * bool) option =
  Option.map (Model.addr_of_rhs (Def.rhs d)) ~f:(fun (addr, size) ->
      (addr, Size.in_bytes size, Option.is_some (Model.store_data_of_rhs (Def.rhs d))))

let collect (env : env) (prog : program term) : collecting =
  (* The stack arguments of each call block, by sub. *)
  let call_sites =
    Term.enum sub_t prog
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun acc sub ->
        let sites =
          Model.call_sites ~word:env.word ~sp:env.sp ~denote:env.denote sub in
        Core.Map.set acc ~key:(Term.tid sub) ~data:(sub, sites))
  in
  let ownership_visitor =
    object
      inherit [ collecting ] Term.visitor

      method! enter_sub s acc = { acc with sub = Term.tid s; tree = Tree.empty }

      method! leave_sub s acc =
        { acc with subs = Core.Map.set acc.subs ~key:(Term.tid s) ~data:acc.tree }

      method! enter_blk b acc = { acc with blk = b }

      method! leave_blk _ acc =
        (* A parameter holding a stack value at the block's post-state
           escapes: its extent joins the identity members. *)
        let acc =
          Base.List.fold env.params ~init:acc ~f:(fun acc v ->
              Option.fold
                (Option.bind
                   (Result.ok
                      (env.denote ~blk:acc.blk
                         (Bil.Var (Model.version_at_end acc.blk v))))
                   ~f:(Model.escape_extent ~entry:env.entry))
                ~init:acc
                ~f:(fun acc ext ->
                  Base.List.fold (escape_members ~sub:acc.sub ~env ext)
                    ~init:acc
                    ~f:(fun acc m -> { acc with tree = insert acc.tree m })))
        in
        (* A call exposes the stack-argument stores its caller built:
           those of this block and those of other blocks that fill a
           slot this block's stores do not. *)
        let stores =
          match Core.Map.find call_sites acc.sub with
          | None -> []
          | Some (sub, sites) ->
            (match Core.Map.find sites (Term.tid acc.blk) with
             | None -> []
             | Some site ->
               Base.List.map site.Model.cs_own ~f:(fun b ->
                   (acc.blk, b.Model.sb_def))
               @ Base.List.filter_map site.Model.cs_remote ~f:(fun b ->
                   Option.map (Term.find blk_t sub b.Model.rb_blk)
                     ~f:(fun blk -> (blk, b.Model.rb_def))))
        in
        Base.List.fold
          (call_window_members ~sub:acc.sub ~env stores)
          ~init:acc
          ~f:(fun acc m -> { acc with tree = insert acc.tree m })

      method! enter_def d acc =
        let dtid = Term.tid d in
        match access_of d with
        | None -> acc
        | Some (addr, width, store) -> (
            (* The def's projection, computed once: the rewrite reads
               this record instead of re-deriving it from the seam. *)
            let projected : projection option =
              match env.denote ~blk:acc.blk ~def:d addr with
              | Error _ -> None
              | Ok ws ->
                let tag, portions =
                  range_of_denotation                      ~word:env.word ~entry:env.entry ~spans:env.spans
                     ~synth:env.synth ~address:addr ~width ws
                in
                let offsets =
                  if Vsa.WordSet.is_infinite ws then None
                  else
                    match Model.positions_of_offsets ws with
                    | Some (lo, hi)
                      when Stdlib.Int64.compare lo hi <= 0 -> Some (lo, hi)
                    | _ -> None
                in
                Some { tag; origin = Vsa.WordSet.origin ws; portions; offsets }
            in
            let tag, portions =
              match projected with
              | Some p -> (p.tag, p.portions)
              | None ->
                  (* A failed query keeps the access: the unknown
                     identity contributes full members. *)
                  top_claim ~cause:Query_failed
                    ~entry:env.entry ~word:env.word
            in
            let acc =
              match tag with
              | Some t -> { acc with tags = Core.Map.set acc.tags ~key:dtid ~data:t }
              | None -> acc
            in
            let acc =
              { acc with
                projections = Core.Map.set acc.projections ~key:dtid ~data:projected }
            in
            Base.List.fold portions ~init:acc ~f:(fun acc p ->
                let m =
                  member_of ~sub:acc.sub ~def:(Some dtid) ~width ~store
                    ~word:env.word ~spans:env.spans p
                in
                if is_sub_local p.pt_sec then
                  { acc with tree = insert acc.tree m }
                else { acc with data = insert acc.data m })
            |> fun acc ->
            (* A stored stack-symbolic value escapes into memory: its
               reloaded copies deref through the raw lane. *)
            Option.fold
              (Option.bind (Model.store_data_of_rhs (Def.rhs d))
                 ~f:(fun data ->
                   Option.bind
                     (Result.ok (env.denote ~blk:acc.blk ~def:d data))
                     ~f:(Model.escape_extent ~entry:env.entry)))
              ~init:acc
              ~f:(fun acc ext ->
                Base.List.fold (escape_members ~sub:acc.sub ~env ext)
                  ~init:acc
                  ~f:(fun acc m -> { acc with tree = insert acc.tree m })))

    end
  in
  ownership_visitor#run prog
    { sub = Tid.create ();
      blk = Blk.Builder.result (Blk.Builder.create ());
      tree = Tree.empty;
      data = Tree.empty; subs = Tid.Map.empty; tags = Tid.Map.empty;
      projections = Tid.Map.empty }

(* Rounds [n] up to the ABI's stack alignment. *)
let align_up n =
  let align = Stdlib.Int64.of_int Hike_abi.stack_align in
  let r = Stdlib.Int64.rem n align in
  if Stdlib.Int64.equal r 0L then n else Stdlib.Int64.add n (Stdlib.Int64.sub align r)

let region_max_bytes : int64 = 67108864L (* a binding above this stays in the residue *)

(* A stack region's alloca size: its byte span, 16-aligned. *)
let region_bytes (k : range) : int64 =
  align_up (Stdlib.Int64.add (Stdlib.Int64.sub k.hi.p_pos k.lo.p_pos) 1L)

(* Whether [pos] sits inside the span served whole. *)
let in_whole_span (whole : data_span list) (s : sec) (pos : int64) : bool =
  match span_of whole s with
  | Some d ->
    in_span ~lo:d.ds_lo ~hi:d.ds_hi pos
  | None -> false


(* The data spans served whole (identity): a span with any identity
   binding, or with copy-relocated slots (externally-owned bytes). *)
let whole_spans_of (spans : data_span list) (bindings : (range * member list) list) :
    data_span list =
  let tainted =
    Base.List.filter_map bindings ~f:(fun (k, ms) ->
        if is_data_sec k.lo.p_sec && Base.List.exists ms ~f:(fun m -> m.m_identity)
        then
          Option.bind (span_of spans k.lo.p_sec)
            ~f:(fun d ->
              if in_span ~lo:d.ds_lo ~hi:d.ds_hi k.lo.p_pos
              then Some d else None)
        else None)
  in
  Base.List.filter spans ~f:(fun d ->
      (not (Base.List.is_empty d.ds_slots)) || Base.List.mem tainted d ~equal:equal_data_span)

let finalize_tree ~(word : int) ~(entry : int64)
    ~(whole : data_span list)
    (tree : member list Tree.t) : range_storage Tree.t =
  (* The tree yields its bindings in key order. *)
  let bindings = Tree.to_sequence tree |> Seq.to_list in
#ifdef VSA_DEBUG
  assert (Base.List.is_sorted bindings ~compare:(fun (k1, _) (k2, _) ->
      compare k1 k2));
#endif
  let ret_lo = entry in
  let ret_hi = Stdlib.Int64.pred (Stdlib.Int64.add entry (Stdlib.Int64.of_int word)) in
  (* The residue (id 0) is the stack's fallback storage.  A whole span
     is one data region — every range in it shares the span's id;
     carved ranges mint an id each, per sub (stack) / module-wide
     (data, minting from 0). *)
  let next_region_id = ref Model.residue_id in
  let next_global_id = ref (-1) in
  let span_ids = ref [] in
  let decide (k : range) (ms : member list) : range_storage =
    let any_identity = Base.List.exists ms ~f:(fun m -> m.m_identity) in
#ifdef VSA_DEBUG
    let bump name = Cbat_vsa.Cbat_attr_census.bump name in
#else
    let bump name = () in
#endif
    match k.lo.p_sec with
    | Stack ->
        let overlaps_ret =
          Stdlib.Int64.compare k.hi.p_pos ret_lo >= 0
          && Stdlib.Int64.compare k.lo.p_pos ret_hi <= 0
        in
        let bytes = region_bytes k in
        if overlaps_ret then bump "region.stack.retaddr";
        if any_identity then bump "region.stack.identity";
        if Stdlib.Int64.compare bytes region_max_bytes > 0 then
          bump "region.stack.oversize";
        if overlaps_ret || any_identity || Stdlib.Int64.compare bytes region_max_bytes > 0
        then { storage = Stack_residue; members = ms }
        else (
          bump "region.stack.carved";
          incr next_region_id;
          { storage = Stack_region !next_region_id; members = ms })
    | Args ->
        (* Every Args binding lies at or above the entry line, so its
           cells are caller slots.  The unit is the word cell, never the
           binding: a binding may span several cells.  A member that is
           not a bounded single-cell access — a TOP claim (whose address
           may alias any of them) or a multi-cell span — keeps the whole
           binding write-closed in the residue. *)
        if
          Base.List.for_all ms ~f:(fun m ->
              Base.Option.is_some (args_member_cell ~word ~entry m))
        then (
          bump "region.args.slot";
          { storage = Arg_slot; members = ms })
        else (
          bump "region.args.residue";
          { storage = Stack_residue; members = ms })
    | sec ->
        if in_whole_span whole sec k.lo.p_pos then
          let id =
            match Base.List.Assoc.find !span_ids sec ~equal:equal_sec with
            | Some id -> id
            | None ->
                incr next_global_id;
                span_ids := (sec, !next_global_id) :: !span_ids;
                !next_global_id
          in
          { storage = Data_region id; members = ms }
        else (
          incr next_global_id;
          { storage = Data_region !next_global_id; members = ms })
  in
  Base.List.fold bindings ~init:Tree.empty ~f:(fun t (k, ms) ->
      Tree.add t k (decide k ms))

(* The stack binding wholly owning [lo, hi]: a value spanning two
   bindings names no one storage. *)
let owning_storage (tree : sub_tree) (lo : int64) (hi : int64) :
    storage option =
  Tree.lookup tree (point Stack lo)
  |> Seq.find_map ~f:(fun (k, rs) ->
         if
           Stdlib.Int64.compare k.lo.p_pos lo <= 0
           && Stdlib.Int64.compare hi k.hi.p_pos <= 0
         then Some rs.storage
         else None)

(* The data binding wholly owning [c]: (component id, its native low
   bound).  A constant spanning bindings names no one storage. *)
let owning_data_binding (tree : data_tree) (c : int64) :
    (int * int64) option =
  Tree.lookup tree (point Rodata c)
  |> Seq.find_map ~f:(fun (k, rs) ->
         if
           in_span ~lo:k.lo.p_pos ~hi:k.hi.p_pos c
         then (
           match rs.storage with
           | Data_region id ->
               Some (id, k.lo.p_pos)
           | _ -> None)
         else None)

(* Merged bindings never overlap, so the binding containing the
   range's least point is THE owner. *)
let storage_of_range (tree : range_storage Tree.t) (r : range) :
    range_storage option =
  (* The rewrite's hottest query; the tree's lookup yields the
     containing entry, which decides. *)
  match Seq.hd (Tree.lookup tree r.lo) with
  | Some (_, v) -> Some v
  | None -> None

let region_id_of_storage (s : storage) : int =
  match s with
  | Stack_region n | Data_region n -> n
  | Stack_residue | Arg_slot -> Model.residue_id


(* The rewrite decision reads the attribution's own projection of the
   def (ctx.projections) — the collect path computed it; the rewrite
   cannot disagree with the tree. *)
let conversion_of ~(word : int) ~(entry : int64) ~(synth : Hike_synth.table)
    ~(tree : sub_tree) ~(data : data_tree)
    ~(projected : projection option)
    ~(access : (exp * int * bool) option) : conv * Tag.t option =
  match access with
  | None -> (Keep, None)
  | Some (addr, _, _) -> (
      match projected with
      (* A failed attribution query keeps the memory form. *)
      | None -> (Keep, None)
      | Some p ->
          (* An unbounded address keeps its memory form: an above-entry
             direction's storage is the caller's world, which the typed
             arguments carry; a below-entry one is a pointer into the
             residue, exactly like a bounded one. *)
          let tag = p.tag in
          let portions = p.portions in
          match tag with
          | Some Tag.Unbounded -> (Keep, tag)
          | _ ->
          (* A return-address cell keeps its tag — the emitter's
             return arm. *)
          let retaddr_cell =
            match tag with
            | Some t -> Model.is_return_address_tag t
            | None -> false
          in
          (* A conversion needs the eligibility proof: an identity
             portion (an escape, a full-span claim) keeps
             the memory form — the raw lane is its sound answer. *)
          let owned =
            Base.List.filter portions ~f:(fun p ->
                p.pt_elig
                && (if is_sub_local p.pt_sec then not retaddr_cell
                    else Base.Option.is_some
                        (Hike_synth_addr.address_of_exp synth addr)))
          in
          match owned with
          | [ p ] -> (
              let owner =
                let space = if is_sub_local p.pt_sec then tree else data in
                storage_of_range space (range p.pt_sec p.pt_lo p.pt_hi)
              in
              match owner with
              | Some rs -> (
                  match (p.pt_sec, rs.storage) with
                  | (Stack, (Stack_region _ | Stack_residue)) ->
                    (Conv_region (region_id_of_storage rs.storage), tag)
                  | (Args, Stack_residue) -> (Conv_window, tag)
                  | Args, Arg_slot -> (
                      (* The slot index is the ACCESS's own word cell,
                         never the binding's: a binding may span several
                         cells.  A span outside a single cell is not a
                         slot (the binding's promotability proved one, so
                         this is the defensive identity). *)
                      match
                        Model.args_cell_of_span ~word ~entry p.pt_lo
                          p.pt_hi
                      with
                      | Some i ->
                        let cell_lo =
                          Stdlib.Int64.add entry (Model.slot_offset ~word i)
                        in
                        ( Conv_slot
                            (i, Stdlib.Int64.to_int (Stdlib.Int64.sub p.pt_lo cell_lo)),
                          tag )
                      | None -> (Keep, tag))
                  | _, Data_region id -> (Conv_global id, tag)
                  | _ -> (Keep, tag))
              | None -> (Keep, tag))
          | _ -> (Keep, tag))


let attribute ~(facts : Hike_kb.facts) ~(word : int) ~(entry : int64)
    ~(spans : data_span list)
    (prog : program term) : ctx =
  let abi = facts.abi in
  let env =
    (* Only the integer params ride the escape fold: the vector lanes
       are FP values the model's stack offsets never serve. *)
    { word; entry; spans;
      params = abi.Hike_abi.int_param_regs;
      synth = facts.synth; sp = abi.Hike_abi.sp; denote = facts.denote }
  in
  let collected = collect env prog in
  (* The whole-served set: computed once, consumed by the data
     finalization and both spec projections. *)
  let whole =
    whole_spans_of spans (Tree.to_sequence collected.data |> Seq.to_list)
  in
  let sub_trees =
    Core.Map.map collected.subs ~f:(fun tree ->
        finalize_tree ~word ~entry ~whole:[] tree)
  in
  let data_tree =
    finalize_tree ~word ~entry ~whole collected.data in
  let conversions =
    Term.enum sub_t prog
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun acc sub ->
           let tid = Term.tid sub in
           let tree = Core.Map.find_exn sub_trees tid in
           Term.enum blk_t sub
           |> Seq.concat_map ~f:(Term.enum def_t)
           |> Seq.fold ~init:acc ~f:(fun acc d ->
                  match access_of d with
                  | None -> acc
                  | Some _ as access ->
                    let projected =
                      Base.Option.join
                        (Core.Map.find collected.projections (Term.tid d))
                    in
                    let c, _ =
                      conversion_of ~word ~entry ~synth:facts.synth ~tree
                        ~data:data_tree ~projected ~access
                    in
                    Core.Map.set acc ~key:(Term.tid d) ~data:c))
  in
  { sub_trees; data_tree; tags = collected.tags;
    projections = collected.projections; conversions; whole }

(* A whole span serves as ONE component covering the span, stored in
   the section's own image global (the emitter wires the id to it). *)
let whole_comps_of (ctx : ctx) : (int * int64 * int64) list =
  let bindings = Tree.to_sequence ctx.data_tree |> Seq.to_list in
  Base.List.filter_map ctx.whole ~f:(fun d ->
      Base.List.find_map bindings ~f:(fun (k, rs) ->
          match rs.storage with
          | Data_region id when equal_sec k.lo.p_sec d.ds_sec ->
            Some (id, d.ds_lo, d.ds_hi)
          | _ -> None))

(* The carved data ranges' global components: word-grid tile and typed
   width; whole spans contribute nothing (they serve whole). *)
let global_comps_of ~(word : int) ~(spans : data_span list)
    (ctx : ctx) : Model.sec_comp list =
  let w = Stdlib.Int64.of_int word in
  let bindings = Tree.to_sequence ctx.data_tree |> Seq.to_list in
  let comps =
    bindings
    |> Base.List.filter_map ~f:(fun (k, rs) ->
        if in_whole_span ctx.whole k.lo.p_sec k.lo.p_pos then None
        else
          match rs.storage with
          | Data_region id ->
              Option.bind
                (Base.List.find spans ~f:(fun d ->
                     equal_sec d.ds_sec k.lo.p_sec))
                ~f:(fun d ->
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
  comps

let stamp_tags (c : ctx) (sub : sub term) : sub term =
  Term.map blk_t sub ~f:(fun blk ->
      Term.map def_t blk ~f:(fun d ->
          Option.value_map (Core.Map.find c.tags (Term.tid d)) ~default:d
            ~f:(fun t -> Hike_def_slots.set_sec_tag t d)))

(* The layout is the fold of the finalized tree: an unserved member
   fails loudly.  The residue (id 0) is the fallback storage, sized to
   the reach its def-backed members PROVE: an escape member (no def) is
   a claim about the callee's reach and never sizes it. *)
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
  (* Args-space residue accesses need the incoming caller window. A
     recognized va_list construction also consumes the overflow area
     through its stored pointer, even when the read is in a helper. *)
  let args_residue =
    Base.List.exists bindings ~f:(fun (k, rs) ->
        match rs.storage with
        | Stack_residue -> equal_sec k.lo.p_sec Args
        | _ -> false)
  in
  (* A def-backed member's proven above-entry reach; a def-backed
     identity member is an unbounded claim and keeps the fixed
     fallback. *)
  let member_above (m : member) : int64 =
    match m.m_def with
    | None -> 0L
    | Some _ ->
      let reach =
        Stdlib.Int64.max 0L
          (Stdlib.Int64.add (Stdlib.Int64.sub m.m_hi entry) 1L)
      in
      if m.m_identity then
        Stdlib.Int64.min reach Hike_stack_model.caller_window_bytes
      else reach
  in
  (* A def-backed member whose below-entry extent is unbounded or too
     deep for an alloca selects the runtime stack. *)
  let member_runtime (m : member) : bool =
    Option.is_some m.m_def
    && (Stdlib.Int64.equal m.m_lo (Model.stack_floor ~entry)
        || Stdlib.Int64.compare (Stdlib.Int64.sub entry m.m_lo)
             Hike_stack_model.frame_alloca_max > 0)
  in
  (* A def-backed member's proven below-entry depth. *)
  let member_below (m : member) : int64 =
    match m.m_def with
    | None -> 0L
    | Some _ when member_runtime m -> 0L
    | Some _ -> Stdlib.Int64.max (Stdlib.Int64.sub entry m.m_lo) 0L
  in
  let ( below, carved ), residue_seen =
    Base.List.fold bindings
      ~init:
        ( ( Stdlib.Int64.max (Hike_stack_model.deepest_sp_decrement sub ~abi) w64,
            [] ),
          false )
      ~f:(fun ((below, carved), residue_seen) (k, rs) ->
        match rs.storage with
        | Arg_slot -> ((below, carved), residue_seen)
        | Stack_residue ->
            let below =
              Base.List.fold rs.members ~init:below ~f:(fun acc m ->
                  Stdlib.Int64.max acc (member_below m))
            in
            ((below, carved), true)
        | Stack_region id ->
            let bytes = region_bytes k in
            (( below,
               { Model.Sub_layout.r_id = id;
                 r_lo = k.lo.p_pos;
                 r_hi = k.hi.p_pos;
                 r_bytes = bytes }
               :: carved ),
             residue_seen)
        | Data_region _ -> fail_unserved "data binding in a sub tree" k)
  in
  let pushes = Hike_stack_model.has_call_push sub in
  let below = if pushes then Stdlib.Int64.add below w64 else below in
  let residue_above =
    Base.List.fold bindings ~init:0L ~f:(fun acc (_, rs) ->
        match rs.storage with
        | Stack_residue ->
            Base.List.fold rs.members ~init:acc ~f:(fun acc m ->
                Stdlib.Int64.max acc (member_above m))
        | _ -> acc)
  in
  let below = if residue_seen then below else Stdlib.Int64.add below w64 in
  let window = residue_above in
  (* The anchor sits at the SysV entry-SP alignment inside the
     residue: idx ≡ align − word (mod align), so the lifted arithmetic
     (an SSE #GP guard tests (frame_base + k) & (align − 1)) matches the
     native. *)
  let align = Stdlib.Int64.of_int Hike_abi.stack_align in
  let residue_mod = Stdlib.Int64.sub align (Stdlib.Int64.rem w64 align) in
  let anchor_idx =
    Stdlib.Int64.add below
      (Stdlib.Int64.logand
         (Stdlib.Int64.sub residue_mod
            (Stdlib.Int64.rem below align))
         (Stdlib.Int64.sub align 1L))
  in
  let residue_bytes =
    align_up (Stdlib.Int64.add anchor_idx window) in
  let rlo = Stdlib.Int64.sub entry anchor_idx in
  let rhi = Stdlib.Int64.pred (Stdlib.Int64.add entry window) in
  let regions =
    if residue_seen || Stdlib.Int64.compare window 0L > 0 then
      { Model.Sub_layout.r_id = Model.residue_id;
        r_lo = rlo;
        r_hi = rhi;
        r_bytes = residue_bytes }
      :: Base.List.rev carved
    else Base.List.rev carved
  in
  let window_param = args_residue || Hike_variadic.is_variadic sub in
  let runtime_residue =
    Base.List.exists bindings ~f:(fun (_, rs) ->
        match rs.storage with
        | Stack_residue -> Base.List.exists rs.members ~f:member_runtime
        | _ -> false)
  in
  { Hike_stack_model.regions; window_param; runtime_residue }

type def_fact = {
  fr_conv : conv;
  fr_bits : int;
  fr_addr : exp option;
  fr_rhs : exp option;
}

let no_fact = { fr_conv = Keep; fr_bits = 0; fr_addr = None; fr_rhs = None }

(* The sub's storage spans: the layout's regions in the synth fact
   shape, built once and read by every consumer. *)
let spans_of_layout ~(synth : Hike_synth.table ref) ~(word : int)
    (layout : Hike_stack_model.sub_layout) : Hike_synth.storage_span list =
  Base.List.map layout.Hike_stack_model.regions
    ~f:(fun { Model.Sub_layout.r_id = id; r_lo = lo; r_hi = hi; _ } ->
        Hike_synth.record synth
          (Hike_synth.storage_span ~addr_bits:(Model.word_bits word)
             (Hike_synth.Stack id) ~lo ~hi))

(* The per-def rewrite facts of one sub: every access keeps its
   conversion; every address def whose value routes to a storage takes
   the base + displacement form. *)
let def_facts ~(synth : Hike_synth.table ref) ~(word : int) ~(entry : int64)
    ~(abi : Hike_abi.t)
    ~(tree : sub_tree) ~(data : data_tree)
    ~(projections : projection option Tid.Map.t)
    ~(conversions : conv Tid.Map.t)
    ~(storages : Hike_synth.storage_span list)
    ~(window_param : bool)
    ~(spans : data_span list)
    ~(denote : blk:blk term -> ?def:def term -> exp ->
                (Vsa.WordSet.t, Type.error) Result.t)
    (sub : sub term) : def_fact Tid.Map.t =
#ifdef VSA_DEBUG
  let census key = Cbat_vsa.Cbat_attr_census.bump key in
#else
  let census _ = () in
#endif
  let addr_bits = Model.word_bits word in
  let window_var () =
    Hike_synth.record synth (Hike_synth.mint_base ~addr_bits Hike_synth.Window)
  in
  let sec_comp_ptr id =
    Hike_synth.record synth
      (Hike_synth.mint_base ~addr_bits (Hike_synth.Global id))
  in
  (* The rewrite's admissibility: the address's whole range lies inside
     the storage's allocated extent — a value or access outside it names
     no storage, and the model arithmetic keeps it. *)
  (* An access keeps its conversion; a routable address base rides the
     fact. *)
  let access_fact ~leaves acc d (addr, w, _) =
    let fact = no_fact in
    let projected =
      Base.Option.join
        (Core.Map.find projections (Term.tid d))
    in
    let conv =
      Base.Option.value
        (Core.Map.find conversions (Term.tid d))
        ~default:Keep
    in
    let addr_range () =
      Base.Option.bind projected
        ~f:(fun p -> p.offsets)
    in
    match conv with
    | Conv_region id when
        Base.Option.value_map (addr_range ())
          ~default:false ~f:(fun (lo, hi) ->
            Hike_synth_addr.fits_span ~storages (Hike_synth.Stack id) lo hi)
        -> (
        let folded = Hike_synth_addr.offset_of ~addr_bits ~leaves addr in

        census
          (if Int.equal id Model.residue_id then
             (match folded with
              | Some _ -> "rw.access.residue.folded"
              | None -> "rw.access.residue.geom")
           else
             (match folded with
              | Some _ -> "rw.access.region.folded"
              | None -> "rw.access.region.geom"));
        let f =
          match Hike_synth_addr.span_base ~addr_bits ~storages (Hike_synth.Stack id) folded with
          | Some a -> { fact with fr_addr = Some a }
          | None -> fact
        in
        Core.Map.set acc ~key:(Term.tid d)
          ~data:{ f with fr_conv = conv; fr_bits = 8 * w })
    | Conv_region id ->
        census
          (if Int.equal id Model.residue_id then
             "rw.access.residue.outside"
           else "rw.access.region.outside");
        Core.Map.set acc ~key:(Term.tid d)
          ~data:{ fact with fr_conv = conv; fr_bits = 8 * w }
    | Conv_window ->
        census "rw.access.window";
        (* The window's base is the parameter; its
           coordinate IS the entry-relative offset. *)
        let f =
          match
            Hike_synth_addr.base_form ~addr_bits ~leaves
              ~base:(window_var ()) ~rel:0L addr
          with
          | Some a -> { fact with fr_addr = Some a }
          | None -> fact
        in
        Core.Map.set acc ~key:(Term.tid d)
          ~data:{ f with fr_conv = conv; fr_bits = 8 * w }
    | Conv_global _ ->
        census "rw.access.section";
        Core.Map.set acc ~key:(Term.tid d)
          ~data:{ fact with fr_conv = conv; fr_bits = 8 * w }
    | Keep | _ ->
        census "rw.access.keep";
        Core.Map.set acc ~key:(Term.tid d)
          ~data:
            { fact with fr_conv = conv;
              fr_bits = 8 * w }
  in
  (* A value def whose denotation routes to a storage takes the base +
     displacement form. *)
  let value_fact ~blk ~leaves acc d =
    let fact = no_fact in
    let v = Def.lhs d in
    if
      Model.is_mem v
      || Hike_abi.is_sp abi (Var.base v)
      || not
           (match Var.typ v with
            | Type.Imm n -> Int.equal n addr_bits
            | _ -> false)
    then acc
    else
      match denote ~blk ~def:d (Def.rhs d) with
      | Error _ -> acc
      | Ok ws
        when not (Vsa.WordSet.in_stack_segment ws)
             && not (Vsa.WordSet.is_top ws)
             && not (Vsa.WordSet.is_bottom ws) -> (
          (* A plain constant address routes to its
             component's base: the binding wholly
             owning it, minus the component's own low
             bound.  A constant at a copy-relocated
             slot is externally owned — it keeps the
             raw lane. *)
          match Model.singleton_i64 ws with
          | None -> census "rw.value.raw"; acc
          | Some c -> (
              match owning_data_binding data c with
              | Some (id, comp_lo) -> (
                  (* A pure constant address materializes
                     at this def: the component's pointer
                     base plus its own constant.  A value
                     with var leaves composes over its
                     operands' own pointers — the address
                     defs carrying it already render the
                     real bits, so a re-base here would
                     materialize the address twice. *)
                  match
                    Hike_synth_addr.offset_of ~addr_bits ~leaves (Def.rhs d)
                  with
                  | Some (Bil.Int w) ->
                      census "rw.value.section";
                      let rhs =
                        match
                          Cbat_word.to_int64
                            (Cbat_word.of_word w)
                        with
                        | Ok k
                          when Stdlib.Int64.equal k c ->
                            Hike_synth_addr.base_plus ~addr_bits
                              (sec_comp_ptr id)
                              ~rel:comp_lo (Bil.Int w)
                        | _ ->
                            Bil.BinOp
                              ( Bil.PLUS,
                                Bil.Var
                                  (sec_comp_ptr id),
                                Bil.BinOp
                                  ( Bil.MINUS,
                                    Bil.Int w,
                                    Bil.Int
                                      (Cbat_word.to_word
                                         (Cbat_word
                                            .of_int64
                                            ~width:addr_bits
                                            comp_lo))
                                  ) )
                      in
                      Core.Map.set acc ~key:(Term.tid d)
                        ~data:
                          { fact with fr_rhs = Some rhs }
                  | _ ->
                      census "rw.value.section.carried";
                      acc)
              | None -> census "rw.value.raw"; acc))
      | Ok ws -> (
          (* The routing of an address value: at/above
             the args base it names the caller's window
             (the parameter is the base); below the
             entry line the tree's binding owns its
             whole range. *)
          (
              let a_base = Model.args_base ~entry ~word in
              match
                (not (Vsa.WordSet.is_infinite ws),
                 Model.positions_of_offsets ws)
              with
              | true, Some (lo, hi)
                when Stdlib.Int64.compare lo hi <= 0
                     && Stdlib.Int64.compare lo a_base >= 0
                     && window_param -> (
                  match
                    Hike_synth_addr.base_form ~addr_bits ~leaves
                      ~base:(window_var ())
                      ~rel:0L (Def.rhs d)
                  with
                  | Some rhs ->
                      census "rw.value.window";
                      Core.Map.set acc ~key:(Term.tid d)
                        ~data:{ fact with fr_rhs = Some rhs }
                  | None ->
                      census "rw.value.window.unfoldable";
                      acc)
              | true, Some (lo, hi)
                when Stdlib.Int64.compare lo hi <= 0 -> (
                  match owning_storage tree lo hi with
                  | Some
                      ((Stack_region _ | Stack_residue) as
                      st)
                    when Hike_synth_addr.fits_span ~storages
                           (Hike_synth.Stack
                              (region_id_of_storage st))
                           lo hi
                    -> (
                      match
                        Hike_synth_addr.span_base ~addr_bits ~storages
                          (Hike_synth.Stack
                             (region_id_of_storage st))
                          (Hike_synth_addr.offset_of ~addr_bits ~leaves
                             (Def.rhs d))
                      with
                      | Some rhs ->
                          census "rw.value.region";
                          Core.Map.set acc
                            ~key:(Term.tid d)
                            ~data:{ fact with fr_rhs = Some rhs }
                      | None ->
                          census "rw.value.region.unfoldable";
                          acc)
                  | Some _ -> acc
                  | None -> census "rw.value.raw"; acc)
              | _ -> census "rw.value.raw"; acc))
  in
  Term.enum blk_t sub
  |> Seq.fold ~init:Tid.Map.empty ~f:(fun acc blk ->
         Term.enum def_t blk
         |> Seq.fold ~init:acc ~f:(fun acc d ->
                let leaves =
                  Hike_synth_addr.address_leaves ~synth:!synth ~denote ~storages ~blk
                    ~def:d (Def.rhs d) in
                match access_of d with
                | Some access -> access_fact ~leaves acc d access
                | None -> value_fact ~blk ~leaves acc d))

let slot_arity ~(word : int) ~(entry : int64) (tree : sub_tree) : int =
  let arity =
    Tree.to_sequence tree
    |> Seq.fold ~init:None ~f:(fun mx (_, rs) ->
           match rs.storage with
           | Arg_slot ->
               Base.List.fold rs.members ~init:mx ~f:(fun mx mm ->
                   match args_member_cell ~word ~entry mm with
                   | Some i -> (
                       match mx with
                       | Some n -> Some (Int.max n i)
                       | None -> Some i)
                   | None -> mx)
           | _ -> mx)
  in
  match arity with Some i -> i + 1 | None -> 0
