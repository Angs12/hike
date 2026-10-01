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
  sm_const : bool;
  sm_lo : int64;
  sm_hi : int64;
  sm_words : int;
  sm_image : Bytes.t option;  (* None = the bss region *)
  sm_copy_relocs : (int * string) list;  (* bss: (byte offset, symbol) *)
}

let bss_region proj =
  let regions = Hike_image.get_named_region_info proj in
  Base.Option.map (Seq.find regions ~f:(fun { name; _ } -> String.equal name ".bss"))
    ~f:(fun { addr; size; _ } ->
      (addr, size, Hike_image.get_copy_relocations proj ~bss_addr:addr ~bss_size:size))

let sec_meta ~(word : int) (proj : Project.t) : sec_meta option list =
  let byte_row (sm_type : sec) ~is_const =
    let llvm_name = Model.sec_name sm_type in
    Hike_image.get_section_mem ("." ^ llvm_name) proj |> Hike_image.get_section_data
    |> Base.Option.map ~f:(fun (arr, min_addr, max_addr) ->
        { sm_type;
          sm_const = is_const;
          sm_lo = Word.to_int64_exn min_addr;
          sm_hi = Word.to_int64_exn max_addr;
          sm_words = Hike_stack_bounds.cdiv (Bytes.length arr) word;
          sm_image = Some arr;
          sm_copy_relocs = [] })
  in
  let bss_row =
    Base.Option.map (bss_region proj) ~f:(fun (addr, size, copy_relocs) ->
        { sm_type = Bss;
          sm_const = false;
          sm_lo = addr;
          sm_hi = Stdlib.Int64.sub (Stdlib.Int64.add addr size) 1L;
          sm_words =
            Stdlib.Int64.to_int
              (Stdlib.Int64.div (Stdlib.Int64.add size (Stdlib.Int64.of_int (word - 1)))
                 (Stdlib.Int64.of_int word));
          sm_image = None;
          sm_copy_relocs = copy_relocs })
  in
  [ byte_row Data ~is_const:false;
    byte_row Rodata ~is_const:true;
    bss_row;
    byte_row Got ~is_const:true;
    byte_row Gotplt ~is_const:true;
    byte_row Datarelro ~is_const:true;
    byte_row Text ~is_const:true ]

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
    ~(relative : (int64 * int64) list)
    ~(externals : (int64 * string) list) : Bil2llvm_env.section_spec =
  let open Bil2llvm_env in
  { spec_comps = comps;
    spec_whole = whole;
    spec_word = word;
    spec_sections = meta;
    spec_relative = relative;
    spec_externals = externals;
    spec_copy_relocs =
      Base.List.concat_map meta ~f:(fun m ->
          Base.Option.value_map m ~default:[] ~f:slot_addrs_of) }

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
   section's image global); the residue is the stack's fallback alloca. *)
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
}

type ctx = {
  sub_trees : sub_tree Tid.Map.t;
  data_tree : data_tree;
  tags : sec_tag Tid.Map.t;
  (* Each access def's projection; [None] = the attribution's query
     failed and the rewrite keeps the memory form. *)
  projections : projection option Tid.Map.t;
  (* The data spans served whole, computed once by [attribute] and
     shared by the finalize and both spec projections. *)
  whole : data_span list;
}


(* The sub-local line: entry RSP at [entry], signed positions; the
   return-address bytes are [entry, entry + word - 1], then Args. *)

(* Bottom yields no portion; every reachable unknown address
   contributes its full possible range to each space it may touch. *)

(* Why an address denotated TOP: the denotation query itself failed, a
   stack-symbolic set with no surviving bounds, or a plain top — no
   stack basis and no rip proof (the heap). *)
type top_cause = Query_failed | Unbounded_stack | Foreign

(* Splits [lo, hi] around the run's VLA extents: the surviving runs,
   and the extent intersections — the allocation's bytes bind to their
   own dynamic alloca, so every claim is cut around them. *)
let split_around_extents (extents : (int64 * int64) list) (lo : int64)
    (hi : int64) : (int64 * int64) list * (int64 * int64) list =
  let c = Stdlib.Int64.compare in
  Base.List.sort extents ~compare:(fun (a, _) (b, _) -> c a b)
  |> Base.List.fold ~init:([], [], lo)
       ~f:(fun (stack, vlas, cur) ext ->
         let elo = if c (fst ext) lo > 0 then fst ext else lo in
         let ehi = if c (snd ext) hi < 0 then snd ext else hi in
         if c elo ehi > 0 then (stack, vlas, cur)
         else
           let stack' =
             if c cur (Stdlib.Int64.pred elo) >= 0 then stack
             else (cur, Stdlib.Int64.pred elo) :: stack
           in
           (stack', (elo, ehi) :: vlas, Stdlib.Int64.succ ehi))
  |> fun (stack, vlas, cur) ->
     ( (if c cur hi <= 0 then (cur, hi) :: stack else Base.List.rev stack),
       Base.List.rev vlas )

(* Portions of the occupied interval [lo,hi]; the tag carries the
   ADDRESS bounds [alo,ahi].  The sub-local line's spaces are the
   frame [floor, s_top] cut around the VLA extents, and the args
   [a_base, ceiling]; the extent cuts are the VLA portions. *)
let sub_portions ~(extents : (int64 * int64) list) ~(entry : int64)
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
  let stack_runs, vla_runs =
    match Model.clip ~cmp:Stdlib.Int64.compare lo hi floor s_top with
    | Some (slo, shi) -> split_around_extents extents slo shi
    | None -> ([], [])
  in
  let parts =
    Base.List.filter_map
      ( Base.List.map stack_runs ~f:(fun r -> portion Stack (Some r) elig)
        @ [ portion Args (Model.clip ~cmp:Stdlib.Int64.compare lo hi a_base cei)
              elig ]
        @ Base.List.map vla_runs ~f:(fun r -> portion Vla (Some r) false) )
      ~f:(fun x -> x)
  in
  ( (if Option.is_some (Model.clip ~cmp:Stdlib.Int64.compare lo hi floor cei)
     then Some (Tag.Range (alo, ahi))
     else None),
    parts )

(* The full-span claim for a TOP address: a stack-symbolic top claims
   below-entry only, clamped by [stack_max], cut around the VLA
   extents; imprecision never reaches the Args slots; any other top
   claims the sub-local spaces' full range — the identity member
   forcing write closure with the carved cells. *)
let top_claim ~(extents : (int64 * int64) list) ~(cause : top_cause)
    ~(entry : int64) ~(word : int) : sec_tag option * portion list =
  match cause with
  | Unbounded_stack ->
    ( Some Tag.Unbounded,
      snd (sub_portions ~extents ~entry ~word ~elig:false
             ~alo:(Model.stack_floor ~entry) ~ahi:Model.args_ceiling
             (Stdlib.Int64.sub entry Hike_stack_model.stack_max)
             (Stdlib.Int64.pred entry)) )
  | Query_failed | Foreign ->
    (None,
     snd (sub_portions ~extents ~entry ~word ~elig:false
            ~alo:(Model.stack_floor ~entry) ~ahi:Model.args_ceiling
            (Model.stack_floor ~entry) Model.args_ceiling))

(* Case 1: the address carries stack offsets.  Bounded positions carve;
   an unbounded direction takes the full supported bounds of the side
   it reaches.  The bounded case clips PER RUN: a disjoint-run address
   (the va_arg reg-save/overflow join) keeps both bands instead of
   hulling across the entry line. *)
let stack_offset_portions ~(extents : (int64 * int64) list) ~(word : int)
    ~(entry : int64) ~(width : int) (ws : Vsa.WordSet.t) :
    sec_tag option * portion list =
  let cei = Model.args_ceiling in
  let a_base = Model.args_base ~entry ~word in
  let sub_portions = sub_portions ~extents ~entry ~word in
  match Model.positions_of_offsets ws with
  | None -> top_claim ~extents ~cause:Unbounded_stack ~entry ~word
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

(* Case 2: a plain (offset-free) address.  A stack-band hull keeps
   the memory form; an unbounded ascending set's minimum names its
   section; the remaining bounded sets split across the data spans,
   with a rip proof where one span owns the whole occupied extent. *)
let plain_portions ~(extents : (int64 * int64) list) ~(word : int)
    ~(entry : int64) ~(spans : data_span list) ~(rip : bool) ~(width : int)
    (ws : Vsa.WordSet.t) : sec_tag option * portion list =
  let cei = Model.args_ceiling in
  let in_band = Vsa.WordSet.in_stack_segment ws in
  match (if in_band then Model.unsigned_bounds ws else None) with
  | Some (lo, hi) ->
    (* A band hull gets no conversion proof — identity. *)
    sub_portions ~extents ~entry ~word ~elig:false ~alo:lo ~ahi:hi lo
      (Model.expand_hi ~cap:cei hi width)
  | None ->
    match Model.unsigned_bounds ws with
    | None ->
      (* No surviving bound: the identity claim, never the heap claim. *)
      top_claim ~extents ~cause:Foreign ~entry ~word
    | Some (lo, hi) ->
      if Vsa.WordSet.is_infinite ws && Vsa.WordSet.is_ascending ws then begin
        (* Accesses never cross sections, so an unbounded ascending
           access's minimum names its section; the claim clamps into
           it.  A non-rip address outside every span is the heap. *)
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
          | None -> top_claim ~extents ~cause:Foreign ~entry ~word
        else top_claim ~extents ~cause:Foreign ~entry ~word
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
              Stdlib.Int64.unsigned_compare plo s <= 0
              && Stdlib.Int64.unsigned_compare s phi <= 0)
        in
        let elig =
          rip && whole_in_one
          && not (Base.List.exists parts ~f:at_slot)
        in
        ( None,
          Base.List.map parts ~f:(fun (d, plo, phi) ->
              { pt_sec = d.ds_sec; pt_lo = plo; pt_hi = phi;
                pt_elig = elig } ))

(* The def's address claim: the sections each reachable position may
   touch, and whether conversion is proven. *)
let range_of_denotation ~(extents : (int64 * int64) list) ~(word : int)
    ~(entry : int64) ~(spans : data_span list) ~(rip : bool) ~(width : int)
    (ws : Vsa.WordSet.t) : sec_tag option * portion list =
  if Vsa.WordSet.is_bottom ws then (Some Tag.Dead, [])
  else if Vsa.WordSet.is_top ws then
    (* A plain top claims the sub-local spaces' full range — the
       identity member forcing write closure; a rip-relative address
       is a link-time constant in the encoding, so plain top there is
       an analysis loss answered the same way. *)
    if Option.is_some (Vsa.WordSet.stack_offsets ws) then
      top_claim ~extents ~cause:Unbounded_stack ~entry ~word
    else top_claim ~extents ~cause:Foreign ~entry ~word
  else
    match Vsa.WordSet.origin ws with
    | Some (Vsa.WordSet.Origin.Vla _) ->
      (* A VLA claim's real storage is the dynamic alloca the origin
         names; it binds nothing in the section tree. *)
      (None, [])
    | _ -> (
      match Vsa.WordSet.stack_offsets ws with
      | Some _ -> stack_offset_portions ~extents ~word ~entry ~width ws
      | None -> plain_portions ~extents ~word ~entry ~spans ~rip ~width ws)

type env = {
  word : int;
  entry : int64;
  spans : data_span list;
  extents : (int64 * int64) list;
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

(* The identity members of an escape extent, projected into the
   sub-local spaces; no def.  [sub_portions]'s two clip windows ARE
   the sub-local line's geometry. *)
let escape_members ~(sub : Tid.t) ~(env : env) (ext : int64 * int64) :
    member list =
  let lo, hi = ext in
  let _, parts =
    sub_portions ~extents:env.extents ~entry:env.entry ~word:env.word
      ~elig:false ~alo:lo ~ahi:hi lo hi
  in
  Base.List.map
    (Base.List.filter parts ~f:(fun p -> not (equal_sec p.pt_sec Vla)))
    ~f:(fun p ->
      { m_sec = p.pt_sec; m_lo = p.pt_lo; m_hi = p.pt_hi; m_sub = sub;
        m_def = None; m_width = 0; m_store = false; m_identity = true })

(* Pure constant arithmetic — the address shape whose emission
   evaluates to the exact native bits. *)
let is_const_chain (e : exp) : bool =
  Hike_exp_fold.fold
    (fun e child ->
      match e with
      | Bil.Int _ -> true
      | Bil.BinOp ((Bil.PLUS | Bil.MINUS), a, b) -> child a && child b
      | _ -> false)
    e

(* The caller-window hull's slack above the call-time SP: pushes and
   alignment spillover the window must cover. *)
let window_push_slop_words = 8

(* The def's memory access: (address, width in bytes, stores). *)
let access_of (d : def term) : (exp * int * bool) option =
  Option.map (Model.addr_of_rhs (Def.rhs d)) ~f:(fun (addr, size) ->
      (addr, Size.in_bytes size, Option.is_some (Model.store_data_of_rhs (Def.rhs d))))

let collect (env : env) (prog : program term) : collecting =
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
                   (Result.ok (env.denote ~blk:acc.blk (Bil.Var v)))
                   ~f:(Model.escape_extent ~entry:env.entry))
                ~init:acc
                ~f:(fun acc ext ->
                  Base.List.fold (escape_members ~sub:acc.sub ~env ext)
                    ~init:acc
                    ~f:(fun acc m -> { acc with tree = insert acc.tree m })))
        in
        (* A calling block exposes the call window to the callee —
           those bytes must live in the residue, never a carved
           region; the identity member spanning the window forces the
           residue and grows its extent. *)
        let has_call =
          Term.enum jmp_t acc.blk
          |> Seq.exists ~f:(fun j -> Hike_stack_model.call_pushes j)
        in
        if not has_call then acc
        else
          Option.fold
            (Option.bind
               (Result.ok (env.denote ~blk:acc.blk (Bil.Var env.sp)))
               ~f:Model.positions_of_offsets)
            ~init:acc
            ~f:(fun acc (lo, hi) ->
              if not (Stdlib.Int64.equal lo hi) then acc
              else
                let sp_abs = lo in
                let win_lo =
                  Stdlib.Int64.sub sp_abs (Stdlib.Int64.of_int env.word) in
                let win_hi =
                  Stdlib.Int64.add
                    (Stdlib.Int64.add sp_abs
                       (Stdlib.Int64.of_int
                          (window_push_slop_words * env.word)))
                    Hike_stack_model.caller_window_bytes
                in
                Base.List.fold (escape_members ~sub:acc.sub ~env (win_lo, win_hi))
                  ~init:acc
                  ~f:(fun acc m -> { acc with tree = insert acc.tree m }))

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
                  range_of_denotation ~extents:env.extents
                     ~word:env.word ~entry:env.entry ~spans:env.spans
                     ~rip:(Hike_def_slots.def_is_rip_relative d) ~width ws
                in
                Some { tag; origin = Vsa.WordSet.origin ws; portions }
            in
            let tag, portions =
              match projected with
              | Some p -> (p.tag, p.portions)
              | None ->
                  (* A failed query keeps the access: the unknown
                     identity contributes full members. *)
                  top_claim ~extents:env.extents ~cause:Query_failed
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
                (* A VLA-band portion binds nowhere: its real storage is
                   the dynamic alloca the pointer chain already names. *)
                if equal_sec p.pt_sec Vla then acc
                else
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
    Stdlib.Int64.unsigned_compare pos d.ds_lo >= 0
    && Stdlib.Int64.unsigned_compare pos d.ds_hi <= 0
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
              if Stdlib.Int64.unsigned_compare k.lo.p_pos d.ds_lo >= 0
                 && Stdlib.Int64.unsigned_compare k.lo.p_pos d.ds_hi <= 0
              then Some d else None)
        else None)
  in
  Base.List.filter spans ~f:(fun d ->
      (not (Base.List.is_empty d.ds_slots)) || Base.List.mem tainted d ~equal:equal_data_span)

let finalize_tree ~(word : int) ~(entry : int64)
    ~(whole : data_span list)
    (tree : member list Tree.t) : range_storage Tree.t =
  let bindings = Tree.to_sequence tree |> Seq.to_list in
  let sorted = Base.List.sort bindings ~compare:(fun (k1, _) (k2, _) -> compare k1 k2) in
  let ret_lo = entry in
  let ret_hi = Stdlib.Int64.pred (Stdlib.Int64.add entry (Stdlib.Int64.of_int word)) in
  (* The residue (id 0) is the stack's fallback region.  A whole span
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
    | Args -> (
        let base = Model.args_base ~entry ~word in
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
          let () = bump "region.args.slot" in
          { storage =
              Arg_slot
                (Model.slot_index_of_offset ~word
                   (Stdlib.Int64.sub k.lo.p_pos entry));
            members = ms }
        else (
          bump "region.args.residue";
          { storage = Stack_residue; members = ms }))
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
  Base.List.fold sorted ~init:Tree.empty ~f:(fun t (k, ms) ->
      Tree.add t k (decide k ms))

let attribute ~(facts : Hike_kb.facts) ~(word : int) ~(entry : int64)
    ~(spans : data_span list)
    (prog : program term) : ctx =
  let abi = facts.abi in
  let env =
    (* Only the integer params ride the escape fold: the vector lanes
       are FP values the model's stack offsets never serve. *)
    { word; entry; spans;
      extents = [];
      params = abi.Hike_abi.int_param_regs;
      sp = abi.Hike_abi.sp; denote = facts.denote }
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
  { sub_trees; data_tree; tags = collected.tags; projections = collected.projections;
    whole }

(* The dynamic-allocation set is the seed's own, re-validated against
   the final denotations: the event predicate over the def's SP-before
   and SP-after words.  An alloca without an origin and an origin
   without an alloca are the same set. *)
let dynamic_alloc_tids_of ~(facts : Hike_kb.facts)
    (sub : sub term) : Tid.Set.t =
  let sp = facts.abi.Hike_abi.sp in
  let def_at =
    Term.enum blk_t sub
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m blk ->
        Term.enum def_t blk
        |> Seq.fold ~init:m ~f:(fun m d ->
            Core.Map.set m ~key:(Term.tid d) ~data:(d, blk)))
  in
  Core.Map.filter_keys facts.Hike_kb.vla_extents ~f:(fun tid ->
      match Core.Map.find def_at tid with
      | None -> false
      | Some (d, blk) -> (
        match facts.denote ~blk ~def:d (Bil.Var sp),
              facts.denote ~blk ~def:d (Def.rhs d) with
        | Ok before, Ok after -> Option.is_some (Vsa.vla_event ~before ~after)
        | _ -> false))
  |> Core.Map.key_set

(* Merged bindings never overlap, so the binding containing the
   range's least point is THE owner. *)
let storage_of_range (tree : range_storage Tree.t) (r : range) :
    range_storage option =
  (* The rewrite's hottest query; the tree's lookup yields the
     containing (or nearest) entries, of which the first decides. *)
  match Seq.hd (Tree.lookup tree r.lo) with
  | Some (_, v) -> Some v
  | None -> None

(* The mem vars of storages carrying identity members: bytes another
   world (a callee, the window) reads through an escaped address — no
   def of this sub is their reader, so the DCE sweep keeps them as
   roots. *)
let escape_roots_of_tree ~(addr_bits : int) (tree : sub_tree) : Var.Set.t =
  Tree.to_sequence tree
  |> Seq.fold ~init:Var.Set.empty ~f:(fun acc (_, rs) ->
         if not (Base.List.exists rs.members ~f:(fun m -> m.m_identity)) then acc
         else
           let mem_var = function
             | Stack_region id -> Some (Model.region_mem ~addr_bits id)
             | Stack_residue -> Some (Model.region_mem ~addr_bits Model.residue_id)
             | Arg_slot _ -> None
             | Data_region _ ->
               failwith "hike-sections: a data binding in a sub tree"
           in
           match mem_var rs.storage with
           | Some v -> Core.Set.add acc v
           | None -> acc)

(* A whole span serves as ONE component covering the span, stored in
   the section's own image global (the emitter wires the id to it). *)
let whole_comps_of (ctx : ctx) : (int * int64 * int64) list =
  let bindings = Tree.to_sequence ctx.data_tree |> Seq.to_list in
  Base.List.filter_map ctx.whole ~f:(fun d ->
      Option.bind
        (Base.List.find bindings ~f:(fun (k, rs) ->
             equal_sec k.lo.p_sec d.ds_sec
             && (match rs.storage with Data_region _ -> true | _ -> false)))
        ~f:(fun (_, rs) ->
          match rs.storage with
          | Data_region id -> Some (id, d.ds_lo, d.ds_hi)
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
   fails loudly.  The residue (id 0) is the fallback alloca, sized to
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
  (* The Args-space residue members are the caller-window's readers:
     they force the window and the window parameter alike. *)
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
  (* A def-backed member's proven below-entry depth; an unbounded claim
     keeps the fixed fallback. *)
  let member_below (m : member) : int64 =
    match m.m_def with
    | None -> 0L
    | Some _ ->
      let depth = Stdlib.Int64.sub entry m.m_lo in
      if
        Stdlib.Int64.equal m.m_lo (Model.stack_floor ~entry)
        || Stdlib.Int64.compare depth Hike_stack_model.stack_max > 0
      then Hike_stack_model.stack_max
      else Stdlib.Int64.max depth 0L
  in
  let ( below, carved ), residue_seen =
    Base.List.fold bindings
      ~init:
        ( ( Stdlib.Int64.max (Hike_stack_model.deepest_sp_decrement sub ~abi) w64,
            [] ),
          false )
      ~f:(fun ((below, carved), residue_seen) (k, rs) ->
        match rs.storage with
        | Arg_slot _ -> ((below, carved), residue_seen)
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
  let window_param = args_residue in
  { Hike_stack_model.regions; window_param }

