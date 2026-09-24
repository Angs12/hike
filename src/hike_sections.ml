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
type sec_meta = {
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
    let llvm_name = Bil2llvm_env.section_type_to_string sm_type in
    Hike_image.get_section_mem ("." ^ llvm_name) proj |> Hike_image.get_section_data
    |> Base.Option.map ~f:(fun (arr, min_addr, max_addr) ->
        { sm_type;
          sm_const = is_const;
          sm_lo = Word.to_int64_exn min_addr;
          sm_hi = Word.to_int64_exn max_addr;
          sm_words = (Bytes.length arr + word - 1) / word;
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
let copy_reloc_slot_addrs (meta : sec_meta option list) : int64 list =
  Base.List.concat_map meta ~f:(fun m ->
      Base.Option.value_map m ~default:[] ~f:(fun m ->
          Base.List.map m.sm_copy_relocs
            ~f:(fun (off, _) ->
              Stdlib.Int64.add m.sm_lo (Stdlib.Int64.of_int off))))
let attrib_spans ~(meta : sec_meta option list) : data_span list =
  Base.List.filter_map meta
    ~f:(Base.Option.map ~f:(fun m ->
            { ds_sec = m.sm_type;
              ds_lo = m.sm_lo;
              ds_hi = m.sm_hi;
              ds_slots =
                Base.List.map m.sm_copy_relocs ~f:(fun (off, _) ->
                    Stdlib.Int64.add m.sm_lo (Stdlib.Int64.of_int off)) }))

(* The emitter's section spec; a [whole] entry (id, lo, hi) is a span
   served whole — the section's own image global is the id's storage. *)
let section_spec_of ~(word : int) ~(comps : Model.sec_comp list)
    ~(whole : (int * int64 * int64) list) ~(meta : sec_meta option list) :
    Bil2llvm_env.section_spec =
  let spec_section (m : sec_meta) =
    let open Bil2llvm_env in
    match m.sm_image with
    | Some arr ->
        Sec_bytes
          { si_type = m.sm_type;
            si_lo = m.sm_lo;
            si_hi = m.sm_hi;
            si_words = m.sm_words;
            si_const = m.sm_const;
            si_image = arr }
    | None ->
        Sec_bss
          { si_lo = m.sm_lo;
            si_hi = m.sm_hi;
            si_words = m.sm_words;
            si_copy_relocs = m.sm_copy_relocs }
  in
  let open Bil2llvm_env in
  { spec_comps = comps;
    spec_whole = whole;
    spec_word = word;
    spec_sections =
      Base.List.map meta
        ~f:(Base.Option.map ~f:spec_section) }

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

type ctx = {
  sub_trees : sub_tree Tid.Map.t;
  data_tree : data_tree;
  tags : sec_tag Tid.Map.t;
  (* Each access def's (tag, portions) projection; [None] = the
     attribution's query failed and the rewrite keeps the memory form. *)
  projections : (sec_tag option * portion list) option Tid.Map.t;
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

(* Portions of the occupied interval [lo,hi]; the tag carries the
   ADDRESS bounds [alo,ahi]. *)
let sub_portions ~(entry : int64) ~(word : int) ~(elig : bool)
    ~(alo : int64) ~(ahi : int64) (lo : int64) (hi : int64)
    : sec_tag option * portion list =
  let floor = Model.stack_floor ~entry in
  let cei = Model.args_ceiling in
  let a_base = Model.args_base ~entry ~word in
  let s_top = Model.stack_top ~entry ~word in
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
      [ portion Stack (Model.clip ~cmp:Stdlib.Int64.compare lo hi floor s_top);
        portion Args (Model.clip ~cmp:Stdlib.Int64.compare lo hi a_base cei) ]
      ~f:(fun x -> x)
  in
  ( (if Option.is_some (Model.clip ~cmp:Stdlib.Int64.compare lo hi floor cei)
     then Some (tag alo ahi)
     else None),
    parts )

(* The full-span claim for a TOP address: a stack-symbolic top claims
   below-entry only, clamped by [stack_max] — imprecision never
   reaches the Args slots; any other top claims the sub-local spaces'
   full range — the identity member forcing write closure with the
   carved cells. *)
let top_claim ~(cause : top_cause) ~(entry : int64) ~(word : int)
    : sec_tag option * portion list =
  match cause with
  | Unbounded_stack ->
    let lo = Stdlib.Int64.sub entry Hike_stack_model.stack_max in
    ( Some Tag.Stack_unbounded,
      snd (sub_portions ~entry ~word ~elig:false ~alo:lo
             ~ahi:(Stdlib.Int64.pred entry) lo (Stdlib.Int64.pred entry)) )
  | Query_failed | Foreign ->
    (None,
     snd (sub_portions ~entry ~word ~elig:false
            ~alo:(Model.stack_floor ~entry) ~ahi:Model.args_ceiling
            (Model.stack_floor ~entry) Model.args_ceiling))

(* Case 1: the address carries stack offsets.  Bounded positions
   carve; an unbounded direction takes the full supported bounds of
   the side it reaches — identity, never carved. *)
let stack_offset_portions ~(word : int) ~(entry : int64) ~(width : int)
    (ws : Vsa.WordSet.t) : sec_tag option * portion list =
  let cei = Model.args_ceiling in
  let a_base = Model.args_base ~entry ~word in
  let sub_portions = sub_portions ~entry ~word in
  match Model.positions_of_offsets ws with
  | None -> top_claim ~cause:Unbounded_stack ~entry ~word
  | Some (lo, hi) ->
    let occ_hi = Model.expand_hi ~cap:cei hi width in
    if Vsa.WordSet.is_infinite ws || Stdlib.Int64.compare lo hi > 0 then
      let nlo, nhi = Model.full_bounds ws ~flo:(Model.stack_floor ~entry) ~cei lo hi in
      let t =
        if Stdlib.Int64.compare nlo a_base >= 0 then Tag.Args_unbounded
        else Tag.Stack (nlo, nhi)
      in
      (Some t, snd (sub_portions ~elig:false ~alo:nlo ~ahi:nhi nlo nhi))
    else
      (* Conversion is proven only when the occupied bytes stay
         in one space. *)
      let single =
        Stdlib.Int64.compare occ_hi a_base < 0
        || Stdlib.Int64.compare lo a_base >= 0
      in
      sub_portions ~elig:single ~alo:lo ~ahi:hi lo occ_hi

(* Case 2: a plain (offset-free) address.  A stack-band hull keeps
   the memory form; an unbounded ascending set's minimum names its
   section; the remaining bounded sets split across the data spans,
   with a rip proof where one span owns the whole occupied extent. *)
let plain_portions ~(word : int) ~(entry : int64)
    ~(spans : data_span list) ~(rip : bool) ~(width : int)
    (ws : Vsa.WordSet.t) : sec_tag option * portion list =
  let cei = Model.args_ceiling in
  let in_band = Vsa.WordSet.in_stack_segment ws in
  match (if in_band then Model.unsigned_bounds ws else None) with
  | Some (lo, hi) ->
    (* A band hull gets no conversion proof — identity. *)
    sub_portions ~entry ~word ~elig:false ~alo:lo ~ahi:hi lo
      (Model.expand_hi ~cap:cei hi width)
  | None ->
    match Model.unsigned_bounds ws with
    | None ->
      (* Stack-band values with no surviving bound lose the
         Args-vs-Locals distinction — a loud failure, never
         the heap claim. *)
      if in_band then
        failwith "hike-sections: a stack-band access lost all bounds"
      else top_claim ~cause:Foreign ~entry ~word
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
let range_of_denotation ~(word : int) ~(entry : int64)
    ~(spans : data_span list) ~(rip : bool) ~(width : int)
    (ws : Vsa.WordSet.t) : sec_tag option * portion list =
  if Vsa.WordSet.is_bottom ws then (Some Tag.Dead, [])
  else if Vsa.WordSet.is_top ws then
    (* A rip-relative address is a link-time constant in the encoding —
       top there is an analysis loss. *)
    if Option.is_some (Vsa.WordSet.stack_offsets ws) then
      top_claim ~cause:Unbounded_stack ~entry ~word
    else if rip then
      failwith "hike-sections: a rip-relative access denotated plain top"
    else top_claim ~cause:Foreign ~entry ~word
  else
    match Vsa.WordSet.stack_offsets ws with
    | Some _ -> stack_offset_portions ~word ~entry ~width ws
    | None -> plain_portions ~word ~entry ~spans ~rip ~width ws

type env = {
  word : int;
  entry : int64;
  spans : data_span list;
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
  projections : (sec_tag option * portion list) option Tid.Map.t;
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
  Tree.add rest hull (Base.List.fold hits ~init:[ m ] ~f:(fun acc (_, ms) -> acc @ ms))

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

let member_of ~(sub : Tid.t) ~(def : Tid.t option) ~(width : int) ~(store : bool)
    ~(word : int) ~(spans : data_span list) (p : portion) : member =
  let lo, hi =
    if is_sub_local p.pt_sec then (p.pt_lo, p.pt_hi)
    else
        (* The data side owns the emitter's word grid: a member's
           extent is its occupied bytes snapped OUT to the owning
           span's word hull. *)
        Option.value_map
          (Base.List.find spans ~f:(fun d -> equal_sec d.ds_sec p.pt_sec))
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
    sub_portions ~entry:env.entry ~word:env.word ~elig:false
      ~alo:lo ~ahi:hi lo hi
  in
  Base.List.map parts ~f:(fun p ->
      { m_sec = p.pt_sec; m_lo = p.pt_lo; m_hi = p.pt_hi; m_sub = sub;
        m_def = None; m_width = 0; m_store = false; m_identity = true })

let is_rip_relative (d : def term) : bool =
  Hike_def_slots.def_is_rip_relative d

(* Pure constant arithmetic — the address shape whose emission
   evaluates to the exact native bits. *)
let rec is_const_chain (e : exp) : bool =
  match e with
  | Bil.Int _ -> true
  | Bil.BinOp ((Bil.PLUS | Bil.MINUS), e1, e2) ->
    is_const_chain e1 && is_const_chain e2
  | _ -> false

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
            let projected : (sec_tag option * portion list) option =
              match env.denote ~blk:acc.blk ~def:d addr with
              | Error _ -> None
              | Ok ws ->
                Some
                  (range_of_denotation ~word:env.word ~entry:env.entry
                     ~spans:env.spans ~rip:(is_rip_relative d) ~width ws)
            in
            let tag, portions =
              match projected with
              | Some pair -> pair
              | None ->
                  (* A failed query keeps the access: the unknown
                     identity contributes full members. *)
                  top_claim ~cause:Query_failed ~entry:env.entry ~word:env.word
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
                 ~f:(fun (data, _) ->
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

let align16_up n =
  let r = Stdlib.Int64.rem n 16L in
  if Stdlib.Int64.equal r 0L then n else Stdlib.Int64.add n (Stdlib.Int64.sub 16L r)

let region_max_bytes : int64 = 67108864L

(* A stack region's alloca size: its byte span, 16-aligned. *)
let region_bytes (k : range) : int64 =
  align16_up (Stdlib.Int64.add (Stdlib.Int64.sub k.hi.p_pos k.lo.p_pos) 1L)

(* Whether [pos] sits inside one of the spans served whole. *)
let in_whole_span (whole : data_span list) (s : sec) (pos : int64) : bool =
  Base.List.exists whole ~f:(fun d ->
      equal_sec d.ds_sec s
      && Stdlib.Int64.unsigned_compare pos d.ds_lo >= 0
      && Stdlib.Int64.unsigned_compare pos d.ds_hi <= 0)


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
    ~(kind : [ `Sub | `Data ]) ~(whole : data_span list)
    (tree : member list Tree.t) : range_storage Tree.t =
  let bindings = Tree.to_sequence tree |> Seq.to_list in
  let sorted = Base.List.sort bindings ~compare:(fun (k1, _) (k2, _) -> compare k1 k2) in
  let ret_lo = entry in
  let ret_hi = Stdlib.Int64.pred (Stdlib.Int64.add entry (Stdlib.Int64.of_int word)) in
  (* The residue (id 0) is the stack's fallback region.  A whole span
     is one data region — every range in it shares the span's id;
     carved ranges mint an id each, per sub (stack) / module-wide
     (data). *)
  let next_region_id = ref 0 in
  let next_global_id = ref (-1) in
  let span_ids = ref [] in
  let decide (k : range) (ms : member list) : range_storage =
    let any_identity = Base.List.exists ms ~f:(fun m -> m.m_identity) in
    match k.lo.p_sec with
    | Stack ->
        let overlaps_ret =
          Stdlib.Int64.compare k.hi.p_pos ret_lo >= 0
          && Stdlib.Int64.compare k.lo.p_pos ret_hi <= 0
        in
        let bytes = region_bytes k in
        if overlaps_ret || any_identity || Stdlib.Int64.compare bytes region_max_bytes > 0
        then { storage = Stack_residue; members = ms }
        else (
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
          { storage =
              Arg_slot
                (Model.slot_index_of_offset ~word
                   (Stdlib.Int64.sub k.lo.p_pos entry));
            members = ms }
        else { storage = Stack_residue; members = ms })
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
    { word; entry; spans; params = abi.Hike_abi.int_param_regs;
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
        finalize_tree ~word ~entry ~spans ~kind:`Sub ~whole:[] tree)
  in
  let data_tree =
    finalize_tree ~word ~entry ~spans ~kind:`Data ~whole collected.data in
  { sub_trees; data_tree; tags = collected.tags; projections = collected.projections;
    whole }

(* The dynamic-allocation event: a def that moves SP by a runtime
   size — the direct [SP +/- X] form or a copy chain reaching it,
   with a non-fixed size and a strictly-below-SP value. *)
let dynamic_alloc_tids_of ~(facts : Hike_kb.facts)
    (sub : sub term) : Tid.Set.t =
  let sp_base = Var.base facts.abi.Hike_abi.sp in
  let is_sp v = Var.equal (Var.base v) sp_base in
  let denote = facts.denote in
  (* The size's own denotation confirms the event: a singleton
     displacement is a proven-constant frame adjust (no alloca), a
     non-singleton or unknown one is the runtime move. *)
  let runtime_at ~blk ~def d sz =
    match denote ~blk ~def:d sz with
    | Error _ -> true
    | Ok ws ->
      not (Vsa.WordSet.is_top ws)
      && (match Vsa.WordSet.min_elem ws, Vsa.WordSet.max_elem ws with
          | Some lo, Some hi -> not (Cbat_word.equal lo hi)
          | _ -> true)
  in
  (* A literal size is fixed; a var defers to its def; a def cycle or
     any other exp is runtime. *)
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
      Core.Option.value ~default:true (Core.Option.map ~f:next (Core.Map.find chain b))
  in
  (* The def's value must land strictly below the old SP (a
     decrement); an unknown keeps the runtime-move verdict. *)
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
  (* The direct [SP +/- X] form, or the copy chain reaching it. *)
  let rec event_rhs chain seen rhs =
    match rhs with
    | Bil.BinOp ((Bil.PLUS | Bil.MINUS), Bil.Var a, sz) when is_sp a ->
      runtime_size chain seen sz
    | Bil.Var v ->
      let b = Var.base v in
      if Core.Set.mem seen b then false
      else
        let next d = event_rhs chain (Core.Set.add seen b) (Def.rhs d) in
        Core.Option.value ~default:false
          (Core.Option.map ~f:next (Core.Map.find chain b))
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
               let moves =
                 event_rhs chain Var.Set.empty (Def.rhs d)
                 && descends ~blk ~def:d d
                 && (match Model.addr_of_rhs (Def.rhs d) with
                     | Some (sz, _) -> runtime_at ~blk ~def:d d sz
                     | None -> true)
               in
               if moves then (Core.Set.add events (Term.tid d), chain)
               else (events, chain)
             else
               (events,
                Core.Map.set chain ~key:(Var.base (Def.lhs d)) ~data:d)))
       |> fst

(* Merged bindings never overlap, so the binding containing the
   range's least point is THE owner. *)
let storage_of_range (tree : range_storage Tree.t) (r : range) :
    range_storage option =
  (* The rewrite's hottest query; the tree's lookup yields the
     containing (or nearest) entries, of which the first decides. *)
  match Seq.to_list (Tree.lookup tree r.lo) with
  | (_, v) :: _ -> Some v
  | [] -> None

(* The mem vars of storages carrying identity members: bytes another
   world (a callee, the window) reads through an escaped address — no
   def of this sub is their reader, so the DCE sweep keeps them as
   roots. *)
let escape_roots_of_tree (tree : sub_tree) : Var.Set.t =
  Tree.to_sequence tree
  |> Seq.fold ~init:Var.Set.empty ~f:(fun acc (_, rs) ->
         if not (Base.List.exists rs.members ~f:(fun m -> m.m_identity)) then acc
         else
           let mem_var = function
             | Stack_region id -> Some (Model.region_mem id)
             | Stack_residue -> Some (Model.region_mem Model.residue_id)
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

let sec_tag (d : def term) : sec_tag option = Hike_def_slots.sec_tag d

let set_sec_tag (t : sec_tag) (d : def term) : def term =
  Hike_def_slots.set_sec_tag t d

let stamp_tags (c : ctx) (sub : sub term) : sub term =
  Term.map blk_t sub ~f:(fun blk ->
      Term.map def_t blk ~f:(fun d ->
          Option.value_map (Core.Map.find c.tags (Term.tid d)) ~default:d
            ~f:(fun t -> set_sec_tag t d)))

(* The layout is the fold of the finalized tree: an unserved member
   fails loudly.  The residue (id 0) is the fallback alloca, sized to
   its members' below-entry depth plus the caller window. *)
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
                Stdlib.Int64.equal k.lo.p_pos (Model.stack_floor ~entry)
                || Stdlib.Int64.compare (Stdlib.Int64.sub entry k.lo.p_pos)
                     Hike_stack_model.stack_max > 0
              then Stdlib.Int64.max below Hike_stack_model.stack_max
              else Stdlib.Int64.max below (Stdlib.Int64.sub entry k.lo.p_pos)
            in
            ((below, window, carved), true)
        | Stack_region id ->
            let bytes = region_bytes k in
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
  (* The window is the constant SysV extent; a wider reach reads past
     it — a sound over-approximation. *)
  let window =
    if args_residue || residue_seen then Hike_stack_model.caller_window_bytes
    else 0L
  in
  (* The anchor sits at the SysV entry-SP alignment inside the
     residue: idx ≡ 16 − word (mod 16), so the lifted arithmetic (an
     SSE #GP guard tests (stack_0 + k) & 15) matches the native. *)
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
      (Model.residue_id, (rlo, rhi), residue_bytes) :: Base.List.rev carved
    else Base.List.rev carved
  in
  let anchor =
    if residue_seen || Stdlib.Int64.compare window 0L > 0 then
      Some (Model.residue_id, anchor_idx)
    else
      match regions with
      | (id, _, _) :: _ -> Some (id, residue_mod)
      | [] -> None
  in
  let window_param = args_residue in
  { Hike_stack_model.regions; anchor; window_param }

