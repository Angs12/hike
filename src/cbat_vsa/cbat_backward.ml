(* Backward refinement: guard rows, pre-images, the deep walk, the
   inline edge refinement. *)

include Core
open Bap.Std
open Graphlib.Std
open Cbat_vsa_utils
module AI = Cbat_ai_representation
module WordSet = Cbat_clp_set_composite
module Mem = Cbat_ai_memmap
module Word_ops = Cbat_word

module Stages = Cbat_vsa_stages
open Cbat_transfer


(* Proves an expression's every possible value has its sign bit clear:
   literals, positive-preserving arithmetic, and — through unique defs —
   anchored loads seeded and written only with non-negative data. *)
let prove_nonneg ~(defs : (def term * bool) Var.Map.t)
    ~(index : def term list Exp.Map.t)
    ~(env : AI.t) (e : exp) : bool =
  let nonneg_word (n : Cbat_word.t) : bool =
    let w = Cbat_word.bitwidth n in
    w > 0
    && Cbat_word.(<) n (Word_ops.half w) in
  (* Anchored: the address var's word is a stack-symbolic value, so the
     cell is private to this sub's frame. *)
  let stack_anchor (v : var) : bool =
    match Var.typ v with
    | Type.Imm w ->
      Option.is_some (WordSet.stack_offsets (AI.find_word w env v))
    | Type.Mem _ | Type.Unk -> false in
  let rec walk (cells : Exp.Set.t) (vars : Exp.Set.t) (e : exp) : bool =
    match e with
    | Bil.Int n -> nonneg_word (Cbat_word.of_word n)
    | Bil.Var v ->
      let seen = Core.Set.mem vars e in
      (match Core.Map.find defs (Var.base v) with
       | Some (d, true) when seen ->
         (* Loads may close the induction. *)
         (match Def.rhs d with
          | Bil.Load _ -> walk cells vars (Def.rhs d)
          | _ -> false)
       | Some (d, true) -> walk cells (Core.Set.add vars e) (Def.rhs d)
       | _ -> false)
    | Bil.BinOp (Bil.PLUS, a, b) ->
      walk cells vars a && walk cells vars b
    | Bil.BinOp (Bil.MINUS, a, b) ->
      (match b with
       | Bil.Int z when Cbat_word.is_zero (Cbat_word.of_word z) ->
         walk cells vars a
       | _ -> false)
    | Bil.BinOp (Bil.RSHIFT, _, Bil.Int k) ->
      (match Cbat_word.to_int (Cbat_word.of_word k) with
       | Ok n when n > 0 -> true
       | _ -> false)
    | Bil.BinOp (Bil.ARSHIFT, a, Bil.Int k) ->
      (match Cbat_word.to_int (Cbat_word.of_word k) with
       | Ok n when n >= 0 -> walk cells vars a
       | _ -> false)
    | Bil.BinOp (Bil.TIMES, a, Bil.Int k) ->
      let k = Cbat_word.of_word k in
      nonneg_word k && (Cbat_word.is_zero k || walk cells vars a)
    | Bil.BinOp (Bil.DIVIDE, a, Bil.Int k) ->
      (match Cbat_word.to_int (Cbat_word.of_word k) with
       | Ok n when n >= 2 -> true
       | Ok 1 -> walk cells vars a
       | _ -> false)
    | Bil.BinOp (Bil.AND, _, Bil.Int k) ->
      let k = Cbat_word.of_word k in
      let w = Cbat_word.bitwidth k in
      Cbat_word.(<) k (Word_ops.half w)
    | Bil.BinOp (Bil.OR, a, Bil.Int k)
      when Cbat_word.is_zero (Cbat_word.of_word k) -> walk cells vars a
    | Bil.BinOp (Bil.XOR, a, Bil.Int k)
      when Cbat_word.is_zero (Cbat_word.of_word k) -> walk cells vars a
    | Bil.Cast (Bil.HIGH, _, a) -> walk cells vars a
    | Bil.Load (_, addr, _, _) ->
      let addr_vars = Exp.free_vars addr in
      let anchored =
        not (Core.Set.is_empty addr_vars)
        && Core.Set.for_all addr_vars ~f:stack_anchor in
      let reentry = Core.Set.mem cells addr in
      if not anchored then false
      else if reentry then true
      else
        let cells' = Core.Set.add cells addr in
        let matches =
          Core.Map.find index addr |> Option.value ~default:[]
        in
        let has_seed = List.exists matches ~f:(fun d ->
            match Def.rhs d with
            | Bil.Store (_, _, Bil.Int n, _, _) ->
              nonneg_word (Cbat_word.of_word n)
            | _ -> false) in
        let all_values = List.for_all matches ~f:(fun d ->
            match Def.rhs d with
            | Bil.Store (_, _, u, _, _) -> walk cells' vars u
            | _ -> false) in
        has_seed && all_values
    | _ -> false
  in
  walk Exp.Set.empty Exp.Set.empty e

(* A cell constraint awaiting delivery to the store that wrote it: what
   a load read, keyed by the byte range it touched.  An entry dies at the
   store that overwrites its range (a shape-matching one delivers, any
   overlapping one blocks the boundary carry); one no store consumes
   crosses the block boundary into the edge state. *)
type cell = {
  pm : var;              (* the memory var *)
  prange : Mem.Key.t;    (* the read's touched byte range *)
  pc : wordset;          (* the produced value's constraint *)
  pbits : int;           (* the read's width *)
  pendian : endian;      (* the read's endianness *)
}

(* The word constraints still owed to their producers, by base var
   (absent = unconstrained).  A def removes its var's entry; what no
   def consumes crosses the block boundary into the edge state. *)
type word_env = (var * wordset) Var.Map.t

let word_find (we : word_env) (v : var) : wordset option =
  Option.map (Core.Map.find we (Var.base v)) ~f:snd

let word_set (we : word_env) (v : var) (c : wordset) : word_env =
  Core.Map.set we ~key:(Var.base v) ~data:(v, c)

module Cell_key = struct
  type t = Mem.Key.t * int * endian
  let compare (k1, b1, e1) (k2, b2, e2) =
    let c = Mem.Key.compare k1 k2 in
    if c <> 0 then c
    else
      let c = Int.compare b1 b2 in
      if c <> 0 then c else Bitvector.compare_endian e1 e2
  let sexp_of_t (k, b, _) =
    Sexp.List [ Mem.Key.sexp_of_t k; Sexp.Atom (Int.to_string b) ]
  include Core.Comparator.Make (struct
      type nonrec t = t
      let compare = compare
      let sexp_of_t = sexp_of_t
    end)
end

(* The cell constraints still owed to stores, by memory var then by the
   read's range and shape (absent = unconstrained).  Two reads of one
   range and shape owe the meet of their constraints. *)
type cell_env =
  (Cell_key.t, cell, Cell_key.comparator_witness) Core.Map.t Var.Map.t

let no_cells : cell_env = Var.Map.empty

let cell_key (c : cell) : Cell_key.t = (c.prange, c.pbits, c.pendian)

let cell_add (ce : cell_env) (c : cell) : cell_env =
  let key = Var.base c.pm in
  let sub =
    Option.value (Core.Map.find ce key)
      ~default:(Core.Map.empty (module Cell_key)) in
  let c =
    match Core.Map.find sub (cell_key c) with
    | Some old when WordSet.bitwidth old.pc = WordSet.bitwidth c.pc ->
      let m = WordSet.meet old.pc c.pc in
      if Cbat_word.is_zero (WordSet.cardinality m) then old
      else { c with pc = m }
    | _ -> c in
  Core.Map.set ce ~key ~data:(Core.Map.set sub ~key:(cell_key c) ~data:c)

(* The entries of [mv] satisfying [f], and the rest. *)
let cell_take (ce : cell_env) (mv : var) ~(f : cell -> bool)
    : cell list * cell_env =
  match Core.Map.find ce (Var.base mv) with
  | None -> [], ce
  | Some sub ->
    let hit, rest = Core.Map.partition_tf sub ~f in
    if Core.Map.is_empty hit then [], ce
    else
      Core.Map.data hit,
      if Core.Map.is_empty rest then Core.Map.remove ce (Var.base mv)
      else Core.Map.set ce ~key:(Var.base mv) ~data:rest

(* The entries [after] holds that [before] does not hold physically. *)
let cells_pushed ~(before : cell_env) ~(after : cell_env) : cell list =
  Core.Map.fold after ~init:[] ~f:(fun ~key ~data:sub acc ->
      match Core.Map.find before key with
      | Some old when phys_equal old sub -> acc
      | old ->
        let old = Option.value old ~default:(Core.Map.empty (module Cell_key)) in
        Core.Map.fold sub ~init:acc ~f:(fun ~key:ck ~data:c acc ->
            match Core.Map.find old ck with
            | Some c' when phys_equal c c' -> acc
            | _ -> c :: acc))

let cells_fold (ce : cell_env) ~(init : 'a) ~(f : 'a -> cell -> 'a) : 'a =
  Core.Map.fold ce ~init ~f:(fun ~key:_ ~data:sub acc ->
      Core.Map.fold sub ~init:acc ~f:(fun ~key:_ ~data:c acc -> f acc c))
(* THE one leaf meet, keyed by what it constrains (a variable, or a
   memory cell) — the policy both lanes share.  Every meet is acquired
   into the enclosing head's widening table (the excluded boundary when
   the meet empties, the trimmed piece when it narrows).  An empty meet
   is the excluded behavior: observed first, then [on_empty] decides the
   state (unchanged by default).  A meet that does not narrow takes the
   identity.  A real narrowing is written back. *)
let leaf_meet ?(on_empty : 'st -> 'st = Fun.id) ~(landmarks : Cbat_landmarks.t)
    ~(key : Cbat_landmarks.key) ~(cur : wordset)
    ~(meet : wordset -> wordset -> wordset)
    ~(write : wordset -> 'st -> 'st) (cstr : wordset) (st : 'st) : 'st =
  if WordSet.bitwidth cur <> WordSet.bitwidth cstr then st
  else begin
    let m = meet cur cstr in
    ignore (Cbat_landmarks.observe_unsat landmarks ~key ~p:cur ~cstr ~m);
    if Cbat_word.is_zero (WordSet.cardinality m) then on_empty st
    else if (not (WordSet.precedes m cur)) || WordSet.equal m cur then st
    else write m st
  end

(* The leaf var's inverse: the meet, through the one leaf rule.  An empty
   meet is proof no state satisfies the constraint: the dead-path
   bottom. *)
let meet_var ~(landmarks : Cbat_landmarks.t)
    (env : AI.t) (v : var) (refined : wordset) : AI.t =
  match Var.typ v with
  | Type.Imm w ->
    let cur = AI.find_word w env v in
    let on_empty _ = AI.bottom in
    leaf_meet ~on_empty ~landmarks ~key:(Cbat_landmarks.Word v) ~cur
      ~meet:WordSet.meet
      ~write:(fun m env ->
#ifdef VSA_DEBUG
        (match WordSet.stack_offsets cur, WordSet.stack_offsets m with
         | Some _, None ->
           Format.eprintf "DBG SYMBOL-STRIP var=%s cur=%a refined=%a meet=%a\n%!"
             (Var.name v) WordSet.pp cur WordSet.pp refined WordSet.pp m
         | _ -> ());
#endif
        AI.add_word env ~key:v ~data:m)
      refined env
  | Type.Mem _ | Type.Unk -> env

#ifdef VSA_DEBUG
(* The cell-meet soundness differential: each narrowing cell meet is
   checked over its enumerable concrete points — every pre-meet element
   satisfying the produced constraint must survive the meet; a lost
   point is an unsound narrowing and fails the debug run.  Bounded:
   pre-values beyond the enumeration cap count as skipped. *)
let cell_meet_cap = 16
let cell_meet_seq = ref 0
let cell_meet_verified = ref 0
let cell_meet_skipped = ref 0
let cell_meet_violations = ref 0
let cell_meet_diff_dump () =
  Printf.printf "CELL-MEET-DIFF: verified=%d skipped=%d violations=%d\n%!"
    !cell_meet_verified !cell_meet_skipped !cell_meet_violations
let () = at_exit cell_meet_diff_dump
let cell_meet_diff ~(ckey : string) ~(pre : wordset) ~(cstr : wordset)
    ~(res : wordset) : unit =
  incr cell_meet_seq;
  match WordSet.enumerate ~cap:cell_meet_cap pre with
  | None -> incr cell_meet_skipped
  | Some elems ->
    (match List.find elems ~f:(fun v ->
         WordSet.elem v cstr && not (WordSet.elem v res)) with
     | None -> incr cell_meet_verified
     | Some v ->
       incr cell_meet_violations;
       failwith
         (Format.asprintf
            "CELL-MEET-DIFF VIOLATION cell %s: point %s satisfies the \
             constraint %a but is outside the meet %a (pre %a)"
            ckey (Cbat_word.to_string v) WordSet.pp cstr WordSet.pp res
            WordSet.pp pre))
#endif

(* The cell key a backward meet may name: only a bounded address set
   denotes the cell a trace reads.  An unbounded address names no cell,
   so its constraint must stay identity rather than narrow every cell.
   The backward cell meet is sound only when every path reads the SAME
   cell: a single-point address, or a wider address set whose read bytes
   all lie inside one stored cell.  A read that can land on two cells
   reads a different one per path, so the read's value constraint is
   path-local.  ADR 0025's join argument covers the join (a load's value
   contains every contributing cell); it does not license the meet back
   into each cell. *)
let bounded_cell_key (ws : wordset) : Mem.Key.t list =
  if WordSet.is_top ws || WordSet.is_infinite ws then []
  else Mem.Key.of_wordset ws

(* A single-point key names one address (and so one cell on every path). *)
let key_is_point (k : Mem.Key.t) : bool =
  Mem.Key.step k = 1
  && (let lo, hi = Mem.Key.hull k in Cbat_word.equal lo hi)

(* The byte span a stored cell occupies: its key hull grown by its
   value's own width. *)
let cell_span ((k, v) : Mem.Key.t * Mem.Val.t) : Cbat_word.t * Cbat_word.t =
  Mem.Key.hull (Mem.Key.expand k ~bytes:(fst (Mem.Val.get_idx v) / 8))

(* The one stored cell the read's touched bytes all lie inside, when
   exactly one cell covers the read. *)
let covering_cell (mv : Mem.t) (key : Mem.Key.t) ~(bytes : int)
    : Mem.Key.t option =
  let origin = Mem.Key.origin key in
  let r_lo, r_hi = Mem.Key.hull (Mem.Key.expand key ~bytes) in
  let covers (c, v) =
    Hike_origin.equal (Mem.Key.origin c) origin
    && (let c_lo, c_hi = cell_span (c, v) in
        Cbat_word.(<=) c_lo r_lo && Cbat_word.(<=) r_hi c_hi)
  in
  match List.filter (Mem.cells mv) ~f:covers with
  | [ (c, _) ] -> Some c
  | _ -> None

(* The cell keys a backward meet may narrow: the read's own key when the
   read touches one cell on every path; [] otherwise (the meet stays the
   identity, and the address pre-image carries the sound narrowing). *)
let backward_cell_keys (mv : Mem.t) (addr_ws : wordset) ~(bytes : int)
    : Mem.Key.t list =
  match bounded_cell_key addr_ws with
  | [ k ] when key_is_point k -> [ k ]
  | [ k ] ->
    (match covering_cell mv k ~bytes with Some _ -> [ k ] | None -> [])
  | _ -> []

(* Whether a piece's elements fill its hull: its element count equals
   the hull's.  Every piece the address filter decides is finite and
   non-wrapped, so its min/max are its elements' bounds.  A step-1
   traversal (or a singleton) is dense by construction; the hull-count
   test is the general fallback. *)
let piece_dense (p : Cbat_clp.t) ~(lo : Cbat_word.t) ~(hi : Cbat_word.t) : bool =
  (not (Cbat_clp.is_infinite p))
  && (Cbat_word.is_one (Cbat_clp.cardinality p)
      || Cbat_word.is_one (Cbat_clp.step_of p)
      || (let w1 = Cbat_word.bitwidth hi + 1 in
          let hull_card =
            Cbat_word.add
              (Cbat_word.sub
                 (Cbat_word.cast Bil.UNSIGNED w1 hi)
                 (Cbat_word.cast Bil.UNSIGNED w1 lo))
              (Cbat_word.one w1) in
          Cbat_word.equal (Cbat_clp.cardinality p) hull_card))

(* Whether one of [p]'s elements is an address whose [bytes]-wide read
   can touch a stored cell on [line]: the read at [x] meets the cell
   hull [cl, ch] iff [x, x+bytes-1] meets [cl, ch] iff [x] lies in the
   (possibly wrapped) [cl-(bytes-1), ch].  The answer is definitive:
   [Pieces.overlap] never reports disjoint for a non-empty element
   intersection, so a piece it clears hides no read the singleton rule
   could drop.

   [has_cell_in] is the cheap necessary prefilter only: a false span
   answer clears every element; a true one hands the decision to the
   per-cell element test.  The cell's stride is not read: the forward
   load consults cells by hull overlap, and narrowing by the grid could
   clear a consulted read. *)
let piece_touches_cell_bounds ?cells (mv : Mem.t) ~(line : Hike_origin.t)
    ~(bytes : int) ~(lo : Cbat_word.t) ~(hi : Cbat_word.t)
    (p : Cbat_clp.t) : bool =
  let w = Cbat_word.bitwidth hi in
  let back = Cbat_word.of_int ~width:w (bytes - 1) in
  let last = Cbat_word.add hi back in
  (* A wrapped read can meet cells on either side of the modulus. *)
  Cbat_word.(<) last hi
  || (Mem.has_cell_in mv ~origin:line ~lo ~hi:last
      && (let qp = Cbat_clp.Pieces.of_progression p in
          let cells =
            match cells with Some c -> Lazy.force c | None -> Mem.cells mv in
          List.exists cells ~f:(fun (k, _) ->
              Hike_origin.equal (Mem.Key.origin k) line
              && (let cl, ch = Mem.Key.hull k in
                  Cbat_word.bitwidth cl <> w
                  || Cbat_word.bitwidth ch <> w
                  || Cbat_clp.Pieces.overlap qp
                       (Cbat_clp.interval ~width:w
                          (Cbat_word.sub cl back) ch)))))

let piece_touches_cell (mv : Mem.t) ~(line : Hike_origin.t) ~(bytes : int)
    (p : Cbat_clp.t) : bool =
  match Cbat_clp.min_elem p, Cbat_clp.max_elem p with
  | Some lo, Some hi -> piece_touches_cell_bounds mv ~line ~bytes ~lo ~hi p
  | _ -> true

(* The read-start ranges of the threaded images that can hold a
   [bytes]-wide read: [img_lo, img_hi-(bytes-1)] — the forward image
   rule requires the whole read inside one image.  Images too short for
   the read drop out once here. *)
let image_read_starts ~(bytes : int) : (Stdlib.Int64.t * Stdlib.Int64.t) list =
  let back = Stdlib.Int64.of_int (bytes - 1) in
  List.filter_map !section_images_ref ~f:(fun { img_lo; img_hi; _ } ->
      if Stdlib.Int64.unsigned_compare (Stdlib.Int64.sub img_hi img_lo) back >= 0
      then Some (img_lo, Stdlib.Int64.sub img_hi back)
      else None)

(* Whether one of [p]'s elements is an address whose [bytes]-wide read
   fits inside one of the [fits] ranges: a dense piece tests the ranges
   directly, a strided piece intersects them exactly.  Images are the
   host's (64-bit) addresses; a narrower address width keeps the sound
   identity. *)
let piece_touches_image_bounds ~(fits : (Stdlib.Int64.t * Stdlib.Int64.t) list)
    ~(dense : bool) ~(lo : Cbat_word.t) ~(hi : Cbat_word.t)
    (p : Cbat_clp.t) : bool =
  let w = Cbat_word.bitwidth hi in
  if dense then
    (match Cbat_word.to_int64_opt lo, Cbat_word.to_int64_opt hi with
     | Some l, Some h ->
       List.exists fits ~f:(fun (fit_lo, fit_hi) ->
           Stdlib.Int64.unsigned_compare l fit_hi <= 0
           && Stdlib.Int64.unsigned_compare fit_lo h <= 0)
     | _ -> true)
  (* Non-64-bit: the int64-based reader cannot decide; sound identity. *)
  else if w <> 64 then true
  else
    let qp = Cbat_clp.Pieces.of_progression p in
    List.exists fits ~f:(fun (fit_lo, fit_hi) ->
        Cbat_clp.Pieces.overlap qp
          (Cbat_clp.interval ~width:w
             (Cbat_word.of_int64 ~width:w fit_lo)
             (Cbat_word.of_int64 ~width:w fit_hi)))

let piece_touches_image ~(bytes : int) (p : Cbat_clp.t) : bool =
  match Cbat_clp.min_elem p, Cbat_clp.max_elem p with
  | Some lo, Some hi ->
    piece_touches_image_bounds ~fits:(image_read_starts ~bytes)
      ~dense:(piece_dense p ~lo ~hi) ~lo ~hi p
  | _ -> true

(* The load's address pre-image: the addresses whose read can produce a
   value in [produced].  Only known memory — a stored cell or a section
   image — excludes an address: a range covering neither reads top and
   stays whole; a covered range is decided in bulk down to its covered
   elements, each read by the forward load and dropped iff its value, on
   the constraint's own origin, misses [produced].  [None] when nothing is
   excluded, or everything is (the leaf rule's identity). *)
let load_address_constraint ?denoted ~(env : AI.t) ~(mem : exp) ~(addr : exp)
    ~(endian : endian) ~(size : Size.t) (produced : wordset) : wordset option =
  let bits = Size.in_bits size in
  let denoted =
    match denoted with Some d -> d | None -> denote_imm_exp addr env in
  match mem, denoted with
  | Bil.Var m, Ok aws
    when bits mod 8 = 0 && WordSet.bitwidth produced = bits
         && not (WordSet.is_top aws || WordSet.is_infinite aws || WordSet.is_bottom aws) -> (
    match Var.typ m with
    | Type.Mem (addr_i, addressable_size) ->
      let mv = AI.find_memory (mem_idx addr_i addressable_size) env m in
      if Mem.is_bottom mv then None
      else
        let nb = bits / 8 in
        (* The threaded images' read-start ranges: constant across this
           constraint's decisions (one read width). *)
        let image_fits = image_read_starts ~bytes:nb in
        (* The memory's cells, materialized at most once per constraint. *)
        let cells = lazy (Mem.cells mv) in
        (* The singleton rule: the address value of the one-element
           piece [p]; a known read whose value, on this constraint's own
           origin, misses [produced], drops its address. *)
        let drops (v : wordset) : bool =
          Option.equal Hike_origin.equal (WordSet.origin v)
            (WordSet.origin produced)
          && Cbat_word.is_zero (WordSet.cardinality (WordSet.meet v produced)) in
        let read_image = image_point_reader ~endian ~bits mv in
        (* An image word's verdict depends on its value alone. *)
        let image_drops : (int64, bool) Hashtbl.t = Hashtbl.create (module Int64) in
        let image_keep (raw : int64) : bool =
          not
            (Hashtbl.find_or_add image_drops raw ~default:(fun () ->
                 drops
                   (WordSet.singleton
                      (Cbat_word.of_word (Word.of_int64 ~width:bits raw))))) in
        let general_keep line (p : Cbat_clp.t) : bool =
          let one =
            match line with
            | Hike_origin.Stack | Hike_origin.Fs ->
              WordSet.set_origin line (WordSet.stack_word (Cbat_clp.Pieces.of_progression p))
            | _ -> WordSet.of_clp (Cbat_clp.Pieces.of_progression p) in
          not (drops (load_value ~addr:one ~endian ~bits mv)) in
        let singleton_keep line (p : Cbat_clp.t) : bool =
          let point =
            match line, Cbat_clp.min_elem p with
            | (Hike_origin.Stack | Hike_origin.Fs), _ | _, None -> None
            | _, Some x when Cbat_word.bitwidth x <> 64 -> None
            | _, Some x ->
              Base.Option.bind (Cbat_word.to_int64_opt x)
                ~f:(read_image ~cell_free:false) in
          match point with
          | Some raw -> image_keep raw
          | None -> general_keep line p in
        (* The read-start ranges a covered element's read can touch, as
           the element-level tests build them: the same-line cell hulls
           each shifted back by the read width (the span prefilter is
           [has_cell_in]), and — on the Abs line — the images' read
           starts.  A cell hull whose width does not match the piece's
           cannot be intersected and keeps its addresses on the identity
           path.

           Each range carries whether its addresses may be kept
           wholesale.  A cell whose own hull is too wide to enumerate
           decides each address on its own read grid, repeated across
           the whole hull; walking that hull would enumerate the grid
           for no more knowledge than keeping it. *)
        let cell_enum_bound = 65536 in
        let covered_ranges (line : Hike_origin.t) ~(lo : Cbat_word.t)
            ~(hi : Cbat_word.t) ~(last : Cbat_word.t) :
            (Cbat_clp.Pieces.t * bool) list =
          let w = Cbat_word.bitwidth hi in
          let back = Cbat_word.of_int ~width:w (nb - 1) in
          let image_ranges =
            match line with
            | Hike_origin.Abs ->
              List.map image_fits ~f:(fun (fit_lo, fit_hi) ->
                  (Cbat_clp.interval ~width:w
                     (Cbat_word.of_int64 ~width:w fit_lo)
                     (Cbat_word.of_int64 ~width:w fit_hi),
                   false))
            | _ -> [] in
          let cell_ranges =
            if Mem.has_cell_in mv ~origin:line ~lo ~hi:last then
              List.filter_map (Lazy.force cells) ~f:(fun (k, _) ->
                  if Hike_origin.equal (Mem.Key.origin k) line then
                    let cl, ch = Mem.Key.hull k in
                    if Cbat_word.bitwidth cl = w && Cbat_word.bitwidth ch = w
                    then
                      let keep_whole =
                        Cbat_word.gt_int
                          (Cbat_word.succ_exact (Cbat_word.sub ch cl))
                          cell_enum_bound in
                      Some (Cbat_clp.interval ~width:w (Cbat_word.sub cl back) ch,
                            keep_whole)
                    else None
                  else None)
            else [] in
          image_ranges @ cell_ranges in
        (* [q] minus one covered run [h] of [q]'s elements: the elements
           below [h]'s minimum and above its maximum.  [h] contains every
           element between its extrema (it is [q]'s grid intersected with
           an address interval, or that intersection hulled), so the
           dropped middle is exactly [h]'s own enumeration and never
           loses an element. *)
        let subtract_run (q : Cbat_clp.t) (h : Cbat_clp.Pieces.t) : Cbat_clp.t list =
          match Cbat_clp.min_elem q, Cbat_clp.Pieces.min_elem h,
                Cbat_clp.Pieces.max_elem h with
          | Some q_lo, Some h_lo, Some h_hi ->
            let left, q =
              if Cbat_word.(<) q_lo h_lo then
                Cbat_clp.split_at_n q (Cbat_word.pred h_lo)
              else (Cbat_clp.bottom (Cbat_clp.bitwidth q), q) in
            let right =
              match Cbat_clp.min_elem q with
              | Some q_lo' when Cbat_word.(<=) q_lo' h_hi ->
                snd (Cbat_clp.split_at_n q h_hi)
              | _ -> q in
            [ left; right ]
          | _ -> [ q ] in
        (* The bulk partition: [hits] are the covered elements (each a
           contiguous run of [p]'s grid), [rest] keeps everything outside
           them wholesale.  Hits from a wholesale range (an oversized
           cell hull) are not enumerated: their elements stay in [rest]
           — keeping is always sound, and walking the hull would
           enumerate its whole read grid.  The other hits are enumerated
           and the singleton rule applies per element; one that exceeds
           [enum_bound] falls back to the [Split] bisection.  A piece
           whose coverage yields no ranges is kept whole ([`Keep`], the
           sound identity). *)
        let enum_bound = 4096 in
        (* The coverage runs as integer progressions (low, step, count,
           span free of stored cells), for 64-bit addresses below 2^61
           off the stack line; [None] sends the partition to the word
           path. *)
        let int_runs line (small : Cbat_clp.Pieces.t list) ~(width : int) :
            (int * int * int * int * bool) list option =
          let limit = Stdlib.Int64.shift_left 1L 61 in
          let small_int w =
            match Cbat_word.to_int64_opt w with
            | Some v when Stdlib.Int64.compare v 0L >= 0
                          && Stdlib.Int64.compare v limit < 0 ->
              Some (Stdlib.Int64.to_int v)
            | _ -> None in
          let run piece =
            match
              Cbat_clp.min_elem piece, Cbat_clp.max_elem piece,
              small_int (Cbat_clp.cardinality piece)
            with
            | Some lo_w, Some hi_w, Some card ->
              (match small_int lo_w, small_int hi_w with
               | Some lo, Some hi ->
                 let step = if card = 1 then 1 else
                     Option.value (small_int (Cbat_clp.step_of piece)) ~default:0 in
                 if step > 0 && lo + (card - 1) * step = hi then
                   let last = Cbat_word.of_int ~width (hi + nb - 1) in
                   Some (lo, step, card, hi,
                         not (Mem.has_cell_in mv ~origin:Hike_origin.Abs
                                ~lo:lo_w ~hi:last))
                 else None
               | _ -> None)
            | _ -> None in
          match line with
          | Hike_origin.Stack | Hike_origin.Fs -> None
          | _ when width <> 64 || bits > 64 -> None
          | _ ->
            let runs =
              List.concat_map small ~f:(fun h ->
                  List.map (Cbat_clp.Pieces.to_list h) ~f:run) in
            if List.for_all runs ~f:Option.is_some then
              Some (List.filter_map runs ~f:Fn.id)
            else None in
        (* The ordered union of the runs' addresses that survive the
           singleton rule, each read once. *)
        let sweep_runs line runs : Cbat_word.t list =
          let runs = Array.of_list runs in
          let k = Array.length runs in
          let idx = Array.create ~len:k 0 in
          let kept = Stdlib.ref [] in
          let continue = Stdlib.ref true in
          while !continue do
            let m = Stdlib.ref Stdlib.max_int in
            for j = 0 to k - 1 do
              let lo, step, card, _, _ = runs.(j) in
              if idx.(j) < card then m := Int.min !m (lo + idx.(j) * step)
            done;
            if !m = Stdlib.max_int then continue := false
            else begin
              let m = !m in
              let free = Stdlib.ref false in
              for j = 0 to k - 1 do
                let lo, step, card, hi, span_free = runs.(j) in
                if span_free && lo <= m && m <= hi then free := true;
                if idx.(j) < card && lo + idx.(j) * step = m then
                  idx.(j) <- idx.(j) + 1
              done;
              let keep =
                match read_image ~cell_free:!free (Stdlib.Int64.of_int m) with
                | Some raw -> image_keep raw
                | None ->
                  general_keep line
                    (Cbat_clp.singleton (Cbat_word.of_int ~width:64 m)) in
              if keep then kept := Cbat_word.of_int ~width:64 m :: !kept
            end
          done;
          List.rev !kept in
        let partition (line : Hike_origin.t) (p : Cbat_clp.t)
            ~(lo : Cbat_word.t) ~(hi : Cbat_word.t) ~(last : Cbat_word.t) =
          let hits =
            List.filter_map (covered_ranges line ~lo ~hi ~last)
              ~f:(fun (r, keep_whole) ->
                let h = Cbat_clp.Pieces.hull_intersection p r in
                if Cbat_clp.Pieces.is_bottom h then None else Some (h, keep_whole)) in
          let small =
            List.filter_map hits ~f:(fun (h, keep_whole) ->
                if keep_whole then None else Some h) in
          match hits with
          | [] -> `Keep
          | _ when
              List.exists small ~f:(fun h ->
                  List.exists (Cbat_clp.Pieces.to_list h) ~f:Cbat_clp.is_infinite
                  || Cbat_word.gt_int (Cbat_clp.Pieces.cardinality h) enum_bound) ->
            `Split
          | _ ->
            let rest =
              List.fold small ~init:[ p ] ~f:(fun qs h ->
                  List.concat_map qs ~f:(fun q ->
                      if Cbat_clp.Pieces.is_bottom (Cbat_clp.Pieces.hull_intersection q h)
                      then [ q ]
                      else subtract_run q h)) in
            let width = Cbat_word.bitwidth hi in
            let kept =
              match int_runs line small ~width with
              | Some runs -> sweep_runs line runs
              | None ->
                (* Coverage ranges may overlap: merge their ordered grids
                   before reading each covered address once. *)
                let covered =
                  List.concat_map small ~f:(fun h ->
                      List.map (Cbat_clp.Pieces.to_list h) ~f:Cbat_clp.iter)
                  |> Cbat_vsa_utils.merge_balanced
                       ~merge:(Cbat_vsa_utils.merge_dedup ~compare:Cbat_word.compare) in
                List.filter covered ~f:(fun x ->
                    singleton_keep line (Cbat_clp.singleton x)) in
            let kept_runs =
              Cbat_clp.Exact.to_pieces (Cbat_clp.Exact.of_sorted_list ~width kept) in
            let parts =
              Cbat_clp.Pieces.merge_progressions
                (List.filter rest ~f:(fun q -> not (Cbat_clp.is_bottom q)))
                kept_runs
              |> List.map ~f:(fun q -> (q, `Keep)) in
            `Parts parts in
        let decide line p =
          match Cbat_clp.min_elem p, Cbat_clp.max_elem p with
          | Some lo, Some hi ->
            let last = Cbat_word.add hi (Cbat_word.of_int ~width:(Cbat_word.bitwidth hi) (nb - 1)) in
            if Cbat_word.(<) last hi then `Keep
            else if
              not
                ((match line with
                  | Hike_origin.Abs ->
                    piece_touches_image_bounds ~fits:image_fits
                      ~dense:(piece_dense p ~lo ~hi) ~lo ~hi p
                  | _ -> false)
                 || piece_touches_cell_bounds ~cells mv ~line ~bytes:nb ~lo ~hi p)
            then `Keep
            else if Cbat_word.is_one (Cbat_clp.cardinality p) then
              (if singleton_keep line p then `Keep else `Drop)
            else partition line p ~lo ~hi ~last
          | _ -> `Keep in
        let kept = WordSet.filter_addresses aws ~decide in
        if WordSet.is_bottom kept || WordSet.equal kept aws then None else Some kept
    | Type.Imm _ | Type.Unk -> None)
  | _ -> None

(* Whether evaluating [e] reads memory (a load, or a memory-valued
   subterm). *)
let rec reads_memory (e : exp) : bool =
  match e with
  | Bil.Var v -> (match Var.typ v with Type.Mem _ -> true | _ -> false)
  | Bil.Int _ -> false
  | Bil.Load _ | Bil.Store _ | Bil.Unknown _ -> true
  | Bil.BinOp (_, a, b) | Bil.Concat (a, b) -> reads_memory a || reads_memory b
  | Bil.UnOp (_, a) | Bil.Cast (_, _, a) | Bil.Extract (_, _, a) -> reads_memory a
  | Bil.Ite (c, t, f) -> reads_memory c || reads_memory t || reads_memory f
  | Bil.Let (_, a, b) -> reads_memory a || reads_memory b

let rec constrain_operands ~(env : AI.t) ?(seed = false)
    ?(cells : cell_env ref = ref no_cells)
    ?(nonneg : exp -> bool = fun _ -> false)
    ~(landmarks : Cbat_landmarks.t)
    (e : exp) (produced : wordset) : AI.t =
  (* The recursive call on a sub-expression, in [env] unless given. *)
  let recur ?(env = env) e produced =
    constrain_operands ~seed ~env ~cells ~nonneg ~landmarks e produced in
  match e with
  | Bil.Var v ->
    if seed then (match Var.typ v with
      | Type.Imm w when w = WordSet.bitwidth produced ->
        ignore (meet_var ~landmarks env v produced);
        AI.add_word env ~key:v ~data:produced
      | _ -> env)
    else meet_var ~landmarks env v produced
  | Bil.Int c ->
    (* The forward rule always produces the same constant: a disjoint
       produced value is the genuinely empty pre-image. *)
    if not (WordSet.backward0 ~value:(Cbat_word.of_word c) ~result:produced)
    then begin
#ifdef VSA_DEBUG
      Format.eprintf "DBG INT-BOTTOM: const=%s produced=%a\n%!"
        (Cbat_word.to_string (Cbat_word.of_word c)) WordSet.pp produced;
#endif
      AI.bottom
    end
    else env
  | (Bil.UnOp (_, a) | Bil.Cast (_, _, a) | Bil.Extract (_, _, a)) ->
    let op = match e with
      | Bil.UnOp (Bil.NOT,_) -> Cbat_preimage.Lnot
      | Bil.UnOp (Bil.NEG,_) -> Cbat_preimage.Neg
      | Bil.Cast (c,n,_) -> Cbat_preimage.Cast (c,n)
      | Bil.Extract (hi,lo,_) -> Cbat_preimage.Extract (Some hi,lo)
      | _ -> assert false in
    (match denote_imm_exp a env with
     | Ok arg ->
       let c = WordSet.backward1 op ~arg ~result:produced in
       (* A rejected value still supplies its excluding boundary to the
          landmark observer; the leaf owns empty-meet delivery. *)
       let c = if WordSet.is_bottom c then
           WordSet.backward1 op ~arg:(WordSet.top (WordSet.bitwidth arg)) ~result:produced
         else c in
       recur a c
     | Error _ -> env)
  | Bil.Concat (a,b) ->
    constrain_binary ~seed ~env ~cells ~nonneg ~landmarks Cbat_preimage.Concat a b produced
  | Bil.Ite (c, t, f) ->
    (* The branches are alternatives: a condition whose denotation names
       one branch constrains that branch; any other condition leaves the
       state unconstrained. *)
    (match denote_imm_exp c env with
     | Ok c_ws when Cbat_word.is_one (WordSet.cardinality c_ws) ->
       if WordSet.elem Cbat_word.b0 c_ws
       then recur f produced
       else recur t produced
     | Ok _ | Error _ -> env)
  | Bil.Let (_, _, body) -> recur body produced
  | Bil.Load (m, a, en, s) ->
    (* An address that reads no memory denotes the same before and after
       the cell step (which only writes the memory), so one denotation
       serves the whole arm. *)
    let denoted = denote_imm_exp a env in
    let stable = not (reads_memory a) in
    let addr_cstr =
      load_address_constraint ~denoted ~env ~mem:m ~addr:a ~endian:en ~size:s
        produced in
    (* The cell fact meets the env's memory and threads to the store
       that wrote it; the entry carries the touched byte range (the
       address denotation expanded by the read size) and the read's
       endianness, so the store match compares the read's whole
       shape. *)
    let env =
      constrain_cell_on_trace ~denoted ~landmarks ~env ~mem:m ~addr:a ~size:s
        ~endian:en produced in
    (match m with
     | Bil.Var mv ->
       (match Var.typ mv, if stable then denoted else denote_imm_exp a env with
        | Type.Mem (ai, asz), Ok aws ->
          let mv_mem = AI.find_memory (mem_idx ai asz) env mv in
          List.iter (backward_cell_keys mv_mem aws ~bytes:(Size.in_bytes s))
            ~f:(fun k ->
               cells := cell_add !cells
                   { pm = mv;
                     prange = Mem.Key.expand k ~bytes:(Size.in_bytes s);
                     pc = produced;
                     pbits = Size.in_bits s;
                     pendian = en })
        | _ -> ())
     | _ -> ());
    Option.value_map addr_cstr ~default:env
      ~f:(fun a' -> recur ~env a a')
  | Bil.Store (m, a, u, en, s) ->
    (* The store consumes every cell entry whose range it
       overwrites: the constraint speaks about the store's data or
       about nothing.  A shape-matching entry (same width, same
       endianness) delivers into the written value, met against the
       stored data's denotation; a shape-mismatched one is dropped —
       the written bytes reassembled under another shape bound no
       value.  The entry exists only for a read that touches one cell
       on every path (S6), so on the paths it speaks about the read
       reads exactly this store's bytes.  See
       docs/adr/0025-the-join-ruling.md. *)
    (match m with
     | Bil.Var mv when not (Core.Map.is_empty !cells) ->
       let ks =
         Base.Result.ok (denote_imm_exp a env)
         |> Base.Option.value_map ~default:[] ~f:bounded_cell_key in
       if List.is_empty ks then begin
         (* An unbounded address may write any cell: nothing crosses. *)
         cells := snd (cell_take !cells mv ~f:(fun _ -> true));
         env
       end
       else begin
         let written =
           List.map ks ~f:(Mem.Key.expand ~bytes:(Size.in_bytes s)) in
         let hit, rest =
           cell_take !cells mv ~f:(fun p ->
               List.exists written ~f:(fun k -> Mem.Key.overlap k p.prange)) in
         cells := rest;
         (* Only a store certain to write exactly the read's bytes
            delivers; a partial or possible overlap just blocks. *)
         let exact (p : cell) =
           match ks with
           | [ k ] when key_is_point k ->
             Mem.Key.compare (Mem.Key.expand k ~bytes:(Size.in_bytes s))
               p.prange = 0
           | _ -> false in
         List.fold hit ~init:env ~f:(fun env p ->
             if exact p
                && p.pbits = Size.in_bits s
                && Bitvector.compare_endian p.pendian en = 0
             then begin
               let data_cstr =
                 Option.value_map (Base.Result.ok (denote_imm_exp u env))
                   ~default:p.pc ~f:(WordSet.meet p.pc) in
               if Cbat_word.is_zero (WordSet.cardinality data_cstr) then env
               else recur u data_cstr
             end
             else env)
       end
     | Bil.Var _ -> env
     | _ ->
       (* A store onto a computed memory may write any cell. *)
       cells := no_cells;
       env)
  | Bil.BinOp (op,a,b) ->
    constrain_binary ~seed ~env ~cells ~nonneg ~landmarks (Cbat_preimage.Op op) a b produced
  | Bil.Unknown _ -> env

(* Numeric inverses join their alternatives before the effectful walk
   delivers either projection. *)
and constrain_binary ~seed ~env ~cells ~nonneg ~landmarks op a b produced =
  match (denote_imm_exp a env, denote_imm_exp b env) with
  | Ok left, Ok right ->
      let signed =
        match op with
        | Cbat_preimage.Op (Bil.SLT | Bil.SLE) -> true
        | _ -> false
      in
      let domain e value =
        let w = WordSet.bitwidth value in
        if signed && nonneg e then
          WordSet.of_clp
            (Cbat_clp.interval ~width:w (Cbat_word.zero w)
               (Cbat_word.pred (Cbat_word.pow2 ~width:w (w - 1))))
        else WordSet.top w
      in
      let left_domain = domain a left and right_domain = domain b right in
      let left = WordSet.meet left left_domain
      and right = WordSet.meet right right_domain in
      let x, y = WordSet.backward2 op ~left ~right ~result:produced in
      let raw e value domain =
        match e with Bil.Int _ -> value | _ -> domain
      in
      let excluded =
        lazy
          (WordSet.backward2 op ~left:(raw a left left_domain)
             ~right:(raw b right right_domain) ~result:produced)
      in
      let x =
        if WordSet.is_bottom x then
          let c =
            fst (WordSet.backward2 op ~left:left_domain ~right ~result:produced)
          in
          if WordSet.is_bottom c then fst (Lazy.force excluded) else c
        else x
      in
      let y =
        if WordSet.is_bottom y then
          let c =
            snd
              (WordSet.backward2 op ~left ~right:right_domain ~result:produced)
          in
          if WordSet.is_bottom c then snd (Lazy.force excluded) else c
        else y
      in
      (* A comparison is one inequality whatever the iterate gives each
         operand: the landmarks its operands record are named by it. *)
      let guarded side c f =
        match op with
        | Cbat_preimage.Op
            ((Bil.EQ | Bil.NEQ | Bil.LT | Bil.LE | Bil.SLT | Bil.SLE) as cmp) ->
          Cbat_landmarks.with_guard landmarks
            (fun () ->
               Format.asprintf "%s %c %a" (Exp.to_string (Bil.BinOp (cmp, a, b)))
                 side WordSet.pp c)
            f
        | _ -> f ()
      in
      let deliver side env e c =
        match e with
        | Bil.Int k ->
          (* A constant operand the projection excludes cannot produce
             the result. *)
          if (not seed)
             && not (WordSet.backward0 ~value:(Cbat_word.of_word k) ~result:c)
          then AI.bottom
          else env
        | Bil.Let _ -> env
        | _ ->
          guarded side produced (fun () ->
              constrain_operands ~seed ~env ~cells ~nonneg ~landmarks e c)
      in
      let env = deliver 'L' env a x in
      deliver 'R' env b y
  | _ -> env

(* The load's cell fact meets the env's memory at the denoted address:
   stack-symbolic addresses key by segment offsets, foreign by their
   concrete hulls; identity on doubt.  Each fan-out key runs the one
   leaf rule; the write-back is the piecewise meet whose empty piece
   keeps its cell. *)
and constrain_cell_on_trace ?denoted ~(landmarks : Cbat_landmarks.t) ~(env : AI.t) ~(mem : exp)
    ~(addr : exp) ~(size : Size.t) ~(endian : endian) (produced : wordset) : AI.t =
  match mem with
  | Bil.Var m ->
    (match Var.typ m with
     | Type.Mem (addr_i, addressable_size) ->
       let k = mem_idx addr_i addressable_size in
       (match
          (match denoted with Some d -> d | None -> denote_imm_exp addr env)
        with
        | Error _ -> env
        | Ok addr_ws ->
          let res_size = Size.in_bits size in
          (* The cell world is byte-addressed: a sub-byte read's
             meet is unrepresentable — the identity (no meet) keeps
             the cell's pre. *)
          if res_size mod 8 <> 0 then env
          else if WordSet.bitwidth produced <> res_size then env
          else
            let mv = AI.find_memory k env m in
            (match backward_cell_keys mv addr_ws ~bytes:(Size.in_bytes size) with
             | [] -> env
             | keys ->
               List.fold keys ~init:env ~f:(fun env key ->
                   let cur = Mem.Val.data (Mem.find (res_size, endian) mv key) in
#ifdef VSA_DEBUG
                   let res = WordSet.meet cur produced in
                   if not (WordSet.equal res cur) then
                     cell_meet_diff
                       ~ckey:(Sexp.to_string (Mem.Key.sexp_of_t key))
                       ~pre:cur ~cstr:produced ~res;
                   Format.eprintf "DBG MEET-CELL: meet %a into key %s\n%!"
                     WordSet.pp produced
                     (Sexp.to_string (Mem.Key.sexp_of_t key));
#endif
                     leaf_meet ~landmarks
                     ~key:(Cbat_landmarks.Cell (Mem.Key.cell_key key))
                     ~cur ~meet:WordSet.meet
                     ~write:(fun mval mem ->
                         let mvk = AI.find_memory k mem m in
                         AI.add_memory mem ~key:m
                           ~data:(Mem.meet_range_keep mvk ~key
                                    ~data:(Mem.Val.create mval endian)))
                     produced env)))
     | Type.Imm _ | Type.Unk -> env)
  | _ -> env

(* The edge step: the graph's completed cond constrained TRUE — the {1}
   lives here only. *)
let constrain_edge ~(env : AI.t) ~(landmarks : Cbat_landmarks.t)
    (cond : exp) : AI.t =
  constrain_operands ~landmarks ~env cond (WordSet.singleton Cbat_word.b1)

(* A produced-width dummy for mem defs: their constraint derivation reads
   the cells, never the width. *)
let undefined_width = WordSet.bottom 8

let strictly_precedes (narrow : wordset) (wide : wordset) : bool =
  WordSet.precedes narrow wide && not (WordSet.equal narrow wide)

(* The replay's write sites: a def's output fact, a block input fact. *)
type write_site = Output_write | Input_write

(* What the backward pass learned, by position: the constraint each
   def's output satisfies on the edge, and the cells each def's loads
   read under the edge.  The forward replay meets them in place. *)
type walk_state = {
  words : word_env ref;
  cells : cell_env ref;
  outputs : wordset Tid.Map.t ref;
  reads : cell list Tid.Map.t ref;
  landmarks : Cbat_landmarks.t;
}

(* The walk's delivery locus: what the walk's facts become.  ONE walk
   serves both callers — the state-writer records every fact and
   replays the block forward from the refined inputs, so a fact reaches
   the edge exactly as far as the block's own transfer carries it; the
   observer keeps nothing: its walk exists for the leaf meets the seeds
   fire on the way, so its constraints apply as given and no path is
   claimed dead. *)
type locus = {
  at_def : post:(unit -> wordset) -> cstr:wordset -> wordset option;
  invert_mem : cell_env -> bool;
  record_output : walk_state -> def term -> wordset -> unit;
  record_reads :
    walk_state -> def term -> before:cell_env -> after:cell_env -> unit;
  harvest : walk_state -> base:AI.t -> env:AI.t -> rhs:exp -> unit;
  replay :
    walk_state -> entry:AI.t -> prefix:(def term * AI.t * AI.t) list ->
    AI.t -> AI.t;
}

(* A word fact through the one leaf rule's write discipline: an empty
   meet keeps the state, an equal one writes nothing. *)
let meet_word ~(on_write : unit -> unit) (st : AI.t) (v : var) (c : wordset) :
    AI.t =
  match Var.typ v with
  | Type.Imm w when WordSet.bitwidth c = w ->
    let cur = AI.find_word w st v in
    let m = WordSet.meet cur c in
    if (not (Cbat_word.is_zero (WordSet.cardinality m)))
       && strictly_precedes m cur
    then begin on_write (); AI.add_word st ~key:v ~data:m end
    else st
  | _ -> st

(* The owed word constraints met into a state. *)
let meet_owed ~(on_write : unit -> unit) (st : AI.t) (we : word_env) : AI.t =
  Core.Map.fold we ~init:st ~f:(fun ~key:_ ~data:(v, c) acc ->
      meet_word ~on_write acc v c)

(* A cell fact: the read's range meets the memory it names. *)
let meet_cell ~(landmarks : Cbat_landmarks.t option) (st : AI.t) (c : cell) :
    AI.t =
  match Var.typ c.pm with
  | Type.Mem (ai, asz) ->
    let k = mem_idx ai asz in
    let mv = AI.find_memory k st c.pm in
    let cur = Mem.Val.data (Mem.find (c.pbits, c.pendian) mv c.prange) in
    let write mval st =
      AI.add_memory st ~key:c.pm
        ~data:(Mem.meet_range_keep (AI.find_memory k st c.pm) ~key:c.prange
                 ~data:(Mem.Val.create mval c.pendian)) in
    (match landmarks with
     | Some landmarks ->
       leaf_meet ~landmarks
         ~key:(Cbat_landmarks.Cell (Mem.Key.cell_key c.prange))
         ~cur ~meet:WordSet.meet ~write c.pc st
     | None ->
       if WordSet.bitwidth cur <> WordSet.bitwidth c.pc then st
       else
         let m = WordSet.meet cur c.pc in
         if Cbat_word.is_zero (WordSet.cardinality m)
            || not (strictly_precedes m cur) then st
         else write m st)
  | _ -> st

(* The state-writer: the edge state is the block replayed forward from
   its refined inputs, each def's facts met where they hold.  [on_write]
   names each actual write — an output fact at its def, an input fact at
   the entry; a fact equal to the replayed value writes nothing. *)
let writer_locus ~(on_write : write_site -> unit) : locus =
  let at_def ~post ~cstr =
    let m = WordSet.meet cstr (post ()) in
    if Cbat_word.is_zero (WordSet.cardinality m) then None else Some m
  in
  let invert_mem (ce : cell_env) = not (Core.Map.is_empty ce) in
  let record_output (st : walk_state) (d : def term) (c : wordset) =
    st.outputs := Core.Map.set !(st.outputs) ~key:(Term.tid d) ~data:c
  in
  let record_reads (st : walk_state) (d : def term) ~(before : cell_env)
      ~(after : cell_env) =
    (* The cells this def's loads pushed. *)
    let ps = cells_pushed ~before ~after in
    if not (List.is_empty ps) then
      st.reads := Core.Map.update !(st.reads) (Term.tid d)
          ~f:(fun old -> ps @ Option.value old ~default:[])
  in
  let harvest (st : walk_state) ~(base : AI.t) ~(env : AI.t) ~(rhs : exp) =
    Core.Set.fold (Exp.free_vars rhs) ~init:() ~f:(fun () v ->
        match Var.typ v with
        | Type.Imm w ->
          let before = AI.find_word w base v in
          let after = AI.find_word w env v in
          if (not (WordSet.is_bottom after)) && strictly_precedes after before
          then st.words := word_set !(st.words) v after
        | _ -> ())
  in
  let replay (st : walk_state) ~(entry : AI.t)
      ~(prefix : (def term * AI.t * AI.t) list) (_edge : AI.t) =
    (* What no def consumed holds at the block's inputs. *)
    let inputs =
      meet_owed ~on_write:(fun () -> on_write Input_write) entry !(st.words) in
    let inputs =
      cells_fold !(st.cells) ~init:inputs ~f:(fun acc p ->
#ifdef VSA_DEBUG
          Cbat_attr_census.bump "carry.cell.crossed";
#endif
          meet_cell ~landmarks:(Some st.landmarks) acc p)
    in
    (* A def entered in its cached pre-state keeps the cached post; the
       first state a meet changes is denoted afresh from there on. *)
    List.fold_right prefix ~init:inputs ~f:(fun (d, pre, post) acc ->
        let acc =
          List.fold (Core.Map.find_multi !(st.reads) (Term.tid d)) ~init:acc
            ~f:(meet_cell ~landmarks:None) in
        let acc = if phys_equal acc pre then post else denote_def d acc in
        match Core.Map.find !(st.outputs) (Term.tid d) with
        | Some c ->
          meet_word ~on_write:(fun () -> on_write Output_write) acc (Def.lhs d) c
        | None -> acc)
  in
  { at_def; invert_mem; record_output; record_reads; harvest; replay }

(* The observer: the walk's only product is the acquisitions. *)
let observer_locus : locus =
  { at_def = (fun ~post:_ ~cstr -> Some cstr);
    invert_mem = (fun _ -> false);
    record_output = (fun _ _ _ -> ());
    record_reads = (fun _ _ ~before:_ ~after:_ -> ());
    harvest = (fun _ ~base:_ ~env:_ ~rhs:_ -> ());
    replay = (fun _ ~entry:_ ~prefix:_ edge -> edge) }

(* A block's def chain with its pre/post states, positionally, in
   reverse def order.  It depends only on (block, entry state): the
   solve ctx caches the last denotation physically. *)
let cached_prefix
    (cache : (AI.t * (def term * AI.t * AI.t) list) Tid.Map.t ref option)
    (blk : blk term) (entry : AI.t) : (def term * AI.t * AI.t) list =
  let compute () =
    Term.enum def_t blk
    |> Seq.fold ~init:(entry, [])
      ~f:(fun (st, acc) d ->
          let post = denote_def d st in
          (post, (d, st, post) :: acc))
    |> snd
  in
  match cache with
  | Some c ->
    (match Core.Map.find !c (Term.tid blk) with
     | Some (e0, pref) when phys_equal e0 entry -> pref
     | _ ->
       let pref = compute () in
       c := Core.Map.set !c ~key:(Term.tid blk) ~data:(entry, pref);
       pref)
  | None -> compute ()

(* The block's postcondition from the same fold that fills the prefix
   cache, so the guard walk does not denote the chain again. *)
let denote_defs_cached
    (cache : (AI.t * (def term * AI.t * AI.t) list) Tid.Map.t ref)
    (blk : blk term) (entry : AI.t) : AI.t =
  match cached_prefix (Some cache) blk entry with
  | [] -> entry
  | (_, _, post) :: _ -> post

let walk ~(locus : locus)
    ?(cache : (AI.t * (def term * AI.t * AI.t) list) Tid.Map.t ref option)
    ~(entry : AI.t)
    ~(landmarks : Cbat_landmarks.t)
    ~(witness : env:AI.t -> exp -> bool)
    ~(seeds : Var.Set.t)
    (env : AI.t) (blk : blk term) : AI.t =
  (* The walked block's IN state, handed in by the caller — no
     solution lookup, no snapshot copy. *)
  let blk_state = entry in
  let prefixed = cached_prefix cache blk blk_state in
  (* The seeds are the word env's entries (each seed's constraint is
     the edge state's own value for the var); the loads push the cells. *)
  let words =
    ref (Core.Set.fold seeds ~init:(Var.Map.empty : word_env)
           ~f:(fun acc v ->
               match Var.typ v with
               | Type.Imm w -> word_set acc v (AI.find_word w env v)
               | _ -> acc)) in
  let cells = ref no_cells in
  let st = { words; cells; outputs = ref Tid.Map.empty;
             reads = ref Tid.Map.empty; landmarks } in
  (* The def's own pre-state with the owed word constraints met in. *)
  let invert_def (d : def term) (pre : AI.t) (cstr' : wordset) =
    let ce = meet_owed ~on_write:ignore pre !words in
    let before = !cells in
    let env' =
      constrain_operands ~env:ce ~cells ~landmarks
        ~nonneg:(fun e -> witness ~env:ce e)
        (Def.rhs d) cstr'
    in
    (* The cells this def's loads read hold the read constraint here. *)
    locus.record_reads st d ~before ~after:!cells;
    locus.harvest st ~base:ce ~env:env' ~rhs:(Def.rhs d);
    not (AI.equal env' AI.bottom)
  in
  let walk_word_def (d, pre, post) =
    let v = Def.lhs d in
    match Var.typ v with
    | Type.Imm w ->
      (match word_find !words v with
       | Some cstr ->
         (* The def consumes its var's constraint, whatever it says. *)
         words := Core.Map.remove !words (Var.base v);
         (match locus.at_def ~post:(fun () -> AI.find_word w post v) ~cstr with
          | None ->
            (* The produced value cannot satisfy the constraint: no
               state reaches the edge. *)
            false
          | Some cstr' ->
            locus.record_output st d cstr';
            invert_def d pre cstr')
       | None -> true)
    | Type.Mem _ ->
      (* Driven by the cells the loads pushed. *)
      not (locus.invert_mem !cells) || invert_def d pre undefined_width
    | Type.Unk -> true
  in
  (* A def with no state behind it ends the walk: the edge is bottom. *)
  if List.for_all prefixed ~f:walk_word_def
  then locus.replay st ~entry:blk_state ~prefix:prefixed env
  else AI.bottom

(* The walk's seeds: the cond's own constrained vars — every free var
   the guard bounds.  A seed's constraint is the state's own value for
   the var, so the var names the delivery and the walk reads the value
   from the state it walks. *)
let cond_seeds ~(env : AI.t) (cond : exp) : Var.Set.t =
  Core.Set.fold (Exp.free_vars cond) ~init:Var.Set.empty ~f:(fun acc v ->
      match Var.typ v with
      | Type.Imm w ->
        let after = AI.find_word w env v in
        if (not (WordSet.is_bottom after))
           && (not (WordSet.is_top after))
           && not (WordSet.is_infinite after)
        then Core.Set.add acc (Var.base v)
        else acc
      | _ -> acc)

(* The guard names the landmarks its walk records: a constraint carried
   back through the block's defs still measures the edge's own
   inequality, however the iterate moves the bound it arrives with. *)
let rooted ~(landmarks : Cbat_landmarks.t) (cond : exp) (f : unit -> 'a) : 'a =
  Cbat_landmarks.with_guard landmarks
    (fun () -> "edge " ^ Exp.to_string cond) f

(* The refinement walk (the state-writer locus): the constraint meets
   the produced values (the producer subtraction). *)
let walk_block ?(on_write : write_site -> unit = ignore)
    ~(rctx : Cbat_runctx.refine_ctx) ~entry ~landmarks ~witness
    ~seeds env blk =
  walk ~locus:(writer_locus ~on_write)
    ~cache:rctx.Cbat_runctx.rc_prefix ~entry ~landmarks
    ~witness ~seeds env blk

(* The deep walk: the guard block's defs backwards; leftover
   constraints and cell meets flow into the returned edge env. *)
let refine_edge ?(on_write : write_site -> unit = ignore)
    ~(entry : AI.t)
    ~(rctx : Cbat_runctx.refine_ctx)
    ~(seeds : Var.Set.t)
    (env : AI.t) (blk : blk term) : AI.t =
  Stages.incr_walk ();
  walk_block ~on_write ~rctx ~entry ~landmarks:rctx.rc_landmarks
    ~witness:rctx.rc_nonneg ~seeds env blk

(* The disabled continuation observed through the same rules, the
   result DISCARDED: every empty meet records the excluded boundary +
   distance as the enclosing WTO cycle's widening landmark (words and
   memory cells alike). *)
let acquire_unsat ~(entry : AI.t) ~(landmarks : Cbat_landmarks.t)
    ~(cache : (AI.t * (def term * AI.t * AI.t) list) Tid.Map.t ref)
    ~(witness : env:AI.t -> exp -> bool)
    (env : AI.t) (blk : blk term) (disabled : exp) : unit =
  (* Outside a cycle no observation records, so the walk has no effect. *)
  if Cbat_landmarks.in_cycle landmarks then rooted ~landmarks disabled (fun () -> begin
    (* The observer seeds the requested facts even when the live state
       excludes them. This temporary environment never enters the solve. *)
    let constrained = constrain_operands ~seed:true ~env ~landmarks disabled
        (WordSet.singleton Cbat_word.b1) in
    if not (AI.equal constrained AI.bottom) then begin
      let seeds = cond_seeds ~env:constrained disabled in
      (* Without seeds the observer, which never inverts memory defs,
         reaches no leaf meet: skip the walk and its prefix replay. *)
      if not (Core.Set.is_empty seeds) then
        ignore
          (walk ~locus:observer_locus ~cache ~entry ~landmarks ~witness ~seeds
             constrained blk)
    end
  end)

let refine_edge_inline
    ~(entry : AI.t)
    ~(rctx : Cbat_runctx.refine_ctx)
    ~(discarded : bool)
    (b : blk term) (env : AI.t) (acc_cond : exp)
    : AI.t =
  let env_in = env in
  let landmarks = rctx.rc_landmarks in
  let env = rooted ~landmarks acc_cond (fun () ->
      constrain_edge ~env ~landmarks acc_cond) in
  (* No constraint derived: nothing to deliver. *)
  if discarded then env_in
  else if AI.equal env AI.bottom then env
  else
    let seeds = cond_seeds ~env acc_cond in
    if Core.Set.is_empty seeds then env
    else
      Stages.time `Walk (fun () ->
          rooted ~landmarks acc_cond (fun () ->
              refine_edge ~entry ~rctx ~seeds env b))
