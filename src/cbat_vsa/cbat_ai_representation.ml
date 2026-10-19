(* ************************************************************************* *)
(*  *)
(* Copyright (C) Draper Laboratory. Licensed under project LICENSE. *)
(*  *)
(* This file is provided under the license found in the LICENSE file in *)
(* the top-level directory of this project. *)
(*  *)
(* This work is funded in part by ONR/NAWC Contract N6833518C0107. Its *)
(* content does not necessarily reflect the position or policy of the US *)
(* Government and no official endorsement should be inferred. *)
(*  *)
(* ************************************************************************* *)

open !Core
module Abi = Hike_abi
include Bap.Std
include Cbat_vsa_utils
module MapLattice = Cbat_map_lattice
module Mem = Cbat_ai_memmap
module WordSet = Cbat_clp_set_composite

(* Abstract state: words, memories.  Stack provenance is the WORD value
   itself — the entry RSP's word is seeded with the symbolic segment
   base and SP-derived addresses stay [StackOff] through arithmetic,
   memory round-trips, and refinement. *)

type wordset = WordSet.t [@@deriving bin_io, sexp, compare]

(* The frame's escape set: the carried set K of the call-escape design
   (T36 D5/D6) in its first form.  [Whole_frame] says a stack address
   may be held where a callee reaches it (a call argument, or a store
   outside the sub's own frame below entry), so no stack cell survives a
   call.  It joins upward and never returns to [Contained] within a sub;
   a region set grows from [Whole_frame] without replacing this field. *)
type escape = Contained | Whole_frame
[@@deriving bin_io, sexp, compare]

let join_escape (a : escape) (b : escape) : escape =
  match a, b with
  | Contained, Contained -> Contained
  | _ -> Whole_frame

let precedes_escape (a : escape) (b : escape) : bool =
  match a, b with
  | Whole_frame, Contained -> false
  | _ -> true

(* Env keys are the vars' program-wide ids (Cbat_var_id): the maps
   compare ints, so a lookup never walks variable identifiers. *)
module SlotKey = struct
  type t = int [@@deriving bin_io, compare, sexp]
  let pp = Int.pp
end

module MemEnv = MapLattice.Make_indexed_val(SlotKey)(Mem)
module WordEnv = MapLattice.Make_indexed_val(SlotKey)(WordSet)

(* A slice is a fact about the bit range [lo..hi] of a variable's current
   value.  Its key packs the owner's id above the range; a missing key
   reads top.  Redefining the owner discards its slices. *)
module SliceEnv = MapLattice.Make_indexed_val(SlotKey)(WordSet)

let slice_limit = 256

let slice_valid ~hi ~lo = lo >= 0 && lo <= hi && hi < slice_limit

let slice_key (owner : int) ~(hi : int) ~(lo : int) : int =
  (owner lsl 16) lor (hi lsl 8) lor lo

let slice_owner (k : int) : int = k lsr 16
let slice_hi (k : int) : int = (k lsr 8) land 0xff
let slice_lo (k : int) : int = k land 0xff

(* Each SSA value has one cell in the sub.  A block's env holds its
   incoming phi values and its own memory; the definitions' values live
   in the cells.  Edge refinements are transient overrides. *)
type scalar_store = {
  definitions : int Int.Map.t;
  scopes : Int.Set.t Tid.Map.t;
  values : wordset array;
} [@@deriving bin_io, sexp, compare]

type scalar_view = {
  store : scalar_store;
  block : tid;
} [@@deriving bin_io, sexp, compare]

type t = {
  memories : MemEnv.t;
  words : WordEnv.t;
  slices : SliceEnv.t;
  escaped : escape;
  scalar : scalar_view option;
} [@@deriving bin_io, sexp, compare]

(* The escape set is a path fact that only a call or a store raises, so
   [top], the entry state's base, starts [Contained] like [bottom]. *)
let top : t =
  { memories = MemEnv.top;
    words = WordEnv.top;
    slices = SliceEnv.top;
    escaped = Contained;
    scalar = None;
  }
let bottom : t =
  { memories = MemEnv.bottom;
    words = WordEnv.bottom;
    slices = SliceEnv.bottom;
    escaped = Contained;
    scalar = None;
  }

let scalar_slot v k =
  Map.find v.store.definitions k

(* The cell's value: the definition's own fact, shared by every state of
   the sub.  A var with no cell has none. *)
let cell_word v k =
  match scalar_slot v k with
  | None -> None
  | Some slot -> Some (Array.get v.store.values slot)

(* The value of a var in this state: the env's own binding (an incoming
   phi value) when it has one, else the definition's cell. *)
let effective_word (width : int) (e : t) (key : int) : wordset =
  match e.scalar with
  | None -> WordEnv.find width e.words key
  | Some view ->
    (match WordEnv.find_opt width e.words key with
     | Some value -> value
     | None ->
       (match cell_word view key with
        | Some value -> value
        | None -> WordSet.top width))

let equal (e1 : t) e2 : bool =
  phys_equal e1 e2 ||
  (MemEnv.equal e1.memories e2.memories &&
   compare_escape e1.escaped e2.escaped = 0 &&
   WordEnv.equal e1.words e2.words && SliceEnv.equal e1.slices e2.slices)

let equal_slices_top (s : SliceEnv.t) : bool = SliceEnv.equal s SliceEnv.top

let frame_escaped (e : t) : bool =
  match e.escaped with Contained -> false | Whole_frame -> true

let escape_frame (e : t) : t =
  match e.escaped with
  | Whole_frame -> e
  | Contained -> { e with escaped = Whole_frame }

(* Unchanged memory keeps its state record physically shared. *)
let add_memory (e : t) ~(key : var) ~(data : Mem.t) : t =
  let memories = MemEnv.add e.memories ~key:(Cbat_var_id.intern key) ~data in
  if phys_equal memories e.memories then e else { e with memories }

(* The owner's slices describe its previous value: a redefinition
   discards them, whether or not the word changed. *)
let drop_slices (e : t) ~(owner : int) : t =
  let slices =
    SliceEnv.filter_keys e.slices ~f:(fun k -> slice_owner k <> owner) in
  if phys_equal slices e.slices then e else { e with slices }

(* A narrowed word is still described by its slices: they stay. *)
let refine_word (e : t) ~(key : var) ~(data : wordset) : t =
  let key = Cbat_var_id.intern key in
  let width = WordSet.bitwidth data in
  if WordSet.equal (effective_word width e key) data then e
  else
    let words = WordEnv.add e.words ~key ~data in
    if phys_equal words e.words then e else { e with words }

(* The env holds its incoming phi values; a definition of this block
   binds its cell, not the env.  The cell is the sub's current value of
   that variable, exactly as a register is. *)
let add_word (e : t) ~(key : var) ~(data : wordset) : t =
  let owner = Cbat_var_id.intern key in
  match e.scalar with
  | Some v when Set.mem (Map.find_exn v.store.scopes v.block) owner ->
    let e = drop_slices e ~owner in
    (match Map.find v.store.definitions owner with
     | Some slot -> v.store.values.(slot) <- data
     | None -> ());
    e
  | _ -> refine_word (drop_slices e ~owner) ~key ~data

let find_slice (env : t) (v : var) ~(hi : int) ~(lo : int) : wordset =
  if not (slice_valid ~hi ~lo) then WordSet.top 1
  else
    SliceEnv.find (hi - lo + 1) env.slices
      (slice_key (Cbat_var_id.intern v) ~hi ~lo)

let add_slice (e : t) (v : var) ~(hi : int) ~(lo : int) ~(data : wordset) : t =
  if not (slice_valid ~hi ~lo && WordSet.bitwidth data = hi - lo + 1) then e
  else
    let slices =
      SliceEnv.add e.slices
        ~key:(slice_key (Cbat_var_id.intern v) ~hi ~lo) ~data in
    if phys_equal slices e.slices then e else { e with slices }

(* Identity phi operands carry the same bit-range facts under a new name.
   Read them from the incoming state before any phi lhs is overwritten. *)
let copy_slices ~from ~source ~target e =
  let owner = Cbat_var_id.intern source in
  SliceEnv.fold from.slices ~init:e ~f:(fun ~key ~data e ->
      if slice_owner key = owner then
        add_slice e target ~hi:(slice_hi key) ~lo:(slice_lo key) ~data
      else e)

(* The slices of [from] met into [e]'s: a conflicting pair is kept
   apart rather than read as an unreachable state. *)
let carry_slices ~(from : t) (e : t) : t =
  let slices = from.slices in
  if equal_slices_top slices || SliceEnv.equal slices SliceEnv.bottom then e
  else
    let result = SliceEnv.fold slices ~init:(Some e) ~f:(fun ~key ~data acc ->
        Option.bind acc ~f:(fun e ->
            let v = Cbat_var_id.var_of (slice_owner key) in
            let hi = slice_hi key and lo = slice_lo key in
            let old = find_slice e v ~hi ~lo in
            let data = WordSet.meet old data in
            if WordSet.is_bottom data then None
            else Some (if WordSet.equal old data then e else add_slice e v ~hi ~lo ~data))) in
    Option.value result ~default:e

let find_word (i : WordSet.idx) (env : t) (v : var) : wordset =
  effective_word i env (Cbat_var_id.intern v)

let find_memory (i : Mem.idx) (env : t) (v : var) : Mem.t =
  MemEnv.find i env.memories (Cbat_var_id.intern v)

let create_scalars ~variables ~blocks ~seed =
  let next = ref 0 and values = ref [] in
  let allocate value =
    let slot = !next in
    incr next;
    values := value :: !values;
    slot in
  let width v = match Var.typ v with Type.Imm w -> w | _ -> assert false in
  let initial v =
    match seed.scalar with
    | None -> find_word (width v) seed v
    | Some view ->
      Option.value_map (Map.find view.store.definitions (Cbat_var_id.intern v))
        ~default:(WordSet.top (width v)) ~f:(Array.get view.store.values) in
  let definitions = List.fold variables ~init:Int.Map.empty ~f:(fun slots v ->
      Map.set slots ~key:(Cbat_var_id.intern v) ~data:(allocate (initial v))) in
  let scopes = List.fold blocks ~init:Tid.Map.empty
      ~f:(fun scopes (block, locals) ->
          Map.set scopes ~key:block ~data:(Cbat_var_id.intern_set locals)) in
  { definitions; scopes; values = Array.of_list (List.rev !values) }

(* The edge's own bindings: the destination's incoming phi values, read
   from this state's own bindings or from the definitions' cells.  No
   dead scalar binding enters the destination's env.  Existing bindings
   are filtered first; only a kept key with no surviving binding falls
   back to its cell. *)
let project ~keep ~block e =
  if equal e bottom then bottom else
  let words = WordEnv.filter_keys e.words ~f:(fun k -> Set.mem keep k) in
  let words = Set.fold keep ~init:words ~f:(fun words key ->
      match WordEnv.find_opt 0 words key with
      | Some data ->
        (* Re-add through the lattice so a stored top is dropped. *)
        WordEnv.add words ~key ~data
      | None ->
        let v = Cbat_var_id.var_of key in
        match Var.typ v with
        | Type.Imm w -> WordEnv.add words ~key ~data:(find_word w e v)
        | _ -> words) in
  let slices =
    SliceEnv.filter_keys e.slices ~f:(fun k -> Set.mem keep (slice_owner k)) in
  { e with words; slices;
           scalar = (match e.scalar with
             | Some v -> Some { v with block }
             | None -> None) }

(* The block's env keeps its own incoming phi values; the definitions'
   values live in the cells. *)
let enter_block store block e =
  if equal e bottom then bottom else
  { e with scalar = Some { store; block } }

(* The env carries only incoming phi values and memory; a def's cell owns
   its value.  Drop block-local bindings a pre-state may have supplied, so
   they cannot shadow a cell. *)
let scalar_snapshot e =
  match e.scalar with
  | None -> e
  | Some v ->
    let locals = Map.find_exn v.store.scopes v.block in
    let words =
      WordEnv.filter_keys e.words ~f:(fun k -> not (Set.mem locals k)) in
    let slices =
      SliceEnv.filter_keys e.slices
        ~f:(fun k -> not (Set.mem locals (slice_owner k))) in
    if phys_equal words e.words && phys_equal slices e.slices then e
    else { e with words; slices }

(* An SSA version is a single-definition value, never an ABI lane. *)
let versioned (k : int) : bool = Var.index (Cbat_var_id.var_of k) > 0

(* Bindings print by variable, not by id. *)
let pp_words ppf (m : WordEnv.t) =
  WordEnv.fold m ~init:() ~f:(fun ~key ~data () ->
      Format.fprintf ppf "@[<hov 1>[%a@ -> %a]@]@ "
        Var.pp (Cbat_var_id.var_of key) WordSet.pp data)

let pp_memories ppf (m : MemEnv.t) =
  MemEnv.fold m ~init:() ~f:(fun ~key ~data () ->
      Format.fprintf ppf "@[<hov 1>[%a@ -> %a]@]@ "
        Var.pp (Cbat_var_id.var_of key) Mem.pp data)

let pp ppf (e : t) =
  if equal e bottom then
    Format.fprintf ppf "unreachable"
  else if equal e top then
    Format.fprintf ppf "unknown"
  else begin
    Format.fprintf ppf "@[@[<2>Immediate Variables:@ @[<2>{@ %a}@]@]@ "
      pp_words e.words;
    Format.fprintf ppf "@[<2>Memory:@ @[<2>{@ %a}@]@]@]"
      pp_memories e.memories
  end

(* The join's result record is the first operand itself when both
   component maps come back physically unchanged.  The cell table rides
   along: the definitions' values are the sub's, not the state's. *)
let rebuilt (e1 : t) ~(escaped : escape) memories words slices : t =
  if phys_equal memories e1.memories && phys_equal words e1.words
     && phys_equal slices e1.slices
     && compare_escape escaped e1.escaped = 0 then e1
  else { e1 with memories; words; slices; escaped }

let join (e1 : t) (e2 : t) : t =
  if phys_equal e1 e2 || phys_equal e2 bottom then e1
  else if phys_equal e1 bottom then e2
  else
  rebuilt e1 ~escaped:(join_escape e1.escaped e2.escaped)
    (MemEnv.join e1.memories e2.memories)
    (WordEnv.join e1.words e2.words)
    (SliceEnv.join e1.slices e2.slices)

let widen_join (e1 : t) (e2 : t) : t =
  rebuilt e1 ~escaped:(join_escape e1.escaped e2.escaped)
    (MemEnv.widen_join e1.memories e2.memories)
    (WordEnv.widen_join e1.words e2.words)
    (SliceEnv.widen_join e1.slices e2.slices)



(* The one consumption rule, per key.  The head's arm decides the
   round: [Zero] advances every key's own row and joins — the non-
   widening arm, no extrapolation on it; [Finite n]/[Inf] let a key
   read its own row first.  A key whose own arm is [Finite n_own]
   extrapolates by [n_own] (the head's [n] otherwise) and spends its
   own row on the translated answer.  A key whose own arm is [Zero]
   advances and takes its kind's Zero action — [zero_action], the
   word's tuned join vs the cell's loop-stabilizing widen. *)
let consume_arm ~(head : Tid.t) ~(landmarks : Cbat_landmarks.t)
    ~(key : Cbat_landmarks.key) ~(head_arm : Cbat_landmarks.arm)
    ~(extrapolate : steps:int -> ('v * bool))
    ~(zero_action : unit -> 'v) ~(widen : unit -> 'v) : 'v =
  let extr n =
    let v, translated = extrapolate ~steps:n in
    if translated then Cbat_landmarks.clear_key landmarks head key;
    v
  in
  (match Cbat_landmarks.steps landmarks head key with
   | Cbat_landmarks.Finite n -> extr n
   | Cbat_landmarks.Zero -> Cbat_landmarks.advance landmarks head key; zero_action ()
   | Cbat_landmarks.Inf ->
     (* A key with no own answer plain-widens whatever the head's steps:
        a word-steps translation of cell data undershoots growing cells
        and grinds the fixpoint. *)
     (match head_arm with
      | Cbat_landmarks.Finite _ | Cbat_landmarks.Inf -> widen ()
      | Cbat_landmarks.Zero -> assert false))

(* The key's extrapolation by [steps], flagged when it translated; a
   refused one plain-widens. *)
let extrapolate_or_widen ~landmarks ~head ~(key : Cbat_landmarks.key)
    ~(old : WordSet.t) ~(new_ : WordSet.t) ~steps : WordSet.t * bool =
  match
    Cbat_landmarks.extrapolate ~steps ~old ~new_
      ~entries:(Cbat_landmarks.entries landmarks head key)
  with
  | `Extrapolated d -> (d, true)
  | `Widen -> (WordSet.widen_join old new_, false)

(* The landmark walk: each key consumes its OWN row; the head's arm is
   the fallback, never a scope. *)
let walk_landmarks ~(head : Tid.t)
    ~(landmarks : Cbat_landmarks.t)
    ~(need : Int.Set.t) ~(arm : Cbat_landmarks.arm) (e1 : t) (e2 : t) : t =
  if WordEnv.equal e1.words WordEnv.bottom then e2
  else if WordEnv.equal e2.words WordEnv.bottom then e1
  else if Core.Set.is_empty need then join e1 e2
  else if Cbat_landmarks.equal_arm arm Cbat_landmarks.Zero then begin
    (* The non-widening arm: the head's own consumption — every row at
       the head advances (a row outside [need] would otherwise hold
       [steps_head] in Zero forever), and the value is the plain
       join. *)
    List.iter (Cbat_landmarks.keys_at landmarks head)
      ~f:(Cbat_landmarks.advance landmarks head);
    join e1 e2
  end
  else
    let consume_env ~fold ~find ~add ~top ~owner ~lkey env1 env2 =
      fold env1 ~init:top ~f:(fun ~key ~data:data_old acc ->
        let idx = WordSet.bitwidth data_old in
        let data_new = find idx env2 key in
        if WordSet.is_top data_new then acc
        else
          let data_res =
            if not (Core.Set.mem need (owner key)) then
              WordSet.join data_old data_new
            else
              consume_arm ~head ~landmarks
                ~key:(lkey key)
                ~head_arm:arm
                ~extrapolate:(fun ~steps ->
                    extrapolate_or_widen ~landmarks ~head
                      ~key:(lkey key)
                      ~old:data_old ~new_:data_new ~steps)
                ~zero_action:(fun () -> WordSet.join data_old data_new)
                ~widen:(fun () -> WordSet.widen_join data_old data_new)
          in
          if WordSet.is_top data_res then acc
          else add acc ~key ~data:data_res)
    in
    let words =
      consume_env e1.words e2.words ~fold:WordEnv.fold ~find:WordEnv.find
        ~add:WordEnv.add ~top:WordEnv.top ~owner:Fun.id
        ~lkey:(fun key -> Cbat_landmarks.Word (Cbat_var_id.var_of key))
    in
    let slices =
      consume_env e1.slices e2.slices ~fold:SliceEnv.fold ~find:SliceEnv.find
        ~add:SliceEnv.add ~top:SliceEnv.top ~owner:slice_owner
        ~lkey:(fun key ->
            Cbat_landmarks.Slice
              (Cbat_var_id.var_of (slice_owner key), slice_hi key, slice_lo key))
    in
    let memories =
      MemEnv.fold e1.memories ~init:MemEnv.top
        ~f:(fun ~key:mv ~data:old acc ->
            let idx = Mem.get_idx old in
            let nw = MemEnv.find idx e2.memories mv in
            if Mem.equal nw (Mem.top idx) then acc
            else begin
              let extr ck v1 v2 =
                if Mem.Val.equal v1 v2 then Mem.Val.widen_join v1 v2
                else
                  let cl = Cbat_landmarks.Cell (Mem.Key.cell_key ck) in
                  let data_old = Mem.Val.data v1 in
                  let data_new = Mem.Val.data v2 in
                  let data =
                    consume_arm ~head ~landmarks ~key:cl ~head_arm:arm
                      ~extrapolate:(fun ~steps ->
                          extrapolate_or_widen ~landmarks ~head ~key:cl
                            ~old:data_old ~new_:data_new ~steps)
                      ~zero_action:(fun () ->
                          WordSet.widen_join data_old data_new)
                      ~widen:(fun () -> WordSet.widen_join data_old data_new)
                  in
                  let _, e = Mem.Val.get_idx v2 in
                  Mem.Val.create data e
              in
              MemEnv.add acc ~key:mv
                ~data:(Mem.widen_join_op extr old nw)
            end)
    in
    { e1 with memories; words; slices;
             escaped = join_escape e1.escaped e2.escaped }

(* Extrapolate [need]'s keys by [steps]; each key still reads its own
   row first. *)
let selective_widen_extrapolate ~head ~landmarks ~need ~steps e1 e2 =
  walk_landmarks ~head ~landmarks ~need ~arm:(Cbat_landmarks.Finite steps) e1 e2

(* The head has no steps: the keys widen, each still reading its own row. *)
let widen_with_landmarks ~head ~landmarks ~need e1 e2 =
  walk_landmarks ~head ~landmarks ~need ~arm:Cbat_landmarks.Inf e1 e2

(* The head's arm is Zero: advance-and-join per key. *)
let advance_join_landmarks ~head ~landmarks ~need e1 e2 =
  walk_landmarks ~head ~landmarks ~need ~arm:Cbat_landmarks.Zero e1 e2

let meet (e1 : t) (e2 : t) : t =
  let memories = MemEnv.meet e1.memories e2.memories in
  let words = WordEnv.meet e1.words e2.words in
  let slices = SliceEnv.meet e1.slices e2.slices in
  if MemEnv.equal memories MemEnv.bottom || WordEnv.equal words WordEnv.bottom then bottom
  else
    (* Conflicting slices are dropped, not read as unreachable. *)
    let slices =
      if SliceEnv.equal slices SliceEnv.bottom then SliceEnv.top else slices in
    { e1 with memories; words; slices;
             escaped = join_escape e1.escaped e2.escaped }

let precedes (e1 : t) (e2 : t) : bool =
  MemEnv.precedes e1.memories e2.memories &&
  WordEnv.precedes e1.words e2.words &&
  SliceEnv.precedes e1.slices e2.slices &&
  precedes_escape e1.escaped e2.escaped

(* Top every word key not in [preserved]; the memories stay.  An absent
   key reads top, so the others are dropped.  A versioned var keeps its
   value: no call redefines it. *)
let top_words_except ~(preserved : Int.Set.t) (env : t) : t =
  if Option.is_some env.scalar then env else
  let kept k = Core.Set.mem preserved k || versioned k in
  let words = WordEnv.filter_keys env.words ~f:kept in
  let slices =
    SliceEnv.filter_keys env.slices ~f:(fun k -> kept (slice_owner k)) in
  if phys_equal words env.words && phys_equal slices env.slices then env
  else { env with words; slices }

(* Apply [f] to every memory cell; the words stay. *)
let map_memories (env : t) ~(f : key:var -> data:Mem.t -> Mem.t) : t =
  let memories = MemEnv.fold env.memories ~init:env.memories
    ~f:(fun ~key ~data acc ->
      MemEnv.add acc ~key ~data:(f ~key:(Cbat_var_id.var_of key) ~data)) in
  { env with memories }

(* The whole-memory-top fallback; the words stay. *)
let top_memories (env : t) : t = { env with memories = MemEnv.top }

#ifdef VSA_DEBUG
(* The per-visit witness: which word and memory bindings differ between
   two states.  Two states that differ only in a value's representation
   show up here as a same-denotation pair [equal] rejects. *)
let word_keys (e : t) : Int.Set.t =
  WordEnv.fold e.words ~init:Int.Set.empty ~f:(fun ~key ~data:_ acc ->
      Set.add acc key)

let clipped (s : string) : string =
  if String.length s <= 300 then s else String.prefix s 300 ^ "..."

let key_str (k : Mem.Key.t) : string =
  String.substr_replace_all
    (Core.Sexp.to_string (Mem.Key.sexp_of_t k))
    ~pattern:"\n" ~with_:" "

let ws_str (s : WordSet.t) : string =
  clipped (Format.asprintf "%a" WordSet.pp s)

(* The cells of [d1] whose value differs in [d2], first few. *)
let mem_cells (d1 : Mem.t) (d2 : Mem.t) : int * string =
  let n = ref 0 and shown = ref [] in
  List.iter (Mem.cells d1) ~f:(fun (key, v1) ->
      let v2 = Mem.find (Mem.Val.get_idx v1) d2 key in
      if Mem.Val.equal v1 v2 then ()
      else begin
        incr n;
        if List.length !shown < 4 then
          shown :=
            sprintf "%s %s -> %s" (key_str key)
              (ws_str (Mem.Val.data v1)) (ws_str (Mem.Val.data v2))
            :: !shown
      end);
  (!n, String.concat (List.rev !shown) ~sep:"; ")

let mem_diff (e1 : t) (e2 : t) : string =
  let n = ref 0 and shown = ref [] in
  MemEnv.fold e1.memories ~init:() ~f:(fun ~key ~data:m1 () ->
      let m2 = MemEnv.find (Mem.get_idx m1) e2.memories key in
      if Mem.equal m1 m2 then ()
      else begin
        incr n;
        if List.length !shown < 3 then
          let _, cells = mem_cells m1 m2 in
          shown := sprintf "%s {%s}" (Var.name (Cbat_var_id.var_of key)) cells :: !shown
      end);
  sprintf "nmem=%d %s" !n (String.concat (List.rev !shown) ~sep:" | ")

(* (the differing bindings, how many of them print and tag identically
   yet [equal] rejects — the representation-only churn). *)
let diff (e1 : t) (e2 : t) : string * int =
  let same_repr = ref 0 in
  let differing =
    Set.union (word_keys e1) (word_keys e2)
    |> Set.fold ~init:[] ~f:(fun acc key ->
        let d1 = WordEnv.find 64 e1.words key
        and d2 = WordEnv.find 64 e2.words key in
        if WordSet.equal d1 d2 then acc
        else begin
          let p1 = Format.asprintf "%a" WordSet.pp d1
          and p2 = Format.asprintf "%a" WordSet.pp d2 in
          if String.equal p1 p2 && String.equal (WordSet.tag d1) (WordSet.tag d2)
          then incr same_repr;
          sprintf "%s %s:%s -> %s:%s" (Var.name (Cbat_var_id.var_of key))
            (ws_str d1) (WordSet.tag d1) (ws_str d2) (WordSet.tag d2)
          :: acc
        end)
    |> List.rev
  in
  ( sprintf "words[%s] %s" (String.concat differing ~sep:"; ") (mem_diff e1 e2),
    !same_repr )
#endif

#ifdef VSA_DEBUG
(* Every word and memory binding, tagged and printed — a head's state in
   one line. *)
let head_summary (e : t) : string =
  let words =
    Set.fold (word_keys e) ~init:[] ~f:(fun acc key ->
        let d = WordEnv.find 64 e.words key in
        sprintf "%s=%s:%s" (Var.name (Cbat_var_id.var_of key))
          (ws_str d) (WordSet.tag d)
        :: acc)
  in
  let mems =
    MemEnv.fold e.memories ~init:[] ~f:(fun ~key ~data:m acc ->
        let cells =
          List.map (Mem.cells m) ~f:(fun (k, v) ->
              sprintf "%s=>%s" (key_str k) (ws_str (Mem.Val.data v)))
        in
        sprintf "%s={%s}" (Var.name (Cbat_var_id.var_of key))
          (clipped (String.concat cells ~sep:", "))
        :: acc)
  in
  String.concat (List.rev mems @ List.rev words) ~sep:" "
#endif
