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
module Clp = Cbat_clp

(* Abstract state: words, memories.  Stack provenance is the WORD value
   itself — the entry RSP's word is seeded with the symbolic segment
   base and SP-derived addresses stay [StackOff] through arithmetic,
   memory round-trips, and refinement. *)

type wordset = WordSet.t

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

type t = {
  memories : MemEnv.t;
  words : WordEnv.t;
  escaped : escape;
} [@@deriving bin_io, sexp, compare]

(* The escape set is a path fact that only a call or a store raises, so
   [top], the entry state's base, starts [Contained] like [bottom]. *)
let top : t =
  { memories = MemEnv.top;
    words = WordEnv.top;
    escaped = Contained;
  }
let bottom : t =
  { memories = MemEnv.bottom;
    words = WordEnv.bottom;
    escaped = Contained;
  }

let equal (e1 : t) e2 : bool =
  MemEnv.equal e1.memories e2.memories &&
  WordEnv.equal e1.words e2.words &&
  compare_escape e1.escaped e2.escaped = 0

let frame_escaped (e : t) : bool =
  match e.escaped with Contained -> false | Whole_frame -> true

let escape_frame (e : t) : t =
  match e.escaped with
  | Whole_frame -> e
  | Contained -> { e with escaped = Whole_frame }

(* A write that leaves the maps physically unchanged keeps the record,
   so physically keyed caches still hit. *)
let add_memory (e : t) ~(key : var) ~(data : Mem.t) : t =
  let memories = MemEnv.add e.memories ~key:(Cbat_var_id.intern key) ~data in
  if phys_equal memories e.memories then e else { e with memories }

let add_word (e : t) ~(key : var) ~(data : wordset) : t =
  let words = WordEnv.add e.words ~key:(Cbat_var_id.intern key) ~data in
  if phys_equal words e.words then e else { e with words }

let find_word (i : WordSet.idx) (env : t) (v : var) : wordset =
  WordEnv.find i env.words (Cbat_var_id.intern v)

let find_memory (i : Mem.idx) (env : t) (v : var) : Mem.t =
  MemEnv.find i env.memories (Cbat_var_id.intern v)

(* Drop dead virtual temps; machine regs are the ABI surface and stay.
   Missing keys read top, so dropping only weakens. *)
let gc (e : t) ~(keep : Int.Set.t) : t =
  let words =
    WordEnv.filter_keys e.words ~f:(fun k ->
        (not (Cbat_var_id.is_virtual k))
        || Core.Set.mem keep (Cbat_var_id.base_of k)) in
  if phys_equal words e.words then e else { e with words }




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
   component maps come back physically unchanged. *)
let rebuilt (e1 : t) ~(escaped : escape) memories words : t =
  if phys_equal memories e1.memories && phys_equal words e1.words
     && compare_escape escaped e1.escaped = 0 then e1
  else { memories; words; escaped }

let join (e1 : t) (e2 : t) : t =
  rebuilt e1 ~escaped:(join_escape e1.escaped e2.escaped)
    (MemEnv.join e1.memories e2.memories)
    (WordEnv.join e1.words e2.words)

let widen_join (e1 : t) (e2 : t) : t =
  rebuilt e1 ~escaped:(join_escape e1.escaped e2.escaped)
    (MemEnv.widen_join e1.memories e2.memories)
    (WordEnv.widen_join e1.words e2.words)



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
    let words =
      WordEnv.fold e1.words ~init:WordEnv.top ~f:(fun ~key ~data:data_old acc ->
        let idx = WordSet.bitwidth data_old in
        let data_new = WordEnv.find idx e2.words key in
        if WordSet.is_top data_new then acc
        else
          let data_res =
            if not (Core.Set.mem need (Cbat_var_id.base_of key)) then
              WordSet.join data_old data_new
            else
              consume_arm ~head ~landmarks
                ~key:(Cbat_landmarks.Word (Cbat_var_id.var_of key))
                ~head_arm:arm
                ~extrapolate:(fun ~steps ->
                    extrapolate_or_widen ~landmarks ~head
                      ~key:(Cbat_landmarks.Word (Cbat_var_id.var_of key))
                      ~old:data_old ~new_:data_new ~steps)
                ~zero_action:(fun () -> WordSet.join data_old data_new)
                ~widen:(fun () -> WordSet.widen_join data_old data_new)
          in
          if WordSet.is_top data_res then acc
          else WordEnv.add acc ~key ~data:data_res)
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
    { memories; words; escaped = join_escape e1.escaped e2.escaped }

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
  if MemEnv.equal memories MemEnv.bottom || WordEnv.equal words WordEnv.bottom then bottom
  else { memories; words; escaped = join_escape e1.escaped e2.escaped }

let precedes (e1 : t) (e2 : t) : bool =
  MemEnv.precedes e1.memories e2.memories &&
  WordEnv.precedes e1.words e2.words &&
  precedes_escape e1.escaped e2.escaped

(* Top every word key not in [preserved]; the memories stay.  An absent
   key reads top, so the others are dropped.  Both the set's elements
   and the lane's keys are base vars, so membership is a direct set
   lookup. *)
let top_words_except ~(preserved : Int.Set.t) (env : t) : t =
  let words = WordEnv.filter_keys env.words ~f:(Core.Set.mem preserved) in
  if phys_equal words env.words then env else { env with words }

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