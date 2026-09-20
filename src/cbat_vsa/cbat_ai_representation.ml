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
module Utils = Cbat_vsa_utils

(* Abstract state: words, memories.  Stack provenance is the WORD value
   itself — the entry RSP's word is seeded with the symbolic segment
   base ([WordSet.stack_word]) and SP-derived addresses stay [StackOff]
   through arithmetic, memory round-trips, and refinement. *)

type wordset = WordSet.t


(* Env keys compare by [Var.same]. *)
module VarKey = struct
  include Var
  let equal = same
end

module MemEnv = MapLattice.Make_indexed_val(VarKey)(Mem)
module WordEnv = MapLattice.Make_indexed_val(VarKey)(WordSet)

type t = {
  memories : MemEnv.t;
  words : WordEnv.t;
} [@@deriving bin_io, sexp, compare]

let top : t =
  { memories = MemEnv.top;
    words = WordEnv.top;
  }
let bottom : t =
  { memories = MemEnv.bottom;
    words = WordEnv.bottom;
  }

(* Empty word or memory env is bottom. *)


let equal (e1 : t) e2 : bool =
  MemEnv.equal e1.memories e2.memories &&
  WordEnv.equal e1.words e2.words

(* Add a memory binding. *)
let add_memory (e : t) ~(key : var) ~(data : Mem.t) : t =
  {memories = MemEnv.add e.memories ~key ~data;
   words = e.words}

(* Add a word binding. *)
let add_word (e : t) ~(key : var) ~(data : wordset) : t =
  {memories = e.memories;
   words = WordEnv.add e.words ~key ~data}

let find_word (i : WordSet.idx) (env : t) (v : var) : wordset = WordEnv.find i env.words v
let find_memory (i : Mem.idx) (env : t) (v : var) : Mem.t = MemEnv.find i env.memories v

(* Drop dead virtual temps; machine regs are the ABI surface and stay.
   Missing keys read top, so dropping only weakens. *)
let gc (e : t) ~(keep : Var.Set.t) : t =
  { e with
    words =
      WordEnv.filter_keys e.words ~f:(fun k ->
          (not (Var.is_virtual k))
          || Core.Set.mem keep (Var.base k)) }




let pp ppf (e : t) =
  if equal e bottom then
    Format.fprintf ppf "unreachable"
  else if equal e top then
    Format.fprintf ppf "unknown"
  else begin
    Format.fprintf ppf "@[@[<2>Immediate Variables:@ %a@]@ "
      WordEnv.pp e.words;
    Format.fprintf ppf "@[<2>Memory:@ @ %a@]@]"
      MemEnv.pp e.memories
  end

let join (e1 : t) (e2 : t) : t =
  { memories = MemEnv.join e1.memories e2.memories;
    words = WordEnv.join e1.words e2.words;
  }

let widen_join (e1 : t) (e2 : t) : t =
  { memories = MemEnv.widen_join e1.memories e2.memories;
    words = WordEnv.widen_join e1.words e2.words;
  }



(* The landmark consumption rule, shared by the words and memory
   folds: translate [old] toward the head's entries at [old]'s width;
   with no entries the plain steps-extrapolation (negative steps
   widen). *)
let extrapolate_data ~(entries : Cbat_landmarks.lm_entry list) ~(steps : int)
    (old : wordset) (new_ : wordset) : wordset =
  let entries =
    List.filter entries ~f:(fun e ->
        Cbat_word.bitwidth e.Cbat_landmarks.bound = WordSet.bitwidth old) in
  match entries with
  | [] ->
    if steps < 0 then WordSet.widen_join old new_
    else WordSet.extrapolate_steps ~steps old new_
  | _ -> Cbat_landmarks.translate_to ~steps old new_ entries

(* Extrapolate [need] vars by [steps]; negative steps widen. *)
let selective_widen_extrapolate ?(head:Tid.t option=None) ~(need : Var.Set.t) ~(steps : int) (e1 : t) (e2 : t) : t =
  if Core.Set.is_empty need then join e1 e2
  else if WordEnv.equal e1.words WordEnv.bottom then e2
  else if WordEnv.equal e2.words WordEnv.bottom then e1
  else
    let words =
      WordEnv.fold e1.words ~init:WordEnv.top ~f:(fun ~key ~data:data_old acc ->
        let idx = WordSet.bitwidth data_old
        in
        let data_new = WordEnv.find idx e2.words key in
        if WordSet.is_top data_new then acc
        else
          let data_res =
            if Core.Set.mem need (Var.base key) then
              match head with
              | Some h ->
                extrapolate_data ~entries:(Cbat_landmarks.entries_for_head h key)
                  ~steps data_old data_new
              | None -> extrapolate_data ~entries:[] ~steps data_old data_new
            else
              WordSet.join data_old data_new
          in
          if WordSet.is_top data_res then acc
          else WordEnv.add acc ~key ~data:data_res
      )
    in
    let memories =
      match head with
      | Some h when steps > 0 ->
        (* CYCLE-WRITTEN CELLS EXTRAPOLATE: at a warmed head, every
           cell the incoming state differs on was written by the
           cycle's own stores (pre-loop writes are stable by warmup;
           call-mediated writes abstract to whole-memory top, where
           extrapolation is a no-op).  Its data advances by [steps]
           traversals — landmark translation when the head holds
           entries at the cell's width, the plain-widen arm on
           overflow.  Keys never change; bounds only move outward; no
           residency claim. *)
        MemEnv.fold e1.memories ~init:MemEnv.top
          ~f:(fun ~key:mv ~data:old acc ->
              let idx = Mem.get_idx old in
              let nw = MemEnv.find idx e2.memories mv in
              if Mem.equal nw (Mem.top idx) then acc
              else begin
                let entries = Cbat_landmarks.entries_for_head h mv in
                let extr (v1 : Mem.Val.t) (v2 : Mem.Val.t) : Mem.Val.t =
                  if Mem.Val.equal v1 v2 then Mem.Val.widen_join v1 v2
                  else
                    let data_old = Mem.Val.data v1 in
                    let data_new = Mem.Val.data v2 in
                    let data = extrapolate_data ~entries ~steps data_old data_new in
                    (* Overflow escapes to the plain-widen arm. *)
                    let data =
                      if WordSet.is_top data
                      then WordSet.widen_join data_old data_new
                      else data in
                    let _, e = Mem.Val.get_idx v2 in
                    Mem.Val.create data e in
                MemEnv.add acc ~key:mv
                  ~data:(Mem.widen_join_op extr old nw)
              end)
      | _ -> MemEnv.widen_join e1.memories e2.memories in
    { memories; words }

let meet (e1 : t) (e2 : t) : t =
  let memories = MemEnv.meet e1.memories e2.memories in
  let words = WordEnv.meet e1.words e2.words in
  if MemEnv.equal memories MemEnv.bottom || WordEnv.equal words WordEnv.bottom then bottom
  else { memories; words }

let precedes (e1 : t) (e2 : t) : bool =
  MemEnv.precedes e1.memories e2.memories &&
  WordEnv.precedes e1.words e2.words

(* Post-call abstraction. *)
(* Top caller-saved words. *)
let top_non_preserved ~(preserved : Var.Set.t) (env : t) : WordEnv.t =
  WordEnv.fold env.words ~init:env.words
    ~f:(fun ~key ~data acc ->
      if Core.Set.exists preserved ~f:(fun p -> Var.same p key)
      then acc
      else WordEnv.add acc ~key ~data:(WordSet.top (WordSet.bitwidth data)))

let call_abstraction ~(preserved : Var.Set.t) (env : t) : t =
  { memories = MemEnv.top; words = top_non_preserved ~preserved env }

(* Like [call_abstraction]; caller frame survives.  The frame-keep
   boundary and the escape ranges are KEY-space: stack-derived
   cells key by segment offsets, foreign cells by their concrete
   addresses, so the call-time RSP contributes its bounds (offset hull
   for a stack word, concrete extrema otherwise) and pointer-arg
   escapes exclude their own key ranges.  An unbounded RSP or any
   foreign escape keeps the sound whole-memory-top fallback. *)
let call_abstraction_frame ~(preserved : Var.Set.t) ~(rsp : WordSet.t)
    ~(escape : WordSet.t list) (env : t) : t =
  let words' = top_non_preserved ~preserved env in
  let range_of (ws : WordSet.t) : (word * word) option =
    if WordSet.is_top ws || WordSet.is_infinite ws then None
    else
      match WordSet.stack_bounds ws with
      | Some (a, b) -> Some (Word.of_int64 ~width:64 a, Word.of_int64 ~width:64 b)
      | None ->
        Option.map2 (WordSet.min_elem ws) (WordSet.max_elem ws)
          ~f:(fun a b -> (Cbat_word.to_word a, Cbat_word.to_word b)) in
  (* The callee writes below its own RSP; cells at keys at/above the
     HIGHEST possible call-time RSP survive every call site. *)
  let keep_lo = Option.map ~f:snd (range_of rsp) in
  let escape_ranges =
    match List.filter_map escape ~f:range_of with
    | ranges when List.length ranges = List.length escape -> Some ranges
    | _ -> None in
  let memories =
    match keep_lo, escape_ranges with
    | Some lo, Some ranges ->
      MemEnv.fold env.memories ~init:env.memories
        ~f:(fun ~key ~data acc ->
            MemEnv.add acc ~key
              ~data:(Mem.call_keep data ~keep_lo:lo ~escape:ranges))
    | _ -> MemEnv.top in
  { memories; words = words' }
