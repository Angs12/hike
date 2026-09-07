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

open !Core_kernel
module Abi = Hike_abi
include Bap.Std
include Cbat_vsa_utils
module MapLattice = Cbat_map_lattice
module Mem = Cbat_ai_memmap
module WordSet = Cbat_clp_set_composite
module Utils = Cbat_vsa_utils

(* Abstract state: words, memories, frame. *)

type wordset = WordSet.t


(* Env keys compare by [Var.same]. *)
module VarKey = struct
  include Var
  let equal = same
end

module MemEnv = MapLattice.Make_indexed_val(VarKey)(Mem)
module WordEnv = MapLattice.Make_indexed_val(VarKey)(WordSet)

(* Frame relation: offset(X) = fconst + sum k*fvar from the entry RSP. Must-facts; None is bottom. *)

(* Offset expression of a derived register. *)
type frame_term = {
  fconst : WordSet.t;               (* constant part *)
  fvars : (var * int) list;         (* scaled non-derived registers *)
} [@@deriving bin_io, sexp, compare]

(* Per-state facts; absent var is not derived. *)
type frame = (var * frame_term) list [@@deriving bin_io, sexp, compare]

(* Base-normalized lookup key. *)
let frame_key (v : var) : var = Var.base v

let frame_lookup (f : frame) (v : var) : frame_term option =
  List.Assoc.find ~equal:Var.equal f (frame_key v)

let frame_remove (f : frame) (v : var) : frame =
  List.filter f ~f:(fun (v', _) -> not (Var.equal v' (frame_key v)))

let frame_set (f : frame) (v : var) (t : frame_term) : frame =
  (frame_key v, t) :: frame_remove f v

(* Merge consts when shapes agree; else drop. *)
let frame_term_binop (op : wordset -> wordset -> wordset)
    (t1 : frame_term) (t2 : frame_term) : frame_term option =
  let eq_vs (v1, s1) (v2, s2) =
    s1 = s2 && Var.equal (frame_key v1) (frame_key v2) in
  if List.equal eq_vs t1.fvars t2.fvars
  then Some { fconst = op t1.fconst t2.fconst; fvars = t1.fvars }
  else None

(* Join consts of same-shaped terms. *)
let frame_term_join ?(widen = false) (t1 : frame_term) (t2 : frame_term)
    : frame_term option =
  frame_term_binop
    (if widen then WordSet.widen_join else WordSet.join) t1 t2

(* Keep facts present on both sides. *)
let join_frames ?widen (f1 : frame) (f2 : frame) : frame =
  List.filter_map f1 ~f:(fun (v, t1) ->
      match frame_lookup f2 v with
      | Some t2 ->
        (match frame_term_join ?widen t1 t2 with
         | Some t -> Some (frame_key v, t)
         | None -> None)
      | None -> None)

(* Meet consts of same-shaped terms. *)
let frame_term_meet (t1 : frame_term) (t2 : frame_term) : frame_term option =
  frame_term_binop WordSet.meet t1 t2

(* Keep facts present on either side. *)
let meet_frames (f1 : frame) (f2 : frame) : frame =
  let both =
    List.filter_map f1 ~f:(fun (v, t1) ->
        match frame_lookup f2 v with
        | Some t2 ->
          (match frame_term_meet t1 t2 with
           | Some t -> Some (frame_key v, t)
           | None -> Some (frame_key v, t1))
        | None -> None) in
  let only_f2 =
    List.filter_map f2 ~f:(fun (v, t2) ->
        match frame_lookup f1 v with
        | Some _ -> None
        | None -> Some (frame_key v, t2)) in
  both @ only_f2

let frame_equal (f1 : frame) (f2 : frame) : bool =
  List.equal (fun (v1, t1) (v2, t2) ->
      Var.equal v1 v2
      && WordSet.equal t1.fconst t2.fconst
      && List.equal (fun (a1, s1) (a2, s2) -> s1 = s2 && Var.equal a1 a2)
          t1.fvars t2.fvars) f1 f2

let frame_opt_equal (f1 : frame option) (f2 : frame option) : bool =
  match f1, f2 with
  | None, None -> true
  | Some a, Some b -> frame_equal a b
  | _ -> false

(* LUB; None is the identity. *)
let join_opt ?widen (f1 : frame option) (f2 : frame option) : frame option =
  match f1, f2 with
  | None, x | x, None -> x
  | Some a, Some b -> Some (join_frames ?widen a b)

(* GLB; None meets to None. *)
let meet_opt (f1 : frame option) (f2 : frame option) : frame option =
  match f1, f2 with
  | None, _ | _, None -> None
  | Some a, Some b -> Some (meet_frames a b)

(* Must-lattice order. *)
let frame_precedes (f1 : frame option) (f2 : frame option) : bool =
  match f1, f2 with
  | None, _ -> true
  | Some _, None -> false
  | Some a, Some b -> frame_equal (join_frames a b) b

(* Entry frame: entry RSP has offset 0. *)
let seed_frame : frame option =
  Some [ (Var.base Abi.x86_64_sysv.sp, { fconst = WordSet.singleton (Cbat_word.of_word (Word.zero 64)); fvars = [] }) ]

(* Restore RSP's offset by +8. *)
let frame_add_rsp (f : frame option) : frame option =
  let rsp = frame_key Abi.x86_64_sysv.sp in
  let eight = WordSet.singleton (Cbat_word.of_word (Word.of_int ~width:64 8)) in
  match f with
  | None -> None
  | Some f ->
    (match frame_lookup f rsp with
     | Some t ->
       Some (List.map f ~f:(fun (v, t') ->
           if Var.equal v rsp then (v, { t' with fconst = WordSet.add t'.fconst eight })
           else (v, t')))
     | None -> Some f)

(* Bil-free record updates. *)
let frame_add_const (t : frame_term) (c : WordSet.t) : frame_term =
  { t with fconst = WordSet.add t.fconst c }

let frame_sub_const (t : frame_term) (c : WordSet.t) : frame_term =
  { t with fconst = WordSet.sub t.fconst c }

let frame_add_fvar (t : frame_term) (v : var) (k : int) : frame_term =
  { t with fvars = (frame_key v, k) :: t.fvars }

type t = {
  memories : MemEnv.t;
  words : WordEnv.t;
  frame : frame option;             (* frame relation *)
} [@@deriving bin_io, sexp, compare]

let top : t =
  { memories = MemEnv.top;
    words = WordEnv.top;
    frame = None;
  }
let bottom : t =
  { memories = MemEnv.bottom;
    words = WordEnv.bottom;
    frame = None;
  }

(* Empty word or memory env is bottom. *)


let equal (e1 : t) e2 : bool =
  MemEnv.equal e1.memories e2.memories &&
  WordEnv.equal e1.words e2.words &&
  frame_opt_equal e1.frame e2.frame

(* Frame relation of a state. *)
let frame_of (e : t) : frame option = e.frame

(* State with the frame replaced. *)
let set_frame (e : t) (f : frame option) : t = { e with frame = f }

(* Add a memory binding. *)
let add_memory (e : t) ~(key : var) ~(data : Mem.t) : t =
  {memories = MemEnv.add e.memories ~key ~data;
   words = e.words;
   frame = e.frame}

(* Add a word binding. *)
let add_word (e : t) ~(key : var) ~(data : wordset) : t =
  {memories = e.memories;
   words = WordEnv.add e.words ~key ~data;
   frame = e.frame}

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
    frame = join_opt e1.frame e2.frame
  }

let widen_join (e1 : t) (e2 : t) : t =
  { memories = MemEnv.widen_join e1.memories e2.memories;
    words = WordEnv.widen_join e1.words e2.words;
    frame = join_opt ~widen:true e1.frame e2.frame
  }



(* Extrapolate [need] vars by [steps]; negative steps widen. *)
let selective_widen_extrapolate ?(head:Tid.t option=None) ~(need : Var.Set.t) ~(steps : int) (e1 : t) (e2 : t) : t =
  if Core.Set.is_empty need then join e1 e2
  else if WordEnv.equal e1.words WordEnv.bottom then e2
  else if WordEnv.equal e2.words WordEnv.bottom then e1
  else
    let words =
      WordEnv.fold e1.words ~init:WordEnv.top ~f:(fun ~key ~data:data_old acc ->
        let idx = WordSet.bitwidth data_old in
        let data_new = WordEnv.find idx e2.words key in
        if WordSet.is_top data_new then acc
        else
          let data_res =
            if Core.Set.mem need (Var.base key) then
              match head with
              | Some h ->
                let entries = Cbat_landmarks.entries_for_head h key in
                let entries = List.filter entries ~f:(fun e -> Cbat_word.bitwidth e.Cbat_landmarks.bound = WordSet.bitwidth data_old) in
                (match entries with
                 | [] ->
                   if steps < 0 then WordSet.widen_join data_old data_new
                   else WordSet.extrapolate_steps ~steps data_old data_new
                 | _ ->
                   (* Translate bounds toward landmarks. *)
                   if steps < 0 then
                     (* No steps: widen. *)
                     WordSet.widen_join data_old data_new
                   else
                     (* Landmark translation. *)
                     Cbat_landmarks.translate_to ~steps data_old data_new entries)
              | None ->
                if steps < 0 then WordSet.widen_join data_old data_new
                else WordSet.extrapolate_steps ~steps data_old data_new
            else
              WordSet.join data_old data_new
          in
          if WordSet.is_top data_res then acc
          else WordEnv.add acc ~key ~data:data_res
      )
    in
    let memories = MemEnv.widen_join e1.memories e2.memories in
    { memories; words; frame = join_opt ~widen:true e1.frame e2.frame
    }

let meet (e1 : t) (e2 : t) : t =
  let memories = MemEnv.meet e1.memories e2.memories in
  let words = WordEnv.meet e1.words e2.words in
  if MemEnv.equal memories MemEnv.bottom || WordEnv.equal words WordEnv.bottom then bottom
  else { memories; words; frame = meet_opt e1.frame e2.frame
  }

let precedes (e1 : t) (e2 : t) : bool =
  MemEnv.precedes e1.memories e2.memories &&
  WordEnv.precedes e1.words e2.words &&
  frame_precedes e1.frame e2.frame

(* Post-call abstraction. *)
(* Top caller-saved words. *)
let top_non_preserved ~(preserved : Var.Set.t) (env : t) : WordEnv.t =
  WordEnv.fold env.words ~init:env.words
    ~f:(fun ~key ~data acc ->
      if Core.Set.exists preserved ~f:(fun p -> Var.same p key)
      then acc
      else WordEnv.add acc ~key ~data:(WordSet.top (WordSet.bitwidth data)))

let call_abstraction ~(preserved : Var.Set.t) (env : t) : t =
  { memories = MemEnv.top; words = top_non_preserved ~preserved env; frame = env.frame }

(* Like [call_abstraction]; caller frame survives. *)
let call_abstraction_frame ~(preserved : Var.Set.t) ~(rsp : WordSet.t)
    ~(escape : WordSet.t list) (env : t) : t =
  let words' = top_non_preserved ~preserved env in
  let rsp_lo =
    match WordSet.min_elem rsp, WordSet.max_elem rsp with
    | Some lo, Some hi when Cbat_word.equal lo hi -> Some lo
    | _ -> None in
  let escape_ranges =
    match rsp_lo with
    | None -> None
    | Some _ ->
      let ranges = List.filter_map escape ~f:(fun ws ->
          if WordSet.is_top ws || WordSet.is_infinite ws then None
          else match WordSet.min_elem ws, WordSet.max_elem ws with
            | Some a, Some b -> Some (Cbat_word.to_word a, Cbat_word.to_word b)
            | _ -> None) in
      if List.length ranges = List.length escape then Some ranges
      else None in
  let memories =
    match rsp_lo, escape_ranges with
    | Some lo, Some ranges ->
      MemEnv.fold env.memories ~init:env.memories
        ~f:(fun ~key ~data acc ->
            MemEnv.add acc ~key
              ~data:(Mem.call_keep data ~keep_lo:(Cbat_word.to_word lo) ~escape:ranges))
    | _ -> MemEnv.top in
  { memories; words = words'; frame = env.frame }

