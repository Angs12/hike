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
include Bap.Std
include Cbat_vsa_utils
module MapLattice = Cbat_map_lattice
module Mem = Cbat_ai_memmap
module WordSet = Cbat_clp_set_composite
module Utils = Cbat_vsa_utils
let max_int = Sys.max_array_length (* approx; we use 1 lsl 40 via Cbat_landmarks *)

(* The full abstract representation for the value set analysis *)

type wordset = WordSet.t


(* Rename same to equal so that variables as keys to the environment are compared ignoring their indices (a peice of BAP metadata). TODO: is this right & is this sufficient? (maybe, no) *)
module VarKey = struct
  include Var
  let equal = same
end

module MemEnv = MapLattice.Make_indexed_val(VarKey)(Mem)
module WordEnv = MapLattice.Make_indexed_val(VarKey)(WordSet)

(* ------------------------------------------------------------------ *)
(* Frame-relation facts (hike port: WYSINWYX-2 — the a-priori frame. *)
(* relation carried IN the abstract state). *)
(*  *)
(* A FRAME-DERIVED register is one provably equal to the frame origin *)
(* (the sub's entry RSP) plus an offset expression: *)
(*  *)
(* offset(X) = fconst + Σ k·fvar *)
(*  *)
(* — fconst: a CLP (usually a singleton); fvars: scaled non-derived *)
(* registers (the -O0 index shapes). The relation [rbp = rsp + N] is *)
(* entailed as [offset(RBP) − offset(RSP) = N]; both offsets share the *)
(* origin, so addresses over either base normalize to the same key *)
(* (the WYSINWYX a-loc unification). The facts are DERIVED from the *)
(* def chain (a def [RBP := RSP ± k] earns RBP frame-base status; a *)
(* GPR RBP gets nothing), and are MUST-facts over paths: the join *)
(* keeps a fact only if every path derived it (a clobber on any path *)
(* clears it below the merge). *)
(*  *)
(* LATTICE: [frame option] — None = the BOTTOM state (vacuously *)
(* everything derived with the empty offset set), the JOIN IDENTITY *)
(* ([None ⊔ x = x]): the value fixpoint's least-fixpoint ascent from *)
(* bottom converges to the rich facts, and the relation consts widen *)
(* with the fixpoint's own loop-head widening. Some [] = the TOP *)
(* (nothing derived). The TRANSFER ([Cbat_vsa.apply_frame_def] — *)
(* Bil-dependent, lives in cbat_vsa.ml) advances the state's frame *)
(* through each def; the +8 call-revert is [frame_add_rsp]. *)

(* [frame_term]: the offset-from-origin expression of a derived *)
(* register. *)
type frame_term = {
  fconst : WordSet.t;               (* constant part (CLP; usually a singleton) *)
  fvars : (var * int) list;         (* scaled non-derived registers *)
} [@@deriving bin_io, sexp, compare]

(* [frame]: the per-state facts — absent var = not derived. *)
type frame = (var * frame_term) list [@@deriving bin_io, sexp, compare]

(* [frame_key v]: the base-normalized lookup key (the Var.same env-key idiom). *)
let frame_key (v : var) : var = Var.base v

let frame_lookup (f : frame) (v : var) : frame_term option =
  List.Assoc.find ~equal:Var.equal f (frame_key v)

let frame_remove (f : frame) (v : var) : frame =
  List.filter f ~f:(fun (v', _) -> not (Var.equal v' (frame_key v)))

let frame_set (f : frame) (v : var) (t : frame_term) : frame =
  (frame_key v, t) :: frame_remove f v

(* [frame_term_binop op t1 t2]: the MUST merge of two frame terms with the same expression shape — the consts combined with [op], the fvars kept from the first; a shape mismatch drops the fact (None). *)
let frame_term_binop (op : wordset -> wordset -> wordset)
    (t1 : frame_term) (t2 : frame_term) : frame_term option =
  let eq_vs (v1, s1) (v2, s2) =
    s1 = s2 && Var.equal (frame_key v1) (frame_key v2) in
  if List.equal eq_vs t1.fvars t2.fvars
  then Some { fconst = op t1.fconst t2.fconst; fvars = t1.fvars }
  else None

(* [frame_term_join ?widen]: the MUST join (consts unioned, or widened under [widen_join]). *)
let frame_term_join ?(widen = false) (t1 : frame_term) (t2 : frame_term)
    : frame_term option =
  frame_term_binop
    (if widen then WordSet.widen_join else WordSet.join) t1 t2

(* [join_frames ?widen]: the MUST-fact merge — keep-if-both. *)
let join_frames ?widen (f1 : frame) (f2 : frame) : frame =
  List.filter_map f1 ~f:(fun (v, t1) ->
      match frame_lookup f2 v with
      | Some t2 ->
        (match frame_term_join ?widen t1 t2 with
         | Some t -> Some (frame_key v, t)
         | None -> None)
      | None -> None)

(* [frame_term_meet]: the MUST meet — the consts intersected when the shapes agree. *)
let frame_term_meet (t1 : frame_term) (t2 : frame_term) : frame_term option =
  frame_term_binop WordSet.meet t1 t2

(* [meet_frames]: keep-if-either (a fact holding in EITHER state holds in their intersection); both present -> the term meet (shape mismatch keeps the first — sound, the S1 fact holds in S1 ∩ S2). *)
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

(* [join_opt ?widen]: the LUB over [frame option] — None is the BOTTOM state (the join identity: every var vacuously derived with the empty offset set), so an unprocessed predecessor never pollutes a merge and the rich paths flow through loops. *)
let join_opt ?widen (f1 : frame option) (f2 : frame option) : frame option =
  match f1, f2 with
  | None, x | x, None -> x
  | Some a, Some b -> Some (join_frames ?widen a b)

(* [meet_opt]: the GLB over [frame option] — None (the bottom state) meets to None (the intersection with the empty state is empty). *)
let meet_opt (f1 : frame option) (f2 : frame option) : frame option =
  match f1, f2 with
  | None, _ | _, None -> None
  | Some a, Some b -> Some (meet_frames a b)

(* [frame_precedes]: the must-lattice order — bottom (None) precedes everything; Some a <= Some b iff the LUB of a and b is b. *)
let frame_precedes (f1 : frame option) (f2 : frame option) : bool =
  match f1, f2 with
  | None, _ -> true
  | Some _, None -> false
  | Some a, Some b -> frame_equal (join_frames a b) b

(* [seed_frame]: the entry-state frame — the ORIGIN definition: the sub's entry RSP has offset 0 (in BOTH anchored and unanchored runs; the origin is the entry RSP, not an assumption about its absolute value). Seeded by [Cbat_vsa.init_sol]. *)
let seed_frame : frame option =
  Some [ (Var.base rsp_var, { fconst = WordSet.singleton (Word.zero 64); fvars = [] }) ]

(* [frame_add_rsp f]: The call-revert — the callee's ret pops exactly the retaddr the caller pushed, so RSP's offset restores by +8 (the L-E1 matched-pair semantics, applied to the state's frame at the call-abstraction site in cbat_vsa.ml). *)
let frame_add_rsp (f : frame option) : frame option =
  let rsp = frame_key rsp_var in
  let eight = WordSet.singleton (Word.of_int ~width:64 8) in
  match f with
  | None -> None
  | Some f ->
    (match frame_lookup f rsp with
     | Some t ->
       Some (List.map f ~f:(fun (v, t') ->
           if Var.equal v rsp then (v, { t' with fconst = WordSet.add t'.fconst eight })
           else (v, t')))
     | None -> Some f)

(* The transfer's record-update helpers (Bil-free; the def-shape logic lives in [Cbat_vsa.apply_frame_def]). *)
let frame_add_const (t : frame_term) (c : WordSet.t) : frame_term =
  { t with fconst = WordSet.add t.fconst c }

let frame_sub_const (t : frame_term) (c : WordSet.t) : frame_term =
  { t with fconst = WordSet.sub t.fconst c }

let frame_add_fvar (t : frame_term) (v : var) (k : int) : frame_term =
  { t with fvars = (frame_key v, k) :: t.fvars }

(* ------------------------------------------------------------------ *)

type t = {
  memories : MemEnv.t;
  words : WordEnv.t;
  frame : frame option;             (* WYSINWYX-2: the in-state frame relation *)
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

(* if either the word env or mem env represents the empty set of states then this abstract state represents the empty set of states, i.e. bottom. Function in this module assume the inputs are canonized in this fashion. *)
(* canonize removed: every AI is produced canonical — join/widen/meet handle bottom directly *)

let equal (e1 : t) e2 : bool =
  MemEnv.equal e1.memories e2.memories &&
  WordEnv.equal e1.words e2.words &&
  frame_opt_equal e1.frame e2.frame

(* [frame_of e]: the state's frame relation (None = the vacuous bottom state). *)
let frame_of (e : t) : frame option = e.frame

(* [set_frame e f]: the state with the frame replaced (the transfer's write — see [Cbat_vsa.apply_frame_def]). *)
let set_frame (e : t) (f : frame option) : t = { e with frame = f }

(* adds a variable to the memories of the input env *)
let add_memory (e : t) ~(key : var) ~(data : Mem.t) : t =
  {memories = MemEnv.add e.memories ~key ~data;
   words = e.words;
   frame = e.frame}

(* adds a variable to the words of the input env *)
let add_word (e : t) ~(key : var) ~(data : wordset) : t =
  {memories = e.memories;
   words = WordEnv.add e.words ~key ~data;
   frame = e.frame}

let find_word (i : WordSet.idx) (env : t) (v : var) : wordset = WordEnv.find i env.words v
let find_memory (i : Mem.idx) (env : t) (v : var) : Mem.t = MemEnv.find i env.memories v

(* Printing *)

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

(* Hike addition (docs/widening-thresholds-plan.md): the thresholded widen — THE widening of the production fixpoint. *)
let widen_join_threshold (ladders : (int * word list) list) (e1 : t) (e2 : t) : t =
  let ladder_for ws =
    Option.value ~default:[]
      (List.Assoc.find ladders (WordSet.bitwidth ws) ~equal:Int.equal)
  in
  { memories = MemEnv.widen_join_op
      (Mem.widen_join_threshold ladders) e1.memories e2.memories;
    words = WordEnv.widen_join_op
      (fun ws1 ws2 -> WordSet.widen_join_threshold (ladder_for ws1) ws1 ws2)
      e1.words e2.words;
    frame = join_opt ~widen:true e1.frame e2.frame
  }

(* SiftAbs H3 — selective widen: only vars in [need] (value-flow cycle) are widened, others are joined. *)
let selective_widen_join_threshold ?(head:Tid.t option=None) (ladders : (int * word list) list) ~(need : Var.Set.t) (e1 : t) (e2 : t) : t =
  if Core.Set.is_empty need then join e1 e2
  else if WordEnv.equal e1.words WordEnv.bottom then e2
  else if WordEnv.equal e2.words WordEnv.bottom then e1
  else
    let ladder_for ws key =
      let extra =
        match head with
        | Some h ->
          let per = Cbat_landmarks.bounds_for_head h key in
          if List.is_empty per then Cbat_landmarks.bounds_for key else per
        | None -> Cbat_landmarks.bounds_for key
      in
      let extra = List.filter extra ~f:(fun w -> Word.bitwidth w = WordSet.bitwidth ws) in
      if List.is_empty extra then Option.value ~default:[]
        (List.Assoc.find ladders (WordSet.bitwidth ws) ~equal:Int.equal)
      else
        let max_extra = List.fold extra ~init:(List.hd_exn extra) ~f:(fun acc w -> if Word.compare w acc > 0 then w else acc) in
        [max_extra]
    in
    let words =
      let acc = ref WordEnv.top in
      WordEnv.fold e1.words ~init:() ~f:(fun ~key ~data:data_old () ->
        let idx = WordSet.bitwidth data_old in
        let data_new = WordEnv.find idx e2.words key in
        if WordSet.is_top data_new then ()
        else
          let data_res =
            if Core.Set.mem need (Var.base key) then
              WordSet.widen_join_threshold (ladder_for data_old key) data_old data_new
            else
              WordSet.join data_old data_new
          in
          if not (WordSet.is_top data_res) then
            acc := WordEnv.add !acc ~key ~data:data_res
      );
      !acc
    in
    let memories =
      (* Memory widen is needed whenever a cycled word var flows to an address; if any word needs widen, widen memory too, else join. *)
      MemEnv.widen_join_op (Mem.widen_join_threshold ladders) e1.memories e2.memories
    in
    { memories; words; frame = join_opt ~widen:true e1.frame e2.frame
    }

(* Landmark-directed extrapolation (Simon & King Listing 4) — per-var steps. *)
let selective_widen_extrapolate ?(head:Tid.t option=None) ~(need : Var.Set.t) ~(steps : int) (e1 : t) (e2 : t) : t =
  if Core.Set.is_empty need then join e1 e2
  else if WordEnv.equal e1.words WordEnv.bottom then e2
  else if WordEnv.equal e2.words WordEnv.bottom then e1
  else
    let words =
      let acc = ref WordEnv.top in
      WordEnv.fold e1.words ~init:() ~f:(fun ~key ~data:data_old () ->
        let idx = WordSet.bitwidth data_old in
        let data_new = WordEnv.find idx e2.words key in
        if WordSet.is_top data_new then ()
        else
          let data_res =
            if Core.Set.mem need (Var.base key) then
              match head with
              | Some h ->
                let entries = Cbat_landmarks.entries_for_head h key in
                let entries = List.filter entries ~f:(fun e -> Word.bitwidth e.Cbat_landmarks.bound = WordSet.bitwidth data_old) in
                (match entries with
                 | [] ->
                   if steps < 0 then WordSet.widen_join data_old data_new
                   else WordSet.extrapolate_steps ~steps data_old data_new
                 | _ ->
                   (* Listing 4: apply each landmark's dist as a per-bound translate.
                      When steps finite, the landmark path translates by dist*steps (rounded outward).
                      The landmark bound is the clamp; overflow -> infinite arm. *)
                   if steps < 0 then
                     (* No steps from lm_calc_steps -> fall through to widen_join (the
                        paper's Inf arm) *)
                     WordSet.widen_join data_old data_new
                   else
                     let width = WordSet.bitwidth data_old in
                     let lo' = List.filter entries ~f:(fun e -> not e.Cbat_landmarks.is_upper) in
                     let hi' = List.filter entries ~f:(fun e -> e.Cbat_landmarks.is_upper) in
                     let lo_base = match WordSet.min_elem data_new with Some w -> w | None -> Word.zero width in
                     let hi_base = match WordSet.max_elem data_new with Some w -> w | None -> Word.zero width in
                     let extrap_lo =
                       match lo' with
                       | _ :: _ ->
                         let min_dist = List.fold lo' ~init:(1 lsl 40)
                           ~f:(fun acc e -> match e.Cbat_landmarks.dist with
                               | Some d -> min acc d | None -> acc) in
                         let w_dist = Word.of_int ~width min_dist in
                         let w_steps = Word.of_int ~width steps in
                         let delta = Word.mul w_dist w_steps in
                         if Word.compare delta (Word.zero width) = 0 then lo_base
                         else
                           let v = Word.sub lo_base delta in
                           if Word.compare v lo_base > 0 then lo_base else v
                       | [] -> lo_base
                     in
                     let extrap_hi =
                       match hi' with
                       | _ :: _ ->
                         let max_dist = List.fold hi' ~init:0
                           ~f:(fun acc e -> match e.Cbat_landmarks.dist with
                               | Some d -> max acc d | None -> acc) in
                         let w_dist = Word.of_int ~width max_dist in
                         let w_steps = Word.of_int ~width steps in
                         let delta = Word.mul w_dist w_steps in
                         let v = Word.add hi_base delta in
                         if Word.compare v hi_base < 0 then
                           (* overflow -> infinite arm (Listing 4): word_max *)
                           Word.ones width
                         else v
                       | [] -> hi_base
                     in
                     let lo = if Word.compare extrap_lo lo_base > 0 then extrap_lo else lo_base in
                     let hi = if Word.compare extrap_hi hi_base < 0 then extrap_hi else hi_base in
                     if Word.compare lo hi > 0 then WordSet.widen_join data_old data_new
                     else WordSet.of_clp (Cbat_clp.interval ~width lo hi))
              | None ->
                if steps < 0 then WordSet.widen_join data_old data_new
                else WordSet.extrapolate_steps ~steps data_old data_new
            else
              WordSet.join data_old data_new
          in
          if not (WordSet.is_top data_res) then
            acc := WordEnv.add !acc ~key ~data:data_res
      );
      !acc
    in
    let memories = MemEnv.widen_join e1.memories e2.memories in
    { memories; words; frame = join_opt ~widen:true e1.frame e2.frame
    }

let selective_widen ~(need : Var.Set.t) (e1 : t) (e2 : t) : t =
  selective_widen_extrapolate ~need ~steps:(-1) e1 e2

let equal_need ~(need : Var.Set.t) (e1 : t) (e2 : t) : bool =
  if Core.Set.is_empty need then true
  else
    Core.Set.for_all need ~f:(fun v ->
      match Var.typ v with
      | Type.Imm w ->
          let ws1 = find_word w e1 v in
          let ws2 = find_word w e2 v in
          WordSet.equal ws1 ws2
      | Type.Mem _ | Type.Unk -> true)

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

(* P2d-1b (lane A) — Call-ABI abstraction of an abstract state (post-call, intra-procedural). *)
(* [top_non_preserved ~preserved env]: the caller-saved (non-preserved) words of [env] set to TOP — the shared tail of [call_abstraction] and [call_abstraction_frame]. *)
let top_non_preserved ~(preserved : Var.Set.t) (env : t) : WordEnv.t =
  WordEnv.fold env.words ~init:env.words
    ~f:(fun ~key ~data acc ->
      if Core.Set.exists preserved ~f:(fun p -> Var.same p key)
      then acc
      else WordEnv.add acc ~key ~data:(WordSet.top (WordSet.bitwidth data)))

let call_abstraction ~(preserved : Var.Set.t) (env : t) : t =
  { memories = MemEnv.top; words = top_non_preserved ~preserved env; frame = env.frame }

(* Hike addition (the call-abstraction precision lane — the fix for the whole-memory-top gap): like [call_abstraction], but the caller's OWN frame survives the call. *)
let call_abstraction_frame ~(preserved : Var.Set.t) ~(rsp : WordSet.t)
    ~(escape : WordSet.t list) (env : t) : t =
  let words' = top_non_preserved ~preserved env in
  let rsp_lo =
    match WordSet.min_elem rsp, WordSet.max_elem rsp with
    | Some lo, Some hi when Word.equal lo hi -> Some lo
    | _ -> None in
  let escape_ranges =
    match rsp_lo with
    | None -> None
    | Some _ ->
      let ranges = List.filter_map escape ~f:(fun ws ->
          if WordSet.is_top ws || WordSet.is_infinite ws then None
          else match WordSet.min_elem ws, WordSet.max_elem ws with
            | Some a, Some b -> Some (a, b)
            | _ -> None) in
      if List.length ranges = List.length escape then Some ranges
      else None in
  let memories =
    match rsp_lo, escape_ranges with
    | Some lo, Some ranges ->
      MemEnv.fold env.memories ~init:env.memories
        ~f:(fun ~key ~data acc ->
            MemEnv.add acc ~key
              ~data:(Mem.call_keep data ~keep_lo:lo ~escape:ranges))
    | _ -> MemEnv.top in
  { memories; words = words'; frame = env.frame }

