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

(* The VERSION-KEYED MEMO — one owner of the change-driven-cache
   discipline (architecture review 2026-09-02, candidate #2).

   THE DISCIPLINE (extracted verbatim from the two caches it used to be
   copy-pasted across — the walk memo [refine_hit] and the transfer memo
   [transfer_hit]; their snapshot twins were byte-identical):

   - STAMP: a memo entry records the read-set (the blocks whose
     solution states the computation read), each stamped with the
     block's VERSION at compute time.  The engine's [set] bumps a
     block's version ONLY under [not (AI.equal old new_val)], so an
     unchanged version is EXACTLY identity of the stored state — the
     O(1) form of the [AI.equal] key (the ticket-03 validity argument;
     [rc_versions] in [cbat_vsa] is the oracle).

   - VALIDITY: a stored entry is reusable iff every recorded
     (block, version) still matches — no block the computation read
     has changed state since.  Short-circuits on the first mismatch
     ([List.for_all]).

   - STALE-OVERWRITE: a stale entry is never invalidated by walking
     the table — it is simply never read again (validity fails), and
     the next recompute overwrites it.  No invalidation pass, no
     per-entry tombstones.

   WHY A MODULE (the review's locality argument): the F3 incident
   proved this is exactly the rule a caller gets wrong when it is
   duplicated — [precedes] was mistaken for containment and the join
   gate silently dropped keys.  One implementation, and the L2 walk
   schedule (the next consumer) inherits it tested instead of copying
   it a third time.

   THE SHAPE: functorized over the value module (the review's call —
   the two call sites pass plain module types, one variable each):
   the walk memo instantiates with [AI.t], the transfer memo with a
   pair (result, fired).  The entry record DECOMPOSES: the read-set is
   the MEMO's own business (stamped/validated here, invisible to the
   caller), the value type is what the cache is actually about.

   KEYS: two-level (block, jmp-or-target) — the shape both caches
   already had (the nested Tid.Map × Tid.Map).  A cache with another
   arity composes by nesting inside the value; the discipline is
   arity-independent. *)

open Core_kernel
open Bap.Std

(* The value type a cache memoizes.  Only [t] — values are never
   compared (stale entries are overwritten, not merged), so there is
   no [equal] and no lattice discipline here. *)
module type Value = sig
  type t
end

(* THE VERSION ORACLE IS THREADED, NOT FUNCTORIZED: every memo call
   site has the run context in hand ([rc] — the caller just built or
   is threading it), and the versions map MUTATES during the run
   (the engine's [set] bumps it per visit), so a functor-captured
   oracle would have to reach into mutable state to stay current.
   Threading [~version] (the ctx's [ver_of], partially applied) keeps
   the discipline pure and the context the single owner of state —
   the ARCH-3 lesson applied to the memo's own interface. *)
module Make (V : Value) = struct
  type value = V.t

  (* ONE entry: the stamped read-set + the memoized value.  The
     read-set is internal to the discipline — callers see only
     [value]. *)
  type entry = {
    e_reads : (Tid.t * int) list;
    e_value : value;
  }

  (* The table: outer key (the block) -> inner key (the jmp or the
      target) -> the entry.  Immutable Core.Map — the update returns
      the new table (the run context rebinds it), matching the
      previous rc_cache/rc_out_cache discipline. *)
  type t = entry Tid.Map.t Tid.Map.t

  let empty : t = Tid.Map.empty

  (* [valid ~version entry]: every recorded (block, version) still
      matches — no block the computation read has changed state since
      the entry was stamped. *)
  let valid ~(version : Tid.t -> int) (e : entry) : bool =
    List.for_all e.e_reads ~f:(fun (t, v) -> version t = v)

  (* [stamp ~version reads]: the version-stamped read-set of the
      computation that just finished (the caller's accumulated
      visited set). *)
  let stamp ~(version : Tid.t -> int) (reads : Tid.Set.t)
      : (Tid.t * int) list =
    Core.Set.to_list reads |> List.map ~f:(fun t -> (t, version t))

  (* [find ~version t outer inner]: the memoized value iff the entry
      exists AND is still valid; None on a miss or a stale entry (the
      stale entry is never removed here — it is simply never read
      again, and the next [add] overwrites it). *)
  let find ~(version : Tid.t -> int) (t : t) (outer : Tid.t)
      (inner : Tid.t) : value option =
    match Core.Map.find t outer with
    | None -> None
    | Some by_inner -> (
      match Core.Map.find by_inner inner with
      | None -> None
      | Some e when valid ~version e -> Some e.e_value
      | Some _ -> None)

  (* [add ~version t outer inner ~reads value]: the table with the
      entry recorded.  The caller passes the computation's read-set
      (its accumulated visited blocks); [add] stamps it here — the
      caller never builds the (tid, version) pairs itself. *)
  let add ~(version : Tid.t -> int) (t : t) (outer : Tid.t)
      (inner : Tid.t) ~(reads : Tid.Set.t) (value : value) : t =
    let e = { e_reads = stamp ~version reads; e_value = value } in
    Core.Map.set t ~key:outer
      ~data:(match Core.Map.find t outer with
          | None -> Tid.Map.singleton inner e
          | Some by_inner -> Core.Map.set by_inner ~key:inner ~data:e)
end
