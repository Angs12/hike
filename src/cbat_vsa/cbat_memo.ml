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

(* Version-keyed walk memo. Entries stamp the read-set with block versions; a stored entry is reusable while every stamped version still matches. Stale entries are overwritten, never invalidated. *)

open Core_kernel
open Bap.Std
module AI = Cbat_ai_representation

#ifdef VSA_DEBUG
(* Hit accounting, compiled out of production. *)
let lookups = ref 0
let hits = ref 0
let stores = ref 0
let stale = ref 0
let empty_lookups = ref 0
let reset_stats () =
  lookups := 0; hits := 0; stores := 0; stale := 0; empty_lookups := 0
#endif

type value = AI.t

  (* Stamped read-set plus value. *)
  type entry = {
    e_reads : (Tid.t * int) list;
    e_value : value;
  }

  (* Outer key is the block, inner key the jmp or target. *)
  type t = entry Tid.Map.t Tid.Map.t

  let empty : t = Tid.Map.empty

  (* True when no recorded block changed state. *)
  let valid ~(version : Tid.t -> int) (e : entry) : bool =
    List.for_all e.e_reads ~f:(fun (t, v) -> version t = v)

  (* Stamp a finished computation's read-set. *)
  let stamp ~(version : Tid.t -> int) (reads : Tid.Set.t)
      : (Tid.t * int) list =
    Core.Set.to_list reads |> List.map ~f:(fun t -> (t, version t))

  (* Value of a live entry, if any. *)
  let find ~(version : Tid.t -> int) (t : t) (outer : Tid.t)
      (inner : Tid.t) : value option =
#ifdef VSA_DEBUG
    incr lookups;
    if Core.Map.is_empty t then incr empty_lookups;
#endif
    match Core.Map.find t outer with
    | None -> None
    | Some by_inner -> (
      match Core.Map.find by_inner inner with
      | None -> None
      | Some e when valid ~version e ->
#ifdef VSA_DEBUG
        incr hits;
#endif
        Some e.e_value
      | Some _ ->
#ifdef VSA_DEBUG
        incr stale;
#endif
        None)

  (* Record a value with its read-set. *)
  let add ~(version : Tid.t -> int) (t : t) (outer : Tid.t)
      (inner : Tid.t) ~(reads : Tid.Set.t) (value : value) : t =
#ifdef VSA_DEBUG
    incr stores;
#endif
    let e = { e_reads = stamp ~version reads; e_value = value } in
    Core.Map.set t ~key:outer
      ~data:(match Core.Map.find t outer with
          | None -> Tid.Map.singleton inner e
          | Some by_inner -> Core.Map.set by_inner ~key:inner ~data:e)

