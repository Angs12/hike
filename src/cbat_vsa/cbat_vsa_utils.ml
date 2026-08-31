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

(* Utility functions specific to this project but not associated with any particular piece of functionality. *)

exception NotImplemented of string

(* [NotImplemented]: raised only by [not_implemented] when no ~top fallback value is supplied (there is nothing else to return). The production call sites always pass ~top, so the raise is a development aid. *)

(* Call as a placeholder where a piece of code has not been written yet. *)
let not_implemented ?(top : 'a option) component : 'a = match top with
  | None -> raise (NotImplemented component)
  | Some tp ->
    Bap.Std.Event.Log.message Bap.Std.Event.Log.Warning
      ~section:"cbat_vsa"
      "not_implemented: %s (degrading to top)" component;
    Format.eprintf "hike: cbat_vsa: not_implemented %s (degrading to top)@."
      component;
    tp

(* Determines the maximum number of elements in an exact set abstraction. *)
let fin_set_size : int = 10

(* implements integer division rounding upwards *)
let cdiv (x : int) (y : int) : int = (x - 1)/y + 1

open !Core_kernel
open Bap.Std

(* Relevance restriction (user design, ora-4, reworked per ora-5 / P2d-1b, and the 2026-08-10 simplification): a per-def Unit- payload tag. *)

(* P2d-1b (lane A) — the per-def relevance tag (Unit payload; the uuid is fresh and distinct from every other tag in the library). The former [back_edge]/[do_widen] neighbours are gone: the WTO fixpoint computes its widening points from the WTO head set, so the back-edge labelling pass was deleted. *)
let relevant = Value.Tag.register (module Unit)
    ~name:"relevant"
    ~uuid:"58a2e009-3d14-4c7d-ba75-42f9de98dc30"

let exn_on_err : ('a, Type.error) Result.t -> 'a = function
  | Ok e -> e
  | Error e -> raise (Type.Error.T e)

let rotate_list (l : 'a list) : 'a list =
  let l_r = List.rev l in
  match l_r with
  | [] -> []
  | hd::tl -> hd::(List.rev tl)
