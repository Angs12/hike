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

(* Cbat_vsa_utils: small shared utilities. The [relevant] tag is deleted
   (spec §2.1); every def is denoted. *)

exception NotImplemented of string

(* Raised by [not_implemented] without a [~top] fallback. *)

(* Placeholder degrading to [~top]. *)
let not_implemented ?(top : 'a option) component : 'a = match top with
  | None -> raise (NotImplemented component)
  | Some tp ->
    (* Log through Event.Log. *)
    Bap.Std.Event.Log.message Bap.Std.Event.Log.Warning
      ~section:"cbat_vsa"
      "not_implemented: %s (degrading to top)" component;
    tp

(* Max elements of an exact set. *)
let fin_set_size : int = 10

(* Integer division rounding up. *)
let cdiv (x : int) (y : int) : int = (x - 1)/y + 1

open !Core_kernel
open Bap.Std

let exn_on_err : ('a, Type.error) Result.t -> 'a = function
  | Ok e -> e
  | Error e -> raise (Type.Error.T e)

let rotate_list (l : 'a list) : 'a list =
  let l_r = List.rev l in
  match l_r with
  | [] -> []
  | hd::tl -> hd::(List.rev tl)
