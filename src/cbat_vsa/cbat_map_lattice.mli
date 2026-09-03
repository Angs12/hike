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

open Core_kernel
open Bap.Std

(* Finite map onto a lattice; unmapped keys read the default. *)

module type S_indexed = sig

  module Key : Sexpable.S
  module Val : Cbat_lattice_intf.S_indexed

  type t
  type idx

  include Cbat_lattice_intf.S_indexed with type t := t and type idx := idx

  (* Meet the new value into the key. *)
  val meet_add : t -> key:Key.t -> data:Val.t -> t
  (* Join the new value into the key. *)
  val join_add : t -> key:Key.t -> data:Val.t -> t
  (* Overwrite the key. *)
  val add : t -> key:Key.t -> data:Val.t -> t

  (* Read a key; unmapped keys read the default. *)
  val find : Val.idx -> t -> Key.t -> Val.t

end

module type S = sig
  module Key : Sexpable.S
  module Val : Cbat_lattice_intf.S_indexed

  type t

  include Cbat_lattice_intf.S with type t := t

  (* Meet the new value into the key. *)
  val meet_add : t -> key:Key.t -> data:Val.t -> t
  (* Join the new value into the key. *)
  val join_add : t -> key:Key.t -> data:Val.t -> t
  (* Overwrite the key. *)
  val add : t -> key:Key.t -> data:Val.t -> t

  (* Read a key; unmapped keys read the default. *)
  val find : Val.idx -> t -> Key.t -> Val.t

  (* Fold stored bindings. *)
  val fold : t -> init:'a -> f:(key:Key.t -> data:Val.t -> 'a -> 'a) -> 'a
end

module type S_indexed_val = sig
  type t
  module Key : Value.S
  include S_indexed with type t := t and module Key := Key
  include Value.S with type t := t
end

module type S_val = sig
  type t
  module Key : Value.S
  include S with type t := t and module Key := Key
  include Value.S with type t := t
end

module type Key_val = sig
  include Map.Key
  include Value.S with type t := t
end

module Make_indexed_val(K : Key_val)(L : Cbat_lattice_intf.S_indexed_val) : S_val
  with module Key = K and module Val = L

module Make_indexed(K : Map.Key)(L : Cbat_lattice_intf.S_indexed) : S
  with module Key = K and module Val = L

module Make_val(K : Key_val)(L : Cbat_lattice_intf.S_val) : S_val
  with module Key = K and module Val = Cbat_lattice_intf.Free_index_val(L)

module Make(K : Map.Key)(L : Cbat_lattice_intf.S) : S
  with module Key = K and module Val = Cbat_lattice_intf.Free_index(L)
