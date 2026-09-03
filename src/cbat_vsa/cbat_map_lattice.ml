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

module Map = Core_kernel.Map
module Option = Core_kernel.Option
module Sexp = Core_kernel.Sexp
module Sexpable = Core_kernel.Sexpable
module Fn = Core_kernel.Fn
module Value = Bap.Std.Value
module Lattice = Cbat_lattice_intf

(* Finite map onto a lattice; unmapped keys read the default. *)

module type S_indexed = sig

  module Key : Sexpable.S
  module Val : Lattice.S_indexed

  type t
  type idx

  include Lattice.S_indexed with type t := t and type idx := idx

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
  module Val : Lattice.S_indexed

  type t

  include Lattice.S with type t := t

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

(* Parameterized by the map implementation. *)
module Make_indexed_from_map
    (K : Map.Key)
    (M : Map.S with type Key.t = K.t)
    (L : Lattice.S_indexed)
= struct

  module Key = K
  module Val = L

  type map = L.t M.t
  type t = map option
  type idx = L.idx

  let top : t = Some M.empty
  let bottom : t = None

  let lift : (L.t M.t -> L.t M.t) -> t -> t = Fn.flip Option.(>>|)

  let lift_meet f = Option.map2 ~f

  let lift_join (f : map -> map -> map) (t1 : t) (t2 : t) : t =
    match t1, t2 with
    | Some m1, Some m2 -> Some (f m1 m2)
    | Some m1, None -> Some m1
    | None, Some m2 -> Some m2
    | None, None -> None

  let meet' (m1 : map) (m2 : map) : map =
    (* One-sided keys meet the other side's default. *)
    let mFunc ~key:_ vs = match vs with
      | `Left v1 -> Some v1
      | `Right v2 -> Some v2
      | `Both (v1,v2) -> Some (L.meet v1 v2)
    in
    Map.merge m1 m2 ~f:mFunc

  let meet : t -> t -> t = lift_meet meet'

  let join' ljoin (m1 : map) (m2 : map) : map =
    (* Fold the smaller side. *)
    if Map.length m1 < Map.length m2 then
      Map.fold m1 ~init:M.empty ~f:(fun ~key ~data acc ->
        match Map.find m2 key with
        | Some d2 -> Map.set acc ~key ~data:(ljoin data d2)
        | None -> acc)
    else
      Map.fold m2 ~init:M.empty ~f:(fun ~key ~data acc ->
        match Map.find m1 key with
        | Some d1 -> Map.set acc ~key ~data:(ljoin d1 data)
        | None -> acc)

  let join : t -> t -> t = lift_join (join' L.join)
  let widen_join = lift_join (join' L.widen_join)
  (* Widening with a caller-supplied per-key operator. *)

  let op_add op (m : map) ~key:key ~data:data : t =
    let idx = L.get_idx data in
    let old_data = Option.value ~default:(L.top idx) (Map.find m key) in
    Option.return @@ Map.set m ~key ~data:(op data old_data)

  let lift_add op : t -> key:Key.t -> data:Val.t -> t =
    let default = fun ~key:_ ~data:_ -> None in
    Option.value_map ~default ~f:(op_add op)

  let join_add : t -> key:Key.t -> data:Val.t -> t = lift_add L.join
  let meet_add = lift_add L.meet
  let add = lift_add (fun x _ -> x)

  let find' (idx : idx) (m : map) (k : K.t) : L.t =
    Option.value ~default:(L.top idx) (Map.find m k)

  let find idx (t : t) (k : K.t) : L.t =
    Option.value_map t ~default:(L.bottom idx)
      ~f:(fun m -> find' idx m k)

  (* Enumerate stored bindings. *)
  let fold (t : t) ~init ~f =
    Option.value_map t ~default:init ~f:(fun m ->
      Map.fold m ~init ~f:(fun ~key ~data acc -> f ~key ~data acc))

  (* No stored tops. *)
  let canonize' (m : map) : map = m
  let canonize : t -> t = Fn.id

  (* Shared fold for [precedes'] and [equal']. *)
  let fold2_both
      (branch : [ `Left of L.t | `Right of L.t | `Both of L.t * L.t ] -> bool)
      (m1 : map) (m2 : map) : bool =
    Map.fold2 m1 m2 ~init:true ~f:(fun ~key:_ ~data cur -> cur && branch data)

  let precedes' (m1 : map) (m2 : map) : bool =
    fold2_both (function
        | `Both (a, b) -> L.precedes a b
        | `Left _ -> true (* missing key reads top *)
        | `Right b -> L.equal b (L.top (L.get_idx b)))
      m1 m2

  let precedes (t1 : t) (t2 : t) : bool =
    Option.value_map t1 ~default:true
      ~f:(fun m1 -> Option.value_map t2 ~default:false ~f:(precedes' m1))

  let equal' (e1 : map) (e2 : map) : bool =
    fold2_both (function
        | `Both (a, b) -> L.equal a b
        | `Left a -> L.equal a (L.top (L.get_idx a))
        | `Right b -> L.equal b (L.top (L.get_idx b)))
      e1 e2

  let equal (t1 : t) (t2 : t) : bool =
    Option.value_map t1 ~default:(not @@ Option.is_some t2)
      ~f:(fun m1 -> Option.value_map t2 ~default:false ~f:(equal' m1))

end

module Make_indexed(K : Map.Key) = Make_indexed_from_map(K)(Map.Make(K))

module type Key_val = sig
  include Map.Key
  include Value.S with type t := t
end

module Make_indexed_val(K : Key_val)(L : Lattice.S_indexed_val) = struct

  module M = Map.Make_binable(K)

  module Base = Make_indexed_from_map(K)(M)(L)

  module Key = K
  module Val = L

  type t = L.t M.t Option.t [@@deriving bin_io, compare, sexp]

  include (Base : S
           with type t := t
            and module Key := Key
            and module Val := Val)

  let pp ppf m = match m with
    | _ when equal m top-> Format.fprintf ppf "unknown"
    | None -> Format.fprintf ppf "unreachable"
    | Some m ->
      Format.fprintf ppf "@[<2>{@ ";
      Map.iteri m ~f:begin fun ~key ~data ->
        Format.fprintf ppf "@[<hov 1>[%a@ -> %a]@]@ "
          K.pp key
          L.pp data
      end;
      Format.fprintf ppf "}@]"

end


module Make (K : Map.Key)(L : Lattice.S) = struct
  module IL = Lattice.Free_index(L)
  include Make_indexed(K)(IL)
end

module Make_val (K : Key_val)(L : Lattice.S_val) = struct
  module IL = Lattice.Free_index_val(L)
  include Make_indexed_val(K)(IL)
end
