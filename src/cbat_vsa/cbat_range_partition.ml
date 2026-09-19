(* The general range partition: the sweep traversal, the per-component
   hull, and the classification hook over arbitrary interval-keyed
   items (see the .mli for the sweep invariant). *)

type ('item, 'cls) component = {
  hull : int64 * int64;
  members : 'item list;
  class_ : 'cls;
}

let partition ~(key : 'item -> 'item -> int)
    ~(span : 'item -> int64 * int64)
    ~(classify : hull:(int64 * int64) -> 'item list -> 'cls)
    (items : 'item list) : ('item, 'cls) component list =
  Cbat_interval.connected_components ~key ~span items
  |> List.map (fun members ->
         let hull = Cbat_interval.hull ~span members in
         { hull; members; class_ = classify ~hull members })
