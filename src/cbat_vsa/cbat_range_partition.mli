(* The general range partition: connected components of the
   closed-interval-overlap graph over arbitrary items, each component
   carrying the hull of its members' spans and the side's class
   decision.  One engine serves every range kind — a side supplies how
   to read an item's interval and how to decide a component's class;
   the traversal, the hull, and the component record are the engine's. *)

(* One partition component: the members in the engine's sweep order,
   their hull (min lo / max hi of the members' spans), and the class
   the side's hook decided. *)
type ('item, 'cls) component = {
  hull : int64 * int64;
  members : 'item list;
  class_ : 'cls;
}

val partition :
  key:('item -> 'item -> int) ->
  span:('item -> int64 * int64) ->
  classify:(hull:(int64 * int64) -> 'item list -> 'cls) ->
  'item list ->
  ('item, 'cls) component list
(** The components of [items], ascending by their least lo.  The
    traversal is the [Cbat_interval] sweep — sort by (lo, hi, key); a
    member joins the open component when its lo is at most the running
    max hi — and each hull is [Cbat_interval.hull] of the members.
    [classify] is total: it decides every component. *)
