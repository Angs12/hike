(* Connected components of the closed-interval-overlap graph: sort by
   (span.lo, span.hi, key); sweep with the running max hi; a member
   joins the open component when its lo <= that max — it then overlaps
   the member holding the max, whose lo is <= every later member's lo
   by the sort.  Members keep the sorted order inside their component;
   components ascend by their least lo. *)

val connected_components :
  key:('a -> 'a -> int) ->
  span:('a -> int64 * int64) ->
  'a list ->
  'a list list
(** The components of [items]; [items] may hold any member type.  For
    well-formed spans ([lo <= hi]) the components are the overlap
    graph's connected components — unique as sets. *)

val hull : span:('a -> int64 * int64) -> 'a list -> int64 * int64
(** The min-lo / max-hi span of [members]; [(0L, 0L)] for the empty
    list. *)
