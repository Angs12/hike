(* KB operation census.  Keys are [<slot>.<get|put>] for every hike KB
   slot, [seam.query.def] / [seam.query.nodef] for the denotation seam,
   and [domain.*] for the domain callbacks the KB invokes on a put. *)

#ifdef VSA_DEBUG
include Cbat_census.Make (struct let prefix = "hike-kb-census" end)
#endif
