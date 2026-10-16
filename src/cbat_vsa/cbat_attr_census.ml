(* Attribution census.  Keys name the mechanism: [unbounded.stack.*] /
   [ld.top.*] for the top-address roots, [blind.*] for the bit-reading
   op, [b65p.shape.*] for the band shapes, [call.frame.*] for the
   call-clamp arms, [band.*] for the backward rows, [bottomskip.*] for
   the dead-edge visits. *)

#ifdef VSA_DEBUG
include Cbat_census.Make (struct let prefix = "hike-attr-census" end)
#endif
