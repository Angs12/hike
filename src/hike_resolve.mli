(* Indirect-target resolution. *)
open Bap.Std

  (** A singleton whose word names a lifted sub resolves ([Some tid]);
      a bounded multi-target set, a foreign singleton, and TOP take
      the pointer call ([None]). *)
  val resolve_target :
    lookup:(int64 -> Tid.t option) -> Cbat_vsa.WordSet.t -> Tid.t option
