(* The canary-strip pass. *)
open Bap.Std

  (** [strip_sub ~facts ~names sub] removes every proven canary
      composition; an unrecognized composition is the identity. *)
  val strip_sub :
    facts:Hike_kb.facts -> names:string Tid.Map.t -> sub term -> sub term
