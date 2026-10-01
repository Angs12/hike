(* Indirect-target resolution. *)
open Bap.Std

  (** A singleton whose word names a lifted sub resolves ([Some tid]);
      a bounded multi-target set, a foreign singleton, and TOP take
      the pointer call ([None]). *)
  val resolve_target :
    lookup:(int64 -> Tid.t option) -> Cbat_vsa.WordSet.t -> Tid.t option

  (** The run's name table: one symtab lookup per address. *)
  val symtab_lookup :
    symtab:Symtab.t option ->
    table:Tid.t Core.String.Map.t -> addr_bits:int -> int64 -> Tid.t option

  (** The sub-name table the lookup reads. *)
  val name_table_of : program term -> Tid.t Core.String.Map.t
