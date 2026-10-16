open Bap.Std

(** Resolve carried FS origins to the owning TLS/TCB runtime storage. *)
val rewrite_program :
  addr_bits:int -> tls:Hike_spec.tls_spec option ->
  denote:Hike_kb.denote -> program term -> program term
