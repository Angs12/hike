(* The per-def KB value slot: one descriptor derives the domain, the
   property, and the getter/stamper from the payload's equal, inspect
   and empty.  A leaf library — the payloads come from both the
   production and the vendored sides, and neither owns the spelling. *)

open Bap.Std
open Bap_core_theory
open! Core

module KB = Bap_knowledge.Knowledge

type 'a t = {
  slot : (Theory.Value.cls, 'a) KB.slot;
  get : def term -> 'a;
  put : 'a -> def term -> def term;
}

(* The registered property (the registration IS the property). *)
let slot (s : 'a t) : (Theory.Value.cls, 'a) KB.slot = s.slot

(* The getter: reads the payload off the def's value. *)
let get (s : 'a t) (d : def term) : 'a = s.get d

(* The stamper: writes one payload onto one def. *)
let put (s : 'a t) (v : 'a) (d : def term) : def term = s.put v d

(* The reader/writer pair every descriptor shares: the census observer
   at the access, the payload on the def's value. *)
let accessors ~(get_bump : string) ~(put_bump : string)
    ~(bump : string -> unit)
    (slot : (Theory.Value.cls, 'a) KB.slot) : 'a t =
  { slot;
    get =
      (fun d ->
        bump get_bump;
        KB.Value.get slot (Def.value d));
    put =
      (fun v d ->
        bump put_bump;
        Def.with_value d (KB.Value.put slot (Def.value d) v)) }

(* A flat payload: [empty] the identity, [equal]/[inspect] the
   payload's own. *)
let flat ~(name : string) ~(get_bump : string) ~(put_bump : string)
    ~(bump : string -> unit) ~(empty : 'a) ~(equal : 'a -> 'a -> bool)
    ~(inspect : 'a -> Sexp.t) : 'a t =
  accessors ~get_bump ~put_bump ~bump
    (KB.Class.property ~package:"hike" Theory.Value.cls name
       (KB.Domain.flat ~inspect ~equal ~empty name))

(* An optional payload with a caller's join policy: two different
   payloads for one def resolve by [join] — a conflict error leaves
   the read to the KB, a coarsening answers its own sound merge. *)
let optional ~(name : string) ~(get_bump : string) ~(put_bump : string)
    ~(bump : string -> unit)
    ~(equal : 'p -> 'p -> bool)
    ~(join : 'p -> 'p -> ('p, KB.conflict) result)
    ~(inspect : 'p -> Sexp.t) : 'p option t =
  accessors ~get_bump ~put_bump ~bump
    (KB.Class.property ~package:"hike" Theory.Value.cls name
       (KB.Domain.optional ~inspect ~join ~equal name))
