(* The per-def runtime origin: the origin ADT value the solve computed
   for the def, stamped at the solve boundary and read through the
   seam.  Absence means the def is outside the analysis boundary —
   minted after it, or its sub did not converge — and reads Abs. *)

include Core
open Bap.Std
open Bap_core_theory

module AI = Cbat_ai_representation
module WordSet = Cbat_clp_set_composite
module Origin = Hike_origin

module KB = Bap_knowledge.Knowledge

type KB.conflict += Def_origin_conflict

let () =
  KB.Conflict.register_printer (function
    | Def_origin_conflict ->
      Some
        "hike: def-origin conflict: two different origins were stamped for one def"
    | _ -> None)

(* Two different origins for one def coarsen to Abs: the absolute
   world is the sound join. *)
let def_origin_domain : Origin.t option KB.Domain.t =
  KB.Domain.optional
    ~inspect:(fun _ -> Sexp.Atom "hike:def-origin")
    ~join:(fun a b ->
        if Origin.equal a b then Ok a else Ok Origin.Abs)
    ~equal:Origin.equal
    "hike:def-origin"

let def_origin_slot : (Theory.Value.cls, Origin.t option) KB.slot =
  KB.Class.property ~package:"hike" Theory.Value.cls "hike-def-origin"
    def_origin_domain

let def_origin (d : def term) : Origin.t option =
  KB.Value.get def_origin_slot (Def.value d)

(* The def's stamped origin: its value's own origin, derived from the
   offset bands; an absolute or band-spanning value reads Abs. *)
let origin_of_def_value (v : WordSet.t) : Origin.t =
  match WordSet.origin v with
  | Some o -> o
  | None -> Origin.Abs

(* The stamp sweep's per-def step: the after-state carries the def's
   value; the origin reads off it. *)
let stamp_origin (d : def term) (after : AI.t) : def term =
  let width =
    match Var.typ (Def.lhs d) with
    | Type.Imm n -> n
    | _ -> 64
  in
  let v = AI.find_word width after (Def.lhs d) in
  let o = origin_of_def_value v in
  Def.with_value d (KB.Value.put def_origin_slot (Def.value d) (Some o))
