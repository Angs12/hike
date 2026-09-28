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
let denote_imm_exp = Cbat_transfer.denote_imm_exp

(* The store's address expression, if the rhs holds a store. *)
let store_addr_of (e : exp) : exp option =
  let vis =
    object
      inherit [ exp option ] Exp.visitor
      method! visit_store ~mem:_ ~addr ~exp:_ _ _ acc =
        match acc with Some _ -> acc | None -> Some addr
    end
  in
  vis#visit_exp e None

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

(* Writes the origin onto the def (the fixture seam's writer). *)
let with_origin (o : Origin.t) (d : def term) : def term =
  Def.with_value d (KB.Value.put def_origin_slot (Def.value d) (Some o))

(* The def's stamped origin: its value's own (band-refined) origin.
   An absolute or band-spanning value reads Abs. *)
let origin_of_def_value (v : WordSet.t) : Origin.t =
  match WordSet.origin v with
  | Some o -> o
  | None -> Origin.Abs

(* The stamp sweep's per-def step: the after-state carries the def's
   value; the origin reads off it. *)
let stamp_origin ~(before : AI.t) (d : def term) (after : AI.t) : def term =
  (* A word def's origin is its value's; a store's is its ADDRESS's —
     where the traffic lands. *)
  match store_addr_of (Def.rhs d) with
  | Some addr ->
    let o =
      match denote_imm_exp addr before with
      | Ok ws -> origin_of_def_value ws
      | Error _ -> Origin.Abs
    in
    Def.with_value d (KB.Value.put def_origin_slot (Def.value d) (Some o))
  | None ->
    let width =
      match Var.typ (Def.lhs d) with
      | Type.Imm n -> n
      | _ -> 64
    in
    let v = AI.find_word width after (Def.lhs d) in
    let o = origin_of_def_value v in
    Def.with_value d (KB.Value.put def_origin_slot (Def.value d) (Some o))
