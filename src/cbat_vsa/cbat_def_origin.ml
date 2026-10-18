(* The per-def runtime origin: the origin ADT value the solve computed
   for the def, stamped at the solve boundary and read through the
   seam.  Absence means the def is outside the analysis boundary —
   minted after it, or its sub did not converge — and reads no origin. *)

include Core
open Bap.Std
open Bap_core_theory

module AI = Cbat_ai_representation
module WordSet = Cbat_clp_set_composite
module Origin = Hike_origin
let denote_imm_exp = Cbat_transfer.denote_imm_exp

(* The memory node's address expression, if the rhs reads or writes
   memory: the address the access lands at — the routing fact. *)
let mem_addr_of (e : exp) : exp option =
  let vis =
    object
      inherit [ exp option ] Exp.visitor
      method! visit_load ~mem:_ ~addr _ _ acc =
        match acc with Some _ -> acc | None -> Some addr
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

(* Two different origins for one def coarsen to no origin: the plain
   world is the sound join. *)
let def_origin_d : Origin.t option option Hike_def_slot.t =
  Hike_def_slot.optional ~name:"hike-def-origin"
    ~inspect:(fun _ -> Sexp.Atom "hike:def-origin")
    ~join:(fun a b ->
        if Option.equal Origin.equal a b then Ok a else Ok None)
    ~equal:(Option.equal Origin.equal)
    ~get_bump:"" ~put_bump:"" ~bump:(fun _ -> ())

let def_origin (d : def term) : Origin.t option =
  Option.join (Hike_def_slot.get def_origin_d d)

(* Writes the origin onto the def (the fixture seam's writer). *)
let with_origin (o : Origin.t) (d : def term) : def term =
  Hike_def_slot.put def_origin_d (Some (Some o)) d

(* The def's stamped origin: its value's own origin; a mixed or plain
   value reads no origin, the sound fallback. *)
let origin_of_def_value (v : WordSet.t) : Origin.t option = WordSet.origin v

(* The stamp sweep's per-def step: the routed origin is the memory
   node's ADDRESS (where the traffic lands, for a load and a store
   alike); a non-memory def's is its value's. *)
let stamp_origin ~(synth : Hike_synth.table) ~(before : AI.t)
    (d : def term) (after : AI.t) : def term =
  let o =
    match mem_addr_of (Def.rhs d) with
    | Some addr -> (
        match denote_imm_exp ~synth addr before with
        | Ok ws -> origin_of_def_value ws
        | Error _ -> None)
    | None ->
      let width =
        match Var.typ (Def.lhs d) with
        | Type.Imm n -> n
        | _ -> 64
      in
      origin_of_def_value (AI.find_word width after (Def.lhs d))
  in
  Hike_def_slot.put def_origin_d (Some o) d
