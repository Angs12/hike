(* The VSA: the in-place-solving solver and the def-origin stamp.  The
   worklist owns discovery, resolution and the builder; this module is
   the solver seam.  A site materialization installs into the SAME solve
   through [Cbat_vsa.static_graph_vsa]'s [materialize_transfer] hook: no
   restart, no rebuilt context and no wake. *)

open Bap.Std
open Bap_core_theory
module Vsa = Cbat_vsa
module Def_origin = Cbat_vsa.Def_origin
module Model = Hike_stack_model

let set_addr_bits (n : int) : unit = Vsa.set_addr_bits n

(* Every analysis entry self-arms the address width from the target it
   carries — no cross-pass init order exists. *)
let self_arm (target : Theory.Target.t) : unit =
  set_addr_bits (Bap_core_theory.Theory.Target.data_addr_size target)

type section_image = Vsa.section_image = {
  img_lo : int64;
  img_hi : int64;
  img_bytes : Bytes.t;
  img_slots : Core.Int64.Set.t;
}

(* The per-sub written-register summary: every def whose lhs base is a
   persistent register; [Var.base] normalizes partial defs. *)
let written_regs_of_sub ~(synth : Hike_synth.table) (sub : sub term) : Var.Set.t =
  Term.enum blk_t sub
  |> Seq.concat_map ~f:(Term.enum def_t)
  |> Seq.fold ~init:Var.Set.empty ~f:(fun acc d ->
      let lhs = Def.lhs d in
      match Var.typ (Var.base lhs) with
      | Type.Imm _ when not (Hike_synth.is_temporary ~table:synth lhs) ->
        Core.Set.add acc (Var.base lhs)
      | _ -> acc)

type lookup_fn = int64 -> Tid.t option

(* The site materializer seam: the worklist owns enumeration/validation
   and returns a complete transfer; VSA installs and delivers it in the
   current source fan-out. *)
type materialize_transfer = Vsa.materialize_transfer

(* A converged solve: the solution the worklist resolves from, the table
   its replay grew, and the persisted state the next phase reuses. *)
type solution = {
  sol : Vsa.vsa_sol;
  synth : Hike_synth.table;
  state : Vsa.run_state;
  sub : sub term;
}

type outcome = Solved of solution

(* Edge-dirty blocks keep their incoming state; the solve starts from
   their successors, which replay the changed terms.  The entry keeps the
   ABI seed. *)
let warm_seed ~abi ~sub ~woken ?old sol =
  let entry = Base.Option.map (Vsa.entry_block_of sub) ~f:Term.tid in
  let initial = Vsa.init_sol ~abi sub in
  (* A block the old sub did not have is new: its pre-SSA values cannot
     survive the rewrite, so its seed is bottom and the normal fan-out
     delivers its first state. *)
  let new_block b =
    match old with
    | None -> false
    | Some old -> Option.is_none (Term.find blk_t old b) in
  let seed = Graphlib.Std.Solution.enum sol
    |> Seq.filter ~f:(fun (b, _) ->
        Option.is_some (Term.find blk_t sub b))
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m (b, v) ->
        Core.Map.set m ~key:b ~data:(if new_block b then Vsa.AI.bottom else v)) in
  let seed = match entry with
    | Some b when Core.Set.mem woken b ->
      Core.Map.set seed ~key:b ~data:(Graphlib.Std.Solution.get initial b)
    | _ -> seed in
  (* A block absent from the seed is new (or unreachable): its pre-state
     is bottom, never the old default. *)
  let seed = Graphlib.Std.Solution.create seed Vsa.AI.bottom in
  (seed, woken)

(* One solve pass.  A site materialization installs into the same
   [run_state] and its new edges are delivered by the current fan-out. *)
let solve ?state ?materialize_transfer
    (target : Theory.Target.t) ~(lookup : lookup_fn)
    ~(images : Vsa.section_image list)
    ~(callee : Tid.t -> Vsa.Call_effects.callee)
    ~(foreign_slots : Core.Int64.Set.t) ~(sub : sub term)
    ~(resolved : Tid.Set.t Tid.Map.t)
    ~(synth : Hike_synth.table) ~(seed : Vsa.vsa_sol option)
    ~(wake : Tid.Set.t) : outcome =
  self_arm target;
  Vsa.reset_memos ();
  let abi = Hike_abi.of_target target in
  let synth = ref synth in
  let init = Base.Option.value seed ~default:(Vsa.init_sol ~abi sub) in
  let sol, state =
    Vsa.with_images images (fun () ->
        Vsa.static_graph_vsa ~abi ~synth
          ~def_reads:(fun d -> Model.reads (`Def d))
          ~def_writes:(fun d -> Model.writes (`Def d))
          ~phi_reads:(fun p -> Model.reads (`Phi p))
          ~phi_writes:(fun p -> Model.writes (`Phi p))
          ~jmp_reads:(fun j ->
              Core.Set.union (Model.reads (`Jmp j)) (Model.writes (`Jmp j)))
          ~callee ~resolved ~sub_lookup:lookup ~wake ?state
          ?materialize_transfer sub init)
  in
  Solved
    { sol;
      synth = Vsa.state_synth state;
      state;
      sub = Vsa.state_sub state }

(* The boundary stamp reads image-backed loads, so it brackets the same
   images as the solve. *)
let stamp ~(images : Vsa.section_image list) ~(synth : Hike_synth.table)
    ~(sol : Vsa.vsa_sol) (sub : sub term) =
  Vsa.with_images images (fun () -> Vsa.stamp_envs_of_sol ~synth ~sol sub)

(* The construction-time normalization seam used by the worklist on the
   initial body and on a batch's created blocks. *)
let normalize_round ~synth sub = Vsa.normalize_round_with_synth ~synth sub
