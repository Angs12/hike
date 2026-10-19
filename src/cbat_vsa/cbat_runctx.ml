(* ************************************************************************* *)
(*  *)
(* Copyright (C) Draper Laboratory. Licensed under project LICENSE. *)
(*  *)
(* This file is provided under the license found in the LICENSE file in *)
(* the top-level directory of this project. *)
(*  *)
(* This work is funded in part by ONR/NAWC Contract N6833518C0107. Its *)
(* content does not necessarily reflect the position or policy of the US *)
(* Government and no official endorsement should be inferred. *)
(*  *)
(* ************************************************************************* *)


(* Per-run analysis context: static per-block facts and the versioned
   solution threaded through the engine. *)

open Core
open Bap.Std
open Graphlib.Std
module Utils = Cbat_vsa_utils
module AI = Cbat_ai_representation

(* A block's static call facts: the lanes a machine call reads and the SP
   version it reads. *)
type call_facts = {
  cf_lanes : var list;
  cf_sp : var;
}

(* Static block facts: the term, call lanes, and scalar input names. *)
type block_facts = {
  bf_term : blk term;
  bf_defs : def term list;
  (* Exact SSA lhs to its block-local statement position and definition.
     Backward scalar refinement follows this index; it does not replay
     unrelated scalar definitions. *)
  bf_def_index : (int * def term) Var.Map.t;
  bf_call_facts : call_facts;
  bf_live_ids : Int.Set.t;
}

type refine_ctx = {
  rc_ssa : bool;
  (* The run's convention facts (Hike_abi is the one home): the sp var
     the walk anchors on, the call-read lanes, and the
     word size behind every word lookup. *)
  rc_abi : Hike_abi.t;
  rc_synth : Hike_synth.table ref;
  rc_blocks : block_facts Tid.Map.t;
  (* Refined edge states for one source IN state, before target phis bind. *)
  rc_edges : (AI.t * AI.t Tid.Map.t) Tid.Map.t ref;
  (* The producer non-negativity oracle (the walk's signed rows): an
     expression whose every possible value has its sign bit clear.  The
     default proves nothing. *)
  rc_nonneg : env:AI.t -> exp -> bool;
  (* The solve's own widening-landmark state (Simon & King): fresh per
     [mk_rctx], never the process's. *)
  rc_landmarks : Cbat_landmarks.t;
  (* The run's sub-address lookup: a call-target word names a lifted
     sub of this program, or none — every address foreign.  The
     indirect call site's summary derivation reads it. *)
  rc_sub_lookup : int64 -> Tid.t option;
}

(* The block's call facts.  The program carries the SP restore of a
   call's pushed word itself. *)
let call_facts_of_block ~(abi : Hike_abi.t) (b : blk term) :
    call_facts =
  let machine_reads =
    Term.enum jmp_t b
    |> Seq.filter_map ~f:(fun j ->
           match Jmp.kind j with
           | Call _ when Hike_stack_model.machine_call j ->
             Some (Hike_stack_model.effects j).reads
           | _ -> None)
    |> Seq.concat_map ~f:Seq.of_list
    |> Seq.to_list
  in
  let is_sp v = Var.same v abi.Hike_abi.sp in
  let cf_lanes =
    List.filter machine_reads ~f:(fun v -> not (is_sp v))
    |> Var.Set.of_list
    |> Core.Set.to_list
  in
  let cf_sp =
    Option.value (List.find machine_reads ~f:is_sp) ~default:abi.Hike_abi.sp in
  { cf_lanes; cf_sp }

(* SSA construction gives every cross-block scalar its own phi. *)
let scalar_ssa ~synth s =
  let word v = match Var.typ v with Type.Imm _ -> true | _ -> false in
  let definitions = Term.enum blk_t s
    |> Seq.concat_map ~f:(fun b ->
        Seq.append (Term.enum def_t b |> Seq.map ~f:Def.lhs)
          (Term.enum phi_t b |> Seq.map ~f:Phi.lhs))
    |> Seq.filter ~f:word |> Seq.to_list in
  let result = Term.enum blk_t s |> Seq.for_all ~f:(fun b ->
      Term.has_attr b Hike_stack_model.ssa_tag)
  && List.exists definitions ~f:(fun v -> Var.index v > 0)
  && List.for_all definitions ~f:(fun v ->
      Var.index v > 0 || Hike_synth.is_temporary ~table:synth v)
  && List.length definitions = Set.length (Var.Set.of_list definitions) in
  result

(* The block's free inputs: reads with no prior local definition and no
   incoming phi.  Only the sub-entry has word inputs here (its index-0
   ABI arguments, seeded by the caller); a non-entry word input is an
   SSA construction error. *)
let local_inputs ~def_reads ~def_writes ~jmp_reads b =
  let phis = Term.enum phi_t b |> Seq.map ~f:Phi.lhs |> Seq.to_list
    |> Var.Set.of_list in
  let written, needed = Term.enum def_t b
    |> Seq.fold ~init:(phis, Var.Set.empty) ~f:(fun (written, needed) d ->
        (Set.union written (def_writes d),
         Set.union needed (Set.diff (def_reads d) written))) in
  Term.enum jmp_t b |> Seq.fold ~init:needed ~f:(fun needed j ->
      Set.union needed (Set.diff (jmp_reads j)
          (Set.union written (Hike_stack_model.writes (`Jmp j)))))

(* Only SSA block inputs participate in scalar fixpoint delivery. *)
let mk_rctx ~(abi : Hike_abi.t) ~def_reads ~def_writes ~phi_writes:_
    ~jmp_reads
    ~(synth : Hike_synth.table ref)
    ?(sub_lookup : int64 -> Tid.t option = fun _ -> None)
    (s : sub term) : refine_ctx =
  let ssa = scalar_ssa ~synth:!synth s in
  {
    rc_ssa = ssa;
    rc_edges = ref Tid.Map.empty;
    rc_nonneg = (fun ~env:_ _ -> false);
    rc_landmarks = Cbat_landmarks.create ();
    rc_abi = abi;
    rc_synth = synth;
    rc_sub_lookup = sub_lookup;
    rc_blocks =
      Term.enum blk_t s
      |> Seq.fold ~init:Tid.Map.empty ~f:(fun m b ->
          let defs = Term.enum def_t b |> Seq.to_list in
          let def_index =
            List.foldi defs ~init:Var.Map.empty ~f:(fun pos index d ->
                Map.set index ~key:(Def.lhs d) ~data:(pos, d)) in
          let inputs =
            if ssa then local_inputs ~def_reads ~def_writes ~jmp_reads b
            else Var.Set.empty in
          Core.Map.set m ~key:(Term.tid b)
            ~data:{
              bf_term = b;
              bf_defs = defs;
              bf_def_index = def_index;
              bf_call_facts = call_facts_of_block ~abi b;
              bf_live_ids = Cbat_var_id.intern_set
                  (Set.union inputs
                     (Term.enum phi_t b |> Seq.map ~f:Phi.lhs |> Seq.to_list
                      |> Var.Set.of_list));
            });
  }
