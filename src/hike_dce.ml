(* Post-SSA dead-code elimination.  Only target flags and virtual
   temporaries are candidates: a term whose left side is a named
   non-flag value stays even when unread.  A candidate is removed only
   after a fixed point proves its left side has no remaining model
   read. *)

open Bap.Std
open Bap_core_theory

module Model = Hike_stack_model
module Abi = Hike_abi

let is_mem v = Model.is_mem v

let rhs_has_memory (d : def term) : bool =
  Model.reads_mem (Def.rhs d)
  || Core.Set.exists (Model.reads (`Def d)) ~f:is_mem

let lhs_kept ~(synth : Hike_synth.table) ~(abi : Abi.t)
    ~(target : Theory.Target.t) v : bool =
  let base = Var.base v in
  is_mem v
  || Model.is_call_arg synth v
  || Model.is_arg_slot synth v
  || Model.is_model_storage synth v
  || Hike_synth.is_address_var synth v
  || Model.is_window_var synth v
  || Abi.is_sp abi base
  || Abi.is_return_reg abi base
  || Abi.is_env_reg abi base
  || Base.List.exists (Abi.param_regs abi) ~f:(Var.same base)
  || Var.same base (Abi.pc target)

(* The narrow candidate set: target flags and virtual temporaries only. *)
let narrow_lhs ~synth ~abi ~target (v : var) : bool =
  (Var.is_virtual v || Abi.is_flag_reg abi (Var.base v))
  && not (lhs_kept ~synth ~abi ~target v)

let def_lhs d =
  match Core.Set.to_list (Model.writes (`Def d)) with
  | [ v ] -> v
  | _ -> failwith "Hike_dce: def has no single written var"

let phi_lhs p =
  match Core.Set.to_list (Model.writes (`Phi p)) with
  | [ v ] -> v
  | _ -> failwith "Hike_dce: phi has no single written var"

let def_candidate ~synth ~abi ~target (d : def term) : bool =
  narrow_lhs ~synth ~abi ~target (def_lhs d) && not (rhs_has_memory d)

let phi_candidate ~synth ~abi ~target (p : phi term) : bool =
  narrow_lhs ~synth ~abi ~target (phi_lhs p)

(* A use count per variable, over every model read in the sub.  Set
   semantics per term: a repeated variable within one term counts
   once, which can only keep a value alive longer. *)
let use_counts (sub : sub term) : int Var.Table.t =
  let uses : int Var.Table.t = Core.Hashtbl.create (module Var) in
  let bump v =
    Core.Hashtbl.update uses v ~f:(function Some n -> n + 1 | None -> 1)
  in
  let bump_set s = Core.Set.iter s ~f:bump in
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun b ->
         Term.enum def_t b
         |> Seq.iter ~f:(fun d -> bump_set (Model.reads (`Def d)));
         Term.enum phi_t b
         |> Seq.iter ~f:(fun p -> bump_set (Model.reads (`Phi p)));
         Term.enum jmp_t b
         |> Seq.iter ~f:(fun j -> bump_set (Model.reads (`Jmp j))));
  Term.enum arg_t sub
  |> Seq.iter ~f:(fun a -> bump_set (Model.reads (`Arg a)));
  uses

let decr_some uses s =
  Core.Set.iter s ~f:(fun v ->
      Core.Hashtbl.update uses v ~f:(function Some n -> max 0 (n - 1) | None -> 0))

(* The dead fixed point: remove every candidate whose left side has no
   remaining read, then subtract what the removed term read. *)
let dead_fixed_point ?(only = fun _ -> true) ~synth ~abi ~target
    (sub : sub term) =
  let uses = use_counts sub in
  let candidates : (var, [ `Def of def term | `Phi of phi term ]) Core.Hashtbl.t =
    Core.Hashtbl.create (module Var) in
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun b ->
         if only (Term.tid b) then begin
           Term.enum def_t b
           |> Seq.iter ~f:(fun d ->
                  if def_candidate ~synth ~abi ~target d then
                    Core.Hashtbl.set candidates ~key:(def_lhs d) ~data:(`Def d));
           Term.enum phi_t b
           |> Seq.iter ~f:(fun p ->
                  if phi_candidate ~synth ~abi ~target p then
                    Core.Hashtbl.set candidates ~key:(phi_lhs p) ~data:(`Phi p))
         end);
  let removed = ref [] in
  let changed = ref true in
  while !changed do
    changed := false;
    let dead =
      Core.Hashtbl.fold candidates ~init:[] ~f:(fun ~key:v ~data:c acc ->
          match Core.Hashtbl.find uses v with
          | Some n when n > 0 -> acc
          | _ -> (v, c) :: acc)
    in
    Base.List.iter dead ~f:(fun (v, c) ->
        Core.Hashtbl.remove candidates v;
        removed := c :: !removed;
        changed := true;
        match c with
        | `Def d -> decr_some uses (Model.reads (`Def d))
        | `Phi p -> decr_some uses (Model.reads (`Phi p)))
  done;
  let removed_defs =
    Base.List.filter_map !removed ~f:(function `Def d -> Some d | _ -> None)
  in
  let removed_phis =
    Base.List.filter_map !removed ~f:(function `Phi p -> Some p | _ -> None)
  in
  let dead =
    Base.List.fold removed_defs ~init:Var.Set.empty ~f:(fun s d ->
        Core.Set.add s (def_lhs d))
    |> fun s ->
    Base.List.fold removed_phis ~init:s ~f:(fun s p ->
        Core.Set.add s (phi_lhs p))
  in
  (removed_defs, removed_phis, dead)

let dce_sub ~(synth : Hike_synth.table) ~(target : Theory.Target.t)
    (sub : sub term) : sub term =
  if Seq.is_empty (Term.enum blk_t sub) then sub
  else
    let abi = Abi.of_target target in
    let removed_defs, removed_phis, dead =
      dead_fixed_point ~synth ~abi ~target sub
    in
    if Base.List.is_empty removed_defs && Base.List.is_empty removed_phis then
      sub
    else
      Term.map blk_t sub ~f:(fun b ->
          let b =
            Term.filter def_t b ~f:(fun d ->
                not (Core.Set.mem dead (def_lhs d)))
          in
          Term.filter phi_t b ~f:(fun p ->
              not (Core.Set.mem dead (phi_lhs p))))

(* The post-Finalize variant: candidates only in the created blocks, use
   counts over the whole sub.  Old blocks are never DCE'd again. *)
let dce_blocks ~(synth : Hike_synth.table) ~(target : Theory.Target.t)
    ~(blocks : Tid.Set.t) (sub : sub term) : sub term =
  if Core.Set.is_empty blocks then sub
  else
    let abi = Abi.of_target target in
    let removed_defs, removed_phis, dead =
      dead_fixed_point ~only:(fun tid -> Core.Set.mem blocks tid)
        ~synth ~abi ~target sub
    in
    if Base.List.is_empty removed_defs && Base.List.is_empty removed_phis then
      sub
    else
      Term.map blk_t sub ~f:(fun b ->
          if not (Core.Set.mem blocks (Term.tid b)) then b
          else
            let b =
              Term.filter def_t b ~f:(fun d ->
                  not (Core.Set.mem dead (def_lhs d)))
            in
            Term.filter phi_t b ~f:(fun p ->
                not (Core.Set.mem dead (phi_lhs p))))
