(* The dead-def sweep: plain liveness over the model's read sets.  The
   roots are every jump's reads — its operand expressions and the kind's
   ABI boundary (a ret consumes the return registers and SP; a call the
   parameter registers, the ABI return registers the call produces, and
   SP).  A def or phi is live iff its lhs is read by a live node, to a
   fixpoint.  Everything unmarked leaves — no per-var keep arms. *)
open Bap.Std
open Bap.Std.Bil.Types
module Abi = Hike_abi
module Model = Hike_stack_model

let dce ~(target : Bap_core_theory.Theory.Target.t) (sub : sub term) :
    sub term =
  let abi = Abi.of_target target in
  (* A mapped-intrinsic sub's body is the emitter's interface. *)
  if Model.is_intrinsic sub then sub
  else
    let nodes =
      Term.enum blk_t sub
      |> Seq.concat_map ~f:(fun b ->
             Seq.append
               (Term.enum def_t b
               |> Seq.map ~f:(fun d ->
                      (Term.tid d, Def.lhs d, Model.def_reads d)))
               (Term.enum phi_t b
               |> Seq.map ~f:(fun p ->
                      (Term.tid p, Phi.lhs p, Model.phi_reads p))))
      |> Seq.to_list
    in
    let exact_roots = ref Var.Set.empty in
    let base_roots = ref Var.Set.empty in
    Term.enum blk_t sub
    |> Seq.iter ~f:(fun b ->
           Term.enum jmp_t b
           |> Seq.iter ~f:(fun j ->
               exact_roots :=
                 Core.Set.union !exact_roots (Model.jmp_operand_reads j);
               base_roots :=
                 Core.Set.fold (Model.jmp_boundary_reads ~abi j)
                   ~init:!base_roots
                   ~f:(fun acc v -> Core.Set.add acc (Var.base v))));
    (* Liveness is per STORAGE, not per SSA version: the roots and every
       node's reads project to base vars, so a load of any version of a
       mem var roots the stores into it. *)
    let live_bases =
      ref
        (Core.Set.fold !exact_roots ~init:Var.Set.empty ~f:(fun acc v ->
             Core.Set.add acc (Var.base v)))
    in
    let live_tids = ref Tid.Set.empty in
    let changed = ref true in
    while !changed do
      changed := false;
      Base.List.iter nodes ~f:(fun (tid, lhs, reads) ->
          if
            (not (Core.Set.mem !live_tids tid))
            && (Core.Set.mem !live_bases (Var.base lhs)
                || Core.Set.mem !base_roots (Var.base lhs))
          then begin
            live_tids := Core.Set.add !live_tids tid;
            live_bases :=
              Core.Set.fold reads ~init:!live_bases ~f:(fun acc v ->
                  Core.Set.add acc (Var.base v));
            changed := true
          end)
    done;
    Term.map blk_t sub ~f:(fun b ->
        let b =
          Term.filter def_t b ~f:(fun d ->
              Core.Set.mem !live_tids (Term.tid d))
        in
        Term.filter phi_t b ~f:(fun p ->
            Core.Set.mem !live_tids (Term.tid p)))
