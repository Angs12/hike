(* The dead-def sweep: plain liveness over the model's read sets.  The
   roots are every jump's reads — its operand expressions and the kind's
   ABI boundary (a ret consumes the return registers and SP; a call the
   parameter registers, the ABI return registers it produces, and SP) —
   a call-bearing block's mem-typed defs (the memory state the site
   hands its callee), and the sub's escape roots (the storages whose
   bytes leave the sub: an incoming stack-address parameter's target,
   a typed call argument's storage).  A def or phi is live iff its lhs
   is read by a live node, to a fixpoint.  Everything unmarked leaves —
   no per-var keep arms. *)
open Bap.Std
open Bap.Std.Bil.Types
module Abi = Hike_abi
module Model = Hike_stack_model

let dce ~(target : Bap_core_theory.Theory.Target.t)
    ~(escape_roots : Var.Set.t) (sub : sub term) :
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
    (* Global storage crosses sub boundaries; every written component
       is rooted because its reader may be another sub. *)
    let global_mem_bases =
      Term.enum blk_t sub
      |> Seq.concat_map ~f:(fun b -> Term.enum def_t b)
      |> Seq.filter ~f:(fun d -> Model.is_global_mem (Def.lhs d))
      |> Seq.fold ~init:Var.Set.empty ~f:(fun acc d ->
          Core.Set.add acc (Var.base (Def.lhs d)))
    in
    let base_roots =
      ref
        (Core.Set.fold escape_roots
           ~init:global_mem_bases
           ~f:(fun acc v -> Core.Set.add acc (Var.base v)))
    in
    Term.enum blk_t sub
    |> Seq.iter ~f:(fun b ->
           Term.enum jmp_t b
           |> Seq.iter ~f:(fun j ->
               exact_roots :=
                 Core.Set.union !exact_roots (Model.jmp_operand_reads j));
           let boundary =
             Core.Set.union
               (Term.enum jmp_t b
                |> Seq.fold ~init:Var.Set.empty ~f:(fun reads j ->
                       Core.Set.union reads (Model.jmp_boundary_reads ~abi j)))
               (Model.blk_boundary_reads b)
           in
           base_roots :=
             Core.Set.fold boundary ~init:!base_roots
               ~f:(fun acc v -> Core.Set.add acc (Var.base v)));
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
