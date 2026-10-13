(* The emission signature, and the home of each lane's TYPE.  Every sub's
   arguments and returns are computed once here and written onto the sub's
   own [arg] terms (the returns are the [Out] intents); each lane carries
   its pointer-ness.  The emitter reads them off the sub — no side table. *)

open Bap.Std

module Model = Hike_stack_model
module Abi = Hike_abi

(* A lane is a pointer when it is an address lane: a by-reference
   argument, a memory var (its storage), or the caller window. *)
let tag_lane (a : Arg.t) : Arg.t =
  let v = Arg.lhs a in
  if
    Arg.intent a = Some Both
    || Model.is_mem v
    || Model.is_window_var v
  then Model.set_ptr_arg a
  else a

(* The sub's entry reads: SSA index-0 reads, or pre-SSA liveness over
   the BIR's explicit edges. *)
let free_regs_of_sub ~(target : Bap_core_theory.Theory.Target.t)
    (sub : sub term) : var list =
  let abi = Abi.of_target target in
  if Hike_ssa.is_ssa sub then Hike_ssa.free_regs_ssa ~abi sub
  else Hike_split_blocks.free_regs ~abi sub

let compute_sub_sig ~(free_vars : var list)
    (target : Bap_core_theory.Theory.Target.t)
    (sub : sub term) : Arg.t list * Arg.t list =
  let abi = Abi.of_target target in
  let rets =
    (* The return carriers: an internal sub returns every carrier the
       model can carry (RAX, RDX, and the vector return — the boundary
       facts, not a body scan); the boundary itself (the C entry and
       the emitted intrinsics) keeps its ABI shape, and a foreign
       target answers no returns. *)
    let carriers =
      if not (Abi.is_primary_target target) then []
      else abi.Abi.return_regs
    in
    Base.List.map carriers ~f:(fun reg -> Arg.create ~intent:Out reg (Var reg))
  in
  let rets, args =
    (* A sub reading its incoming window carries the caller-window
       base: its above-entry accesses materialize against the
       caller's frame. *)
    let window_arg =
      match Term.get_attr sub Model.layout_tag with
      | Some { Model.window_param = true; _ } ->
        let w = abi.Abi.word in
        [ Arg.create ~intent:In (Model.hike_window_var ~word:w)
            (Bil.Var (Model.hike_window_var ~word:w)) ]
      | _ -> []
    in
    if Model.is_emittable_intrinsic sub then begin
      let args =
        Base.List.map free_vars ~f:(fun reg -> Arg.create ~intent:In reg (Var reg))
      in
      let rets =
        Term.enum blk_t sub
        |> Seq.fold ~init:[] ~f:(fun acc blk ->
            Term.enum def_t blk
            |> Seq.fold ~init:acc ~f:(fun acc d ->
                let v = Def.lhs d in
                let is_input =
                  Base.List.exists free_vars ~f:(fun fv -> Var.same fv v)
                in
                let already =
                  Base.List.exists acc ~f:(fun a -> Var.same (Arg.lhs a) v)
                in
                if is_input || already then acc
                else Arg.create ~intent:Out v (Var v) :: acc))
      in
      (rets, args)
    end
    else if Model.fixed_signature sub then
      let rdi, rsi = Abi.argc_argv_regs abi in
      let args =
        [
          Arg.create ~intent:In rdi (Var rdi);
          Arg.create ~intent:In rsi (Var rsi);
        ]
      in
      (rets, args)
    else
      (* The signature transcribes the sub term's own BIR args
         (promoted slots included). *)
      let arg_terms = Term.enum arg_t sub |> Base.Sequence.to_list in
      let args =
        let nonparam_rank = 100 in
        let param_regs = Abi.param_regs abi in
        let rank_of_var (v : var) : int * string =
          let n = Var.name (Var.base v) in
          match Base.List.findi param_regs ~f:(fun _ r -> Var.same r v) with
          | Some (i, _) -> (i, n)
          | None -> (nonparam_rank, n)
        in
        Base.List.filter free_vars ~f:(fun reg ->
            let n = Var.name (Var.base reg) in
            let is_callee_saved = Abi.is_callee_saved abi reg in
            let is_nonparam_vector =
              match Var.typ reg with
              | Type.Imm bits ->
                bits > Model.word_bits abi.Abi.word
                && not (Abi.is_vector_param_reg abi reg)
              | _ -> false
            in
            not
              (Var.same reg (Abi.sp target)
              || Var.same reg abi.thread_pointer
              || is_callee_saved
              || Abi.is_env_reg abi reg
              || Abi.is_flag_reg abi reg
              || is_nonparam_vector
              || Hike_abi.is_intrinsic_name n
              || Model.is_arg_slot (Var.base reg)
              || Model.is_call_arg (Var.base reg)
              || Model.is_window_var reg
              || Model.is_storage_base reg))
        |> Base.List.sort ~compare:(fun a b ->
            let ra, na = rank_of_var a in
            let rb, nb = rank_of_var b in
            match Int.compare ra rb with
            | 0 -> String.compare na nb
            | c -> c)
        |> Base.List.map ~f:(fun reg -> Arg.create ~intent:In reg (Var reg))
        |> fun regs -> regs @ arg_terms
      in
      (* A call can consume an incoming register that the BIL body never
         mentions; retain the complete native integer-parameter ABI. *)
      let has_call =
        let is_native_call c =
          match Call.target c with
          | Indirect _ -> true
          | Direct t ->
              not (Hike_return.is_target t && Option.is_none (Call.return c))
        in
        Term.enum blk_t sub
        |> Seq.exists ~f:(fun blk ->
               Term.enum jmp_t blk
               |> Seq.exists ~f:(fun j ->
                      match Jmp.kind j with
                      | Call c -> is_native_call c
                      | _ -> false))
      in
      let args =
        if has_call then
          let is_plt_sig = Model.is_declared sub in
          let params =
            if is_plt_sig then Abi.param_regs abi else abi.Abi.int_param_regs
          in
          let is_param v = Base.List.exists params ~f:(Var.same v) in
          let param_args =
            Base.List.map params ~f:(fun reg ->
                Arg.create ~intent:In reg (Var reg))
          in
          let other_args =
            Base.List.filter args ~f:(fun arg -> not (is_param (Arg.lhs arg)))
          in
          param_args @ other_args
        else args
      in
      (rets, args @ window_arg)
  in
  ( Base.List.map rets ~f:tag_lane,
    Base.List.map args ~f:tag_lane )

(* The sign pass's one per-sub entry: the PLT-trampoline stamp (the
   emitter reads it) and the lane list. *)
let sign_sub ~(target : Bap_core_theory.Theory.Target.t)
    (sub : sub term) : sub term =
  let sub =
    if Model.is_self_call_shape ~target sub then
      Model.set_plt_trampoline sub
    else sub
  in
  let free_vars = free_regs_of_sub ~target sub in
  let rets, args = compute_sub_sig ~free_vars target sub in
  Model.set_sig sub (rets @ args)

(* The pipeline's pass, and any direct emitter caller (the fixtures),
   run exactly this. *)
let sign_program ~(target : Bap_core_theory.Theory.Target.t)
    (prog : program term) : program term =
  Term.map sub_t prog ~f:(sign_sub ~target)

(* ---- The value kind (ptr vs int) ----
   A value is a pointer when any part of its denotation is a bounded
   stack or VLA address.  Computed here, pre-SSA, where the denotation
   resolves; the emitter's ptr discipline consumes it. *)

module Vsa = Cbat_vsa

let ptr_kind_of ~(facts : Hike_kb.facts) ~(blk : blk term) ?def (e : exp) :
    bool =
  match facts.Hike_kb.denote ~blk ?def e with
  | Ok ws -> Vsa.WordSet.in_stack_segment ws
  | Error _ -> false

(* The pointer facts of one sub: the defs proved to be pointers, each such
   def's storage, and the pointer value vars. *)
type ptr_facts = {
  def_tids : Tid.Set.t;
  def_storages : Hike_stack_model.ptr_storage Tid.Map.t;
  vars : Var.Set.t;
}

let ptr_facts_empty =
  { def_tids = Tid.Set.empty; def_storages = Tid.Map.empty; vars = Var.Set.empty }

(* The pointer-kind inference: a forward may-analysis over the sub's CFG
   (the BAP [Graphlib] fixpoint).  The data is the set of vars proven to
   be stack/VLA addresses; the seed is the VSA denotation (a bounded
   stack/VLA value) plus the caller-proven lanes; the transfer adds every
   def whose rhs is a pointer-preserving shape over a proven operand.
   The join is set union (any pointer use makes a var a pointer). *)
let ptr_defs ?(extra = Var.Set.empty) ~(facts : Hike_kb.facts)
    (sub : sub term) : ptr_facts =
  let layout =
    Base.Option.value (Term.get_attr sub Hike_stack_model.layout_tag)
      ~default:
        { Hike_stack_model.Sub_layout.regions = [];
          window_param = false }
  in
  let word = facts.Hike_kb.abi.Hike_abi.word in
  let vla_reach (ws : Vsa.WordSet.t) : bool =
    match Vsa.WordSet.origin ws with
    | Some (Vsa.WordSet.Origin.Vla _) -> true
    | _ -> false
  in
  let storage_of (ws : Vsa.WordSet.t) : Hike_stack_model.ptr_storage option =
    (* One storage per value: the denotation must name exactly one
       alloca.  A value whose offsets span several regions (a phi's
       mixed-incoming join, a two-band hull) names none — the emitter
       keeps such a value on the pointer-value lane, where each path
       carries its own storage's pointer. *)
    if vla_reach ws then Some Hike_stack_model.Ptr_vla
    else if
      Hike_stack_model.is_window_denotation
        ~entry:Hike_stack_model.segment_base ~word ws
    then Some Hike_stack_model.Ptr_window
    else
      match Hike_stack_model.positions_of_offsets ws with
      | Some (lo, hi) -> (
          match
            Base.List.find layout.Hike_stack_model.Sub_layout.regions
              ~f:(fun { Hike_stack_model.Sub_layout.r_lo = rlo; r_hi = rhi; _ } ->
                Stdlib.Int64.compare lo rlo >= 0
                && Stdlib.Int64.compare hi rhi <= 0)
          with
          | Some { Hike_stack_model.Sub_layout.r_id = id; _ } ->
            Some (Hike_stack_model.Ptr_region id)
          | None -> None)
      | None -> None
  in
  let addr_width = Hike_stack_model.word_bits word in
  let is_addr_width (d : def term) : bool =
    match Var.typ (Def.lhs d) with
    | Type.Imm n -> Int.equal n addr_width
    | _ -> true
  in
  (* A model memory-state var is storage, never a pointer value. *)
  let is_value_var v =
    not
      (Hike_stack_model.is_region_mem v
      || Hike_stack_model.is_window_mem v
      || Hike_stack_model.is_sec_comp_mem v)
  in
  let add_value acc d =
    let v = Def.lhs d in
    let load_word =
      match Hike_stack_model.addr_of_rhs (Def.rhs d) with
      | Some (_, size) -> Int.equal (Size.in_bytes size) word
      | None -> true
    in
    if
      is_value_var v
      && Base.Option.is_none (Hike_stack_model.store_data_of_rhs (Def.rhs d))
      && is_addr_width d && load_word
    then Core.Set.add acc v
    else acc
  in
  (* The entry SP is a pointer by construction; the window lane too. *)
  let extra =
    let sp = facts.Hike_kb.abi.Hike_abi.sp in
    let window =
      Hike_stack_model.hike_window_var ~word:facts.Hike_kb.abi.Hike_abi.word
    in
    Core.Set.add (Core.Set.add extra sp) window
  in
  let is_stack_addr (ws : Vsa.WordSet.t) : bool =
    Vsa.WordSet.in_stack_segment ws
  in
  let denot_storage blk d =
    match facts.Hike_kb.denote ~blk ~def:d (Def.rhs d) with
    | Ok ws when is_stack_addr ws -> storage_of ws
    | _ -> None
  in
  let shape_ptr (ptrs : Var.Set.t) (e : exp) : bool =
    Hike_exp_fold.fold
      (fun e child ->
        match e with
        | Bil.Var v ->
            Core.Set.mem ptrs v
            || Core.Set.mem ptrs (Var.base v)
            || (match Var.typ (Var.base v) with
               | Type.Mem _ -> true
               | _ -> false)
        | Bil.BinOp ((Bil.PLUS | Bil.MINUS), a, b) -> child a || child b
        | Bil.Ite (_, a, b) -> child a || child b
        | _ -> false)
      e
  in
  let seed_of blk =
    Term.enum def_t blk
    |> Seq.fold ~init:extra ~f:(fun acc d ->
           match facts.Hike_kb.denote ~blk ~def:d (Def.rhs d) with
             | Ok ws when is_stack_addr ws -> add_value acc d
             | _ -> acc)
  in
  let def ptrs d =
    if shape_ptr ptrs (Def.rhs d) then add_value ptrs d else ptrs
  in
  let phi ptrs p =
    let inc =
      Phi.values p
      |> Seq.exists ~f:(fun (_, e) ->
             match e with
             | Bil.Var v ->
                 Core.Set.mem ptrs v || Core.Set.mem ptrs (Var.base v)
             | _ -> false)
    in
    if inc && is_value_var (Phi.lhs p) then
      Core.Set.add ptrs (Phi.lhs p)
    else ptrs
  in
  let jmp ptrs _ = ptrs in
  let base_map =
    Term.enum blk_t sub
    |> Seq.fold
         ~init:(Core.Map.set Tid.Map.empty ~key:Graphs.Tid.start ~data:extra)
         ~f:(fun m blk ->
           Core.Map.set m ~key:(Term.tid blk) ~data:(seed_of blk))
  in
  let graph = Sub.to_graph sub in
  let flow =
    Hike_bir_flow.run ~graph ~sub ~rev:false ~initial:base_map
      ~default:Var.Set.empty ~equal:Core.Set.equal ~merge:Core.Set.union
      ~def ~phi ~jmp
  in
  let ptrs =
    Term.enum blk_t sub
    |> Seq.fold ~init:extra ~f:(fun acc blk ->
           Core.Set.union acc
             (Option.value (Core.Map.find flow.after (Term.tid blk))
                ~default:Var.Set.empty))
  in
  (* The storage of each pointer def: the denotation's, else inherited
     from a pointer operand. *)
  let struct_storage (var_stors : Hike_stack_model.ptr_storage Var.Map.t)
      (e : exp) : Hike_stack_model.ptr_storage option =
    Hike_exp_fold.fold
      (fun e child ->
        match e with
        | Bil.Var v -> (
            let self =
              match Hike_stack_model.region_ptr_id_of (Var.base v) with
              | Some id -> Some (Hike_stack_model.Ptr_region id)
              | None -> None
            in
            match self with
            | Some st -> Some st
            | None -> (
                match Core.Map.find var_stors v with
                | Some st -> Some st
                | None -> Core.Map.find var_stors (Var.base v)))
        | Bil.BinOp ((Bil.PLUS | Bil.MINUS), a, b) ->
            Base.Option.first_some (child a) (child b)
        | Bil.Ite (_, a, b) -> Base.Option.first_some (child a) (child b)
        | _ -> None)
      e
  in
  let defs =
    Term.enum blk_t sub
    |> Seq.concat_map ~f:(fun blk ->
           Term.enum def_t blk |> Seq.map ~f:(fun d -> (blk, d)))
    |> Seq.to_list
  in
  let rec stor_loop stors var_stors =
    let stors', var_stors' =
      Base.List.fold defs ~init:(stors, var_stors)
        ~f:(fun (stors, var_stors) (blk, d) ->
          let v = Def.lhs d in
          if not (Core.Set.mem ptrs v) then (stors, var_stors)
          else
            let st =
              match denot_storage blk d with
              | Some st -> Some st
              | None -> struct_storage var_stors (Def.rhs d)
            in
            match st with
            | None -> (stors, var_stors)
            | Some st ->
                let stors =
                  if Core.Map.mem stors (Term.tid d) then stors
                  else Core.Map.set stors ~key:(Term.tid d) ~data:st
                in
                let var_stors =
                  if Core.Map.mem var_stors v then var_stors
                  else Core.Map.set var_stors ~key:v ~data:st
                in
                (stors, var_stors))
    in
    if Core.Map.length stors' = Core.Map.length stors then (stors', var_stors')
    else stor_loop stors' var_stors'
  in
  let stors, _ = stor_loop Tid.Map.empty Var.Map.empty in
  let tids =
    Base.List.fold defs ~init:Tid.Set.empty ~f:(fun acc (_, d) ->
        if Core.Set.mem ptrs (Def.lhs d) then Core.Set.add acc (Term.tid d)
        else acc)
  in
  { def_tids = tids; def_storages = stors; vars = ptrs }

let sub_of_program (prog : program term) : sub term Tid.Map.t =
  Term.enum sub_t prog
  |> Seq.fold ~init:Tid.Map.empty ~f:(fun m s ->
      Core.Map.set m ~key:(Term.tid s) ~data:s)

(* The whole-program pointer-kind fixpoint.  A value is a pointer when
   the VSA proves its denotation is a stack/VLA address, or it flows
   from one: a copy, an address offset, an ite; a callee parameter a
   caller proves; a caller's return lane whose callee proves.  The
   def-use part runs per sub ([ptr_defs]); the call-graph edges run to a
   fixpoint over the subs.  A var is a pointer when any of its defs is
   (the join is [int ⊑ ptr]; the emitter inttoptrs the integer paths). *)
let ptr_kinds ~(facts : Hike_kb.facts) ~(sub_of : sub term Tid.Map.t)
    (prog : program term) : Var.Set.t Tid.Map.t * ptr_facts Tid.Map.t =
  let add acc t v =
    Core.Map.update acc t ~f:(function
        | None -> Var.Set.singleton v
        | Some s -> Core.Set.add s v)
  in
  let subs = Term.enum sub_t prog |> Seq.to_list in
  let rec fix pks inferred =
    let inferred' =
      Base.List.fold subs ~init:Tid.Map.empty ~f:(fun acc sub ->
          let extra =
            Core.Map.find pks (Term.tid sub)
            |> Base.Option.value ~default:Var.Set.empty
          in
          Core.Map.set acc ~key:(Term.tid sub)
            ~data:(ptr_defs ~extra ~facts sub))
    in
    let ptr_vars_of sub =
      let vars =
        Core.Map.find inferred' (Term.tid sub)
        |> Base.Option.value ~default:ptr_facts_empty
        |> fun pf -> pf.vars
      in
      Core.Set.union vars
        (Core.Map.find pks (Term.tid sub)
        |> Base.Option.value ~default:Var.Set.empty)
    in
    let pks' =
      Base.List.fold subs ~init:pks ~f:(fun pks caller ->
          let ctv = ptr_vars_of caller in
          Term.enum blk_t caller
          |> Seq.fold ~init:pks ~f:(fun pks blk ->
                 Term.enum jmp_t blk
                 |> Seq.fold ~init:pks ~f:(fun pks j ->
                        match Jmp.kind j with
                        | Call c -> (
                            match Call.target c with
                            | Direct t -> (
                                match Core.Map.find sub_of t with
                                | Some callee ->
                                    let callee_ptr = ptr_vars_of callee in
                                    (* caller arg -> callee param *)
                                    let pks =
                                      Base.List.fold
                                        (Hike_stack_model.sig_args callee)
                                        ~init:pks ~f:(fun pks a ->
                                          if Hike_stack_model.is_ret a then pks
                                          else if
                                            Core.Set.mem ctv (Arg.lhs a)
                                            || ptr_kind_of ~facts ~blk
                                                 (Arg.rhs a)
                                          then add pks t (Arg.lhs a)
                                          else pks)
                                    in
                                    (* callee ret -> caller ret lane *)
                                    Base.List.fold
                                      facts.Hike_kb.abi.Hike_abi.return_regs
                                      ~init:pks ~f:(fun pks r ->
                                        if Core.Set.mem callee_ptr r then
                                          add pks (Term.tid caller) r
                                        else pks)
                                | None -> pks)
                            | Indirect _ -> pks)
                        | _ -> pks)))
    in
    if Core.Map.equal Var.Set.equal pks pks' then (pks', inferred')
    else fix pks' inferred'
  in
  fix Tid.Map.empty Tid.Map.empty

(* Stamps each In lane's kind: the mem/window lanes are pointers by
   construction; a value lane is a pointer when its parameter is. *)
let stamp_arg_kinds ~(param_kinds : Var.Set.t Tid.Map.t)
    (prog : program term) : program term =
  Term.map sub_t prog ~f:(fun sub ->
      let kinds =
        Core.Map.find param_kinds (Term.tid sub)
        |> Base.Option.value ~default:Var.Set.empty
      in
      Term.map arg_t sub ~f:(fun a ->
          if Hike_stack_model.is_ret a then a
          else if
            Hike_stack_model.is_ptr_arg a
            || Hike_stack_model.is_window_var (Arg.lhs a)
            || Core.Set.mem kinds (Arg.lhs a)
          then Hike_stack_model.set_arg_ptr_kind a
          else a))

#ifdef VSA_DEBUG
let kind_census (prog : program term) : unit =
  let defs = ref 0 and ptrs = ref 0 and wins = ref 0 in
  Term.enum sub_t prog
  |> Seq.iter ~f:(fun sub ->
      Term.enum blk_t sub
      |> Seq.iter ~f:(fun blk ->
          Term.enum def_t blk
          |> Seq.iter ~f:(fun d ->
              incr defs;
              if Hike_def_slots.def_ptr_kind d then incr ptrs;
              if Hike_def_slots.def_is_window_value d then incr wins)));
  Printf.eprintf "hike-kinds: defs=%d ptr=%d window=%d\n%!" !defs !ptrs !wins
#endif

(* A lane is a pointer when its own var is: the convention's fact (the
   exact lane var the param-kind fixpoint proves), never a body
   redefinition of the register. *)
let stamp_lane_types (prog : program term) : program term =
  Term.map sub_t prog ~f:(fun sub ->
      let env = Model.ptr_vars sub in
      Term.map arg_t sub ~f:(fun a ->
          if Core.Set.mem env (Arg.lhs a) then Model.set_ptr_arg a else a))

(* The signature pass: write every sub's lane list onto its own [arg]
   terms.  It does not need the value types, so it runs BEFORE SSA. *)
let sign_run (proj : Project.t) : Project.t =
  let target = Project.target proj in
  Project.map_program proj ~f:(sign_program ~target)

(* The type pass: infer every value's type (AFTER SSA, per version) and
   stamp it — the sub's pointer environment, the lane kinds and lane
   types.  The BIR keeps its sorts; the emitter reads the stamps. *)
let run (proj : Project.t) : Project.t =
  Project.map_program proj ~f:(fun prog ->
      match Hike_kb.facts_opt () with
      | None -> prog
      | Some facts ->
          let sub_of = sub_of_program prog in
          let pks, inferred = ptr_kinds ~facts ~sub_of prog in
          let ptr_vars_of_sub sub =
            let vars =
              Core.Map.find inferred (Term.tid sub)
              |> Base.Option.value ~default:ptr_facts_empty
              |> fun pf -> pf.vars
            in
            Core.Set.union vars
              (Core.Map.find pks (Term.tid sub)
              |> Base.Option.value ~default:Var.Set.empty)
          in
          let prog =
            Term.map sub_t prog ~f:(fun sub ->
                let pf =
                  Core.Map.find inferred (Term.tid sub)
                  |> Base.Option.value ~default:ptr_facts_empty
                in
                let sub =
                  Hike_def_slots.stamp_ptr_kinds ~ptr_tids:pf.def_tids sub
                in
                let sub =
                  Hike_def_slots.stamp_ptr_storages ~storages:pf.def_storages
                    sub
                in
                let lane_vars =
                  Term.enum arg_t sub
                  |> Seq.fold ~init:Var.Set.empty ~f:(fun acc a ->
                         Core.Set.add acc (Arg.lhs a))
                in
                let param_vars =
                  Core.Map.find pks (Term.tid sub)
                  |> Base.Option.value ~default:Var.Set.empty
                  |> Core.Set.filter ~f:(fun v ->
                         Core.Set.mem lane_vars v
                         || Core.Set.mem lane_vars (Var.base v))
                in
                (* A call-ret version is a pointer when its callee's ret
                   lane is. *)
                let minted =
                  Term.enum blk_t sub
                  |> Seq.fold ~init:Var.Set.empty ~f:(fun acc blk ->
                         let cptr =
                           Term.enum jmp_t blk
                           |> Seq.fold ~init:Var.Set.empty ~f:(fun a j ->
                                  match Jmp.kind j with
                                  | Call c -> (
                                      match Call.target c with
                                      | Direct t -> (
                                          match Core.Map.find sub_of t with
                                          | Some callee ->
                                              Core.Set.union a
                                                (ptr_vars_of_sub callee)
                                          | None -> a)
                                      | Indirect _ -> a)
                                  | _ -> a)
                         in
                         match
                           Term.get_attr blk Hike_stack_model.versions_tag
                         with
                         | Some vs ->
                             Base.List.fold
                               vs.Hike_stack_model.Versions.rets ~init:acc
                               ~f:(fun acc (v, v') ->
                                 if Core.Set.mem cptr v then
                                   Core.Set.add acc v'
                                 else acc)
                         | None -> acc)
                in
                let ptr_vars =
                  Core.Set.union pf.vars
                    (Core.Set.union param_vars minted)
                in
                let ptr_vars =
                  Core.Set.add ptr_vars facts.Hike_kb.abi.Hike_abi.sp
                in
                let ptr_vars =
                  Core.Set.add ptr_vars
                    (Hike_stack_model.hike_window_var
                       ~word:facts.Hike_kb.abi.Hike_abi.word)
                in
                (* An indirect target keeps the word sort: the term
                   layer cannot carry a Mem-sorted label exp (the call
                   or dispatch would degrade to its plain transfer),
                   and the emitter materializes the code address from
                   the integer at the site. *)
                let with_base (vs : Var.Set.t) : Var.Set.t =
                  Core.Set.fold vs ~init:vs ~f:(fun acc v ->
                      Core.Set.add acc (Var.base v))
                in
                let target_vars =
                  Term.enum blk_t sub
                  |> Seq.fold ~init:Var.Set.empty ~f:(fun acc blk ->
                         Term.enum jmp_t blk
                         |> Seq.fold ~init:acc ~f:(fun acc j ->
                                Core.Set.union acc
                                  (Model.jmp_target_reads j)))
                in
                let target_vars = with_base target_vars in
                let ptr_vars =
                  Core.Set.diff ptr_vars target_vars
                in
                Model.set_ptr_vars ptr_vars sub)
          in
          let prog = stamp_arg_kinds ~param_kinds:pks prog in
          let prog = stamp_lane_types prog in
#ifdef VSA_DEBUG
          kind_census prog;
#endif
          prog)
