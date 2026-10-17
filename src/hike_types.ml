(* The emission signature, and the home of each lane's TYPE.  Every sub's
   arguments and returns are computed once here and written onto the sub's
   own [arg] terms (the returns are the [Out] intents); each lane carries
   its pointer-ness.  The emitter reads them off the sub — no side table. *)

open Bap.Std

module Model = Hike_stack_model
module Abi = Hike_abi

let return_lanes ~target sub =
  let carriers =
    if Abi.is_primary_target target then (Abi.of_target target).Abi.return_regs
    else []
  in
  Base.List.map carriers ~f:(fun reg -> Arg.create ~intent:Out reg (Bil.Var reg))
  @ Base.List.filter (Model.sig_rets sub) ~f:(fun arg ->
      not (Base.List.exists carriers ~f:(Var.same (Arg.lhs arg))))

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
    return_lanes ~target sub
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
    else if Model.is_declared sub then
      (* A declaration's signature is the machine's own convention: the
         loader binds the name, so it carries no lanes of its own. *)
      ( rets,
        Base.List.map (Abi.param_regs abi) ~f:(fun reg ->
            Arg.create ~intent:In reg (Var reg)) )
    else
      (* The signature transcribes the sub term's own BIR args
         (promoted slots included). *)
      let arg_terms = Model.sig_args sub in
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
          let params = abi.Abi.int_param_regs in
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
  let sub =
    if Model.is_emittable_intrinsic sub then sub
    else Model.set_sig sub (return_lanes ~target sub @ Model.sig_args sub)
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
   A value is a pointer when it is a bounded stack address (the VSA
   denotation, computed pre-SSA where it resolves), flows from one
   (a copy, an offset, an ite), or is used as a load/store address.
   Provenance and use are one joint fixpoint ([ptr_defs]); the emitter's
   ptr discipline consumes it. *)

module Vsa = Cbat_vsa

let ptr_kind_of ~(facts : Hike_kb.facts) ~(blk : blk term) ?def (e : exp) :
    bool =
  match facts.Hike_kb.denote ~blk ?def e with
  | Ok ws -> Vsa.WordSet.in_stack_segment ws
  | Error _ -> false

(* SP and the caller window hold addresses in every SSA version. *)
let is_address_reg ~(facts : Hike_kb.facts) (v : var) : bool =
  Var.same v facts.Hike_kb.abi.Hike_abi.sp || Model.is_window_var v

(* A block's SSA versions of base register [r]: after its defs (what a
   call passes), and its call's minted result. *)
let blk_version field (blk : blk term) (r : var) : var option =
  Base.Option.bind (Term.get_attr blk Model.versions_tag) ~f:(fun vs ->
      Base.List.Assoc.find (field vs) r ~equal:Var.same)

let passed_at = blk_version (fun vs -> vs.Model.Versions.args)
let minted_at = blk_version (fun vs -> vs.Model.Versions.rets)

(* A block that leaves the sub: a return, a tail call, or no transfer. *)
let is_exit_blk (blk : blk term) : bool =
  let jmps = Term.enum jmp_t blk in
  Seq.is_empty jmps
  || Seq.exists jmps ~f:(fun j ->
         match Jmp.kind j with
         | Ret _ -> true
         | Call c -> Base.Option.is_none (Call.return c)
         | Goto _ | Int _ -> false)

(* The return registers the sub returns a pointer in: a version of the
   register reaching an exit is a pointer.  An exit no version reaches
   is no evidence (the base register is an argument lane, not a return
   one).  A fixed signature keeps the ABI's integer returns. *)
let ptr_returns ~(facts : Hike_kb.facts) (sub : sub term) (ptrs : Var.Set.t)
    : Var.Set.t =
  if Model.fixed_signature sub then Var.Set.empty
  else
    Base.List.filter facts.Hike_kb.abi.Hike_abi.return_regs ~f:(fun r ->
        Term.enum blk_t sub
        |> Seq.exists ~f:(fun blk ->
               is_exit_blk blk
               && Base.Option.value_map ~default:false
                    (Base.Option.first_some (minted_at blk r)
                       (passed_at blk r))
                    ~f:(Core.Set.mem ptrs)))
    |> Var.Set.of_list

(* Every SSA version of SP and the window the sub names. *)
let address_versions ~(facts : Hike_kb.facts) (sub : sub term) : Var.Set.t =
  let add acc v = if is_address_reg ~facts v then Core.Set.add acc v else acc in
  (object
     inherit [Var.Set.t] Term.visitor as super
     method! visit_var v acc = add acc v
     method! visit_def d acc = super#visit_def d (add acc (Def.lhs d))
     method! visit_phi p acc = super#visit_phi p (add acc (Phi.lhs p))
   end)#visit_sub sub Var.Set.empty

(* The pointer facts of one sub: the defs proved to be pointers, each such
   def's storage, and the pointer value vars. *)
type ptr_facts = {
  def_tids : Tid.Set.t;
  def_storages : Hike_stack_model.ptr_storage Tid.Map.t;
  vars : Var.Set.t;
}

let ptr_facts_empty =
  { def_tids = Tid.Set.empty; def_storages = Tid.Map.empty; vars = Var.Set.empty }

(* The pointer-kind inference, two [Hike_bir_flow] passes joined to a
   fixpoint.  The forward pass (provenance) seeds on the VSA denotation (a
   bounded stack value) plus the caller-proven lanes, and adds every def
   whose rhs is a pointer-preserving shape over a proven operand.  The
   backward pass (use) adds the base var of every load/store address,
   and through a pointer-preserving def the operand of a proven var.
   Each result seeds the other; both are unions over the finite set of
   SSA versions, so the loop terminates.  A var is a pointer when any of
   its defs is (the join is [int ⊑ ptr]).  Use-based pointers get no
   stack storage: [storage_of] still needs a VSA proof.  [used] seeds
   the backward pass (the versions a caller passes into pointer lanes).
   Without SSA versions, or for a fixed signature's lanes, a use proves
   nothing. *)
let ptr_defs ?(extra = Var.Set.empty) ?(used = Var.Set.empty)
    ~(facts : Hike_kb.facts)
    (sub : sub term) : ptr_facts =
  let layout =
    Base.Option.value (Term.get_attr sub Hike_stack_model.layout_tag)
      ~default:
        { Hike_stack_model.Sub_layout.regions = [];
          window_param = false;
          runtime_residue = false }
  in
  let word = facts.Hike_kb.abi.Hike_abi.word in
  let storage_of (ws : Vsa.WordSet.t) : Hike_stack_model.ptr_storage option =
    (* One storage per value: the denotation must name exactly one
       alloca.  A value whose offsets span several regions (a phi's
       mixed-incoming join, a two-band hull) names none — the emitter
       keeps such a value on the pointer-value lane, where each path
       carries its own storage's pointer. *)
    if
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
  (* A def that can hold a pointer value: a word-wide value, not a
     store, not a narrower load. *)
  let value_def d =
    let load_word =
      match Hike_stack_model.addr_of_rhs (Def.rhs d) with
      | Some (_, size) -> Int.equal (Size.in_bytes size) word
      | None -> true
    in
    is_value_var (Def.lhs d)
    && Base.Option.is_none (Hike_stack_model.store_data_of_rhs (Def.rhs d))
    && is_addr_width d && load_word
  in
  let add_value acc d =
    if value_def d then Core.Set.add acc (Def.lhs d) else acc
  in
  (* The entry SP is a pointer by construction; the window lane too. *)
  let with_roots extra =
    let sp = facts.Hike_kb.abi.Hike_abi.sp in
    let window =
      Hike_stack_model.hike_window_var ~word:facts.Hike_kb.abi.Hike_abi.word
    in
    Core.Set.add (Core.Set.add extra sp) window
  in
  (* Every var [is_ptr] sees occurs in the sub: classify each once. *)
  let addrs = address_versions ~facts sub in
  let is_ptr ptrs v = Core.Set.mem ptrs v || Core.Set.mem addrs v in
  let is_stack_addr (ws : Vsa.WordSet.t) : bool =
    Vsa.WordSet.in_stack_segment ws
  in
  let defs =
    Term.enum blk_t sub
    |> Seq.concat_map ~f:(fun blk ->
           Term.enum def_t blk |> Seq.map ~f:(fun d -> (blk, d)))
    |> Seq.to_list
  in
  (* Each def's stack-address denotation, with its storage: independent
     of [extra], so denoted once per sub. *)
  let stack_denots =
    Base.List.fold defs ~init:Tid.Map.empty ~f:(fun m (blk, d) ->
        match facts.Hike_kb.denote ~blk ~def:d (Def.rhs d) with
        | Ok ws when is_stack_addr ws ->
            Core.Map.set m ~key:(Term.tid d) ~data:(lazy (storage_of ws))
        | _ -> m)
  in
  let denot_storage d =
    match Core.Map.find stack_denots (Term.tid d) with
    | Some st -> Lazy.force st
    | None -> None
  in
  let rec shape_ptr (ptrs : Var.Set.t) (e : exp) : bool =
    match e with
    | Bil.Var v ->
        is_ptr ptrs v || (match Var.typ v with Type.Mem _ -> true | _ -> false)
    | Bil.BinOp ((Bil.PLUS | Bil.MINUS), a, b) ->
        shape_ptr ptrs a || shape_ptr ptrs b
    | Bil.Ite (_, a, b) -> shape_ptr ptrs a || shape_ptr ptrs b
    | _ -> false
  in
  let seed_of extra blk =
    Term.enum def_t blk
    |> Seq.fold ~init:extra ~f:(fun acc d ->
           if Core.Map.mem stack_denots (Term.tid d) then add_value acc d
           else acc)
  in
  let def ptrs d =
    if shape_ptr ptrs (Def.rhs d) then add_value ptrs d else ptrs
  in
  let phi ptrs p =
    let inc =
      Phi.values p
      |> Seq.exists ~f:(fun (_, e) ->
             match e with
             | Bil.Var v -> is_ptr ptrs v
             | _ -> false)
    in
    if inc && is_value_var (Phi.lhs p) then
      Core.Set.add ptrs (Phi.lhs p)
    else ptrs
  in
  let jmp ptrs _ = ptrs in
  let graph = Sub.to_graph sub in
  let forward extra =
    let extra = with_roots extra in
    let base_map =
      Term.enum blk_t sub
      |> Seq.fold
           ~init:(Core.Map.set Tid.Map.empty ~key:Graphs.Tid.start ~data:extra)
           ~f:(fun m blk ->
             Core.Map.set m ~key:(Term.tid blk) ~data:(seed_of extra blk))
    in
    let flow =
      Hike_bir_flow.run ~graph ~sub ~rev:false ~initial:base_map
        ~default:Var.Set.empty ~equal:Core.Set.equal ~merge:Core.Set.union
        ~def ~phi ~jmp
    in
    Term.enum blk_t sub
    |> Seq.fold ~init:extra ~f:(fun acc blk ->
           Core.Set.union acc
             (Option.value (Core.Map.find flow.after (Term.tid blk))
                ~default:Var.Set.empty))
  in
  (* The use pass.  Under SSA each version has one def, so the set only
     grows; a use in a later block flows back to its def's block. *)
  let versioned =
    Model.is_ssa sub
    && Seq.exists (Term.enum blk_t sub) ~f:(fun blk ->
           Term.has_attr blk Model.versions_tag)
  in
  let fixed_lanes =
    if Model.fixed_signature sub then
      Var.Set.of_list (Base.List.map (Model.sig_args sub) ~f:Arg.lhs)
    else Var.Set.empty
  in
  let def_of =
    Base.List.fold defs ~init:Var.Map.empty ~f:(fun m (_, d) ->
        Core.Map.set m ~key:(Def.lhs d) ~data:d)
  in
  (* Only a version that can hold a pointer: an address-width value, not
     a fixed signature's lane. *)
  let use_ok v =
    versioned && is_value_var v
    && (match Var.typ v with Type.Imm n -> Int.equal n addr_width | _ -> false)
    && (not (Core.Set.mem fixed_lanes v))
    && (match Core.Map.find def_of v with
        | Some d -> value_def d
        | None -> true)
  in
  let add_used acc vs =
    Base.List.fold vs ~init:acc ~f:(fun acc v ->
        if use_ok v then Core.Set.add acc v else acc)
  in
  (* The vars an address expression is based on: [v], [v ± k], [v + idx]
     with a shift, multiply, cast or constant index, an [ite]'s arms.  A
     sum of two bare vars names no base: neither is known to be the
     pointer, so both stay integers. *)
  let rec bases (e : exp) : var list =
    let is_sum = function
      | Bil.BinOp ((Bil.PLUS | Bil.MINUS), _, _) -> true
      | _ -> false
    in
    let is_var = function Bil.Var _ -> true | _ -> false in
    match e with
    | Bil.Var v -> [ v ]
    | Bil.Ite (_, a, b) -> bases a @ bases b
    | Bil.BinOp (Bil.MINUS, a, b) ->
        if is_var a && is_var b then [] else bases a
    | Bil.BinOp (Bil.PLUS, a, b) -> (
        match (is_var a, is_sum a, is_var b, is_sum b) with
        | true, _, true, _ -> []
        | _, true, _, true -> []
        | true, _, _, false -> bases a
        | _, false, true, _ -> bases b
        | _, true, _, _ -> bases a
        | _, _, _, true -> bases b
        | _ -> [])
    | _ -> []
  in
  let used_def used d =
    let used =
      match Hike_stack_model.addr_of_rhs (Def.rhs d) with
      | Some (a, _) -> add_used used (bases a)
      | None -> used
    in
    if Core.Set.mem used (Def.lhs d) then add_used used (bases (Def.rhs d))
    else used
  in
  let used_phi used p =
    if Core.Set.mem used (Phi.lhs p) then
      add_used used
        (Phi.values p
         |> Seq.filter_map ~f:(fun (_, e) ->
                match e with Bil.Var v -> Some v | _ -> None)
         |> Seq.to_list)
    else used
  in
  let backward seed =
    let initial =
      Term.enum blk_t sub
      |> Seq.fold
           ~init:(Core.Map.set Tid.Map.empty ~key:Graphs.Tid.exit
                    ~data:Var.Set.empty)
           ~f:(fun m blk -> Core.Map.set m ~key:(Term.tid blk) ~data:seed)
    in
    let flow =
      Hike_bir_flow.run ~graph ~sub ~rev:true ~initial ~default:Var.Set.empty
        ~equal:Core.Set.equal ~merge:Core.Set.union ~def:used_def
        ~phi:used_phi ~jmp:(fun used _ -> used)
    in
    Core.Map.fold flow.before ~init:seed ~f:(fun ~key:_ ~data acc ->
        Core.Set.union acc data)
  in
  (* Provenance feeds use and back, until neither grows. *)
  let rec joint extra =
    let ptrs = forward extra in
    if not versioned then ptrs
    else
      let extra' = Core.Set.union extra (backward ptrs) in
      if Core.Set.equal extra' extra then ptrs else joint extra'
  in
  let extra = Core.Set.union extra (add_used Var.Set.empty (Core.Set.to_list used)) in
  let ptrs = joint extra in
  (* The storage of each pointer def: the denotation's, else inherited
     from a pointer operand. *)
  let rec struct_storage (var_stors : Hike_stack_model.ptr_storage Var.Map.t)
      (e : exp) : Hike_stack_model.ptr_storage option =
    match e with
    | Bil.Var v -> (
        match Hike_stack_model.region_ptr_id_of (Var.base v) with
        | Some id -> Some (Hike_stack_model.Ptr_region id)
        | None -> (
            match Core.Map.find var_stors v with
            | Some st -> Some st
            | None -> Core.Map.find var_stors (Var.base v)))
    | Bil.BinOp ((Bil.PLUS | Bil.MINUS), a, b) | Bil.Ite (_, a, b) ->
        Base.Option.first_some (struct_storage var_stors a)
          (struct_storage var_stors b)
    | _ -> None
  in
  let rec stor_loop stors var_stors =
    let stors', var_stors' =
      Base.List.fold defs ~init:(stors, var_stors)
        ~f:(fun (stors, var_stors) (_, d) ->
          let v = Def.lhs d in
          if not (Core.Set.mem ptrs v) then (stors, var_stors)
          else
            let st =
              match denot_storage d with
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

(* A sub's pointer versions: its inferred ones and those its callers
   prove. *)
let ptr_vars_of ~(pks : Var.Set.t Tid.Map.t) ~(inferred : ptr_facts Tid.Map.t)
    (sub : sub term) : Var.Set.t =
  let vars =
    Core.Map.find inferred (Term.tid sub)
    |> Base.Option.value ~default:ptr_facts_empty
    |> fun pf -> pf.vars
  in
  Core.Set.union vars
    (Core.Map.find pks (Term.tid sub) |> Base.Option.value ~default:Var.Set.empty)

(* Every direct call of [sub], in order, with its block. *)
let fold_direct_calls (sub : sub term) ~(init : 'a)
    ~(f : 'a -> blk term -> Tid.t -> 'a) : 'a =
  Term.enum blk_t sub
  |> Seq.fold ~init ~f:(fun acc blk ->
         Term.enum jmp_t blk
         |> Seq.fold ~init:acc ~f:(fun acc j ->
                match Jmp.kind j with
                | Call c -> (
                    match Call.target c with
                    | Direct t -> f acc blk t
                    | Indirect _ -> acc)
                | _ -> acc))

(* The whole-program pointer-kind fixpoint.  A value is a pointer when
   the VSA proves its denotation is a stack address, it flows from one
   (a copy, an address offset, an ite), or it is used as a load/store
   address; a callee parameter a caller proves; a caller's return lane
   whose callee proves; a version a caller passes into a pointer lane.
   The def-use part runs per sub ([ptr_defs]); the call-graph edges run
   to a fixpoint over the subs.  A var is a pointer when any of its defs
   is (the join is [int ⊑ ptr]; the emitter inttoptrs the integer paths). *)
let ptr_kinds ~(facts : Hike_kb.facts) ~(sub_of : sub term Tid.Map.t)
    (prog : program term) : Var.Set.t Tid.Map.t * ptr_facts Tid.Map.t =
  let add acc t v =
    Core.Map.update acc t ~f:(function
        | None -> Var.Set.singleton v
        | Some s -> Core.Set.add s v)
  in
  let subs = Term.enum sub_t prog |> Seq.to_list in
  let extra_of pks sub =
    Core.Map.find pks (Term.tid sub) |> Base.Option.value ~default:Var.Set.empty
  in
  (* [pks] seeds a sub's provenance pass, [uks] its use pass.  [inferred]
     was computed under the previous pair; a sub whose seeds are unchanged
     keeps its result. *)
  let rec fix (pks, uks) (prev_pks, prev_uks) inferred =
    let inferred' =
      Base.List.fold subs ~init:Tid.Map.empty ~f:(fun acc sub ->
          let extra = extra_of pks sub and used = extra_of uks sub in
          let pf =
            match Core.Map.find inferred (Term.tid sub) with
            | Some pf
              when Core.Set.equal extra (extra_of prev_pks sub)
                   && Core.Set.equal used (extra_of prev_uks sub) ->
                pf
            | _ -> ptr_defs ~extra ~used ~facts sub
          in
          Core.Map.set acc ~key:(Term.tid sub) ~data:pf)
    in
    let ptr_vars_of = ptr_vars_of ~pks ~inferred:inferred' in
    let pks', uks' =
      Base.List.fold subs ~init:(pks, uks) ~f:(fun acc caller ->
          let ctv = ptr_vars_of caller in
          fold_direct_calls caller ~init:acc ~f:(fun (pks, uks) blk t ->
              match Core.Map.find sub_of t with
              | Some callee ->
                  let callee_ptrs = ptr_vars_of callee in
                  (* the version the caller passes <-> the callee's
                     parameter: a pointer either way *)
                  let pks, uks =
                    Base.List.fold (Hike_stack_model.sig_args callee)
                      ~init:(pks, uks) ~f:(fun (pks, uks) a ->
                        let r = Arg.lhs a in
                        let passed = passed_at blk r in
                        let v = Base.Option.value ~default:r passed in
                        let pks =
                          if
                            Core.Set.mem ctv v
                            || is_address_reg ~facts v
                            || ptr_kind_of ~facts ~blk (Arg.rhs a)
                          then add pks t r
                          else pks
                        in
                        let uks =
                          match passed with
                          | Some v when Core.Set.mem callee_ptrs r ->
                              add uks (Term.tid caller) v
                          | _ -> uks
                        in
                        (pks, uks))
                  in
                  (* the callee's pointer return -> the caller's minted
                     version *)
                  let pks =
                    Core.Set.fold
                      (ptr_returns ~facts callee callee_ptrs)
                      ~init:pks ~f:(fun pks r ->
                        match minted_at blk r with
                        | Some v -> add pks (Term.tid caller) v
                        | None -> pks)
                  in
                  (pks, uks)
              | None -> (pks, uks)))
    in
    if
      Core.Map.equal Var.Set.equal pks pks'
      && Core.Map.equal Var.Set.equal uks uks'
    then (pks', inferred')
    else fix (pks', uks') (pks, uks) inferred'
  in
  fix (Tid.Map.empty, Tid.Map.empty) (Tid.Map.empty, Tid.Map.empty)
    Tid.Map.empty

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


(* The value type of a pointer: `Mem (addr, byte)`; the emitter lowers
   it to LLVM `ptr`.  The address size is the target's, never a literal. *)
let mem_type_of_target (target : Bap_core_theory.Theory.Target.t) : Type.t =
  let bits = Bap_core_theory.Theory.Target.bits target in
  let addr_size = Hike_abi.addr_size_of_bits bits in
  Type.Mem (addr_size, `r8)

(* Types each pointer SSA version [Mem]: a version has one def, so its
   sort is its type at every occurrence.  An input lane takes its entry
   version's type (a by-reference lane is a pointer), an output lane the
   type of the version it returns.
   Only the sort changes; the ident (name and version) is preserved. *)
let retype_sub ~(mem_typ : Type.t) ~(ptr_vars : Var.Set.t)
    ~(ptr_rets : Var.Set.t) (sub : sub term) : sub term =
  let mem_sort =
    match mem_typ with
    | Type.Mem (a, b) ->
        Bap_core_theory.Theory.Value.Sort.forget
          (Bap_core_theory.Theory.Mem.define
             (Bap_core_theory.Theory.Bitv.define (Size.in_bits a))
             (Bap_core_theory.Theory.Bitv.define (Size.in_bits b)))
    | _ -> assert false
  in
  let to_mem v =
    Var.reify (Bap_core_theory.Theory.Var.create mem_sort (Var.ident v))
  in
  let repl v = if Core.Set.mem ptr_vars v then to_mem v else v in
  (object
     inherit Term.mapper as super

     method! map_sym v = repl v
     method! map_def d = Def.with_lhs (super#map_def d) (repl (Def.lhs d))
     method! map_phi p = Phi.with_lhs (super#map_phi p) (repl (Phi.lhs p))
     method! map_jmp j =
       super#map_jmp j |> Model.map_effects ~read:repl ~write:repl
     method! map_arg a =
       let ret = Model.is_ret a in
       let lhs = Arg.lhs a in
       let ptr =
         if ret then Core.Set.mem ptr_rets lhs
         else Core.Set.mem ptr_vars lhs || Model.is_ptr_arg a
       in
       (* An output lane is typed by [ptr_rets] alone: an input fact on
          the same register does not reach it. *)
       if ret && not ptr then a
       else
         let a' = super#map_arg a in
         if not ptr then a'
         else
           Term.with_attrs
             (Arg.create ~tid:(Term.tid a') ?intent:(Arg.intent a')
                (to_mem lhs) (Arg.rhs a'))
             (Term.attrs a')
   end)#map_sub sub

(* The signature pass: write every sub's lane list onto its own [arg]
   terms.  It does not need the value types, so it runs BEFORE SSA. *)
let sign_run (proj : Project.t) : Project.t =
  let target = Project.target proj in
  Project.map_program proj ~f:(sign_program ~target)

(* Infer every value's kind over [prog] (per version), stamp the lane
   kinds, and retype the pointer versions. *)
let type_program ~(facts : Hike_kb.facts) ~(mem_typ : Type.t)
    (prog : program term) : program term =
  let sub_of = sub_of_program prog in
  let pks, inferred = ptr_kinds ~facts ~sub_of prog in
  let ptr_vars_of_sub = ptr_vars_of ~pks ~inferred in
  let prog =
    Term.map sub_t prog ~f:(fun sub ->
        let pf =
          Core.Map.find inferred (Term.tid sub)
          |> Base.Option.value ~default:ptr_facts_empty
        in
        let sub = Hike_def_slots.stamp_ptr_kinds ~ptr_tids:pf.def_tids sub in
        let sub =
          Hike_def_slots.stamp_ptr_storages ~storages:pf.def_storages sub
        in
        let ptr_vars =
          Core.Set.union (ptr_vars_of_sub sub) (address_versions ~facts sub)
        in
        let ptr_rets = ptr_returns ~facts sub ptr_vars in
        retype_sub ~mem_typ ~ptr_vars ~ptr_rets sub)
  in
#ifdef VSA_DEBUG
  kind_census prog;
#endif
  prog

(* The type pass: [type_program] on the SSA program.  The emitter reads
   [Var.typ]. *)
let run (proj : Project.t) : Project.t =
  let mem_typ = mem_type_of_target (Project.target proj) in
  Project.map_program proj ~f:(fun prog ->
      match Hike_kb.facts_opt () with
      | None -> prog
      | Some facts -> type_program ~facts ~mem_typ prog)
