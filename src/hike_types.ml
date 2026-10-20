(* The emission signature, and the home of each lane's TYPE.  Every sub's
   arguments and returns are computed once here and written onto the sub's
   own [arg] terms (the returns are the [Out] intents); each lane carries
   its pointer-ness.  The emitter reads them off the sub — no side table. *)

open Bap.Std

module Model = Hike_stack_model
module Abi = Hike_abi

let return_lanes = Model.return_lanes

(* A lane is a pointer when it is an address lane: a by-reference
   argument, a memory var (its storage), or the caller window. *)
let tag_lane ~(synth : Hike_synth.table) (a : Arg.t) : Arg.t =
  let v = Arg.lhs a in
  if
    Arg.intent a = Some Both
    || Model.is_mem v
    || Model.is_window_var synth v
  then Model.set_ptr_arg a
  else a

(* The sub's entry reads: its SSA index-0 reads, without memory-sorted
   values (pointer values take their lane after the type pass).  Signing
   assumes an SSA program. *)
let free_regs_of_sub ~(synth : Hike_synth.table)
    ~(target : Bap_core_theory.Theory.Target.t)
    (sub : sub term) : var list =
  Hike_ssa.free_regs_ssa ~synth ~abi:(Abi.of_target target) sub
  |> Base.List.filter ~f:(fun v ->
         match Var.typ v with Type.Mem _ -> false | _ -> true)

let compute_sub_sig ~(synth : Hike_synth.table) ~(free_vars : var list)
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
                (* Its lane is the base variable: the versions are the body's. *)
                let v = Var.base (Def.lhs d) in
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
              || Model.is_arg_slot synth (Var.base reg)
              || Model.is_call_arg synth (Var.base reg)
              || Model.is_window_var synth reg
              || Model.is_storage_base synth reg))
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
  ( Base.List.map rets ~f:(tag_lane ~synth),
    Base.List.map args ~f:(tag_lane ~synth) )

(* The sign pass's one per-sub entry: the PLT-trampoline stamp (the
   emitter reads it) and the lane list. *)
let sign_sub ~(synth : Hike_synth.table)
    ~(target : Bap_core_theory.Theory.Target.t)
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
  let free_vars = free_regs_of_sub ~synth ~target sub in
  let rets, args = compute_sub_sig ~synth ~free_vars target sub in
  Model.set_sig sub (rets @ args)

(* The pipeline's pass, and any direct emitter caller (the fixtures),
   run exactly this: every sub signs on the SSA the drive built, whose
   calls read the machine convention; then each call narrows to its
   callee's signed lanes. *)
let sign_program ~(synth : Hike_synth.table)
    ~(target : Bap_core_theory.Theory.Target.t)
    (prog : program term) : program term =
  let open Graphlib.Std in
  let module G = Graphs.Callgraph in
  let originals = Term.enum sub_t prog
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m sub ->
        Core.Map.set m ~key:(Term.tid sub) ~data:sub) in
  let graph = Program.to_graph prog in
  let graph = G.nodes graph |> Seq.fold ~init:graph ~f:(fun g tid ->
      if Core.Map.mem originals tid then g else G.Node.remove tid g) in
  let partition = Graphlib.strong_components (module G) graph in
  let summaries = ref (Core.Map.map originals ~f:(sign_sub ~synth ~target)) in
  let lanes sub = Term.enum arg_t sub |> Seq.to_list
    |> Base.List.map ~f:(fun a -> (Arg.lhs a, Arg.intent a)) in
  Graphlib.postorder_traverse (module G) graph
  |> Seq.iter ~f:(fun tid ->
      let group = Partition.group partition tid |> Base.Option.value_exn in
      if Tid.equal tid (Group.top group) then begin
        let members = Group.enum group |> Seq.to_list in
        let changed = ref true in
        while !changed do
          changed := false;
          Base.List.iter members ~f:(fun tid ->
              let old = Core.Map.find_exn !summaries tid in
              let sub = Hike_ssa.relane_sub ~synth ~target
                  ~callee:(Core.Map.find !summaries) old in
              let original = Core.Map.find_exn originals tid in
              let sub = Model.set_sig sub (Term.enum arg_t original |> Seq.to_list)
                |> sign_sub ~synth ~target in
              if not (Base.List.equal
                        (fun (a, i) (b, j) -> Var.same a b && i = j)
                        (lanes old) (lanes sub)) then changed := true;
              summaries := Core.Map.set !summaries ~key:tid ~data:sub)
        done
      end);
  Term.map sub_t prog ~f:(fun sub -> Core.Map.find_exn !summaries (Term.tid sub))

(* ---- The value kind (ptr vs int) ----
   A value is a pointer when it is a bounded stack address (the VSA
   denotation, computed pre-SSA where it resolves), flows from one
   (a copy, an offset, an ite), or is used as a load/store address.
   Provenance and use are one joint fixpoint ([ptr_defs]); the emitter's
   ptr discipline consumes it. *)

module Vsa = Cbat_vsa

(* SP and the caller window hold addresses in every SSA version. *)
let is_address_reg ~(facts : Hike_kb.facts) (v : var) : bool =
  Var.same v facts.Hike_kb.abi.Hike_abi.sp
  || Model.is_window_var facts.Hike_kb.synth v

let passed_at = Model.passed_version
let minted_at = Model.boundary_write

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

(* An address expression's candidate bases, read once: a lone var, or the
   spine's vars (each with its lazily-decided seed-independent base
   status). *)
type site =
  | Lone of var
  | Spine of (var * bool Lazy.t) list

(* Forward provenance and backward address uses meet at a local monotone
   fixpoint over SSA versions (int <= ptr).  Callee contracts seed the
   call results and pointer arguments; storage still needs a VSA proof.
   One Bir_flow closure carries the local solve; the seed list survives
   across calls so a growing recursive callee's contract is re-seeded. *)
let ptr_solver ~(facts : Hike_kb.facts) (sub : sub term) :
    extra:Var.Set.t -> used:Var.Set.t -> ptr_facts =
  let layout =
    Base.Option.value (Term.get_attr sub Hike_stack_model.layout_tag)
      ~default:
        { Hike_stack_model.Sub_layout.regions = [];
          window_param = false;
          runtime_residue = false }
  in
  let word = facts.Hike_kb.abi.Hike_abi.word in
  let rec spine (e : exp) =
    match e with
    | Bil.Var v -> [ v ]
    | Bil.Ite (_, a, b) | Bil.BinOp (Bil.PLUS, a, b) -> spine a @ spine b
    | Bil.BinOp (Bil.MINUS, a, _) -> spine a
    | _ -> []
  in
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
      (Hike_stack_model.is_region_mem facts.Hike_kb.synth v
      || Hike_stack_model.is_window_mem facts.Hike_kb.synth v
      || Hike_stack_model.is_sec_comp_mem facts.Hike_kb.synth v)
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
  (* The entry SP is a pointer by construction; the window lane too. *)
  let roots =
    [ facts.Hike_kb.abi.Hike_abi.sp;
      Hike_stack_model.hike_window_var ~word:facts.Hike_kb.abi.Hike_abi.word ]
  in
  (* Every var [is_ptr] sees occurs in the sub: classify each once. *)
  let addrs = Var.Table.create () in
  Core.Set.iter (address_versions ~facts sub) ~f:(fun v ->
      Core.Hashtbl.set addrs ~key:v ~data:());
  let is_ptr holds v = holds v || Core.Hashtbl.mem addrs v in
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
  (* The vars whose pointer-ness carries to an expression's value. *)
  let rec shape_vars acc (e : exp) : var list =
    match e with
    | Bil.Var v -> v :: acc
    | Bil.BinOp ((Bil.PLUS | Bil.MINUS), a, b) | Bil.Ite (_, a, b) ->
        shape_vars (shape_vars acc a) b
    | _ -> acc
  in
  (* The stack-denoted value defs: independent of the seeds. *)
  let denot_vars =
    Base.List.filter_map defs ~f:(fun (_, d) ->
        if Core.Map.mem stack_denots (Term.tid d) && value_def d then
          Some (Def.lhs d)
        else None)
  in
  let fixed_lanes = Var.Table.create () in
  if Model.fixed_signature sub then
    Base.List.iter (Model.sig_args sub) ~f:(fun a ->
        Core.Hashtbl.set fixed_lanes ~key:(Arg.lhs a) ~data:());
  let def_of = Var.Table.create () in
  Base.List.iter defs ~f:(fun (_, d) ->
      Core.Hashtbl.set def_of ~key:(Def.lhs d) ~data:d);
  (* Only a version that can hold a pointer: an address-width value, not
     a fixed signature's lane. *)
  let use_ok v =
    is_value_var v
    && (match Var.typ v with Type.Imm n -> Int.equal n addr_width | _ -> false)
    && (not (Core.Hashtbl.mem fixed_lanes v))
    && (match Core.Hashtbl.find def_of v with
        | Some d -> value_def d
        | None -> true)
  in
  let blk_of_def =
    Base.List.fold defs ~init:Tid.Map.empty ~f:(fun m (blk, d) ->
        Core.Map.set m ~key:(Term.tid d) ~data:blk)
  in
  let synth = ref facts.Hike_kb.synth in
  let storages =
    Hike_sections.spans_of_layout ~synth ~word layout
  in
  let synth = !synth in
  (* The vars an address expression is based on, read off the
     denotation's leaf census ([Hike_synth_addr.address_leaves]).  A lone
     var is the address itself.  On the additive spine, a leaf that is a
     stack, storage or module address, or already proven a pointer, is
     the base and the visible [Int] leaves are indices.  With no such
     evidence there is no base: a var the denotation does not know is an
     integer.  Everything but "already proven a pointer" is read once per
     expression into a [site]. *)
  let site_of d (e : exp) : site =
    match (e, Core.Map.find blk_of_def (Term.tid d)) with
    | Bil.Var v, _ -> Lone v
    | _, None -> Spine []
    | _, Some blk ->
        let vs = spine e in
        (* The denotation keys on the base register: its value in the
           before-env of [d] is the version's. *)
        let leaves =
          Hike_synth_addr.address_leaves ~synth
            ~denote:facts.Hike_kb.denote ~storages ~blk ~def:d
            ((object
                inherit Exp.mapper
                method! map_sym v = Var.base v
              end)#map_exp e)
        in
        let leaf v = Core.Map.find leaves (Var.base v) in
        (* A module address is an [Int] piece to attribution's folding but
           a base here: by its synthetic identity or a module origin. *)
        let module_base v =
          (match Hike_synth.classify synth (Var.base v) with
           | Some (Hike_synth.Module_addr _) -> true
           | _ -> false)
          || (match facts.Hike_kb.denote ~blk ~def:d (Bil.Var v) with
              | Ok ws -> (
                  match Vsa.WordSet.origin ws with
                  | Some (Hike_origin.Rip _) -> true
                  | _ -> false)
              | Error _ -> false)
        in
        let fixed v =
          lazy
            ((match leaf v with
              | Some (`Static _ | `Addr) -> true
              | Some `Int | None -> false)
             || module_base v)
        in
        Spine (Base.List.map vs ~f:(fun v -> (v, fixed v)))
  in
  let sites =
    Base.List.fold defs ~init:Tid.Map.empty ~f:(fun m (_, d) ->
        let addr =
          Base.Option.map (Hike_stack_model.addr_of_rhs (Def.rhs d))
            ~f:(fun (a, _) -> lazy (site_of d a))
        in
        Core.Map.set m ~key:(Term.tid d)
          ~data:(addr, lazy (site_of d (Def.rhs d))))
  in
  let bases holds (site : site Lazy.t) : var list =
    match Lazy.force site with
    | Lone v -> [ v ]
    | Spine vs ->
        Base.List.filter_map vs ~f:(fun (v, fixed) ->
            if is_ptr holds v || Lazy.force fixed then Some v else None)
  in
  (* Pointer-ness is a fact of a version: provenance (a pointer operand
     makes the result one) and use (an address base, or an operand of a
     pointer, is one) close together in one flow-insensitive solve. *)
  let use_all add vs = Base.List.iter vs ~f:(fun v -> if use_ok v then add v) in
  let def_rules (_, d) =
    let lhs = Def.lhs d in
    let addr, rhs = Core.Map.find_exn sites (Term.tid d) in
    let provenance =
      if value_def d then
        let vs = shape_vars [] (Def.rhs d) in
        [ { Hike_bir_flow.reads = vs;
            fire =
              (fun ~holds ~add ->
                if Base.List.exists vs ~f:(fun v -> is_ptr holds v || Model.is_mem v)
                then add lhs) } ]
      else []
    in
    let addr_use =
      match (addr, Hike_stack_model.addr_of_rhs (Def.rhs d)) with
      | Some a, Some (e, _) ->
          [ { Hike_bir_flow.reads = spine e;
              fire = (fun ~holds ~add -> use_all add (bases holds a)) } ]
      | _ -> []
    in
    let rhs_use =
      { Hike_bir_flow.reads = lhs :: spine (Def.rhs d);
        fire =
          (fun ~holds ~add ->
            if holds lhs then use_all add (bases holds rhs)) }
    in
    provenance @ addr_use @ [ rhs_use ]
  in
  let phi_rules p =
    let lhs = Phi.lhs p in
    let incoming =
      Phi.values p
      |> Seq.filter_map ~f:(fun (_, e) ->
             match e with Bil.Var v -> Some v | _ -> None)
      |> Seq.to_list
    in
    (if is_value_var lhs then
       [ { Hike_bir_flow.reads = incoming;
           fire =
             (fun ~holds ~add ->
               if Base.List.exists incoming ~f:(is_ptr holds) then add lhs) } ]
     else [])
    @ [ { Hike_bir_flow.reads = [ lhs ];
          fire = (fun ~holds ~add -> if holds lhs then use_all add incoming) } ]
  in
  let solve =
    Hike_bir_flow.closure
      (Base.List.concat_map defs ~f:def_rules
       @ (Term.enum blk_t sub
          |> Seq.concat_map ~f:(Term.enum phi_t)
          |> Seq.to_list
          |> Base.List.concat_map ~f:phi_rules))
  in
  (* The previous solve's pointers: seeds only grow across solves, so
     they stay below the next solution. *)
  let last = ref [] in
  (* The storage of each pointer def: the denotation's, else inherited
     from a pointer operand. *)
  let rec struct_storage (var_stors : Hike_stack_model.ptr_storage Var.Map.t)
      (e : exp) : Hike_stack_model.ptr_storage option =
    match e with
    | Bil.Var v -> (
        match Hike_stack_model.region_ptr_id_of facts.Hike_kb.synth (Var.base v) with
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
  let rec stor_loop ptrs stors var_stors =
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
    else stor_loop ptrs stors' var_stors'
  in
  fun ~extra ~used ->
    let members =
      solve
        (roots @ Core.Set.to_list extra @ !last @ denot_vars
         @ Base.List.filter (Core.Set.to_list used) ~f:use_ok)
    in
    last := members;
    let ptrs = Var.Set.of_list members in
    let stors, _ = stor_loop ptrs Tid.Map.empty Var.Map.empty in
    let tids =
      Base.List.fold defs ~init:Tid.Set.empty ~f:(fun acc (_, d) ->
          if Core.Set.mem ptrs (Def.lhs d) then Core.Set.add acc (Term.tid d)
          else acc)
    in
    { def_tids = tids; def_storages = stors; vars = ptrs }

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

let pointer_lanes lanes =
  Base.List.filter_map lanes ~f:(fun a ->
      match Var.typ (Arg.lhs a) with
      | Type.Mem _ -> Some (Arg.lhs a)
      | _ when Model.is_ptr_arg a -> Some (Arg.lhs a)
      | _ -> None)

let type_sub ~facts ~mem_typ sub (pf : ptr_facts) =
  let ptr_vars = Core.Set.union pf.vars (address_versions ~facts sub) in
  let ptr_rets = ptr_returns ~facts sub ptr_vars in
  sub
  |> Hike_def_slots.stamp_ptr_kinds ~ptr_tids:pf.def_tids
  |> Hike_def_slots.stamp_ptr_storages ~storages:pf.def_storages
  |> retype_sub ~mem_typ ~ptr_vars ~ptr_rets

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

(* Callees publish concrete argument and return types before their
   callers solve.  Only members of a recursive component can resume;
   their declared lane types are the component's initial summaries. *)
let type_program ~(facts : Hike_kb.facts) ~(mem_typ : Type.t)
    (prog : program term) : program term =
  let open Graphlib.Std in
  let module G = Graphs.Callgraph in
  let sub_of =
    Term.enum sub_t prog
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m sub ->
           Core.Map.set m ~key:(Term.tid sub) ~data:sub)
  in
  let graph = Program.to_graph prog in
  (* Targets without a sub term are native/external transfers, not
     members of the program's type-inference call graph. *)
  let graph =
    G.nodes graph
    |> Seq.fold ~init:graph ~f:(fun g tid ->
           if Core.Map.mem sub_of tid then g else G.Node.remove tid g)
  in
  let partition = Graphlib.strong_components (module G) graph in
  let components =
    Graphlib.postorder_traverse (module G) graph
    |> Seq.filter_map ~f:(fun tid ->
           let group = Partition.group partition tid |> Base.Option.value_exn in
           (* An SCC's DFS root exits after all of its callees. *)
           if Tid.equal tid (Group.top group) then
             Some (Group.enum group |> Seq.to_list)
           else None)
  in
  let calls =
    Core.Map.map sub_of ~f:(fun sub ->
        fold_direct_calls sub ~init:[] ~f:(fun acc blk tid ->
            if Core.Map.mem sub_of tid then (blk, tid) :: acc else acc)
        |> Base.List.rev)
  in
  let summaries = ref Tid.Map.empty in
  Seq.iter components ~f:(fun members ->
      let member_set = Tid.Set.of_list members in
      let solvers =
        Base.List.fold members ~init:Tid.Map.empty ~f:(fun m tid ->
            let sub = Core.Map.find_exn sub_of tid in
            summaries := Core.Map.set !summaries ~key:tid ~data:sub;
            Core.Map.set m ~key:tid ~data:(ptr_solver ~facts sub))
      in
      let pending = Stdlib.Queue.create () in
      let queued = ref member_set in
      Base.List.iter members ~f:(fun tid -> Stdlib.Queue.add tid pending);
      while not (Stdlib.Queue.is_empty pending) do
        let tid = Stdlib.Queue.take pending in
        queued := Core.Set.remove !queued tid;
        let sub = Core.Map.find_exn sub_of tid in
        let extra, used =
          Base.List.fold (Core.Map.find_exn calls tid)
            ~init:
              (Var.Set.of_list (pointer_lanes (Model.sig_args sub)), Var.Set.empty)
            ~f:(fun (extra, used) (blk, target) ->
              let callee = Core.Map.find_exn !summaries target in
              let extra =
                Base.List.fold (pointer_lanes (Model.sig_rets callee))
                  ~init:extra ~f:(fun extra r ->
                    match minted_at blk r with
                    | Some v -> Core.Set.add extra v
                    | None -> extra)
              in
              let used =
                Base.List.fold (pointer_lanes (Model.sig_args callee))
                  ~init:used ~f:(fun used r ->
                    match passed_at blk r with
                    | Some v -> Core.Set.add used v
                    | None -> used)
              in
              (extra, used))
        in
        let pf = (Core.Map.find_exn solvers tid) ~extra ~used in
        let typed = type_sub ~facts ~mem_typ sub pf in
        let old = Core.Map.find_exn !summaries tid in
        let changed =
          not (Base.List.equal Var.same (pointer_lanes (Model.sig_args old))
                 (pointer_lanes (Model.sig_args typed)))
          || not (Base.List.equal Var.same (pointer_lanes (Model.sig_rets old))
                    (pointer_lanes (Model.sig_rets typed)))
        in
        summaries := Core.Map.set !summaries ~key:tid ~data:typed;
        if changed then
          G.Node.inputs tid graph
          |> Seq.iter ~f:(fun edge ->
                 let caller = G.Edge.src edge in
                 if Core.Set.mem member_set caller
                    && not (Core.Set.mem !queued caller) then begin
                   queued := Core.Set.add !queued caller;
                   Stdlib.Queue.add caller pending
                 end)
      done);
  let prog =
    Term.map sub_t prog ~f:(fun sub ->
        Core.Map.find_exn !summaries (Term.tid sub))
  in
#ifdef VSA_DEBUG
  kind_census prog;
#endif
  prog

(* The signature pass: write every sub's lane list onto its own [arg]
   terms.  It does not need the value types. *)
let sign_run (proj : Project.t) : Project.t =
  let target = Project.target proj in
  let synth =
    match Hike_kb.facts_opt () with
    | Some facts -> facts.Hike_kb.synth
    | None -> Hike_synth.empty
  in
  Project.map_program proj ~f:(sign_program ~synth ~target)

(* The type pass: [type_program].  The emitter reads [Var.typ]. *)
let run (proj : Project.t) : Project.t =
  let mem_typ = mem_type_of_target (Project.target proj) in
  Project.map_program proj ~f:(fun prog ->
      match Hike_kb.facts_opt () with
      | None -> prog
      | Some facts -> type_program ~facts ~mem_typ prog)
