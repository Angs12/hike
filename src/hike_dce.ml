(* Sweeps dead defs and phis; region mems survive iff loaded. *)
open Bap.Std
open Bap.Std.Bil.Types
module Abi = Hike_abi
module Model = Hike_stack_model

(* The call-register set, built once per sub's sweep; membership is
   the per-node predicate. *)
let call_reg_set ~(abi : Abi.t) : Var.Set.t =
  Base.List.fold (Abi.param_regs abi @ abi.Abi.return_regs)
    ~init:Var.Set.empty ~f:(fun acc r -> Core.Set.add acc (Var.base r))

let is_call_reg ~(call_regs : Var.Set.t) (v : var) : bool =
  Core.Set.mem call_regs (Var.base v)

(* A sweep node: a def or a phi.  Both define one var and read vars, so
   the worklist treats them alike — a read by a dead phi does not pin its
   operands, and a phi whose result no survivor reads is swept. *)
type body = Def of def term | Phi of phi term

type node = {
  n_tid : Tid.t;
  n_lhs : var;
  n_reads : Var.Set.t;   (* the rhs free vars / the phi's incomings *)
  n_loads : Var.Set.t;   (* the load mem vars (defs only) *)
  n_body : body;
}

let def_node (d : def term) : node =
  {
    n_tid = Term.tid d;
    n_lhs = Def.lhs d;
    n_reads = Model.def_reads d;
    n_loads = Model.load_mem_vars (Def.rhs d);
    n_body = Def d;
  }

let phi_node (p : phi term) : node =
  {
    n_tid = Term.tid p;
    n_lhs = Phi.lhs p;
    n_reads = Model.phi_reads p;
    n_loads = Var.Set.empty;
    n_body = Phi p;
  }

(* The sweep census: contributor counts behind [used]/[roots].  Jmp
   mentions are permanent (a jump is never removed); [cnt]/[rcnt] count
   SURVIVING nodes mentioning each var, so a var leaves its set exactly
   when its count hits zero outside [perm] and the cascade re-checks
   precisely the nodes whose [keep] verdict could have flipped. *)
type sweep_census = {
  nodes : node Tid.Map.t;
  (* Nodes whose lhs is the key var (re-check set when the var leaves). *)
  by_lhs : Tid.Set.t Var.Map.t;
  reads : Var.Set.t Tid.Map.t;
  loads : Var.Set.t Tid.Map.t;
  cnt : int Var.Map.t;
  rcnt : int Var.Map.t;
  perm : Var.Set.t;
  (* The SP versions the emitter resolves through a block's SSA stamp:
     its defs/phis must survive even with no BIR read. *)
  versions : Var.Set.t;
}

let sweep_census_of ~(sp : var) (sub : sub term) : sweep_census =
  let bump m v =
    Core.Map.update m v ~f:(function None -> 1 | Some n -> n + 1)
  in
  let bump_all m vs = Core.Set.fold vs ~init:m ~f:(fun m v -> bump m v) in
  let init =
    {
      nodes = Tid.Map.empty;
      by_lhs = Var.Map.empty;
      reads = Tid.Map.empty;
      loads = Tid.Map.empty;
      cnt = Var.Map.empty;
      rcnt = Var.Map.empty;
      perm = Var.Set.empty;
      versions = Var.Set.empty;
    }
  in
  let add acc (n : node) =
    let by_lhs =
      Core.Map.update acc.by_lhs n.n_lhs ~f:(function
        | None -> Tid.Set.singleton n.n_tid
        | Some s -> Core.Set.add s n.n_tid)
    in
    {
      acc with
      nodes = Core.Map.set acc.nodes ~key:n.n_tid ~data:n;
      by_lhs;
      reads = Core.Map.set acc.reads ~key:n.n_tid ~data:n.n_reads;
      loads = Core.Map.set acc.loads ~key:n.n_tid ~data:n.n_loads;
      cnt = bump_all acc.cnt n.n_reads;
      rcnt = bump_all acc.rcnt n.n_loads;
    }
  in
  (* The emitter reads the SP version of a block through the stamp's
     [entry]/[args] maps; both must resolve. *)
  let versions_of acc blk =
    match Term.get_attr blk Model.versions_tag with
    | None -> acc
    | Some vs ->
      let sp_vers =
        Base.List.filter_map
          (vs.Model.Versions.entry @ vs.Model.Versions.args)
          ~f:(fun (b, v) -> if Var.same b sp then Some v else None)
      in
      Core.Set.union acc (Core.Set.of_list (module Var) sp_vers)
  in
  let census_blk acc blk =
    let acc =
      Term.enum def_t blk
      |> Seq.fold ~init:acc ~f:(fun a d -> add a (def_node d))
    in
    let acc =
      Term.enum phi_t blk
      |> Seq.fold ~init:acc ~f:(fun a p -> add a (phi_node p))
    in
    let jreads =
      Term.enum jmp_t blk
      |> Seq.fold ~init:Var.Set.empty ~f:(fun a j ->
             Core.Set.union a (Model.jmp_operand_reads j))
    in
    {
      acc with
      perm = Core.Set.union acc.perm jreads;
      versions = versions_of acc.versions blk;
    }
  in
  Term.enum blk_t sub |> Seq.fold ~init ~f:census_blk

(* A def survives when a survivor reads its lhs, it is an always-kept
   lane (an ABI return/param register, a call argument, an intrinsic
   result), or its lhs is [Mem]-sorted — the raw memory lane and, after
   [hike-types], every pointer value.  Region and section-component
   storages survive iff loaded; the incoming window survives
   unconditionally (its stores are the call's outgoing arguments, read
   by the callee). *)
let keep_def ~(load_roots : Var.Set.t) ~(abi : Abi.t)
    ~(call_regs : Var.Set.t) ~(versions : Var.Set.t) (d : def term)
    (used : Var.Set.t) : bool =
  let lhs = Def.lhs d in
  if Model.is_window_mem lhs then true
  else if Model.is_region_mem lhs || Model.is_sec_comp_mem lhs then
    Core.Set.mem load_roots lhs
  else
    Core.Set.mem used lhs || Abi.is_return_reg abi (Var.base lhs)
    || Abi.is_env_reg abi (Var.base lhs)
    || Model.is_mem lhs
    || Model.is_call_arg lhs
    || is_call_reg ~call_regs lhs
    || Core.Set.mem versions lhs
    (* Mapped-intrinsic results keep hike's own [intrinsic:<name>]
       var namespace (the sub-level [Sub.intrinsic] attr is BAP's
       twin fact for the whole sub). *)
    || Hike_abi.is_intrinsic_name (Var.name (Var.base lhs))

(* A phi survives when a survivor reads its result, it names an ABI lane
   the emitter resolves at the block, or it is one of the SP versions the
   block's SSA stamp hands the emitter.  An environment register's phi
   keeps too: its incomings store the process-global cell. *)
let keep_phi ~(abi : Abi.t) ~(call_regs : Var.Set.t) ~(versions : Var.Set.t)
    (p : phi term) (used : Var.Set.t) : bool =
  let lhs = Phi.lhs p in
  Core.Set.mem used lhs || Abi.is_return_reg abi (Var.base lhs)
  || Abi.is_env_reg abi (Var.base lhs)
  || is_call_reg ~call_regs lhs
  || Core.Set.mem versions lhs

let keep_node ~(load_roots : Var.Set.t) ~(abi : Abi.t)
    ~(call_regs : Var.Set.t) ~(versions : Var.Set.t) (n : node)
    (used : Var.Set.t) : bool =
  match n.n_body with
  | Def d -> keep_def ~load_roots ~abi ~call_regs ~versions d used
  | Phi p -> keep_phi ~abi ~call_regs ~versions p used

(* Incremental sweep: [used] and [load_roots] start exact and stay exact
   (a var leaves only when its last contributor is removed), so each
   [keep] verdict is final. *)
let sweep_worklist ~(abi : Abi.t) ~(sp : var) ~(call_regs : Var.Set.t)
    ~(roots : Var.Set.t) (sub : sub term) : sub term =
  let census = sweep_census_of ~sp sub in
  let dom m =
    Core.Map.fold m ~init:Var.Set.empty ~f:(fun ~key:v ~data:_ acc ->
        Core.Set.add acc v)
  in
  let used = ref (Core.Set.union census.perm (dom census.cnt)) in
  let load_roots =
    ref
      (Core.Set.union roots (Core.Set.union census.perm (dom census.rcnt)))
  in
  let cnt = ref census.cnt in
  let rcnt = ref census.rcnt in
  let removed = ref Tid.Set.empty in
  (* A contributor leaving can only flip nodes whose lhs it is. *)
  let readers_of v =
    Core.Map.find census.by_lhs v |> Option.value ~default:Tid.Set.empty
  in
  let leave counts v =
    match Core.Map.find !counts v with
    | Some n when n > 1 ->
        counts := Core.Map.set !counts ~key:v ~data:(n - 1);
        false
    | _ ->
        counts := Core.Map.remove !counts v;
        true
  in
  let rec drain = function
    | [] -> ()
    | tid :: rest -> (
        match Core.Map.find census.nodes tid with
        | None -> drain rest
        | Some n ->
            if
              Core.Set.mem !removed tid
              || keep_node ~load_roots:!load_roots ~abi ~call_regs
                   ~versions:census.versions n !used
            then drain rest
            else begin
              removed := Core.Set.add !removed tid;
              (* A jmp read and an escape root are permanent: the last
                 contributor leaving must not evict them. *)
              let unuse counts set permanent v q =
                if
                  leave counts v
                  && not (Core.Set.mem permanent v)
                then begin
                  set := Core.Set.remove !set v;
                  Core.Set.fold (readers_of v) ~init:q ~f:(fun q t ->
                      t :: q)
                end
                else q
              in
              let rest =
                Core.Set.fold
                  (Core.Map.find census.reads tid
                  |> Option.value ~default:Var.Set.empty)
                  ~init:rest
                  ~f:(fun q v -> unuse cnt used census.perm v q)
              in
              let rest =
                Core.Set.fold
                  (Core.Map.find census.loads tid
                  |> Option.value ~default:Var.Set.empty)
                  ~init:rest
                  ~f:(fun q m ->
                    unuse rcnt load_roots
                      (Core.Set.union census.perm roots)
                      m q)
              in
              drain rest
            end)
  in
  drain (Core.Map.keys census.nodes);
  if Core.Set.is_empty !removed then sub
  else
    Term.map blk_t sub ~f:(fun blk ->
        let dead tid = Core.Set.mem !removed tid in
        let blk =
          if Term.enum def_t blk |> Seq.exists ~f:(fun d -> dead (Term.tid d))
          then
            Term.filter def_t blk ~f:(fun d -> not (dead (Term.tid d)))
          else blk
        in
        if Term.enum phi_t blk |> Seq.exists ~f:(fun p -> dead (Term.tid p))
        then Term.filter phi_t blk ~f:(fun p -> not (dead (Term.tid p)))
        else blk)

(* [roots] names the storage mem vars whose bytes escape this sub — their
   stores' reader lives outside it.  Intrinsics pass through. *)
let dce ?(roots = Var.Set.empty) ~target (sub : sub term) : sub term =
  if Term.has_attr sub Sub.intrinsic then sub
  else
    let abi = Abi.of_target target in
    sweep_worklist ~abi ~sp:abi.Abi.sp ~call_regs:(call_reg_set ~abi) ~roots
      sub
