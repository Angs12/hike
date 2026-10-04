(* The VSA: the solver and its CFG-completion loop.  The products are
   the block-boundary environments and the rewritten sub; consumers
   read them through the Hike_kb facts record. *)

open Bap.Std
open Bap_core_theory
module Vsa = Cbat_vsa
module Def_origin = Cbat_vsa.Def_origin
module Model = Hike_stack_model

let set_addr_bits (n : int) : unit = Vsa.set_addr_bits n

(* Every analysis entry self-arms the address width from the target it
   carries — no cross-pass init order exists. *)
let self_arm (target : Theory.Target.t) : unit =
  set_addr_bits (Hike_abi.addr_size_bits target)

type section_image = Vsa.section_image = {
  img_lo : int64;
  img_hi : int64;
  img_bytes : Bytes.t;
  img_slots : Core.Int64.Set.t;
}

(* The per-sub written-register summary: every def whose lhs base is a
   non-virtual register; [Var.base] normalizes partial defs. *)
let written_regs_of_sub (sub : sub term) : Var.Set.t =
  Term.enum blk_t sub
  |> Seq.concat_map ~f:(Term.enum def_t)
  |> Seq.fold ~init:Var.Set.empty ~f:(fun acc d ->
      let lhs = Def.lhs d in
      match Var.typ (Var.base lhs) with
      | Type.Imm _ when not (Var.is_virtual lhs) ->
        Core.Set.add acc (Var.base lhs)
      | _ -> acc)

let kill_summaries ~(abi : Hike_abi.t) (prog : program term) :
    Core.Int.Set.t option Tid.Map.t =
  let subs = Hike_stack_model.sub_map prog in
  let reads_retaddr (rhs : exp) : bool =
    Base.Option.value_map (Model.addr_of_rhs rhs) ~default:false
      ~f:(fun (addr, _) -> Model.is_return_address_shape ~abi addr)
  in
  (* The sub's call sites: a lifted direct callee, a kill-all site (an
     indirect target, trap, or extern), or no site (the return epilogue
     is no mark at all). *)
  let sites (s : sub term) : Tid.t list * bool =
    Term.enum blk_t s
    |> Seq.concat_map ~f:(fun blk ->
        let last =
          Core.Map.fold (Vsa.last_defs blk) ~init:Var.Map.empty
            ~f:(fun ~key ~data acc ->
                Core.Map.set acc ~key:(Var.base key)
                  ~data:(Def.rhs data))
        in
        Term.enum jmp_t blk
        |> Seq.filter_map ~f:(fun j ->
            match Jmp.kind j with
            | Int _ -> Some `Kill
            | Call c when not (Hike_return.is_jmp j) -> (
                match Call.target c with
                | Indirect (Bil.Var v)
                | Indirect (Bil.Cast (_, _, Bil.Var v))
                  when Base.Option.is_none (Call.return c) -> (
                    match Core.Map.find last (Var.base v) with
                    | Some rhs when reads_retaddr rhs -> None
                    | _ -> Some `Kill)
                | Indirect _ -> Some `Kill
                | Direct t ->
                  if Core.Map.mem subs t then Some (`Call t) else Some `Kill)
            | _ -> None))
    |> Seq.fold ~init:([], false) ~f:(fun (edges, kill) site ->
        match site with
        | `Kill -> (edges, true)
        | `Call c -> (c :: edges, kill))
  in
  (* The may-write summary is the least fixpoint of
     [direct(s) ∪ ⋃ callees' summaries] over the direct-call graph; a
     cycle unions its members instead of killing the whole component.
     A kill-all site or a kill-all callee makes its callers kill-all. *)
  let written = ref Tid.Map.empty in
  let kill = ref Tid.Set.empty in
  let callers = ref Tid.Map.empty in
  Term.enum sub_t prog
  |> Seq.iter ~f:(fun s ->
      let stid = Term.tid s in
      let edges, own_kill = sites s in
      written := Core.Map.set !written ~key:stid ~data:(written_regs_of_sub s);
      if own_kill then kill := Core.Set.add !kill stid;
      Base.List.iter edges ~f:(fun c ->
          callers := Core.Map.add_multi !callers ~key:c ~data:stid));
  let work = ref (Core.Set.of_list (module Tid) (Core.Map.keys !written)) in
  while not (Core.Set.is_empty !work) do
    let t = Core.Set.choose_exn !work in
    work := Core.Set.remove !work t;
    Base.List.iter
      (Base.Option.value (Core.Map.find !callers t) ~default:[])
      ~f:(fun p ->
        if not (Core.Set.mem !kill p) then begin
          let changed =
            if Core.Set.mem !kill t then begin
              kill := Core.Set.add !kill p;
              true
            end
            else
              match Core.Map.find !written t with
              | None -> false
              | Some ws ->
                let before =
                  Base.Option.value (Core.Map.find !written p)
                    ~default:Var.Set.empty in
                let after = Core.Set.union before ws in
                if Core.Set.equal before after then false
                else begin
                  written := Core.Map.set !written ~key:p ~data:after;
                  true
                end
          in
          if changed then work := Core.Set.add !work p
        end)
  done;
  Term.enum sub_t prog
  |> Seq.fold ~init:Tid.Map.empty ~f:(fun m s ->
      let stid = Term.tid s in
      let v =
        if Core.Set.mem !kill stid then None
        else
          Some
            (Cbat_var_id.intern_set
               (Base.Option.value (Core.Map.find !written stid)
                  ~default:Var.Set.empty))
      in
      Core.Map.set m ~key:stid ~data:v)

(* One computation per program, at the pass_vsa boundary; the fixpoint
   consumes the summaries per phase. *)

(* The fused solve: each phase runs the engine over the resolved
   extra-edge set, then the resolver grows the edges and splits
   mid-block case entries — a resolution event — and the next phase
   solves warm.  The BIR's claims are immutable during the solve; at
   drain the materialization lands once.  Non-convergence is the top
   identity: empty environments, the shape-canonicalized sub, the
   input block-address map. *)
type lookup_fn = int64 -> Tid.t option

let fixpoint (target : Theory.Target.t)
    ~(lookup : lookup_fn)
    ~(sub_addrs : Tid.t Addr.Map.t)
    ~(images : Vsa.section_image list)
    ~(written : Core.Int.Set.t option Tid.Map.t)
    ~(block_addrs : Tid.t Addr.Map.t)
    ~(foreign_slots : Core.Int64.Set.t)
    ?(code_range : (int64 * int64) option = None)
    (sub : sub term) :
    (Vsa.AI.t * Vsa.AI.t) Tid.Map.t * sub term * Tid.t Addr.Map.t
    * (Addr.t * bool * Cbat_word.t list) list =
  self_arm target;
  let abi = Hike_abi.of_target target in
#ifdef VSA_DEBUG
  let dump_r8 (sol : Vsa.vsa_sol) (sub : sub term) =
    let rep = Base.List.nth_exn abi.Hike_abi.int_param_regs 4 in
    Term.enum blk_t sub
    |> Seq.iter ~f:(fun b ->
        if Sub.name sub = "main" then
          let st = Graphlib.Std.Solution.get sol (Term.tid b) in
          let w = Vsa.AI.find_word 64 st rep in
          Printf.eprintf "hike-r8: blk %s R8 top=%b lo=%s\n%!"
            (Tid.name (Term.tid b))
            (Vsa.WordSet.is_top w)
            (match Base.Option.map (Vsa.WordSet.min_elem w) ~f:(fun x -> match Cbat_word.to_int64 x with Ok v -> Printf.sprintf "%Lx" v | Error _ -> "err") with Some v -> v | None -> "none"))
  in
#endif
  (* The images arm the whole fused solve: every denotation the
     phases, the completion's rewrites, and the replay compute reads
     them through one bracket. *)
  Vsa.with_images images (fun () ->
      let rec phases (sub : sub term) (resolved : Tid.Set.t Tid.Map.t)
          (block_addrs : Tid.t Addr.Map.t)
          (dfacts : (Addr.t * bool * Cbat_word.t list) list)
          (init : Vsa.vsa_sol option) =
        let seed = match init with Some s -> s | None -> Vsa.init_sol ~abi sub in
        let sol =
          Vsa.static_graph_vsa ~abi ~written ~resolved ~sub_lookup:lookup
            sub seed
        in
#ifdef VSA_DEBUG
        dump_r8 sol sub;
#endif
        let sub', resolved', block_addrs', facts, events =
          Hike_cfg_complete.resolve_phase ~abi ~sol ~images
            ~block_addrs
            ~sub_addrs ~foreign_slots ~code_range:code_range
            sub resolved
        in
        let dfacts = Base.List.append dfacts facts in
        if events then phases sub' resolved' block_addrs' dfacts (Some sol)
        else (sol, sub', block_addrs', dfacts)
      in
      let converged =
        try Some (phases sub Tid.Map.empty block_addrs [] None)
        with Vsa.Fixpoint_not_converged (n, _) ->
#ifdef VSA_DEBUG
          Vsa.Cbat_attr_census.bump "backstop.sub";
#endif
          Hike_diag.warn
            "vsa: sub %s: fixpoint not converged in %d iterations — shape return canonicalization only (every other reader takes the top identity)"
            (Sub.name sub) n;
          None
      in
      match converged with
      | Some (sol, sub', block_addrs', dfacts) ->
        let sub'' =
          Hike_cfg_complete.materialize ~abi ~sol ~images ~block_addrs:block_addrs'
            ~foreign_slots ~code_range:code_range sub'
        in
        (* The round-down normalization rides the returned sub: the
           attribution re-denotes from these rhs's, and the solve's
           materialization may reintroduce the shift pair. *)
        let sub'' = Vsa.normalize_round sub'' in
        let envs, stamped = Vsa.stamp_envs_of_sol ~sol sub'' in
        (envs, stamped, block_addrs', dfacts)
      | None ->
        ( Tid.Map.empty,
          Hike_cfg_complete.canonicalize_shape_returns ~abi sub,
          block_addrs,
          [] ))
