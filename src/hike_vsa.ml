(* The VSA: the solver and its CFG-completion loop.  The products are
   the block-boundary environments and the rewritten sub; consumers
   read them through the Hike_kb facts record. *)

open Bap.Std
open Bap_core_theory
module Vsa = Cbat_vsa
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
    Var.Set.t option Tid.Map.t =
  let subs =
    Term.enum sub_t prog
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m s ->
        Core.Map.set m ~key:(Term.tid s) ~data:s)
  in
  let reads_retaddr (rhs : exp) : bool =
    Base.Option.value_map (Model.addr_of_rhs rhs) ~default:false
      ~f:(fun (addr, _) -> Model.is_return_address_shape ~abi addr)
  in
  let memo = ref Tid.Map.empty in
  let rec summary ~(visited : Tid.Set.t) (s : sub term) : Var.Set.t option =
    let stid = Term.tid s in
    match Core.Map.find !memo stid with
    | Some v -> v
    | None ->
      if Core.Set.mem visited stid then None
      else
        let visited = Core.Set.add visited stid in
        (* Callee marks: [Some None] = a kill-all site (indirect target,
           trap, extern); [Some (Some c)] = a direct known callee.  The
           return epilogue is no mark at all. *)
        let callees =
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
                  | Int _ -> Some None
                  | Call c -> (
                      match Call.target c with
                      | Indirect (Bil.Var v)
                      | Indirect (Bil.Cast (_, _, Bil.Var v))
                        when Base.Option.is_none (Call.return c) -> (
                          match Core.Map.find last (Var.base v) with
                          | Some rhs when reads_retaddr rhs -> None
                          | _ -> Some None)
                      | Indirect _ -> Some None
                      | Direct t -> Some (Core.Map.find subs t))
                  | _ -> None))
          |> Seq.to_list
        in
        let v =
          if Base.List.exists callees ~f:(fun c -> Base.Option.is_none c) then None
          else
            let kill = ref false in
            let ws =
              Base.List.fold callees ~init:(written_regs_of_sub s)
                ~f:(fun acc c ->
                    match Base.Option.bind ~f:(summary ~visited) c with
                    | None -> (kill := true; acc)
                    | Some cw -> Core.Set.union acc cw)
            in
            if !kill then None else Some ws
        in
        memo := Core.Map.set !memo ~key:stid ~data:v;
        v
  in
  Term.enum sub_t prog
  |> Seq.fold ~init:Tid.Map.empty ~f:(fun m s ->
      Core.Map.set m ~key:(Term.tid s) ~data:(summary ~visited:(Tid.Set.empty : Tid.Set.t) s))

(* One computation per program, at the pass_vsa boundary; the fixpoint
   consumes the summaries per phase. *)

(* The fused solve: each phase runs the engine over the resolved
   extra-edge set, then the resolver grows the edges and splits
   mid-block case entries — a resolution event — and the next phase
   solves warm.  The BIR's claims are immutable during the solve; at
   drain the materialization lands once.  [None] = non-convergence:
   no environments, no rewrite — readers take the top identity. *)
let fixpoint (target : Theory.Target.t)
    ~(prog : program term)
    ~(symtab : Symtab.t option)
    ~(images : Vsa.section_image list)
    ~(written : Var.Set.t option Tid.Map.t)
    ~(lift_at : Addr.t -> blk term list option)
    ~(block_addrs : Tid.t Addr.Map.t)
    (sub : sub term) :
    ((Vsa.AI.t * Vsa.AI.t) Tid.Map.t * sub term * Tid.t Addr.Map.t) option =
  self_arm target;
  let abi = Hike_abi.of_target target in
  let sub_lookup =
    Hike_resolve.symtab_lookup ~symtab
      ~name_tid:(Hike_resolve.name_tid_of prog)
  in
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
  let rec phases (sub : sub term) (resolved : Tid.Set.t Tid.Map.t)
      (fresh : Tid.Set.t) (block_addrs : Tid.t Addr.Map.t)
      (init : Vsa.vsa_sol option) =
    let prog' = Program.create ~subs:[ sub ] () in
    let seed = match init with Some s -> s | None -> Vsa.init_sol ~abi sub in
    let sol =
      Vsa.static_graph_vsa ~abi ~written ~resolved ~sub_lookup prog' sub seed
    in
#ifdef VSA_DEBUG
    dump_r8 sol sub;
#endif
    let sub', resolved', fresh', block_addrs', events =
      Hike_cfg_complete.resolve_phase ~abi ~sol ~images ~lift_at ~block_addrs
        sub resolved
    in
    if events then phases sub' resolved' (Core.Set.union fresh fresh') block_addrs' (Some sol)
    else (sol, sub', Core.Set.union fresh fresh', block_addrs')
  in
  match
    try Some (phases sub Tid.Map.empty Tid.Set.empty block_addrs None)
    with Vsa.Fixpoint_not_converged (n, _, _) ->
#ifdef VSA_DEBUG
      Vsa.Cbat_attr_census.bump "backstop.sub";
#endif
      Hike_diag.warn
        "vsa: sub %s: fixpoint not converged in %d iterations — no environments, no rewrite (every reader takes the top identity)"
        (Sub.name sub) n;
      None
  with
  | Some (sol, sub', fresh, block_addrs') ->
    let sub'' =
      Hike_cfg_complete.materialize ~abi ~sol ~images ~block_addrs:block_addrs'
        ~fresh sub'
    in
    let envs, stamped = Vsa.stamp_envs_of_sol ~sol sub'' in
    Some (envs, stamped, block_addrs')
  | None -> None
