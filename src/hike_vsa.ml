(* The VSA: the solver and its CFG-completion loop.  The products are
   the block-boundary environments and the REWRITTEN SUB — nothing
   else crosses to a later pass; every other fact re-derives through
   [denote_exp_at]. *)

open Bap.Std
open Bap_core_theory
module Vsa = Cbat_vsa
module Model = Hike_stack_model

(* Forwards the address width into the VSA. *)
let set_addr_bits (n : int) : unit = Vsa.set_addr_bits n

(* Every analysis entry self-arms the address width from the target it
   carries — no cross-pass init order exists. *)
let self_arm (target : Theory.Target.t) : unit =
  set_addr_bits (Hike_abi.addr_size_bits target)

type section_image = Vsa.section_image = {
  img_lo : int64;
  img_hi : int64;
  img_bytes : int array;
}

(* The consumer seam for environments, three functions: a phi's
   environment is its block's precondition tag, a jmp's is its block's
   postcondition tag, and a def's expression denotes through the replay
   in [denote_exp_at].  Absence (no converged solution) is [AI.top],
   the no-constraint identity. *)
let block_pre (blk : blk term) : Vsa.AI.t =
  Base.Option.value (Base.Option.map (Hike_kb.block_env (Term.tid blk)) ~f:fst)
    ~default:(Vsa.AI.top)

let block_post (blk : blk term) : Vsa.AI.t =
  Base.Option.value (Base.Option.map (Hike_kb.block_env (Term.tid blk)) ~f:snd)
    ~default:(Vsa.AI.top)

(* [e] denotes in the before-env of [def] — the block's defs replay
   from its precondition tag up to [def], the target def's own transfer
   not run — or, with no [def], in the block's postcondition (the full
   replay; the state a jmp reads).  A [def] outside [blk] denotes in
   [AI.top]. *)
let denote_exp_at :
    blk:blk term -> ?def:def term -> exp ->
    (Vsa.WordSet.t, Type.error) Result.t =
  fun ~blk ?def e -> Vsa.denote_exp_at ~pre:(block_pre blk) ~blk ?def e

(* The per-sub written-register summary (the kill the call abstraction
   may shrink on proof): every def whose lhs base is a non-virtual
   register — partial defs included, [Var.base] normalizes them. *)
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

(* The run memo: one computation per program (the per-sub fixpoint
   fold passes the same program; the memo keys on its physical
   identity). *)
let summaries_memo :
    ((program term * Hike_abi.t) * Var.Set.t option Tid.Map.t) option ref =
  ref None

let summaries_of ~(abi : Hike_abi.t) (prog : program term) :
    Var.Set.t option Tid.Map.t =
  match !summaries_memo with
  | Some ((p, a), s) when p == prog && a == abi -> s
  | _ ->
    let s = kill_summaries ~abi prog in
    summaries_memo := Some ((prog, abi), s);
    s

(* The joint fixpoint with its CFG-completion loop: a round runs the
   engine over the sub, the completion rewrites the CFG in the BIL on
   the round's denotations (return epilogues into real [Ret] jmps,
   resolvable dispatches into guarded-goto series), and a changed sub
   re-solves — the rewritten BIR is the memory, so the loop ends at
   the first unchanged round.  The products are the per-block (pre,
   post) environments and the FINAL REWRITTEN SUB.  [None] = the
   engine did not converge: no environments, no rewrite — every reader
   takes the top identity and the sub stays as it came. *)
let fixpoint (target : Theory.Target.t) (sp : var)
    ~(prog : program term)
    ~(images : Vsa.section_image list)
    (sub : sub term) :
    ((Vsa.AI.t * Vsa.AI.t) Tid.Map.t * sub term) option =
  self_arm target;
  let abi = Hike_abi.of_target target in
  let written = summaries_of ~abi prog in
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
  let rec rounds (sub : sub term) : Vsa.vsa_sol * sub term =
    let prog' = Program.create ~subs:[ sub ] () in
    let sol =
      Vsa.static_graph_vsa ~abi ~written [] prog' sub
        (Vsa.init_sol ~abi sub)
    in
#ifdef VSA_DEBUG
    dump_r8 sol sub;
#endif
    let denote = Hike_cfg_complete.denote_of_sol sol in
    let sub', changed =
      Hike_cfg_complete.complete ~denote ~abi ~sol ~images sub
    in
    if changed then rounds sub' else (sol, sub')
  in
  match
    try Some (rounds sub)
    with Vsa.Fixpoint_not_converged (n, _, _) ->
      Hike_diag.warn
        "vsa: sub %s: fixpoint not converged in %d iterations — no environments, no rewrite (every reader takes the top identity)"
        (Sub.name sub) n;
      None
  with
  | Some (sol, sub') ->
      Some (Vsa.block_envs_of_sol ~sol sub', sub')
  | None -> None
