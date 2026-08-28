(* Src/hike_vsa.ml — the VSA tag-EXTRACTION module of the hike library. *)

open Bap.Std
module KB = Bap_knowledge.Knowledge

module AI = Cbat_vsa.AI
module Mem = Cbat_vsa.Mem
module Vsa = Cbat_vsa
module Ws = Cbat_clp_set_composite

(* [set_addr_bits n]: Forward the program architecture's address size in bits (the Target-derived [Targetutils.addr_size_bits]) into the VSA — the memmap's native key width (O1). *)
let set_addr_bits (n : int) : unit = Vsa.set_addr_bits n

(* the RSP identity var for the k-range computation is the TARGET's stack pointer ([Targetutils.sp]) — threaded in as the [sp] argument of [offsets_of_sub] (R2: no [target_ref] global; the caller derives it from [Project.target] once and passes it down). *)
(* sibling inside the hike library — reference DIRECTLY (the [Hike__.Hike_vsa_relevance] alias is only for OUTSIDE consumers). *)
module Relevance = Hike_vsa_relevance

(* [classify ws]: Range, Infinite (widening), or VLA (dynamic size def tid). *)
let classify ?(vla_tid : tid option = None) (ws : Ws.t) : Convutils.vsa_kind option =
  if Ws.is_top ws || Ws.is_bottom ws then None
  else
    match Ws.min_elem ws, Ws.max_elem ws with
    | Some lo, Some hi ->
      (match Word.to_int64 lo, Word.to_int64 hi with
       | Ok lo, Ok hi ->
         let is_inf = Ws.is_infinite ws || Int64.compare lo hi > 0 in
         if is_inf && Option.is_some vla_tid then
           Some (Convutils.VLA (Option.get vla_tid))
         else if is_inf then Some (Convutils.Infinite (lo, hi))
         else Some (Convutils.Range (lo, hi))
       | _ -> None)
    | _ -> None

(* [bounds_of ws]: the signed int64 (lo, hi) bounds of a WordSet, or None when it is top/bottom/empty (the classify pre-conditions). *)
let bounds_of (ws : Ws.t) : (int64 * int64) option =
  if Ws.is_top ws || Ws.is_bottom ws then None
  else
    match Ws.min_elem ws, Ws.max_elem ws with
    | Some lo, Some hi -> (
        match Word.to_int64 lo, Word.to_int64 hi with
        | Ok lo, Ok hi -> Some (lo, hi)
        | _ -> None)
    | _ -> None

(* [k_range_of ws rsp_ws]: the ABI-visible k-range (k = addr - RSP at the def — the arg area is k >= 0). Interval arithmetic on the signed bounds: k_min = addr_lo - rsp_hi, k_max = addr_hi - rsp_lo. *)
let k_range_of (ws : Ws.t) (rsp_ws : Ws.t) : (int64 * int64) option =
  match bounds_of ws, bounds_of rsp_ws with
  | Some (alo, ahi), Some (rlo, rhi) ->
      Some (Int64.sub alo rhi, Int64.sub ahi rlo)
  | _ -> None

(* [has_relevant_tags sub]: Does ANY def of [sub] carry the [relevant] or [direct_sp] tag? *)
let has_relevant_tags (sub : sub term) : bool =
  Term.enum blk_t sub
  |> Seq.exists ~f:(fun b ->
      Term.enum def_t b
      |> Seq.exists ~f:(fun d ->
          Term.has_attr d Cbat_vsa_utils.relevant
          || Term.has_attr d Relevance.direct_sp))

(* [has_direct_sp_tags sub]: Does ANY def of [sub] carry the [direct_sp] tag (an actual direct SP-relative stack access)? *)
let has_direct_sp_tags (sub : sub term) : bool =
  Term.enum blk_t sub
  |> Seq.exists ~f:(fun b ->
      Term.enum def_t b
      |> Seq.exists ~f:(fun d -> Term.has_attr d Relevance.direct_sp))

(* M2 (ADR 0004): per-call-site stack-arg values removed — hike_stack ptr threading replaces arity. *)
let call_stack_args_of_sub (_sp : var) (_sub : sub term)
    (_tags : (tid, AI.t) Graphlib.Std.Solution.t) : (Tid.t * (int * int64) list) list = []

(* [offsets_of_sub sub]: The per-def offset interval tags of [sub]'s Load/Store defs, in block-then-def order (see the header contract). *)
let offsets_of_sub (sp : var) (sub : sub term) : Convutils.vsa_info =
  let sub' = if has_relevant_tags sub then sub else Relevance.analyze sp sub in
  (* A sub with NO direct-SP stack accesses produces an empty offset set regardless of the fixpoint result (only [direct_sp]-tagged Load/Store defs yield offset tags). *)
  if not (has_direct_sp_tags sub') then
    { Convutils.offsets = []; k_ranges = []; regions = []; degraded = false;
      call_stack_args = []; vla_bounds = [] }
  else
  let prog' = Program.create ~subs:[ sub' ] () in
  (* The trace-partitioned tags (docs/trace-partitioning-plan.md §1.4/§2.4): the fixpoint runs with the views (the Phase B post-pass), and the per-block TAG states come from [partitioned_states] — the invariant met with the. *)
  (* The per-def walk (finish): the sequential state (the block input [st], advanced def-by-def exactly like the fixpoint's [denote_defs]) and the two tag accumulators thread through ONE nested fold — no refs. *)
  let finish (sol : Vsa.vsa_sol) (views : Vsa.edge_view list) :
      Convutils.vsa_info =
  (* A sub with an INDIRECT JUMP ([Goto/Ret (Indirect _)]) has an INCOMPLETE CFG — the lifter could not resolve the jump-table targets — so a bottom block state does NOT prove unreachability (the target blocks are stranded, their accesses would be mislabeled dead-path). *)
  let has_indirect_jumps =
    Term.enum blk_t sub'
    |> Seq.exists ~f:(fun blk ->
        Term.enum jmp_t blk
        |> Seq.exists ~f:(fun j ->
            match Jmp.kind j with
            | Goto (Indirect _) | Ret (Indirect _) -> true
            | _ -> false))
  in
  let degraded = has_indirect_jumps in
  let tags = Vsa.partitioned_states sub' sol views in
  (* A Load/Store whose address is NOT frame-derived (rewrite_addr returned it unchanged — its base var has no frame fact) AND does not name RSP/RBP is a runtime POINTER-VALUE deref (the va_arg/argument-deref class, [RAX :=. *)
  let pointer_value_addr (st : AI.t) (addr : exp) : bool =
    let rewritten =
      not
        (Exp.equal
           (Vsa.rewrite_addr (Vsa.frame_of_state st) addr) addr)
    in
    if rewritten then false
    else
      Exp.free_vars addr
      |> Core.Set.for_all ~f:(fun v ->
          let n = Var.name v in
          not (String.equal n "RSP" || String.equal n "RBP"))
  in
  (* The per-def walk: the sequential state (the block input [st], advanced def-by-def exactly like the fixpoint's [denote_defs]) and the two tag accumulators thread through ONE nested fold — no refs. *)
  let raw, kraw =
    Term.enum blk_t sub'
    |> Seq.fold ~init:([], []) ~f:(fun (acc, kacc) blk ->
        (* Walk only the block's defs up to and including its LAST direct_sp Load/Store def — the state advance after it can affect no tag (the address/k-range denotations read the PRE-def state), and a block with NO stack access contributes nothing and skips the walk entirely. *)
        let defs = Term.enum def_t blk |> Seq.to_list in
        let last_tagged =
          Base.List.foldi defs ~init:None ~f:(fun i acc d ->
              if Term.has_attr d Relevance.direct_sp then Some i else acc)
        in
        match last_tagged with
        | None -> (acc, kacc)
        | Some i ->
        let defs' = Base.List.take defs (i + 1) in
        let _, acc, kacc =
          Base.List.fold_left defs'
            ~init:(Graphlib.Std.Solution.get tags (Term.tid blk), acc, kacc)
            ~f:(fun (st, acc, kacc) d ->
                 let st_before = st in
                 let st = Vsa.denote_def d st in
                 if KB.Value.get rip_relative_addr (Def.value d) then
                   (st, acc, kacc)
                 else
                   match Def.rhs d with
                   | Bil.Load (_, addr, _, _) | Bil.Store (_, addr, _, _, _)
                   | Bil.Cast (_, _, Bil.Load (_, addr, _, _))
                   | Bil.Cast (_, _, Bil.Store (_, addr, _, _, _))
                     when
                       Term.has_attr d Relevance.direct_sp
                       && not (pointer_value_addr st_before addr) ->
                     let addr' =
                       Vsa.rewrite_addr
                         (Vsa.frame_of_state st_before) addr in
                     (* The address's free vars are denoted with the PARTITIONED state's values (the invariant ∩ the enclosing guards' iterate/exit constraints), not the sequentially re-denoted ones — the loop-body index var [v := Load(cell)] would otherwise read the solution's widened cell (the w_big class). *)
                     let st_tag =
                       Exp.free_vars addr'
                       |> Core.Set.fold ~init:st_before ~f:(fun acc v ->
                           match Var.typ v with
                           | Type.Imm w ->
                             let tag_v = AI.find_word w
                                 (Graphlib.Std.Solution.get tags
                                    (Term.tid blk)) v in
                             let cur = AI.find_word w acc v in
                             let mm = Ws.meet cur tag_v in
                             (* Option B/c fix : a TOP sequential value is NOT refined by the M6 meet — the partitioned state's value at the block is the JOIN over all paths (e.g. *)
                             if Ws.is_top cur && Word.is_one (Ws.cardinality mm)
                                || Word.is_zero (Ws.cardinality mm)
                                || Ws.equal mm cur
                             then acc
                             else AI.add_word acc ~key:v ~data:mm
                           | Type.Mem _ | Type.Unk -> acc)
                       |> fun acc -> acc in
                     (match
                        Vsa.denote_imm_exp
                          (* WYSINWYX-2 (the in-state relation) — the address is REWRITTEN to its offset-from-origin expression (the frame relation carried in the state) before denotation: the tags are the SP-relative OFFSETS, sourced from the relation rather than the anchored value-sets. *)
                          addr' st_tag
                      with
                      | Ok ws -> (
                          match classify ws with
                          | Some kind ->
                              let acc = (Term.tid d, kind, ws) :: acc in
                              let kacc =
                                match
                                  k_range_of ws
                                    (Vsa.AI.find_word 64 st_before sp)
                                with
                                | Some (klo, khi) ->
                                    (Term.tid d, klo, khi) :: kacc
                                | None -> kacc
                              in
                              (st, acc, kacc)
                          | None -> (st, acc, kacc))
                      | Error _ -> (st, acc, kacc))
                   | _ -> (st, acc, kacc))
        in
        (acc, kacc))
  in
  let raw = List.rev raw in
  (* THE SET-OVERLAP MERGE: the defs whose address WordSets OVERLAP (the domain's membership test — a direct singleton {c} overlaps the indexed CLP {base + step*k} iff c is in its residue class, so `a[1] = 5` and `a[i]` of. *)
  let span_of = function
    | Convutils.Range (lo, hi) -> (lo, hi)
    | Convutils.Infinite (lo, hi) -> (Int64.min lo hi, Int64.max lo hi)
    | Convutils.VLA _ -> (0L, 0L)
  in
  let merged_tags : Convutils.vsa_kind Tid.Map.t =
    let items =
      Base.List.map raw ~f:(fun (dtid, kind, ws) -> (dtid, kind, ws))
    in
    (* Maximal overlap components via Ws.overlap (transitive closure).
       S1 coarser: any overlapping WordSets merge; bridging via a new item
       merges all comps that overlap it. *)
    let rec components acc = function
      | [] -> acc
      | (dtid, kind, ws) :: rest ->
          let overlapping, non_overlapping =
            Base.List.partition_tf acc ~f:(fun comp ->
                Base.List.exists comp ~f:(fun (_, _, ws') -> Ws.overlap ws ws'))
          in
          let new_comp =
            (dtid, kind, ws) :: Base.List.concat overlapping
          in
          components (new_comp :: non_overlapping) rest
    in
    Base.List.fold_left (components [] items) ~init:Tid.Map.empty
      ~f:(fun acc comp ->
        match comp with
        | [ (dtid, kind, _) ] -> Core.Map.set acc ~key:dtid ~data:kind
        | _ ->
            (* Option B fix : the span fold MUST start from the FIRST member's span — the (0L, 0L) init polluted every merged range with the origin 0 (min(0, lo) and max(0, hi) made every negative-span component's merged tag Range(lo,. *)
            let lo, hi =
              match comp with
              | (_, k0, _) :: rest ->
                let slo0, shi0 = span_of k0 in
                Base.List.fold_left rest ~init:(slo0, shi0)
                  ~f:(fun (l, h) (_, k, _) ->
                    let slo, shi = span_of k in
                    (Int64.min l slo, Int64.max h shi))
              | [] -> (0L, 0L) (* unreachable: comp is non-empty *)
            in
            Base.List.fold_left comp ~init:acc
              ~f:(fun acc (dtid, _, _) ->
                Core.Map.set acc ~key:dtid
                  ~data:(Convutils.Range (lo, hi))))
  in
  let offsets =
      Base.List.map raw ~f:(fun (dtid, kind, _) ->
          match Core.Map.find merged_tags dtid with
          | Some k -> (dtid, k)
          | None -> (dtid, kind)) in
  let k_ranges = List.rev kraw in
  let vla_bounds =
    Term.enum blk_t sub'
    |> Seq.concat_map ~f:(fun blk ->
        let blk_tid = Term.tid blk in
        Term.enum def_t blk
        |> Seq.filter ~f:(fun d -> Term.has_attr d Relevance.dynamic_alloc)
        |> Seq.filter_map ~f:(fun d ->
            let size_opt =
              match Def.rhs d with
              | Bil.BinOp (Bil.MINUS, Bil.Var v, size) when Var.same v sp -> Some size
              | Bil.Var tmp ->
                let def_of_lhs =
                  Term.enum blk_t sub'
                  |> Seq.concat_map ~f:(Term.enum def_t)
                  |> Seq.fold ~init:Var.Map.empty ~f:(fun m d -> Core.Map.set m ~key:(Var.base (Def.lhs d)) ~data:d)
                in
                (match Core.Map.find def_of_lhs (Var.base tmp) with
                 | Some d' -> (
                     match Def.rhs d' with
                     | Bil.BinOp (Bil.MINUS, Bil.Var v, size) when Var.same v sp -> Some size
                     | _ -> None)
                 | None -> None)
              | _ -> None
            in
            match size_opt with
            | None -> None
            | Some size ->
              let st = Graphlib.Std.Solution.get tags blk_tid in
              match Vsa.denote_imm_exp size st with
              | Ok ws -> (
                  match Ws.min_elem ws, Ws.max_elem ws with
                  | Some lo, Some hi -> (
                      match Word.to_int64 lo, Word.to_int64 hi with
                      | Ok lo, Ok hi -> Some (Term.tid d, (lo, hi))
                      | _ -> None)
                  | _ -> None)
              | Error _ -> None)
        ) |> Seq.to_list
  in
  let base_info = { Convutils.offsets; k_ranges; regions = []; degraded;
                    call_stack_args = []; vla_bounds = [] } in
  let regions = Hike_stack_to_locals.regions_of_sub sub' base_info in
  let call_stack_args = call_stack_args_of_sub sp sub' tags in
  { Convutils.offsets; k_ranges; regions; degraded; call_stack_args; vla_bounds }
  in
  (* TEMP PROBE: per-sub fixpoint timing *)
  let t0_probe = Unix.gettimeofday () in
  let probe_res =
  (* the solve driver: run the fixpoint; a non-convergent fixpoint (D.1) degrades the sub soundly — no tags, every stack access stays real memory (the emitter's dynamic path). *)
  match
    try
      Some (Vsa.static_graph_vsa_with_views [] prog' sub' (Vsa.init_sol sub'))
    with Vsa.Fixpoint_not_converged (n, _, _) ->
      (* The fixpoint did not converge — the partial solution is an UNDER-APPROXIMATION; narrow offset tags computed from it would exclude reachable values (unsound). *)
      Printf.eprintf
        "hike: vsa: sub %s: fixpoint not converged in %d iterations — degraded (no tags, dynamic stack)\n"
        (Sub.name sub') n;
      None
  with
  | None -> { Convutils.offsets = []; k_ranges = []; regions = []; degraded = true;
              call_stack_args = []; vla_bounds = [] }
  | Some (sol, views) ->
      Hike_kb.add_sol (Term.tid sub) sol;
      finish sol views
  in
  let dt_probe = Unix.gettimeofday () -. t0_probe in
  (try
     let oc = open_out_gen [Open_append; Open_creat] 0o644 "/tmp/vsa_timing.txt" in
     Printf.fprintf oc "%s\t%d\t%.3f\n" (Sub.name sub') (Term.length blk_t sub') dt_probe;
     close_out oc
   with _ -> ());
  probe_res

let offsets_from_partitioned (sp : var) (sub : sub term) (part : Vsa.vsa_sol) : Convutils.vsa_info =
  let has_indirect_jumps =
    Term.enum blk_t sub
    |> Seq.exists ~f:(fun blk ->
        Term.enum jmp_t blk
        |> Seq.exists ~f:(fun j ->
            match Jmp.kind j with
            | Goto (Indirect _) | Ret (Indirect _) -> true
            | _ -> false))
  in
  let degraded = has_indirect_jumps in
  let tags = part in
  let pointer_value_addr (st : AI.t) (addr : exp) : bool =
    let rewritten =
      not
        (Exp.equal
           (Vsa.rewrite_addr (Vsa.frame_of_state st) addr) addr)
    in
    if rewritten then false
    else
      Exp.free_vars addr
      |> Core.Set.for_all ~f:(fun v ->
          let n = Var.name v in
          not (String.equal n "RSP" || String.equal n "RBP"))
  in
  let raw, kraw =
    Term.enum blk_t sub
    |> Seq.fold ~init:([], []) ~f:(fun (acc, kacc) blk ->
        let defs = Term.enum def_t blk |> Seq.to_list in
        let last_tagged =
          Base.List.foldi defs ~init:None ~f:(fun i acc d ->
              if Term.has_attr d Relevance.direct_sp then Some i else acc)
        in
        match last_tagged with
        | None -> (acc, kacc)
        | Some i ->
        let defs' = Base.List.take defs (i + 1) in
        let _, acc, kacc =
          Base.List.fold_left defs'
            ~init:(Graphlib.Std.Solution.get tags (Term.tid blk), acc, kacc)
            ~f:(fun (st, acc, kacc) d ->
                 let st_before = st in
                 let st = Vsa.denote_def d st in
                 if KB.Value.get rip_relative_addr (Def.value d) then
                   (st, acc, kacc)
                 else
                   match Def.rhs d with
                   | Bil.Load (_, addr, _, _) | Bil.Store (_, addr, _, _, _)
                   | Bil.Cast (_, _, Bil.Load (_, addr, _, _))
                   | Bil.Cast (_, _, Bil.Store (_, addr, _, _, _))
                     when
                       Term.has_attr d Relevance.direct_sp
                       && not (pointer_value_addr st_before addr) ->
                     let addr' =
                       Vsa.rewrite_addr
                         (Vsa.frame_of_state st_before) addr in
                     let st_tag =
                       Exp.free_vars addr'
                       |> Core.Set.fold ~init:st_before ~f:(fun acc v ->
                           match Var.typ v with
                           | Type.Imm w ->
                             let tag_v = AI.find_word w
                                 (Graphlib.Std.Solution.get tags
                                    (Term.tid blk)) v in
                             let cur = AI.find_word w acc v in
                             let mm = Ws.meet cur tag_v in
                             if Ws.is_top cur && Word.is_one (Ws.cardinality mm)
                                || Word.is_zero (Ws.cardinality mm)
                                || Ws.equal mm cur
                             then acc
                             else AI.add_word acc ~key:v ~data:mm
                           | Type.Mem _ | Type.Unk -> acc)
                       |> fun acc -> acc in
                     (match
                        Vsa.denote_imm_exp
                          addr' st_tag
                      with
                      | Ok ws -> (
                          match classify ws with
                          | Some kind ->
                              let acc = (Term.tid d, kind, ws) :: acc in
                              let kacc =
                                match
                                  k_range_of ws
                                    (Vsa.AI.find_word 64 st_before sp)
                                with
                                | Some (klo, khi) ->
                                    (Term.tid d, klo, khi) :: kacc
                                | None -> kacc
                              in
                              (st, acc, kacc)
                          | None -> (st, acc, kacc))
                      | Error _ -> (st, acc, kacc))
                   | _ -> (st, acc, kacc))
        in
        (acc, kacc))
  in
  let raw = List.rev raw in
  let span_of = function
    | Convutils.Range (lo, hi) -> (lo, hi)
    | Convutils.Infinite (lo, hi) -> (Int64.min lo hi, Int64.max lo hi)
    | Convutils.VLA _ -> (0L, 0L)
  in
  let merged_tags : Convutils.vsa_kind Tid.Map.t =
    let items =
      Base.List.map raw ~f:(fun (dtid, kind, ws) -> (dtid, kind, ws))
    in
    let rec components acc = function
      | [] -> acc
      | (dtid, kind, ws) :: rest ->
          let overlapping, non_overlapping =
            Base.List.partition_tf acc ~f:(fun comp ->
                Base.List.exists comp ~f:(fun (_, _, ws') -> Ws.overlap ws ws'))
          in
          let new_comp =
            (dtid, kind, ws) :: Base.List.concat overlapping
          in
          components (new_comp :: non_overlapping) rest
    in
    Base.List.fold_left (components [] items) ~init:Tid.Map.empty
      ~f:(fun acc comp ->
        match comp with
        | [ (dtid, kind, _) ] -> Core.Map.set acc ~key:dtid ~data:kind
        | _ ->
            let lo, hi =
              match comp with
              | (_, k0, _) :: rest ->
                let slo0, shi0 = span_of k0 in
                Base.List.fold_left rest ~init:(slo0, shi0)
                  ~f:(fun (l, h) (_, k, _) ->
                    let slo, shi = span_of k in
                    (Int64.min l slo, Int64.max h shi))
              | [] -> (0L, 0L)
            in
            Base.List.fold_left comp ~init:acc
              ~f:(fun acc (dtid, _, _) ->
                Core.Map.set acc ~key:dtid
                  ~data:(Convutils.Range (lo, hi))))
  in
  let offsets =
      Base.List.map raw ~f:(fun (dtid, kind, _) ->
          match Core.Map.find merged_tags dtid with
          | Some k -> (dtid, k)
          | None -> (dtid, kind)) in
  let k_ranges = List.rev kraw in
  let vla_bounds =
    Term.enum blk_t sub
    |> Seq.concat_map ~f:(fun blk ->
        let blk_tid = Term.tid blk in
        Term.enum def_t blk
        |> Seq.filter ~f:(fun d -> Term.has_attr d Relevance.dynamic_alloc)
        |> Seq.filter_map ~f:(fun d ->
            let size_opt =
              match Def.rhs d with
              | Bil.BinOp (Bil.MINUS, Bil.Var v, size) when Var.same v sp -> Some size
              | Bil.Var tmp ->
                let def_of_lhs =
                  Term.enum blk_t sub
                  |> Seq.concat_map ~f:(Term.enum def_t)
                  |> Seq.fold ~init:Var.Map.empty ~f:(fun m d -> Core.Map.set m ~key:(Var.base (Def.lhs d)) ~data:d)
                in
                (match Core.Map.find def_of_lhs (Var.base tmp) with
                 | Some d' -> (
                     match Def.rhs d' with
                     | Bil.BinOp (Bil.MINUS, Bil.Var v, size) when Var.same v sp -> Some size
                     | _ -> None)
                 | None -> None)
              | _ -> None
            in
            match size_opt with
            | None -> None
            | Some size ->
              let st = Graphlib.Std.Solution.get part blk_tid in
              match Vsa.denote_imm_exp size st with
              | Ok ws -> (
                  match Ws.min_elem ws, Ws.max_elem ws with
                  | Some lo, Some hi -> (
                      match Word.to_int64 lo, Word.to_int64 hi with
                      | Ok lo, Ok hi -> Some (Term.tid d, (lo, hi))
                      | _ -> None)
                  | _ -> None)
              | Error _ -> None)
        ) |> Seq.to_list
  in
  let base_info = { Convutils.offsets; k_ranges; regions = []; degraded;
                    call_stack_args = []; vla_bounds = [] } in
  let regions = Hike_stack_to_locals.regions_of_sub sub base_info in
  let call_stack_args = call_stack_args_of_sub sp sub part in
  { Convutils.offsets; k_ranges; regions; degraded; call_stack_args; vla_bounds }

(* M2 (ADR 0004): arity_of_sub and arity_map_of_prog removed — no stack-arg arity, M2 hike_stack ptr only. *)
