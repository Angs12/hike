(* The canary-strip pass, before the fission: the detector composes
   the TLS canary read (the address's base var is
   [Abi.thread_pointer]), its store into one VSA-proven stack cell,
   the reload feeding the comparison, and the not-equal edge to a
   symtab-resolved [__stack_chk_fail]; the equality edge continues
   unconditionally, and an unrecognized composition is the identity. *)

open Bap.Std
open Bap.Std.Bil.Types

module Abi = Hike_abi
module Model = Hike_stack_model
module Vsa = Cbat_vsa

(* [e] denotes in the before-env of [def] — the analysis facts'
   denotation, threaded from the pass entry. *)
type denote = Hike_kb.denote

(* The base var is the thread pointer; the offset is data. *)
let tls_addr (tp : var) (addr : exp) : bool =
  match addr with
  | Bil.Var v -> Var.same v tp
  | Bil.BinOp ((Bil.PLUS | Bil.MINUS), Var v, Bil.Int _) -> Var.same v tp
  | _ -> false

let is_load_rhs (e : exp) : bool = match e with Bil.Load _ -> true | _ -> false

let is_store_rhs (e : exp) : bool =
  match e with Bil.Store _ -> true | _ -> false

let is_tls_read (tp : var) (d : def term) : bool =
  match Def.rhs d with
  | Bil.Load (_, addr, _, _) -> tls_addr tp addr
  | _ -> false

(* The def's cell: the single stack position its address denotates to
   at the def's own before-env. *)
let cell_of ~(denote : denote) (blk : blk term) (d : def term) : int64 option =
  let open Base.Option in
  (Base.Option.map (Model.addr_of_rhs (Def.rhs d)) ~f:fst
   >>= fun addr -> Base.Result.ok (denote ~blk ~def:d addr)
   >>= Model.singleton_stack_position)

(* Every memory def's cell, keyed by def tid. *)
let cells_of_sub ~(denote : denote) (sub : sub term) : int64 Tid.Map.t =
  Term.enum blk_t sub
  |> Seq.fold ~init:Tid.Map.empty ~f:(fun m blk ->
         Seq.fold (Term.enum def_t blk) ~init:m ~f:(fun m d ->
             match cell_of ~denote blk d with
             | Some cell -> Core.Map.set m ~key:(Term.tid d) ~data:cell
             | None -> m))

let store_data (d : def term) : exp option =
  match Def.rhs d with
  | Bil.Store (_, _, data, _, _) -> Some data
  | _ -> None

let is_mem_var (v : var) : bool =
  match Var.typ v with Mem _ -> true | _ -> false

(* The value operands of an exp: the free vars, memory excluded. *)
let value_vars (e : exp) : Var.Set.t =
  Core.Set.filter (Exp.free_vars e) ~f:(fun v -> not (is_mem_var v))

type block_data = {
  b_blk : blk term;
  b_tid : Tid.t;
  b_defs : def term array;
  b_jmps : jmp term array;
  b_phis : phi term list;
}

type ctx = {
  blocks : block_data list;
  by_tid : block_data Tid.Map.t;
  (* May-reaching def tids per base var at each block entry. *)
  entry_in : Tid.Set.t Var.Map.t Tid.Map.t;
  (* In-sub successors per block. *)
  succs : Tid.Set.t Tid.Map.t;
  (* Every def's site: its block and position. *)
  def_site : (Tid.t * int) Tid.Map.t;
  (* Each def's lhs base var, by tid. *)
  def_lhs : Var.t Tid.Map.t;
  (* Each block's last def index per base var. *)
  last_def : int Var.Map.t Tid.Map.t;
}

let jmp_targets (acc : Tid.Set.t) (j : jmp term) : Tid.Set.t =
  let tgt l acc =
    match l with Direct t -> Core.Set.add acc t | Indirect _ -> acc
  in
  let go j acc =
    match Jmp.kind j with
    | Goto l -> tgt l acc
    | Call c -> (match Call.return c with Some l -> tgt l acc | None -> acc)
    | Ret _ | Int _ -> acc
  in
  go j acc

let find_def (b : block_data) (tid : Tid.t) : def term option =
  let rec go i =
    if i >= Array.length b.b_defs then None
    else if Tid.equal (Term.tid b.b_defs.(i)) tid then Some b.b_defs.(i)
    else go (i + 1)
  in
  go 0

let build_ctx (sub : sub term) : ctx =
  let blocks =
    Term.enum blk_t sub
    |> Seq.map ~f:(fun b ->
        { b_blk = b;
          b_tid = Term.tid b;
          b_defs = Array.of_list (Term.enum def_t b |> Seq.to_list);
          b_jmps = Array.of_list (Term.enum jmp_t b |> Seq.to_list);
          b_phis = Term.enum phi_t b |> Seq.to_list })
    |> Seq.to_list
  in
  let by_tid =
    Base.List.fold blocks ~init:Tid.Map.empty ~f:(fun m b ->
        Core.Map.set m ~key:b.b_tid ~data:b)
  in
  let succs =
    Base.List.fold blocks ~init:Tid.Map.empty ~f:(fun m b ->
        let ts =
          Base.List.fold (Array.to_list b.b_jmps) ~init:Tid.Set.empty
            ~f:jmp_targets
          |> Core.Set.filter ~f:(fun t -> Core.Map.mem by_tid t)
        in
        Core.Map.set m ~key:b.b_tid ~data:ts)
  in
  let def_site =
    Base.List.fold blocks ~init:Tid.Map.empty ~f:(fun m b ->
        let rec go i m = function
          | [] -> m
          | d :: rest ->
            go (i + 1)
              (Core.Map.set m ~key:(Term.tid d) ~data:(b.b_tid, i))
              rest
        in
        go 0 m (Array.to_list b.b_defs))
  in
  (* Union over predecessors; a block's own defs kill then gen. *)
  let transfer (entry : Tid.Set.t Var.Map.t) (b : block_data) :
      Tid.Set.t Var.Map.t =
    Base.List.fold (Array.to_list b.b_defs) ~init:entry ~f:(fun st d ->
        Core.Map.set st ~key:(Var.base (Def.lhs d))
          ~data:(Tid.Set.singleton (Term.tid d)))
  in
  let merge_st a b =
    Core.Map.merge a b ~f:(fun ~key:_ el ->
        match el with
        | `Both (x, y) -> Some (Core.Set.union x y)
        | `Left s | `Right s -> Some s)
  in
  (* The predecessor transpose, built once: each block's entry merge
     walks its preds, not the whole successor map. *)
  let preds =
    Core.Map.fold succs ~init:Tid.Map.empty
      ~f:(fun ~key:src ~data:ts acc ->
        Core.Set.fold ts ~init:acc ~f:(fun acc t ->
            Core.Map.add_multi acc ~key:t ~data:src))
  in
  let state = ref Tid.Map.empty in
  let changed = ref true in
  while !changed do
    changed := false;
    Base.List.iter blocks ~f:(fun b ->
        let inn =
          Core.Set.fold
            (Core.Set.of_list (module Tid)
               (Core.Map.find preds b.b_tid |> Option.value ~default:[]))
            ~init:Var.Map.empty
            ~f:(fun acc src ->
              merge_st acc
                (Option.value (Core.Map.find !state src) ~default:Var.Map.empty))
        in
        let out = transfer inn b in
        if
          not
            (Var.Map.equal Core.Set.equal out
               (Option.value (Core.Map.find !state b.b_tid) ~default:Var.Map.empty))
        then (
          changed := true;
          state := Core.Map.set !state ~key:b.b_tid ~data:out));
  done;
  let def_lhs =
    Base.List.concat_map blocks ~f:(fun b ->
        Base.List.map (Array.to_list b.b_defs) ~f:(fun d ->
            (Term.tid d, Var.base (Def.lhs d))))
    |> Core.Map.of_alist_exn (module Tid)
  in
  let last_def =
    Base.List.map blocks ~f:(fun b ->
        let m =
          Base.List.foldi (Array.to_list b.b_defs) ~init:Var.Map.empty
            ~f:(fun i acc d -> Core.Map.set acc ~key:(Var.base (Def.lhs d)) ~data:i)
        in
        (b.b_tid, m))
    |> Core.Map.of_alist_exn (module Tid)
  in
  { blocks; by_tid; entry_in = !state; succs; def_site; def_lhs; last_def }

(* The def tids of [v] reaching def index [i] in block [b]: the block's
   last def of the var before [i], else the entry state. *)
let reaching_at (ctx : ctx) (b : block_data) (i : int) (v : var) : Tid.Set.t =
  let vb = Var.base v in
  let entry () =
    Core.Map.find
      (Option.value (Core.Map.find ctx.entry_in b.b_tid) ~default:Var.Map.empty)
      vb
    |> Option.value ~default:Tid.Set.empty
  in
  (* The block's last def of [vb] answers directly when it precedes
     [i]; only a def at/after [i] falls back to the backward scan. *)
  match Option.bind (Core.Map.find ctx.last_def b.b_tid) (fun m -> Core.Map.find m vb) with
  | Some j when j < i -> Tid.Set.singleton (Term.tid b.b_defs.(j))
  | _ ->
    let rec go j =
      if j < 0 then entry ()
      else if Var.equal (Var.base (Def.lhs b.b_defs.(j))) vb then
        Tid.Set.singleton (Term.tid b.b_defs.(j))
      else go (j - 1)
    in
    go (i - 1)

(* The stored value is the TLS read's value: the data exp is the read
   def's lhs, the read is its unique reaching def, both denote equal. *)
let stored_value_is_read_value ~(denote : denote)
    ~(store_blk : blk term) ~(read_blk : blk term)
    ~(reaching : var -> Tid.Set.t) ~(tp : var) ~(read : def term)
    (store : def term) : bool =
  match store_data store with
  | Some (Bil.Var v) ->
    Core.Set.equal (reaching v) (Tid.Set.singleton (Term.tid read))
    && is_tls_read tp read
    && (match
          denote ~blk:store_blk ~def:store (Bil.Var v),
          denote ~blk:read_blk ~def:read (Def.rhs read)
        with
        | Ok a, Ok b -> Vsa.WordSet.equal a b
        | _ -> false)
  | _ -> false

(* The first def after the reload that reads its lhs denotes it to the
   reload's value — the reload reaches the comparison unmodified. *)
let compare_operand_is_reload_value ~(denote : denote) (b : block_data) (reload : def term) :
    bool =
  let v = Def.lhs reload in
  let rec consumer i =
    if i >= Array.length b.b_defs then None
    else if Tid.equal (Term.tid b.b_defs.(i)) (Term.tid reload) then after (i + 1)
    else consumer (i + 1)
  and after i =
    if i >= Array.length b.b_defs then None
    else if Core.Set.mem (value_vars (Def.rhs b.b_defs.(i))) v then
      Some b.b_defs.(i)
    else after (i + 1)
  in
  Base.Option.value_map (consumer 0) ~default:false ~f:(fun c ->
      match
        denote ~blk:b.b_blk ~def:c (Bil.Var v),
        denote ~blk:b.b_blk ~def:reload (Def.rhs reload)
      with
      | Ok a, Ok w -> Vsa.WordSet.equal a w
      | _ -> false)

(* The in-block def chain behind the compare's operands: each var
   resolves to its block-local last def; cross-block producers stop. *)
let in_block_chain (b : block_data) (from_vars : Var.Set.t) : Tid.Set.t =
  let rec go (visited : Tid.Set.t) (work : (var * int) list) : Tid.Set.t =
    match work with
    | [] -> visited
    | (v, pos) :: rest ->
      let vb = Var.base v in
      let rec find j =
        if j < 0 then None
        else if Var.equal (Var.base (Def.lhs b.b_defs.(j))) vb then Some j
        else find (j - 1)
      in
      match find (pos - 1) with
      | None -> go visited rest
      | Some j ->
        let tid = Term.tid b.b_defs.(j) in
        if Core.Set.mem visited tid then go visited rest
        else
          let visited = Core.Set.add visited tid in
          let vars = value_vars (Def.rhs b.b_defs.(j)) in
          go visited
            (Core.Set.fold vars ~init:rest ~f:(fun acc v -> (v, j) :: acc))
  in
  let vars = Core.Set.filter from_vars ~f:(fun v -> not (is_mem_var v)) in
  go Tid.Set.empty
    (Core.Set.fold vars ~init:[] ~f:(fun acc v ->
         (v, Array.length b.b_defs) :: acc))

(* The compare family: the chain plus every block def whose value
   operands mention a family lhs; memory-typed lhs never propagates. *)
let compare_family ~(ctx : ctx) (b : block_data) (chain : Tid.Set.t) :
    Tid.Set.t =
  let fam = ref chain in
  let changed = ref true in
  while !changed do
    changed := false;
    let vars =
      Core.Set.fold !fam ~init:Var.Set.empty ~f:(fun acc tid ->
          match Core.Map.find ctx.def_lhs tid with
          | Some v -> Core.Set.union acc (value_vars (Bil.Var v))
          | None -> acc)
    in
    Base.List.iter (Array.to_list b.b_defs) ~f:(fun d ->
        let tid = Term.tid d in
        if
          (not (Core.Set.mem !fam tid))
          && not
               (Core.Set.is_empty (Core.Set.inter (value_vars (Def.rhs d)) vars))
        then (
          changed := true;
          fam := Core.Set.add !fam tid));
  done;
  !fam

let is_fail_name (n : string) : bool =
  Base.String.is_substring n ~substring:"stack_chk_fail"

(* A direct call whose target resolves to [__stack_chk_fail]. *)
let is_fail_block ~(names : Tid.t -> string) (b : block_data) : bool =
  Base.List.exists (Array.to_list b.b_jmps) ~f:(fun j ->
      match Jmp.kind j with
      | Call c -> (
          match Call.target c with
          | Direct t -> is_fail_name (names t)
          | Indirect _ -> false)
      | _ -> false)

let reach_fail ~(ctx : ctx) ~(names : Tid.t -> string) : Tid.t -> bool =
  let memo = ref Tid.Map.empty in
  let rec go (path : Tid.Set.t) (t : Tid.t) : bool =
    match Core.Map.find !memo t with
    | Some v -> v
    | None ->
      if Core.Set.mem path t then false
      else
        let v =
          Base.Option.value_map (Core.Map.find ctx.by_tid t) ~default:false
            ~f:(fun b ->
              is_fail_block ~names b
              || Core.Set.exists
                   (Base.Option.value (Core.Map.find ctx.succs t) ~default:Tid.Set.empty)
                   ~f:(go (Core.Set.add path t)))
        in
        memo := Core.Map.set !memo ~key:t ~data:v;
        v
  in
  go Tid.Set.empty

(* One proven composition: the deleted defs and the deleted edge. *)
type comp = {
  c_read : Tid.t; (* the TLS read def *)
  c_store : Tid.t; (* the canary store def *)
  c_cell : int64;
  c_delete : Tid.Set.t; (* read + store + the cmp block's family *)
  c_fail_jmp : Tid.t; (* the not-equal edge's jmp *)
  c_eq_jmp : Tid.t; (* the equality edge's jmp (cond becomes true) *)
  c_cmp_blk : Tid.t;
  c_fail_blk : Tid.t;
}

let comp_of_block ~(denote : denote) ~(reach : Tid.t -> bool)
    ~(tp : var) ~(tls_reads : (block_data * def term) list)
    ~(cell_of : Tid.t -> int64 option) ~(ctx : ctx)
    (b : block_data) : comp option =
  let targets =
    Base.List.map (Array.to_list b.b_jmps) ~f:(fun j ->
        match Jmp.kind j with
        | Goto (Direct t) when Core.Map.mem ctx.by_tid t -> Some t
        | _ -> None)
  in
  match targets with
  | [ Some t1; Some t2 ] when Array.length b.b_jmps = 2 ->
      let f1 = reach t1 in
      let f2 = reach t2 in
      if f1 = f2 then None
      else
        let fail_t = if f1 then t1 else t2 in
        let fail_i = if f1 then 0 else 1 in
        let eq_i = 1 - fail_i in
        let from_vars =
          Base.List.fold (Array.to_list b.b_jmps) ~init:Var.Set.empty
            ~f:(fun acc j -> Core.Set.union acc (value_vars (Jmp.cond j)))
        in
        let chain = in_block_chain b from_vars in
        let cell_of_load tid =
          match find_def b tid with
          | Some d when is_load_rhs (Def.rhs d) -> cell_of tid
          | _ -> None
        in
        let cells =
          Base.List.filter_map (Core.Set.to_list chain) ~f:cell_of_load
          |> Base.List.dedup_and_sort ~compare:Int64.compare
        in
        (match cells with
         | [ cell ] ->
             let one_cell =
               Core.Set.for_all chain ~f:(fun tid ->
                   Base.Option.value_map (cell_of_load tid) ~default:true
                     ~f:(fun c -> Int64.equal c cell))
             in
             let reloads =
               Core.Set.filter chain ~f:(fun tid ->
                   Base.Option.value_map (cell_of_load tid) ~default:false
                     ~f:(fun c -> Int64.equal c cell))
             in
             let reload_tied =
               Core.Set.exists reloads ~f:(fun tid ->
                   Base.Option.value_map (find_def b tid) ~default:false
                     ~f:(compare_operand_is_reload_value ~denote b))
             in
             if not one_cell || not reload_tied then None
             else
               (* The first cell-naming def per block supplies the candidate store. *)
               let cell_defs =
                 Base.List.filter_map ctx.blocks ~f:(fun b' ->
                     Base.List.find_map (Array.to_list b'.b_defs) ~f:(fun d ->
                         match cell_of (Term.tid d) with
                         | Some c when Int64.equal c cell -> Some (b', d)
                         | _ -> None))
               in
               let stores =
                 Base.List.filter cell_defs
                   ~f:(fun (_, d) -> is_store_rhs (Def.rhs d))
               in
               (match stores with
                | [ (sb, sd) ] ->
                    let reaching v =
                      Base.Option.value
                        (Base.Option.map
                           (Core.Map.find ctx.def_site (Term.tid sd))
                           ~f:(fun (_, i) -> reaching_at ctx sb i v))
                        ~default:Tid.Set.empty
                    in
                    let read =
                      Base.List.find tls_reads ~f:(fun (rb, rd) ->
                          stored_value_is_read_value ~denote
                            ~store_blk:sb.b_blk ~read_blk:rb.b_blk ~reaching
                            ~tp ~read:rd sd)
                    in
                    Base.Option.map read ~f:(fun (_, rd) ->
                        let rtid = Term.tid rd in
                        let fam =
                          compare_family ~ctx b
                            (Core.Set.union chain (Tid.Set.singleton rtid))
                        in
                        let delete =
                          Core.Set.union fam
                            (Core.Set.add (Tid.Set.singleton (Term.tid sd)) rtid)
                        in
                        { c_read = rtid;
                          c_store = Term.tid sd;
                          c_cell = cell;
                          c_delete = delete;
                          c_fail_jmp = Term.tid b.b_jmps.(fail_i);
                          c_eq_jmp = Term.tid b.b_jmps.(eq_i);
                          c_cmp_blk = b.b_tid;
                          c_fail_blk = fail_t })
                | _ -> None)
         | _ -> None)
  | _ -> None

let find_comps ~(denote : denote) ~(abi : Abi.t) ~(names : Tid.t -> string)
    ~(cell_of : Tid.t -> int64 option) ~(ctx : ctx) : comp list =
  let reach = reach_fail ~ctx ~names in
  let tp = abi.Abi.thread_pointer in
  let tls_reads =
    Base.List.concat
      (Base.List.map ctx.blocks ~f:(fun b ->
           Array.to_list b.b_defs
           |> Base.List.filter_map ~f:(fun d ->
                  if is_tls_read tp d then Some (b, d) else None)))
  in
  let comps = ref [] in
  Base.List.iter ctx.blocks ~f:(fun b ->
      match
        comp_of_block ~denote ~reach ~tp ~tls_reads ~cell_of ~ctx b
      with
      | Some c -> comps := c :: !comps
      | None -> ());
  !comps

(* A cell converts together: every access the VSA proves lands on it
   must be the composition's store or a tied reload of this round. *)
let cells_accounted ~(cell_of : Tid.t -> int64 option) ~(ctx : ctx)
    (comps : comp list) : comp list =
  (* One pass groups each cell's deletions; no per-composition rescan. *)
  let groups =
    Base.List.fold comps ~init:[] ~f:(fun acc c ->
        match Base.List.Assoc.find acc c.c_cell ~equal:Int64.equal with
        | Some s ->
          Base.List.Assoc.add acc c.c_cell
            (Core.Set.union s c.c_delete) ~equal:Int64.equal
        | None -> (c.c_cell, c.c_delete) :: acc)
  in
  Base.List.filter comps ~f:(fun c ->
      let group_deleted =
        Option.value (Base.List.Assoc.find groups c.c_cell ~equal:Int64.equal)
          ~default:Tid.Set.empty
      in
      Base.List.for_all ctx.blocks ~f:(fun b ->
          Base.List.for_all (Array.to_list b.b_defs) ~f:(fun d ->
              match cell_of (Term.tid d) with
              | Some cell when Int64.equal cell c.c_cell ->
                if is_store_rhs (Def.rhs d) then
                  Tid.equal (Term.tid d) c.c_store
                else
                  (* A tied reload: deleted by one of this cell's
                     compositions. *)
                  Core.Set.mem group_deleted (Term.tid d)
                  && is_load_rhs (Def.rhs d)
              | _ -> true)))

(* The rewrite is valid only when every surviving use reads no deleted
   def (exact reaching analysis). *)
let residual_ok ~(ctx : ctx) ~(deleted : Tid.Set.t) ~(exempt_jmps : Tid.Set.t)
    ~(edge_srcs : Tid.Set.t) : bool =
  (* Only the deleted defs' lhs vars can reach a surviving use; every
     other operand var skips the scan. *)
  let deleted_vars =
    Core.Set.fold deleted ~init:Var.Set.empty ~f:(fun acc t ->
        match Core.Map.find ctx.def_lhs t with
        | Some v -> Core.Set.add acc v
        | None -> acc)
  in
  let check_use b i e =
    Core.Set.for_all (value_vars e) ~f:(fun v ->
        (not (Core.Set.mem deleted_vars v))
        || Core.Set.is_empty (Core.Set.inter deleted (reaching_at ctx b i v)))
  in
  Base.List.for_all ctx.blocks ~f:(fun b ->
      Base.List.for_all (Array.to_list b.b_defs) ~f:(fun d ->
          match Core.Map.find ctx.def_site (Term.tid d) with
          | Some (_, i) ->
            Core.Set.mem deleted (Term.tid d) || check_use b i (Def.rhs d)
          | None -> true)
      && Base.List.for_all (Array.to_list b.b_jmps) ~f:(fun j ->
             Core.Set.mem exempt_jmps (Term.tid j)
             || check_use b (Array.length b.b_defs) (Jmp.cond j))
      && Base.List.for_all b.b_phis ~f:(fun p ->
                Base.List.for_all (Phi.values p |> Seq.to_list)
                  ~f:(fun (pred, e) ->
                    Core.Set.mem edge_srcs pred || check_use b 0 e)))

(* Removes the blocks the rewrite left with zero predecessors,
   cascading.  [pre_preds_count] is the pre-rewrite count: a block
   that was already unreachable stays. *)
let prune ~(pre_preds_count : Tid.t -> int) (sub : sub term)
    ~(seeds : Tid.Set.t) : sub term =
  let succs_of s =
    Term.enum blk_t s
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m b ->
        Core.Map.set m ~key:(Term.tid b)
          ~data:
            (Term.enum jmp_t b
            |> Seq.fold ~init:Tid.Set.empty ~f:(fun a j -> jmp_targets a j)))
  in
  (* Each cascade round derives the current predecessor transpose. *)
  let rec go s pending =
    let succ_m = succs_of s in
    let preds =
      Core.Map.fold succ_m ~init:Tid.Map.empty
        ~f:(fun ~key:src ~data:ts acc ->
          Core.Set.fold ts ~init:acc ~f:(fun acc t ->
              Core.Map.update acc t ~f:(fun ps ->
                Core.Set.add (Option.value ps ~default:Tid.Set.empty) src)))
    in
    match
      Base.List.find (Core.Set.to_list pending) ~f:(fun t ->
          Core.Set.is_empty
            (Option.value (Core.Map.find preds t) ~default:Tid.Set.empty)
          && pre_preds_count t > 0)
    with
    | None -> s
    | Some t ->
      let succ_ts = Option.value (Core.Map.find succ_m t) ~default:Tid.Set.empty in
      let s' = Term.filter blk_t s ~f:(fun b -> not (Tid.equal (Term.tid b) t)) in
      go s' (Core.Set.union (Core.Set.remove pending t) succ_ts)
  in
  go sub seeds

(* Detect, check, rewrite, repeat until the identity. *)
let strip_sub ~(facts : Hike_kb.facts) ~(names : string Tid.Map.t)
    (sub : sub term) : sub term =
  let abi = facts.abi in
  let denote = facts.denote in
  let name_of t =
    match Core.Map.find names t with
    | Some n -> n
    | None -> Tid.name t
  in
  let cells = cells_of_sub ~denote sub in
  let cell_of tid = Core.Map.find cells tid in
  let true_word = Bil.Int (Word.one 1) in
  (* The strip is a bounded fixpoint: 64 rounds, and hitting the cap
     is named on the channel rather than passing silently. *)
  let max_strip_rounds = 64 in
  let rec loop sub depth =
    if depth > max_strip_rounds then begin
      Hike_diag.warn "canary: strip hit the %d-round cap (sub %s)"
        max_strip_rounds (Base.Option.value (Core.Map.find names (Term.tid sub))
            ~default:(Tid.name (Term.tid sub)));
      sub
    end
    else
      let ctx = build_ctx sub in
      (* The pre-rewrite predecessor counts, one fold per round. *)
      let pre_preds =
        Core.Map.fold ctx.succs ~init:Tid.Map.empty
          ~f:(fun ~key:_ ~data:ts acc ->
            Core.Set.fold ts ~init:acc ~f:(fun acc t ->
                Core.Map.update acc t ~f:(function
                    | None -> 1 | Some n -> n + 1)))
      in
      let pre_preds_count t = Option.value (Core.Map.find pre_preds t) ~default:0 in
      match
        find_comps ~denote ~abi ~names:name_of ~cell_of ~ctx
        |> cells_accounted ~cell_of ~ctx
      with
      | [] -> sub
      | comps ->
        let deleted =
          Base.List.fold comps ~init:Tid.Set.empty ~f:(fun acc c ->
              Core.Set.union acc c.c_delete)
        in
        let exempt_jmps =
          Base.List.fold comps ~init:Tid.Set.empty ~f:(fun acc c ->
              Core.Set.add (Core.Set.add acc c.c_fail_jmp) c.c_eq_jmp)
        in
        let edge_srcs =
          Base.List.fold comps ~init:Tid.Set.empty ~f:(fun acc c ->
              Core.Set.add acc c.c_cmp_blk)
        in
        if not (residual_ok ~ctx ~deleted ~exempt_jmps ~edge_srcs) then sub
        else
          let edge_edits =
            Base.List.fold comps ~init:Tid.Map.empty ~f:(fun m c ->
                Core.Map.set m ~key:c.c_cmp_blk
                  ~data:(c.c_fail_jmp, c.c_eq_jmp))
          in
          let touched =
            Core.Set.fold deleted ~init:Tid.Set.empty ~f:(fun acc t ->
                Base.Option.value_map (Core.Map.find ctx.def_site t)
                  ~default:acc
                  ~f:(fun (btid, _) -> Core.Set.add acc btid))
          in
          let sub =
            Term.map blk_t sub ~f:(fun blk ->
                let t = Term.tid blk in
                let blk =
                  if Core.Set.mem touched t then
                    Term.filter def_t blk ~f:(fun d ->
                        not (Core.Set.mem deleted (Term.tid d)))
                  else blk
                in
                Base.Option.value_map (Core.Map.find edge_edits t) ~default:blk
                  ~f:(fun (fail_j, eq_j) ->
                    let blk =
                      Term.filter jmp_t blk ~f:(fun j ->
                          not (Tid.equal (Term.tid j) fail_j))
                    in
                    Term.map jmp_t blk ~f:(fun j ->
                        if Tid.equal (Term.tid j) eq_j then
                          Jmp.with_cond j true_word
                        else j)))
          in
          (* The deleted edges' phi entries die with them. *)
          let sub =
            Base.List.fold comps ~init:sub ~f:(fun s c ->
                Term.map blk_t s ~f:(fun blk ->
                    if Tid.equal (Term.tid blk) c.c_fail_blk then
                      Blk.map_elts ~phi:(fun p -> Phi.remove p c.c_cmp_blk) blk
                    else blk))
          in
          let seeds =
            Base.List.fold comps ~init:Tid.Set.empty ~f:(fun acc c ->
                Core.Set.add acc c.c_fail_blk)
          in
          loop (prune ~pre_preds_count sub ~seeds) (depth + 1)
  in
  loop sub 0
