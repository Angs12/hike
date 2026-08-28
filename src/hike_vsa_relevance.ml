(* Relevance analysis: tags defs that contribute to stack accesses.
   Forward pass tracks vars derived from SP; backward pass collects defs that flow into stack accesses.
   Also detects dynamic allocas (RSP decrements with non-literal size). *)

open Bap.Std
open Bap_core_theory

[@@@alert "-deprecated"]

(* Tags a def whose address uses an SP-derived var (a stack access). *)
let stack_access =
  Value.Tag.register
    (module Core_kernel.Unit)
    ~name:"stack_access" ~uuid:"44f5cc3f-d8a4-472e-8930-435eea4b6a1d"

(* Re-export relevant tag from Cbat_vsa_utils. *)
let relevant = Cbat_vsa_utils.relevant

(* Tags runtime-sized stack allocations (VLA/alloca). *)
let dynamic_alloc =
  Value.Tag.register
    (module Core_kernel.Unit)
    ~name:"dynamic_alloc" ~uuid:"7c2f9a41-1b5e-4a8d-9f6e-3d1c0b5a8e77"

let has_stack_access (d : def term) : bool =
  Term.has_attr d stack_access

let is_sp (target : Theory.Target.t) (v : var) : bool =
  Var.same v (Targetutils.sp target)

(* Normalize a variable to its base form for map/set keys. *)
let base_var (v : var) : var = Var.base v

(* Check if [e] has the shape of a memory Load or Store (including Cast-wrapped). *)
let is_stack_load_store (e : exp) : bool =
  match e with
  | Bil.Load _
  | Bil.Store _
  | Bil.Cast (_, _, Bil.Load _)
  | Bil.Cast (_, _, Bil.Store _) -> true
  | _ -> false

(* Helper 1: collect def maps using a Term.visitor pass. *)
let collect_def_maps (sub : sub term) :
    (def term list Tid.Map.t * Var.Set.t Tid.Map.t * def term Var.Map.t) =
  let v =
    object
      inherit [def term list Tid.Map.t * Var.Set.t Tid.Map.t * def term Var.Map.t] Term.visitor
      method! visit_blk blk (defs_of, rhs_bases, def_of_lhs) =
        let btid = Term.tid blk in
        let ds = Term.enum def_t blk |> Seq.to_list in
        let defs_of' = Core.Map.set defs_of ~key:btid ~data:ds in
        let rhs_bases', def_of_lhs' =
          Base.List.fold ds ~init:(rhs_bases, def_of_lhs) ~f:(fun (rb_acc, dl_acc) d ->
              let bases =
                Exp.free_vars (Def.rhs d)
                |> Core.Set.fold ~init:Var.Set.empty ~f:(fun acc v ->
                    Core.Set.add acc (base_var v))
              in
              let rb_acc' = Core.Map.set rb_acc ~key:(Term.tid d) ~data:bases in
              let dl_acc' = Core.Map.set dl_acc ~key:(base_var (Def.lhs d)) ~data:d in
              (rb_acc', dl_acc'))
        in
        (defs_of', rhs_bases', def_of_lhs')
    end
  in
  v#visit_sub sub (Tid.Map.empty, Tid.Map.empty, Var.Map.empty)

(* Helper 2: forward dataflow to find SP-derived vars and direct stack accesses. *)
let forward_vars (sp : var) (g : Graphs.Tid.t) (sub : sub term)
    (defs_of : def term list Tid.Map.t) (rhs_bases : Var.Set.t Tid.Map.t) :
    Tid.Set.t =
  let defs_of_blk (btid : tid) : def term list =
    match Core.Map.find defs_of btid with Some ds -> ds | None -> []
  in
  let def_uses (d : def term) : Var.Set.t =
    Core.Map.find_exn rhs_bases (Term.tid d)
  in
  let d_of_defs (ds : def term list) (d_in : Var.Set.t) : Var.Set.t =
    if Base.List.is_empty ds then d_in
    else
      let users =
        Base.List.fold ds ~init:Var.Map.empty ~f:(fun m d ->
            Core.Set.fold (def_uses d) ~init:m ~f:(fun m v ->
                let k = base_var v in
                match Core.Map.find m k with
                | None -> Core.Map.set m ~key:k ~data:[ d ]
                | Some l -> Core.Map.set m ~key:k ~data:(d :: l)))
      in
      let result = ref d_in in
      let queue = ref d_in in
      let added = ref Tid.Set.empty in
      let pending = ref (Tid.Set.of_list (Base.List.map ds ~f:(fun d -> Term.tid d))) in
      let rec drain () =
        if Core.Set.is_empty !queue then ()
        else
          let v = Core.Set.choose_exn !queue in
          queue := Core.Set.remove !queue v;
          match Core.Map.find users v with
          | None -> drain ()
          | Some defs_using_v ->
              Base.List.iter defs_using_v ~f:(fun d ->
                  let tid = Term.tid d in
                  if Core.Set.mem !pending tid && not (Core.Set.mem !added tid) then (
                    let lhs = base_var (Def.lhs d) in
                    if not (Core.Set.mem !result lhs) then (
                      result := Core.Set.add !result lhs;
                      queue := Core.Set.add !queue lhs);
                    added := Core.Set.add !added tid;
                    pending := Core.Set.remove !pending tid));
              drain ()
      in
      drain ();
      !result
  in
  let transfer (btid : tid) (d_in : Var.Set.t) : Var.Set.t =
    d_of_defs (defs_of_blk btid) d_in
  in
  (* Forward fixpoint: Monotone forward propagation of SP-derived vars.
     - start: entry block (Graphs.Tid.start)
     - init: singleton SP base var at start, empty elsewhere
     - merge: set union (join on branching paths)
     - equal: set equality *)
  let sol : (tid, Var.Set.t) Graphlib.Std.Solution.t =
    Graphlib.Std.Graphlib.fixpoint (module Graphs.Tid)
      ~start:Graphs.Tid.start
      ~init:
        (Graphlib.Std.Solution.create
           (Tid.Map.singleton Graphs.Tid.start
              (Var.Set.singleton (base_var sp)))
           Var.Set.empty)
      ~equal:Core.Set.equal ~merge:Core.Set.union ~f:transfer g
  in
  Term.enum blk_t sub |> Seq.fold ~init:Tid.Set.empty ~f:(fun acc blk ->
      let d_at =
        d_of_defs (defs_of_blk (Term.tid blk))
          (Graphlib.Std.Solution.get sol (Term.tid blk))
      in
      Term.enum def_t blk |> Seq.fold ~init:acc ~f:(fun acc d ->
          if is_stack_load_store (Def.rhs d)
             && Core.Set.exists (def_uses d) ~f:(fun x -> Core.Set.mem d_at x)
          then Core.Set.add acc (Term.tid d)
          else acc))

(* Helper 3: backward dataflow slice from stack access seeds. *)
let backward_slice (g : Graphs.Tid.t) (sub : sub term)
    (defs_of : def term list Tid.Map.t) (rhs_bases : Var.Set.t Tid.Map.t)
    (is_stack_access : def term -> bool) : Def.Set.t =
  let defs_of_blk (btid : tid) : def term list =
    match Core.Map.find defs_of btid with Some ds -> ds | None -> []
  in
  let def_uses (d : def term) : Var.Set.t =
    Core.Map.find_exn rhs_bases (Term.tid d)
  in
  let block_contributors (ds : def term list) (rel : Def.Set.t) : Def.Set.t =
    let seeds, non_seeds =
      Base.List.partition_tf ds ~f:is_stack_access
    in
    let rel = Core.Set.union rel (Def.Set.of_list seeds) in
    if Base.List.is_empty non_seeds then rel
    else
      let vars =
        Core.Set.fold rel ~init:Var.Set.empty ~f:(fun acc d ->
            Core.Set.union acc (def_uses d))
      in
      Base.List.fold non_seeds ~init:rel ~f:(fun acc d ->
          if Core.Set.mem vars (base_var (Def.lhs d)) then Core.Set.add acc d
          else acc)
  in
  let rev_transfer (btid : tid) (rel : Def.Set.t) : Def.Set.t =
    block_contributors (defs_of_blk btid) rel
  in
  (* Backward fixpoint: Reverse propagation of defs flowing into stack access seeds.
     - rev: true (walk predecessors from exit)
     - start: exit block (Graphs.Tid.exit)
     - init: empty Def.Set everywhere
     - merge: set union (join on merging paths)
     - equal: set equality *)
  let rev_sol : (tid, Def.Set.t) Graphlib.Std.Solution.t =
    Graphlib.Std.Graphlib.fixpoint (module Graphs.Tid)
      ~rev:true ~start:Graphs.Tid.exit
      ~init:(Graphlib.Std.Solution.create Tid.Map.empty Def.Set.empty)
      ~equal:Core.Set.equal ~merge:Core.Set.union ~f:rev_transfer g
  in
  Term.enum blk_t sub
  |> Seq.fold ~init:Def.Set.empty ~f:(fun acc blk ->
      Core.Set.union acc (Graphlib.Std.Solution.get rev_sol (Term.tid blk)))
  |> fun acc ->
     Core.Set.union acc (Graphlib.Std.Solution.get rev_sol Graphs.Tid.start)

(* Helper 4: detect dynamic allocations (VLA / alloca). *)
let detect_dynamic_alloc (sp : var) (sub : sub term)
    (def_of_lhs : def term Var.Map.t) : Tid.Set.t =
  let sp_base = base_var sp in
  let is_sp_var (v : var) : bool = Var.same (base_var v) sp_base in
  let find_def (v : var) : def term option = Core.Map.find def_of_lhs (base_var v) in
  let non_literal_size = function Bil.Int _ -> false | _ -> true in
  let is_dynamic_sp_decrement (e : exp) : bool =
    match e with
    | Bil.BinOp (Bil.MINUS, Bil.Var a, size) ->
        is_sp_var a && non_literal_size size
    | _ -> false
  in
  let v =
    object
      inherit [Tid.Set.t] Term.visitor
      method! visit_def d acc =
        let lhs = Def.lhs d in
        if is_sp_var lhs then
          let rhs = Def.rhs d in
          if is_dynamic_sp_decrement rhs then
            Core.Set.add acc (Term.tid d)
          else
            match rhs with
            | Bil.Var tmp ->
                (match find_def tmp with
                 | Some d' when is_dynamic_sp_decrement (Def.rhs d') ->
                     Core.Set.add (Core.Set.add acc (Term.tid d)) (Term.tid d')
                 | _ -> acc)
            | _ -> acc
        else acc
    end
  in
  v#visit_sub sub Tid.Set.empty

(* Tag every stack-relevant def in [sub] with [relevant], [stack_access], and [dynamic_alloc] as appropriate. *)
let analyze (sp : var) (sub : sub term) : sub term =
  let g = Sub.to_graph sub in
  let defs_of, rhs_bases, def_of_lhs = collect_def_maps sub in
  let sp_relative_tids = forward_vars sp g sub defs_of rhs_bases in
  let is_stack_access (d : def term) : bool =
    Core.Set.mem sp_relative_tids (Term.tid d)
  in
  let tagged_defs = backward_slice g sub defs_of rhs_bases is_stack_access in
  let alloc_tids = detect_dynamic_alloc sp sub def_of_lhs in
  sub
  |> Term.map blk_t ~f:(fun b ->
      Term.map def_t b ~f:(fun d ->
          let d =
            if Core.Set.mem tagged_defs d then
              Term.set_attr d relevant ()
            else d
          in
          let d =
            if Core.Set.mem alloc_tids (Term.tid d) then
              Term.set_attr d dynamic_alloc ()
            else d
          in
          if is_stack_access d then Term.set_attr d stack_access () else d))
