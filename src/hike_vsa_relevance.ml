(* Tags defs feeding stack accesses; detects dynamic allocas. *)

open Bap.Std
open Bap_core_theory
module Abi = Hike_abi

[@@@alert "-deprecated"]

(* Tags stack access defs. *)
let stack_access =
  Value.Tag.register
    (module Core_kernel.Unit)
    ~name:"stack_access" ~uuid:"44f5cc3f-d8a4-472e-8930-435eea4b6a1d"


let relevant = Cbat_vsa_utils.relevant

(* Tags dynamic allocas. *)
let dynamic_alloc =
  Value.Tag.register
    (module Core_kernel.Unit)
    ~name:"dynamic_alloc" ~uuid:"7c2f9a41-1b5e-4a8d-9f6e-3d1c0b5a8e77"

let has_stack_access (d : def term) : bool =
  Term.has_attr d stack_access

let is_sp (target : Theory.Target.t) (v : var) : bool =
  Var.same v (Abi.sp target)


let base_var (v : var) : var = Var.base v

(* Tests for a stack access expression. *)
let stack_load_store_addr_vars (e : exp) : Var.Set.t =
  let vis =
    object
      inherit [Var.Set.t] Exp.visitor
      method! visit_load ~mem:_ ~addr _ _ acc =
        Core.Set.union acc (Exp.free_vars addr)
      method! visit_store ~mem:_ ~addr ~exp:_ _ _ acc =
        Core.Set.union acc (Exp.free_vars addr)
    end
  in
  vis#visit_exp e Var.Set.empty

let is_stack_load_store (sp_derived : Var.Set.t) (e : exp) : bool =
  Core.Set.exists
    (stack_load_store_addr_vars e)
    ~f:(fun v -> Core.Set.mem sp_derived (base_var v))

(* Tests for any memory access. *)
let is_memory_side_effect (e : exp) : bool =
  Exp.free_vars e
  |> Core.Set.exists ~f:(fun v ->
      match Var.typ v with
      | Type.Mem _ -> true
      | _ -> false)

(* Collects def maps. *)
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

(* Finds SP-derived vars and stack accesses. *)
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
        (* Skips memory defs so [mem] never propagates as derived. *)
        Base.List.fold ds ~init:Var.Map.empty ~f:(fun m d ->
            if is_memory_side_effect (Def.rhs d) then m
            else
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
  (* Forward fixpoint over SP-derived vars. *)
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
          if is_stack_load_store d_at (Def.rhs d)
          then Core.Set.add acc (Term.tid d)
          else acc))

(* Backward slice from stack accesses. *)
let backward_slice (g : Graphs.Tid.t) (sub : sub term)
    (defs_of : def term list Tid.Map.t) (rhs_bases : Var.Set.t Tid.Map.t)
    (def_of_lhs : def term Var.Map.t)
    (is_stack_access : def term -> bool) : Def.Set.t =
  let defs_of_blk (btid : tid) : def term list =
    match Core.Map.find defs_of btid with Some ds -> ds | None -> []
  in
  let def_uses (d : def term) : Var.Set.t =
    Core.Map.find_exn rhs_bases (Term.tid d)
  in
  let producer_of (v : var) : def term option =
    Core.Map.find def_of_lhs (base_var v)
  in
  (* Worklist slice within one block. *)
  let block_contributors (ds : def term list) (rel : Def.Set.t) : Def.Set.t =
    let seeds, non_seeds =
      Base.List.partition_tf ds ~f:is_stack_access
    in
    let rel = Core.Set.union rel (Def.Set.of_list seeds) in
    if Base.List.is_empty non_seeds then rel
    else
      let pre_built =
        
        Base.List.map non_seeds ~f:(fun d -> (base_var (Def.lhs d), d))
      in
      let initial_vars =
        Core.Set.fold rel ~init:Var.Set.empty ~f:(fun acc d ->
            Core.Set.union acc (def_uses d))
      in
      let rec loop (vars : Var.Set.t) (worklist : (var * def term) list)
          (rel : Def.Set.t) : Def.Set.t =
        match worklist with
        | [] -> rel
        | (_, d) :: rest when Core.Set.mem rel d -> loop vars rest rel
        | (lhs, d) :: rest when Core.Set.mem vars lhs ->
            (* Adds [d] and enqueues its producers. *)
            let new_vars = def_uses d in
            let vars' = Core.Set.union vars new_vars in
            
            let enqueued =
              Base.List.filter_map (Core.Set.to_list new_vars)
                ~f:(fun v ->
                  match producer_of v with
                  | Some d' when not (Core.Set.mem rel d') ->
                      Some (base_var (Def.lhs d'), d')
                  | _ -> None)
            in
            loop vars' (enqueued @ rest) (Core.Set.add rel d)
        | _ :: rest -> loop vars rest rel
      in
      loop initial_vars pre_built rel
  in
  let rev_transfer (btid : tid) (rel : Def.Set.t) : Def.Set.t =
    block_contributors (defs_of_blk btid) rel
  in
  (* Backward fixpoint over contributing defs. *)
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

(* Detects dynamic allocas. *)
let detect_dynamic_alloc (sp : var) (sub : sub term)
    (def_of_lhs : def term Var.Map.t) : Tid.Set.t =
  let sp_base = base_var sp in
  let is_sp_var (v : var) : bool = Var.same (base_var v) sp_base in
  let find_def (v : var) : def term option = Core.Map.find def_of_lhs (base_var v) in
  (* Shape test lives in [Cbat_extraction]. *)
  let is_dynamic_sp_decrement (e : exp) : bool =
    Cbat_vsa.Cbat_extraction.vla_decrement_p sp_base e
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

(* Tags [sub] with all three tags. *)
let analyze (sp : var) (sub : sub term) : sub term =
  let g = Sub.to_graph sub in
  let defs_of, rhs_bases, def_of_lhs = collect_def_maps sub in
  let sp_relative_tids = forward_vars sp g sub defs_of rhs_bases in
  let is_stack_access (d : def term) : bool =
    Core.Set.mem sp_relative_tids (Term.tid d)
  in
  let tagged_defs = backward_slice g sub defs_of rhs_bases def_of_lhs is_stack_access in
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
