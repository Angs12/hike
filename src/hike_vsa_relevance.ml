(* Relevance analysis: tags defs that contribute to stack accesses. Forward pass tracks vars derived from SP; backward pass collects defs that flow into stack accesses. Also detects dynamic allocas (RSP decrements with non-literal size). *)

open Bap.Std

[@@@alert "-deprecated"]

(* Tags a def whose address uses an SP-derived var (a stack access). *)
let direct_sp =
  Value.Tag.register
    (module Core_kernel.Unit)
    ~name:"direct_sp" ~uuid:"16822ae7-3a5e-477f-b4d3-b3e7e98c6286"

(* Tags runtime-sized stack allocations (VLA/alloca). *)
let dynamic_alloc =
  Value.Tag.register
    (module Core_kernel.Unit)
    ~name:"dynamic_alloc" ~uuid:"7c2f9a41-1b5e-4a8d-9f6e-3d1c0b5a8e77"

(* Tag every stack-relevant def in [sub] with [relevant], [direct_sp], and [dynamic_alloc] as appropriate. *)
let analyze (sp : var) (sub : sub term) : sub term =
  let g = Sub.to_graph sub in
  let defs_of : def term list Tid.Map.t =
    Term.enum blk_t sub
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m blk ->
        Core.Map.set m ~key:(Term.tid blk)
          ~data:(Term.enum def_t blk |> Seq.to_list))
  in
  let rhs_bases : Var.Set.t Tid.Map.t =
    Term.enum blk_t sub
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m blk ->
        Term.enum def_t blk
        |> Seq.fold ~init:m ~f:(fun m d ->
            let bases =
              Exp.free_vars (Def.rhs d)
              |> Core.Set.fold ~init:Var.Set.empty ~f:(fun acc v ->
                  Core.Set.add acc (Var.base v))
            in
            Core.Map.set m ~key:(Term.tid d) ~data:bases))
  in
  let defs_of_blk (btid : tid) : def term list =
    match Core.Map.find defs_of btid with Some ds -> ds | None -> []
  in
  let def_uses (d : def term) : Var.Set.t =
    Core.Map.find_exn rhs_bases (Term.tid d)
  in
  (* Forward closure: vars reachable from the entry SP. *)
  let d_of_defs (ds : def term list) (d_in : Var.Set.t) : Var.Set.t =
    if Base.List.is_empty ds then d_in
    else
      let users =
        Base.List.fold ds ~init:Var.Map.empty ~f:(fun m d ->
            Core.Set.fold (def_uses d) ~init:m ~f:(fun m v ->
                let k = Var.base v in
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
                    let lhs = Var.base (Def.lhs d) in
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
  (* Forward dataflow: per-block SP-derived var sets. *)
  let transfer (btid : tid) (d_in : Var.Set.t) : Var.Set.t =
    d_of_defs (defs_of_blk btid) d_in
  in
  let sol : (tid, Var.Set.t) Graphlib.Std.Solution.t =
    Graphlib.Std.Graphlib.fixpoint (module Graphs.Tid)
      ~start:Graphs.Tid.start
      ~init:
        (Graphlib.Std.Solution.create
           (Tid.Map.singleton Graphs.Tid.start
              (Var.Set.singleton (Var.base sp)))
           Var.Set.empty)
      ~equal:Core.Set.equal ~merge:Core.Set.union ~f:transfer g
  in
  let sp_relative_tids =
    Term.enum blk_t sub |> Seq.fold ~init:Tid.Set.empty ~f:(fun acc blk ->
        let d_at =
          d_of_defs (defs_of_blk (Term.tid blk))
            (Graphlib.Std.Solution.get sol (Term.tid blk))
        in
        Term.enum def_t blk |> Seq.fold ~init:acc ~f:(fun acc d ->
            if
              Core.Set.exists (def_uses d) ~f:(fun x -> Core.Set.mem d_at x)
            then Core.Set.add acc (Term.tid d)
            else acc))
  in
  let is_stack_access (d : def term) : bool =
    Core.Set.mem sp_relative_tids (Term.tid d)
  in
  (* Backward: collect defs that contribute to stack accesses. *)
  let block_contributors (ds : def term list) (relevant : Def.Set.t) :
      Def.Set.t =
    let seeds, non_seeds =
      Base.List.partition_tf ds ~f:is_stack_access
    in
    let relevant = Core.Set.union relevant (Def.Set.of_list seeds) in
    if Base.List.is_empty non_seeds then relevant
    else
      let vars =
        Core.Set.fold relevant ~init:Var.Set.empty ~f:(fun acc d ->
            Core.Set.union acc (def_uses d))
      in
      Base.List.fold non_seeds ~init:relevant ~f:(fun acc d ->
          if Core.Set.mem vars (Var.base (Def.lhs d)) then Core.Set.add acc d
          else acc)
  in
  let rev_transfer (btid : tid) (relevant : Def.Set.t) : Def.Set.t =
    block_contributors (defs_of_blk btid) relevant
  in
  let rev_sol : (tid, Def.Set.t) Graphlib.Std.Solution.t =
    Graphlib.Std.Graphlib.fixpoint (module Graphs.Tid)
      ~rev:true ~start:Graphs.Tid.exit
      ~init:(Graphlib.Std.Solution.create Tid.Map.empty Def.Set.empty)
      ~equal:Core.Set.equal ~merge:Core.Set.union ~f:rev_transfer g
  in
  let tagged =
    Term.enum blk_t sub
    |> Seq.fold ~init:Def.Set.empty ~f:(fun acc blk ->
        Core.Set.union acc (Graphlib.Std.Solution.get rev_sol (Term.tid blk)))
    |> fun acc ->
       Core.Set.union acc (Graphlib.Std.Solution.get rev_sol Graphs.Tid.start)
  in
  let is_arg_setup (d : def term) : bool =
    match Var.typ (Def.lhs d) with
    | Type.Imm 64 ->
      (match Var.name (Def.lhs d) with
       | "RDI" | "RSI" | "RDX" | "RCX" | "R8" | "R9" -> true
       | _ -> false)
    | _ -> false
  in
  (* Detect dynamic allocas: RSP := RSP - size with non-literal size. *)
  let def_of_lhs =
    Term.enum blk_t sub
    |> Seq.fold ~init:Var.Map.empty ~f:(fun m blk ->
        Term.enum def_t blk
        |> Seq.fold ~init:m ~f:(fun m d ->
            Core.Map.set m ~key:(Var.base (Def.lhs d)) ~data:d))
  in
  let non_literal_size = function Bil.Int _ -> false | _ -> true in
  let alloc_rhs (e : exp) : bool =
    match e with
    | Bil.BinOp (Bil.MINUS, Bil.Var a, size) ->
        Var.same a sp && non_literal_size size
    | _ -> false
  in
  let dyn_alloc_tids (d : def term) : Tid.Set.t =
    let lhs = Def.lhs d in
    match Def.rhs d with
    | _ when Var.same lhs sp && alloc_rhs (Def.rhs d) ->
        Tid.Set.singleton (Term.tid d)
    | Bil.Var tmp when Var.same lhs sp ->
        (match Core.Map.find def_of_lhs (Var.base tmp) with
         | Some d' when alloc_rhs (Def.rhs d') ->
             Tid.Set.of_list [ Term.tid d; Term.tid d' ]
         | _ -> Tid.Set.empty)
    | _ -> Tid.Set.empty
  in
  let alloc_tids =
    Term.enum blk_t sub
    |> Seq.fold ~init:Tid.Set.empty ~f:(fun acc blk ->
        Term.enum def_t blk
        |> Seq.fold ~init:acc ~f:(fun acc d ->
            Core.Set.union acc (dyn_alloc_tids d)))
  in
  sub
  |> Term.map blk_t ~f:(fun b ->
      Term.map def_t b ~f:(fun d ->
          let d =
            if
              Core.Set.mem tagged d || is_arg_setup d
              || Core.Set.mem alloc_tids (Term.tid d)
            then Term.set_attr d Cbat_vsa_utils.relevant ()
            else d
          in
          let d =
            if Core.Set.mem alloc_tids (Term.tid d) then
              Term.set_attr d dynamic_alloc ()
            else d
          in
          if is_stack_access d then Term.set_attr d direct_sp () else d))
