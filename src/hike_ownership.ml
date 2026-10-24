(* VSA names each pointer's logical stack ranges; the flow carries those
   ranges through SSA.  A consuming operation that needs one native
   origin contributes its ranges' hull to the interval tree, and
   [Sections.merge_ranges] absorbs every intersecting range. *)

open! Core
open Bap.Std
open Hike_sections
module Model = Hike_stack_model
module Vsa = Cbat_vsa
module Flow = Hike_address_flow

(* One def's rewrite facts: the access's conversion (the mem re-point)
   plus the storage-relative address forms — a value def's whole rhs, an
   access def's mem-node address. *)
type fact = {
  fr_conv : conv;
  fr_bits : int;
  fr_addr : exp option;
  fr_rhs : exp option;
}

let no_fact = { fr_conv = Keep; fr_bits = 0; fr_addr = None; fr_rhs = None }

type rewrites = fact Tid.Map.t Tid.Map.t

type result = {
  sub_trees : sub_tree Tid.Map.t;
  conversions : conv Tid.Map.t;
  rewrites : rewrites;
}

type scan = {
  targets : Flow.anchor Tid.Map.t;
  nonstack : Tid.Set.t;
  leaves : Hike_synth_addr.leaf Var.Map.t Tid.Map.t;
  section_rhs : fact Tid.Map.t;
  (* Ranges an ambiguous value needs the tree to unite. *)
  constraints : range list list;
}

let is_value_addr ~(addr_bits : int) v =
  match Var.typ v with
  | Type.Imm n -> Int.equal n addr_bits
  | _ -> false

let stack_denotation ~(facts : Hike_kb.facts) ~blk ?def e =
  match facts.denote ~blk ?def e with
  | Ok ws -> Vsa.WordSet.in_stack_segment ws
  | Error _ -> false

let stack_anchor (storages : Hike_synth.storage_span list) id =
  match Hike_synth.span_of_storage storages (Hike_synth.Stack id) with
  | Some s ->
      { Flow.base = s.Hike_synth.ss_base;
        offset = Stdlib.Int64.sub s.Hike_synth.ss_lo Model.segment_base }
  | None ->
      failwith
        (Printf.sprintf "hike-ownership: no emitted stack storage %d" id)

(* The window parameter is a property of the raw bindings: the caller
   owns every Args cell except whole argument cells that promotion
   itself binds. *)
let window_param ~(word : int) ~(entry : int64) sub
    (members : member list Tree.t) =
  (Hike_variadic.is_variadic sub
  || (Tree.to_sequence members
      |> Seq.exists ~f:(fun (k, ms) ->
             equal_sec k.lo.p_sec Model.Args
             && not
                  (Base.List.for_all ms ~f:(fun m ->
                       Base.Option.is_some
                         (args_member_cell ~word ~entry m))))))
  && not (Model.fixed_signature sub)

(* A value denotation's logical target.  [Some (target, keys)] asks the
   tree to merge [keys] first; an ambiguous value names the union's
   hull.  No synthetic storage exists here yet. *)
let route ~(word : int) ~(entry : int64)
    ~(members : member list Tree.t) ~window_param ws =
  if (not (Vsa.WordSet.in_stack_segment ws)) || Vsa.WordSet.is_infinite ws then
    None
  else
    match Model.positions_of_offsets ws with
    | Some (lo, hi) when Stdlib.Int64.compare lo hi <= 0 ->
        if window_param && Stdlib.Int64.compare lo
             (Model.args_base ~entry ~word) >= 0
        then Some (Flow.Window, None)
        else (
          match binding_of_range members lo hi with
          | Some (k, _) -> Some (Flow.Binding (k.lo.p_pos, k.hi.p_pos), None)
          | None ->
              let keys =
                Tree.intersections members (range Model.Stack lo hi)
                |> Seq.filter_map ~f:(fun (k, _) ->
                       if equal_sec k.lo.p_sec Model.Stack then Some k
                       else None)
                |> Seq.to_list in
              (match keys with
               | [] | [ _ ] -> None
               | _ -> Some (Flow.Binding (lo, hi), Some keys)))
    | _ -> None

(* A constant data address names its component's base, with the
   displacement folded against the binding's low bound. *)
let section_rhs_of ~(synth : Hike_synth.table ref) ~(addr_bits : int)
    ~(data_tree : data_tree) ~leaves d c =
  match owning_data_binding data_tree c with
  | None -> None
  | Some (id, rel) -> (
      match Hike_synth_addr.offset_of ~addr_bits ~leaves (Def.rhs d) with
      | Some (Bil.Int _ as disp) ->
          let base =
            Hike_synth.record synth
              (Hike_synth.mint_base ~addr_bits (Hike_synth.Global id)) in
          Some (Hike_synth_addr.base_plus ~addr_bits base ~rel disp)
      | _ -> None)

let scan_sub ~(facts : Hike_kb.facts) ~(word : int) ~(entry : int64)
    ~(addr_bits : int) ~(synth : Hike_synth.table ref)
    ~(data_tree : data_tree) ~(members : member list Tree.t) ~window_param sub =
  let targets = ref Tid.Map.empty in
  let nonstack = ref Tid.Set.empty in
  let leaves = ref Tid.Map.empty in
  let section_rhs = ref Tid.Map.empty in
  let constraints = ref [] in
  let record_route d ws =
    match route ~word ~entry ~members ~window_param ws with
    | None -> ()
    | Some (target, None) ->
        targets := Core.Map.set !targets ~key:(Term.tid d) ~data:target
    | Some (target, Some keys) ->
        targets := Core.Map.set !targets ~key:(Term.tid d) ~data:target;
        constraints := keys :: !constraints
  in
  let scan_def ~blk d =
    let ls =
      Hike_synth_addr.address_leaves ~synth:!synth ~denote:facts.denote
        ~storages:[] ~blk ~def:d (Def.rhs d) in
    leaves := Core.Map.set !leaves ~key:(Term.tid d) ~data:ls;
    let v = Def.lhs d in
    if (not (Model.is_mem v))
       && (not (Hike_abi.is_sp facts.abi (Var.base v)))
       && is_value_addr ~addr_bits v
    then
      match facts.denote ~blk ~def:d (Def.rhs d) with
      | Ok ws
        when not (Vsa.WordSet.in_stack_segment ws)
             && not (Vsa.WordSet.is_top ws)
             && not (Vsa.WordSet.is_bottom ws) ->
          nonstack := Core.Set.add !nonstack (Term.tid d);
          Base.Option.iter (Model.singleton_i64 ws) ~f:(fun c ->
              Base.Option.iter
                (section_rhs_of ~synth ~addr_bits ~data_tree ~leaves:ls d c)
                ~f:(fun rhs ->
                  section_rhs :=
                    Core.Map.set !section_rhs ~key:(Term.tid d)
                      ~data:{ no_fact with fr_rhs = Some rhs }))
      | Ok ws -> record_route d ws
      | Error _ -> ();
    (* A load can yield a pointer; its value routes like a value def's. *)
    if Option.is_some (access_of d) then
      match Def.rhs d with
      | Bil.Load _ when is_value_addr ~addr_bits v -> (
          match facts.denote ~blk ~def:d (Def.rhs d) with
          | Ok ws -> record_route d ws
          | Error _ -> ())
      | _ -> ()
  in
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun blk -> Term.enum def_t blk |> Seq.iter ~f:(scan_def ~blk));
  { targets = !targets; nonstack = !nonstack; leaves = !leaves;
    section_rhs = !section_rhs; constraints = !constraints }

(* The ranges a consuming operation needs one origin for. *)
let use_constraints ~(facts : Hike_kb.facts) ~owners
    ~(targets : Flow.anchor Tid.Map.t) ~(pre_conversions : conv Tid.Map.t)
    ~(leaves : Hike_synth_addr.leaf Var.Map.t Tid.Map.t) sub =
  let constraints = ref [] in
  let note_leaf v =
    match Flow.roots (owners v) with
    | roots when Base.List.length roots >= 2 ->
        let keys =
          Base.List.filter_map roots ~f:(function
            | Flow.Binding (lo, hi) -> Some (range Model.Stack lo hi)
            | Flow.Window -> None) in
        if Base.List.length keys >= 2 then constraints := keys :: !constraints
    | _ -> () in
  let note_leaves ls e =
    Exp.free_vars e
    |> Core.Set.iter ~f:(fun v ->
           match Core.Map.find ls v with
           | Some `Addr -> note_leaf v
           | _ -> ()) in
  let note_logical ~blk ?def ls e =
    let visitor =
      object
        inherit [ unit ] Exp.visitor as super
        method! visit_exp e () =
          (match e with
           | Bil.BinOp
               ( (Bil.MINUS | Bil.EQ | Bil.NEQ | Bil.LT | Bil.LE | Bil.SLT
                 | Bil.SLE),
                 a, b )
             when stack_denotation ~facts ~blk ?def a
                  && stack_denotation ~facts ~blk ?def b ->
               note_leaves ls a;
               note_leaves ls b
           | _ -> ());
          super#visit_exp e ()
      end in
    visitor#visit_exp e () in
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun blk ->
         Term.enum def_t blk
         |> Seq.iter ~f:(fun d ->
                let tid = Term.tid d in
                let ls = Core.Map.find_exn leaves tid in
                match access_of d with
                | Some (addr, _, _) -> (
                    match Core.Map.find pre_conversions tid with
                    | Some (Conv_region _ | Conv_window) -> note_leaves ls addr
                    | _ -> ())
                | None -> (
                    match Core.Map.find targets tid with
                    | Some _ -> note_leaves ls (Def.rhs d)
                    | None -> note_logical ~blk ~def:d ls (Def.rhs d)));
         Term.enum jmp_t blk
         |> Seq.iter ~f:(fun j ->
                let ls =
                  Hike_synth_addr.address_leaves ~synth:facts.synth
                    ~denote:facts.denote ~storages:[] ~blk (Jmp.cond j) in
                note_logical ~blk ls (Jmp.cond j)));
  !constraints

let phi_leaves ~(facts : Hike_kb.facts) ~(synth : Hike_synth.table ref) sub =
  Term.enum blk_t sub
  |> Seq.fold ~init:Tid.Map.empty ~f:(fun acc blk ->
         Term.enum phi_t blk
         |> Seq.fold ~init:acc ~f:(fun acc p ->
                let incoming =
                  Phi.values p
                  |> Seq.fold ~init:Tid.Map.empty ~f:(fun incoming (pred, e) ->
                         let ls =
                           Base.Option.value_map (Term.find blk_t sub pred)
                             ~default:Var.Map.empty
                             ~f:(fun blk ->
                               Hike_synth_addr.address_leaves ~synth:!synth
                                 ~denote:facts.denote ~storages:[] ~blk e) in
                         Core.Map.set incoming ~key:pred ~data:ls) in
                Core.Map.set acc ~key:(Term.tid p) ~data:incoming))

let logical_node ~(addr_bits : int) ~stack ~owners ~resolve ~leaves e =
  match e with
  | Bil.BinOp
      ( (Bil.MINUS | Bil.EQ | Bil.NEQ | Bil.LT | Bil.LE | Bil.SLT | Bil.SLE)
        as op,
        a, b )
    when stack a && stack b -> (
      let coordinate e =
        Base.Option.map
          (Flow.logical ~bits:addr_bits ~leaves ~owners ~resolve e)
          ~f:(fun offset ->
            match op with
            | Bil.MINUS | Bil.EQ | Bil.NEQ -> offset
            | _ ->
                Bil.BinOp
                  (Bil.PLUS, Flow.word ~bits:addr_bits Model.segment_base,
                   offset)) in
      match coordinate a, coordinate b with
      | Some a, Some b -> Some (Bil.BinOp (op, a, b))
      | _ -> None)
  | _ -> None

let logical ~(addr_bits : int) ~stack ~owners ~resolve ~leaves e =
  let mapper =
    object
      inherit Exp.mapper as super
      method! map_exp e =
        match
          logical_node ~addr_bits ~stack ~owners ~resolve ~leaves e
        with
        | Some e -> e
        | None -> super#map_exp e
    end in
  mapper#map_exp e

let conversions_of_sub ~(word : int) ~(entry : int64)
    ~(synth : Hike_synth.table ref) ~(ctx : ctx) ~tree sub =
  Term.enum blk_t sub
  |> Seq.concat_map ~f:(Term.enum def_t)
  |> Seq.fold ~init:Tid.Map.empty ~f:(fun acc d ->
         match access_of d with
         | None -> acc
         | Some access ->
             let projected =
               Base.Option.join (Core.Map.find ctx.projections (Term.tid d)) in
             let conv, _ =
               conversion_of ~word ~entry ~synth:!synth ~tree ~data:ctx.data_tree
                 ~projected ~access:(Some access) in
             Core.Map.set acc ~key:(Term.tid d) ~data:conv)

let rewrites_of_sub ~(facts : Hike_kb.facts) ~(addr_bits : int)
    ~(synth : Hike_synth.table ref) ~storages ~window_target ~owners ~resolve
    ~(conversions : conv Tid.Map.t) ~(scan : scan) sub =
  let def_fact ~blk d =
    let tid = Term.tid d in
    let leaves = Core.Map.find_exn scan.leaves tid in
    let access = access_of d in
    let f0 =
      Base.Option.value (Core.Map.find scan.section_rhs tid)
        ~default:no_fact in
    let conv, f0 =
      match access with
      | None -> (Keep, f0)
      | Some (_, width, _) ->
          let conv =
            Base.Option.value (Core.Map.find conversions tid) ~default:Keep in
          (conv, { f0 with fr_conv = conv; fr_bits = 8 * width })
    in
    let target, original =
      match access with
      | Some (addr, _, _) -> (
          match conv with
          | Conv_region id -> (Some (stack_anchor storages id), addr)
          | Conv_window -> (Lazy.force window_target, addr)
          | _ -> (None, addr))
      | None -> (
          match Core.Map.find scan.targets tid with
          | Some anchor -> (resolve anchor, Def.rhs d)
          | None -> (None, Def.rhs d))
    in
    match target with
    | Some target ->
        let exp =
          Flow.substitute ~bits:addr_bits ~leaves ~owners ~resolve
            ~logical:(logical_node ~addr_bits
                        ~stack:(stack_denotation ~facts ~blk ~def:d)
                        ~owners ~resolve ~leaves)
            target original in
        (match access with
         | None -> { f0 with fr_rhs = Some exp }
         | Some _ -> { f0 with fr_addr = Some exp })
    | None when Base.Option.is_none access ->
        let rhs =
          logical ~addr_bits ~stack:(stack_denotation ~facts ~blk ~def:d)
            ~owners ~resolve ~leaves (Def.rhs d) in
        if Exp.equal rhs (Def.rhs d) then f0
        else { f0 with fr_rhs = Some rhs }
    | None -> f0
  in
  Term.enum blk_t sub
  |> Seq.fold ~init:Tid.Map.empty ~f:(fun acc blk ->
         let acc =
           Term.enum def_t blk
           |> Seq.fold ~init:acc ~f:(fun acc d ->
                  Core.Map.set acc ~key:(Term.tid d)
                    ~data:(def_fact ~blk d)) in
         Term.enum jmp_t blk
         |> Seq.fold ~init:acc ~f:(fun acc j ->
                let leaves =
                  Hike_synth_addr.address_leaves ~synth:!synth
                    ~denote:facts.denote ~storages:[] ~blk (Jmp.cond j) in
                let cond =
                  logical ~addr_bits
                    ~stack:(fun e -> stack_denotation ~facts ~blk e)
                    ~owners ~resolve ~leaves (Jmp.cond j) in
                if Exp.equal cond (Jmp.cond j) then acc
                else
                  Core.Map.set acc ~key:(Term.tid j)
                    ~data:{ no_fact with fr_rhs = Some cond }))

let complete_sub ~(facts : Hike_kb.facts) ~(word : int) ~(entry : int64)
    ~(addr_bits : int) ~(synth : Hike_synth.table ref) ~(ctx : ctx) sub =
  let members = Core.Map.find_exn ctx.sub_members (Term.tid sub) in
  let window_param = window_param ~word ~entry sub members in
  let scan = scan_sub ~facts ~word ~entry ~addr_bits ~synth
      ~data_tree:ctx.data_tree ~members ~window_param sub in
  let entry_anchor =
    Base.Option.map (binding_of_range members entry entry)
      ~f:(fun (k, _) -> Flow.Binding (k.lo.p_pos, k.hi.p_pos)) in
  let phi_leaves = phi_leaves ~facts ~synth sub in
  let owners =
    Flow.solve ~sub ~abi:facts.abi ~entry:entry_anchor ~targets:scan.targets
      ~nonstack:scan.nonstack ~leaves:scan.leaves
      ~phi_leaves:(fun p pred ->
        Core.Map.find_exn phi_leaves (Term.tid p) |> fun incoming ->
        Core.Map.find_exn incoming pred)
      ~defs:facts.defs in
  let constraints =
    scan.constraints
    @ use_constraints ~facts ~owners ~targets:scan.targets
        ~pre_conversions:ctx.conversions ~leaves:scan.leaves sub in
  let merged =
    Base.List.fold constraints ~init:members ~f:merge_ranges in
  let tree = finalize_tree ~word ~entry ~whole:[] merged in
  let layout = layout_of_tree ~word ~entry ~abi:facts.abi ~sub tree in
  let storages = spans_of_layout ~synth ~word layout in
  let window_target =
    lazy (
      if layout.Model.window_param && not (Model.fixed_signature sub) then
        Some
          { Flow.base =
              Hike_synth.record synth
                (Hike_synth.mint_base ~addr_bits Hike_synth.Window);
            offset = 0L }
      else None) in
  let resolve = function
    | Flow.Window -> Lazy.force window_target
    | Flow.Binding (lo, hi) -> (
        match storage_of_range tree (range Model.Stack lo hi) with
        | Some rs -> Some (stack_anchor storages
                             (region_id_of_storage rs.storage))
        | None ->
            failwith
              (Printf.sprintf
                 "hike-ownership: no binding for [%Ld, %Ld]" lo hi)) in
  let conversions =
    conversions_of_sub ~word ~entry ~synth ~ctx ~tree sub in
  let rewrites =
    rewrites_of_sub ~facts ~addr_bits ~synth ~storages ~window_target ~owners
      ~resolve ~conversions ~scan sub in
  (tree, conversions, rewrites)

let complete ~(facts : Hike_kb.facts) ~(word : int) ~(entry : int64)
    ~(ctx : ctx) (program : program term) : Hike_synth.table * result =
  let synth = ref facts.synth in
  let addr_bits = Model.word_bits word in
  let sub_trees, conversions, rewrites =
    Term.enum sub_t program
    |> Seq.fold ~init:(Tid.Map.empty, Tid.Map.empty, Tid.Map.empty)
         ~f:(fun (trees, conversions, rewrites) sub ->
           let tid = Term.tid sub in
           let tree, sub_conversions, sub_rewrites =
             complete_sub ~facts ~word ~entry ~addr_bits ~synth ~ctx sub in
           ( Core.Map.set trees ~key:tid ~data:tree,
             Core.Map.fold sub_conversions ~init:conversions
               ~f:(fun ~key ~data acc -> Core.Map.set acc ~key ~data),
             Core.Map.set rewrites ~key:tid ~data:sub_rewrites ))
  in
  !synth, { sub_trees; conversions; rewrites }
