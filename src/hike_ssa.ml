(* SSA materialization: every cross-block register value flows through
   a BIR phi term, so the emitter renders joins straight off the terms.
   The CFG is the BIR's own (every edge an explicit jmp — the completion
   writes the guards' fallthroughs).  SP is renamed like any
   register; the call-pushed word rides a restore def (single-pred
   continuation) or the phi incoming (shared continuation).  Each call
   site's ret lanes mint fresh versions, and every block carries the
   versions in effect at its end. *)

open Bap.Std
open Bap_core_theory

module Model = Hike_stack_model
module Abi = Hike_abi

(* The block's end-of-board version map and the sub's SSA mark live
   in the stack model (the producer/emitter contract home). *)
let versions_tag = Model.versions_tag
let ssa_tag = Model.ssa_tag
let is_ssa = Model.is_ssa
module Versions = Model.Versions

(* Every non-interrupt, non-halt call jmp mints its ret lanes. *)
let call_of_jmp (j : jmp term) : Call.t option =
  match Jmp.kind j with
  | Call c -> (
      match Call.target c with
      | Direct target ->
          if Hike_abi.is_interrupt_name (Tid.name target) then None
          else
            (match Hike_native_fp.native_fp_op (Tid.name target) with
             | Some Hike_native_fp.FHLT -> None
             | _ -> Some c)
      | Indirect _ -> Some c)
  | _ -> None

(* The machine calls: a mapped intrinsic is a soft-float helper, not a
   call — no return address is pushed, so no SP restore rides it.  An
   unmapped intrinsic target (the atomic family's marker stubs) is a
   fact about one instruction, not code — the model's own rule. *)
let machine_call (j : jmp term) : bool =
  match Jmp.kind j with
  | Call c -> (
      match Call.target c with
      | Direct target ->
        Base.Option.is_none (Hike_native_fp.native_fp_op (Tid.name target))
        && not (Hike_abi.is_intrinsic_name (Tid.name target))
      | Indirect _ -> true)
  | _ -> false

let restore_word ~(abi : Abi.t) : exp =
  Bil.Int
    (Cbat_word.to_word
       (Cbat_word.of_int ~width:(Model.word_bits abi.Abi.word) abi.Abi.word))

#ifdef VSA_DEBUG
let debug_graph g =
  Graphs.Tid.nodes g
  |> Seq.iter ~f:(fun n ->
         Format.eprintf "SSA-DBG %s -> [%s]@." (Tid.name n)
           (String.concat ","
              (Graphs.Tid.Node.succs n g |> Seq.to_list
              |> Base.List.map ~f:Tid.name)))

let debug_frontiers g frontier =
  Format.eprintf "SSA-DBG dom-tree: %d nodes; frontiers: %s@."
    (Base.List.length (Graphs.Tid.nodes g |> Seq.to_list))
    (String.concat ","
       (Graphs.Tid.nodes g
        |> Seq.to_list
        |> Base.List.filter_map ~f:(fun n ->
               let fr = Graphlib.Std.Frontier.enum frontier n |> Seq.to_list in
               if Base.List.is_empty fr then None
               else
                 Some
                   (Tid.name n ^ "=>"
                    ^ String.concat "," (Base.List.map fr ~f:Tid.name)))))

let debug_vars vars =
  Format.eprintf "SSA-DBG vars(%d): [%s]@." (Core.Set.length vars)
    (String.concat "," (Core.Set.to_list vars |> Base.List.map ~f:Var.name))

let debug_var_sites ~iterated_frontier v (tids : Tid.t list) =
  let bs = Graphs.Tid.start :: tids |> Core.Set.of_list (module Tid) in
  Format.eprintf "SSA-DBG var %s sites=[%s] idf=[%s]@." (Var.name v)
    (String.concat "," (Base.List.map tids ~f:Tid.name))
    (String.concat ","
       (Core.Set.to_list (iterated_frontier bs) |> Base.List.map ~f:Tid.name))
#endif

(* The SP restore def at a call's single-pred continuation. *)
let with_top_def (blk : blk term) (d : def term) : blk term =
  Term.prepend def_t blk d

(* One phi rewrite: the incoming from [src] becomes [exp]. *)
let set_incoming (phi : phi term) ~(src : Tid.t) (exp : exp) : phi term =
  Phi.of_list (Phi.lhs phi)
    (Phi.values phi
    |> Seq.map ~f:(fun (s, e) -> if Tid.equal s src then (s, exp) else (s, e))
    |> Seq.to_list)

(* Pruned SSA: a phi sits at the iterated dominance frontier of a var's
   writes, and only where the var is live-in.  SP also has an edge
   definition at a machine call with a continuation. *)
let place_phis ~sp ~vars ~def_sites_of ~live_in ~call_blocks
    ~machine_blk_tids ~has_continuation ~iterated_frontier ~preds_of
    (sub : sub term) : sub term =
  let insert_phi ~(preds : Tid.t list) (blk : blk term) (v : var) =
    if
      Term.enum phi_t blk |> Seq.exists ~f:(fun p -> Var.same (Phi.lhs p) v)
    then blk
    else Term.append phi_t blk (Phi.of_list v (Base.List.map preds ~f:(fun p -> (p, Bil.Var v))))
  in
#ifdef VSA_DEBUG
  debug_vars vars;
#endif
  Core.Set.to_list vars
    |> Base.List.fold ~init:sub ~f:(fun sub v ->
#ifdef VSA_DEBUG
        debug_var_sites ~iterated_frontier v (def_sites_of v);
#endif
        let sites = def_sites_of v in
        let sites =
          if Var.same v sp then
            sites
            @ Base.List.filter_map call_blocks ~f:(fun (blk, cs) ->
                  if
                    Core.Set.mem machine_blk_tids (Term.tid blk)
                    && Base.List.exists cs ~f:has_continuation
                  then Some (Term.tid blk)
                  else None)
          else sites
        in
        let bs = Graphs.Tid.start :: sites |> Core.Set.of_list (module Tid) in

        iterated_frontier bs
        |> Core.Set.to_list
        |> Base.List.filter ~f:(fun tid -> Core.Set.mem (live_in tid) v)
        |> Base.List.fold ~init:sub ~f:(fun sub tid ->
               match Term.find blk_t sub tid with
               | None -> sub
               | Some blk ->
                   Term.update blk_t sub
                     (insert_phi ~preds:(preds_of tid) blk v)))

(* The rename walk, dominator-tree ordered from [start]: every def and
   phi takes a fresh version, every read the live one, and each block's
   argument and ret versions are stamped. *)
let rename_versions ~abi ~sp ~g ~dom ~renamable ~succs_of ~machine_blk_tids
    (sub : sub term) : sub term =
  let vars_tbl : var list Var.Table.t = Core.Hashtbl.create (module Var) in
  let nums : int Var.Table.t = Core.Hashtbl.create (module Var) in
  (* Each var's live version: the top entry, when it is versioned. *)
  let live_vers () : (var * var) list =
    Core.Hashtbl.to_alist vars_tbl
    |> Base.List.filter_map ~f:(fun (k, vs) ->
           match vs with
           | d :: _ when Var.index d > 0 -> Some (k, d)
           | _ -> None)
  in
  let top v =
    match Core.Hashtbl.find vars_tbl v with Some (d :: _) -> d | _ -> v
  in
  let new_name x =
    Core.Hashtbl.change nums x ~f:(function
      | None -> Some 1
      | Some k -> Some (k + 1));
    let y = Var.with_index x (Core.Hashtbl.find_exn nums x) in
    Core.Hashtbl.add_multi vars_tbl ~key:x ~data:y;
    y
  in
  let substitute =
    (object
      inherit Exp.mapper

      method! map_sym z =
        match Core.Hashtbl.find vars_tbl z with
        | Some (d :: _) -> d
        | _ -> z
    end)#map_exp
  in
  let stamps : Versions.t Tid.Map.t ref = ref Tid.Map.empty in
  (* The dominator tree's immediate children, indexed once; the rename
     walk queries it per node (any dom-tree order is a valid walk). *)
  let dom_children : Tid.t list Tid.Map.t =
    Graphs.Tid.nodes g
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m n ->
           match Graphlib.Std.Tree.parent dom n with
           | Some p ->
             let cs = Base.Option.value (Core.Map.find m p) ~default:[] in
             Core.Map.set m ~key:p ~data:(n :: cs)
           | None -> m)
  in
  let children tid =
    Base.Option.value (Core.Map.find dom_children tid) ~default:[]
  in
  let rec walk sub' tid =
    let minted = ref [] in
    let sub' =
      match Term.find blk_t sub' tid with
      | None -> sub'
      | Some blk ->
          let blk =
            Term.map phi_t blk ~f:(fun phi ->
                Phi.with_lhs phi (new_name (Phi.lhs phi)))
          in
          let blk =
            Term.map def_t blk ~f:(fun d ->
                let d = Def.with_rhs d (substitute (Def.rhs d)) in
                (* The name-routed lanes (slots, call args, the
                   window) keep their base name: readers find them
                   by name. *)
                if renamable (Def.lhs d) then
                  Def.with_lhs d (new_name (Def.lhs d))
                else d)
          in
          let blk = Term.map jmp_t blk ~f:(fun j ->
              Jmp.map_exp ~f:substitute j
              |> Model.map_effects ~read:top ~write:Fun.id) in
          (* The argument map reads BEFORE the call's ret mints: an
             argument lane passes the machine's current value, not
             the callee's future result. *)
          let arg_vers = live_vers () in
          let blk = Term.map jmp_t blk ~f:(fun j ->
              Model.map_effects ~read:Fun.id ~write:(fun v ->
                  let version = new_name v in
                  minted := (v, version) :: !minted;
                  version) j) in
          stamps :=
            Core.Map.set !stamps ~key:tid
              ~data:
                { Versions.args = arg_vers;
                  rets = !minted };
          Term.update blk_t sub' blk
    in
    (* The successors' phis take this block's tops; the SP incoming
       from a call block carries the pushed word. *)
    let sub' =
      Base.List.fold (succs_of tid) ~init:sub' ~f:(fun acc s ->
          match Term.find blk_t acc s with
          | Some dst ->
              Term.update blk_t acc
                (Term.map phi_t dst ~f:(fun phi ->
                     let base = Var.base (Phi.lhs phi) in
                     let exp =
                       if
                         Var.same base sp
                         && Core.Set.mem machine_blk_tids tid
                       then
                         Bil.BinOp (Bil.PLUS, Bil.Var (top base), restore_word ~abi)
                       else Bil.Var (top base)
                     in
                     set_incoming phi ~src:tid exp))
          | None -> acc)
    in
    let sub' = Base.List.fold (children tid) ~init:sub' ~f:walk in
    (* Pop this block's names: defs, phis, and minted rets. *)
    (match Term.find blk_t sub' tid with
     | Some blk ->
         let pop v =
           Core.Hashtbl.change vars_tbl (Var.base v) ~f:(function
               | Some (_ :: xs) -> Some xs
               | xs -> xs)
         in
         Term.enum phi_t blk |> Seq.iter ~f:(fun phi -> pop (Phi.lhs phi));
         Term.enum def_t blk |> Seq.iter ~f:(fun d -> pop (Def.lhs d));
         Base.List.iter !minted ~f:(fun (v, _) -> pop (Var.base v))
     | None -> ());
    sub'
  in
  let sub = walk sub Graphs.Tid.start in
  !stamps
  |> Core.Map.fold ~init:sub ~f:(fun ~key ~data sub ->
           match Term.find blk_t sub key with
           | None -> sub
           | Some blk ->
               Term.update blk_t sub (Term.set_attr blk versions_tag data))

let ssa_sub ~(target : Bap_core_theory.Theory.Target.t) (sub : sub term) : sub term =
  if is_ssa sub then sub
  else if Seq.is_empty (Term.enum blk_t sub) then sub
  else
    let abi = Abi.of_target target in
    let pc = Abi.pc target in
    (* The sub's own SP var: the retype gave it the pointer sort, and the
       SP-restore def must keep that sort (a fresh [Abi.sp] would
       reintroduce an integer SP beside the pointer one). *)
    let sp =
      Term.enum blk_t sub
      |> Seq.concat_map ~f:(fun b -> Term.enum def_t b)
      |> Seq.find_map ~f:(fun d ->
             let v = Def.lhs d in
             if Abi.is_sp abi (Var.base v) then Some v else None)
      |> Base.Option.value ~default:(Abi.sp target)
    in
    let window = Model.hike_window_var ~word:abi.Abi.word in
    (* A Mem-typed var is a pointer value when it denotes an address and
       a model memory state otherwise; only the model's own memory vars
       (the mem operands) are un-renamable. *)
    let renamable (v : var) =
      not (Model.is_model_storage v)
      && not (Hike_synth.is_address_var Hike_synth.empty v)
      && not (Var.same v pc)
      && not (Var.same v window)
      && not (Model.is_arg_slot (Var.base v))
      && not (Model.is_call_arg (Var.base v))
    in
    (* The sub's CFG, straight from the BIR (every edge is an explicit
       jmp: the completion writes the guards' fallthroughs).  The
       [start]/[exit] pseudo-nodes are dropped for the block relations. *)
    let g = Sub.to_graph sub in
    let is_real tid =
      not (Tid.equal tid Graphs.Tid.start)
      && not (Tid.equal tid Graphs.Tid.exit)
    in
    let succs_of tid =
      Graphs.Tid.Node.succs tid g |> Seq.to_list |> Base.List.filter ~f:is_real
    in
    let preds_of tid =
      Graphs.Tid.Node.preds tid g |> Seq.to_list |> Base.List.filter ~f:is_real
    in
    (* The call blocks: ret-mint sites and (for SP) edge-def sites. *)
    let call_info (blk : blk term) =
      Term.enum jmp_t blk
      |> Seq.filter_map ~f:(fun j ->
             Base.Option.map (call_of_jmp j) ~f:(fun c -> (j, c)))
      |> Seq.to_list
    in
    let call_blocks =
      Term.enum blk_t sub
      |> Seq.filter_map ~f:(fun blk ->
             let cs = call_info blk in
             if Base.List.is_empty cs then None else Some (blk, cs))
      |> Seq.to_list
    in
    let machine_blk_tids =
      Term.enum blk_t sub
      |> Seq.filter ~f:(fun blk ->
             Term.enum jmp_t blk |> Seq.exists ~f:machine_call)
      |> Seq.map ~f:Term.tid
      |> Seq.to_list
      |> Core.Set.of_list (module Tid)
    in
    let has_continuation (_, c) =
      match Call.return c with Some (Direct _) -> true | _ -> false
    in
    let continuation_of (_, c) =
      match Call.return c with
      | Some (Direct t) -> Some t
      | _ -> None
    in
    (* The SP restore def lands at the call's continuation when that
       block's only predecessor is the call block. *)
    let restores =
      Base.List.fold call_blocks ~init:Tid.Map.empty ~f:(fun acc (blk, cs) ->
          Base.List.fold cs ~init:acc ~f:(fun acc site ->
              match continuation_of site with
              | Some ft when
                  Core.Set.mem machine_blk_tids (Term.tid blk)
                  && preds_of ft = [ Term.tid blk ] ->
                  let restore =
                    Def.create sp
                      (Bil.BinOp (Bil.PLUS, Bil.Var sp, restore_word ~abi)) in
                  Core.Map.add_multi acc ~key:ft ~data:restore
              | _ -> acc))
    in
    let sub =
      if Core.Map.is_empty restores then sub
      else
        Term.map blk_t sub ~f:(fun b ->
            match Core.Map.find restores (Term.tid b) with
            | Some defs -> Base.List.fold (Base.List.rev defs) ~init:b ~f:with_top_def
            | None -> b)
    in
    let blks = Term.enum blk_t sub |> Seq.to_list in
    (* The dom/phi machinery walks the BIR's own CFG ([g] above). *)
#ifdef VSA_DEBUG
    debug_graph g;
#endif
    let dom =
      Graphlib.Std.Graphlib.dominators (module Graphs.Tid) g Graphs.Tid.start
    in
    let frontier = Graphlib.Std.Graphlib.dom_frontier (module Graphs.Tid) g dom in
#ifdef VSA_DEBUG
    debug_frontiers g frontier;
#endif
    let df bs =
      Core.Set.fold bs ~init:Tid.Set.empty ~f:(fun dfs b ->
          Graphlib.Std.Frontier.enum frontier b
          |> Seq.fold ~init:dfs ~f:(fun s x -> Core.Set.add s x))
    in
    let iterated_frontier bs =
      let rec fixpoint idf =
        let idf' = df (Core.Set.union idf bs) in
        if Core.Set.equal idf idf' then idf' else fixpoint idf'
      in
      fixpoint Tid.Set.empty
    in
    let vars =
      Base.List.fold blks ~init:Var.Set.empty ~f:(fun acc blk ->
          Blk.elts blk |> Seq.fold ~init:acc ~f:(fun acc term ->
              Core.Set.union acc (Core.Set.union (Model.reads term) (Model.writes term))))
      |> Core.Set.filter ~f:renamable
    in
    (* One term scan indexes the blocks that write each variable. *)
    let def_sites : Tid.t list Var.Map.t =
      Base.List.fold blks ~init:Var.Map.empty ~f:(fun m blk ->
          let written =
            Blk.elts blk
            |> Seq.fold ~init:Var.Set.empty ~f:(fun ws elt ->
                   Core.Set.union ws (Model.writes elt))
          in
          Core.Set.fold written ~init:m ~f:(fun m v ->
              let tids = Base.Option.value (Core.Map.find m v) ~default:[] in
              Core.Map.set m ~key:v ~data:(Term.tid blk :: tids)))
    in
    let def_sites_of v =
      Base.Option.value (Core.Map.find def_sites v) ~default:[]
    in
    (* Block live-in over the terms' own reads and writes. *)
    let live_in =
      let live =
        Hike_bir_flow.liveness ~graph:g ~sub
          ~initial:(Tid.Map.singleton Graphs.Tid.exit Var.Set.empty)
          ~def:(fun d -> (Model.writes (`Def d), Model.reads (`Def d)))
          ~phi:(fun p -> (Model.writes (`Phi p), Model.reads (`Phi p)))
          ~jmp:(fun j -> (Model.writes (`Jmp j), Model.reads (`Jmp j)))
      in
      fun tid ->
        Base.Option.value (Core.Map.find live.Hike_bir_flow.before tid)
          ~default:Var.Set.empty
    in
    let sub =
      place_phis ~sp ~vars ~def_sites_of ~live_in ~call_blocks
        ~machine_blk_tids ~has_continuation ~iterated_frontier ~preds_of sub
    in
    let sub =
      rename_versions ~abi ~sp ~g ~dom ~renamable ~succs_of ~machine_blk_tids sub
    in
    Term.set_attr sub ssa_tag ()

(* Under SSA the sub's input lanes are its index-0 reads: every
   versioned read is dominated by its def.  The model's memory vars and
   storage bases are not lanes; a Mem-typed pointer value is. *)
let free_regs_ssa ~(abi : Abi.t) (sub : sub term) : var list =
  Term.enum blk_t sub
  |> Seq.fold ~init:Var.Set.empty ~f:(fun acc blk ->
      Blk.elts blk |> Seq.fold ~init:acc ~f:(fun acc term ->
          Core.Set.union acc (Model.reads term
              |> Core.Set.filter ~f:(fun v -> Var.index v = 0))))
  |> Core.Set.filter ~f:(fun v ->
         not
           (Model.is_model_storage v
          || Model.is_window_var v || Abi.is_sp abi (Var.base v)
          || Hike_synth.is_address_var Hike_synth.empty v))
  |> Core.Set.to_list

let ssa_program ~(target : Bap_core_theory.Theory.Target.t)
    (prog : program term) : program term =
  let abi = Abi.of_target target in
  let subs =
    Term.enum sub_t prog
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m s ->
          Core.Map.set m ~key:(Term.tid s) ~data:s)
  in
  Term.map sub_t prog ~f:(fun sub ->
      if is_ssa sub then sub
      else
        Model.prepare_effects ~abi ~callee:(Core.Map.find subs) sub
        |> ssa_sub ~target)
