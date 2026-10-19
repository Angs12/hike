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

(* The block's end-of-board version map lives in the stack model (the
   producer/emitter contract home). *)
let versions_tag = Model.versions_tag

(* Marks the SP restore defs the construction inserts at call
   continuations, so an update can drop and re-derive them. *)
let restore_tag : unit Value.Tag.t =
  Value.Tag.register ~package:"hike" ~name:"hike-ssa-restore"
    ~uuid:"7b3e9a14-0c52-4f6d-9d81-5a2c6e4f1b07"
    (module Core.Unit)
module Versions = Model.Versions

module High_water = struct
  open! Core
  type t = (var * int) list [@@deriving bin_io, compare, sexp]
  let pp ppf xs = Format.fprintf ppf "%d variables" (Base.List.length xs)
end

let high_water_tag : High_water.t Value.Tag.t =
  Value.Tag.register ~package:"hike" ~name:"hike-ssa-high-water"
    ~uuid:"543d89dd-dfc1-4bf7-b84f-fb93932026c3" (module High_water)

let high_water sub =
  Base.Option.value (Term.get_attr sub high_water_tag) ~default:[]

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
   definition at a machine call with a continuation.  The result maps
   each block to the base vars that need a phi there. *)
let phi_needs ~sp ~vars ~def_sites_of ~live_in ~call_blocks
    ~machine_blk_tids ~has_continuation ~iterated_frontier :
    Var.Set.t Tid.Map.t =
#ifdef VSA_DEBUG
  debug_vars vars;
#endif
  Core.Set.to_list vars
    |> Base.List.fold ~init:Tid.Map.empty ~f:(fun needs v ->
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
        |> Core.Set.fold ~init:needs ~f:(fun needs tid ->
               if Core.Set.mem (live_in tid) v then
                 Core.Map.update needs tid ~f:(function
                   | None -> Var.Set.singleton v
                   | Some vs -> Core.Set.add vs v)
               else needs))

(* The phis of [needs] in the blocks [only] accepts. *)
let place_phis ~preds_of ~only (needs : Var.Set.t Tid.Map.t) (sub : sub term) :
    sub term =
  let insert_phi ~(preds : Tid.t list) (blk : blk term) (v : var) =
    if
      Term.enum phi_t blk |> Seq.exists ~f:(fun p -> Var.same (Phi.lhs p) v)
    then blk
    else Term.append phi_t blk (Phi.of_list v (Base.List.map preds ~f:(fun p -> (p, Bil.Var v))))
  in
  Core.Map.fold needs ~init:sub ~f:(fun ~key:tid ~data:vs sub ->
      if not (only tid) then sub
      else
        match Term.find blk_t sub tid with
        | None -> sub
        | Some blk ->
            Term.update blk_t sub
              (Core.Set.fold vs ~init:blk
                 ~f:(insert_phi ~preds:(preds_of tid))))

(* How the rename walk treats a block: [Full] renames it, [Reread] keeps
   its names and resolves only the reads of its new jmps, [Fixed] leaves
   it alone.  The latter two still put their names in scope. *)
type mode = Fixed | Reread | Full

(* The rename walk, dominator-tree ordered from [start]: every def and
   phi takes a fresh version, every read the live one, and each block's
   argument and ret versions are stamped. *)
let rename_versions ?(mode = fun _ -> Full) ?(floor = Var.Map.empty) ~abi ~sp
    ~g ~dom ~renamable ~succs_of ~machine_blk_tids (sub : sub term) :
    sub term =
  let vars_tbl : var list Var.Table.t = Core.Hashtbl.create (module Var) in
  let nums : int Var.Table.t = Core.Hashtbl.create (module Var) in
  Base.List.iter (high_water sub) ~f:(fun (key, data) ->
      Core.Hashtbl.set nums ~key ~data);
  Core.Map.iteri floor ~f:(fun ~key ~data ->
      Core.Hashtbl.update nums key ~f:(fun previous ->
          max data (Base.Option.value previous ~default:0)));
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
    let push v = Core.Hashtbl.add_multi vars_tbl ~key:(Var.base v) ~data:v in
    let sub' =
      match Term.find blk_t sub' tid with
      | None -> sub'
      | Some blk when mode tid <> Full ->
          (* A kept block's names stay in scope. *)
          Term.enum phi_t blk |> Seq.iter ~f:(fun phi -> push (Phi.lhs phi));
          Term.enum def_t blk
          |> Seq.iter ~f:(fun d ->
                 if Var.index (Def.lhs d) > 0 then push (Def.lhs d));
          Base.Option.iter (Term.get_attr blk versions_tag) ~f:(fun st ->
              Base.List.iter st.Versions.rets ~f:(fun (v, version) ->
                  minted := (v, version) :: !minted;
                  push version));
          if mode tid = Fixed then sub'
          else
            Term.update blk_t sub'
              (Term.map jmp_t blk ~f:(fun j ->
                   Jmp.map_exp ~f:substitute j
                   |> Model.map_effects ~read:top ~write:Fun.id))
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
          | Some dst when mode s = Full ->
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
          | _ -> acc)
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
  let sub = Term.set_attr sub high_water_tag (Core.Hashtbl.to_alist nums) in
  !stamps
  |> Core.Map.fold ~init:sub ~f:(fun ~key ~data sub ->
           match Term.find blk_t sub key with
           | None -> sub
           | Some blk ->
               Term.update blk_t sub (Term.set_attr blk versions_tag data))

let is_real tid =
  not (Tid.equal tid Graphs.Tid.start) && not (Tid.equal tid Graphs.Tid.exit)

(* What phi placement and renaming share for one pre-SSA sub: its CFG,
   the call restores, and the blocks' phi needs. *)
type ctx = {
  abi : Abi.t;
  sp : var;
  renamable : var -> bool;
  g : Graphs.Tid.t;
  dom : Graphs.Tid.node Graphlib.Std.tree;
  succs_of : Tid.t -> Tid.t list;
  preds_of : Tid.t -> Tid.t list;
  machine_blk_tids : Tid.Set.t;
  sub : sub term;  (* the input with the SP restore defs inserted *)
  needs : Var.Set.t Tid.Map.t;
}

let analyze ~(synth : Hike_synth.table)
    ~(target : Bap_core_theory.Theory.Target.t) (sub : sub term) : ctx =
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
    (* The memory state stays one un-renamed variable: no Mem-typed var
       (the model's memory or an address value) takes versions. *)
    let renamable (v : var) =
      not (Model.is_mem v)
      && not (Model.is_model_storage synth v)
      && not (Hike_synth.is_address_var synth v)
      && not (Var.same v pc)
      && not (Var.same v window)
      && not (Model.is_arg_slot synth (Var.base v))
      && not (Model.is_call_arg synth (Var.base v))
    in
    (* The sub's CFG, straight from the BIR (every edge is an explicit
       jmp: the completion writes the guards' fallthroughs).  The
       [start]/[exit] pseudo-nodes are dropped for the block relations. *)
    let g = Sub.to_graph sub in
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
                      (Bil.BinOp (Bil.PLUS, Bil.Var sp, restore_word ~abi))
                    |> fun d -> Term.set_attr d restore_tag ()
                  in
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
    let needs =
      phi_needs ~sp ~vars ~def_sites_of ~live_in ~call_blocks
        ~machine_blk_tids ~has_continuation ~iterated_frontier
    in
    { abi; sp; renamable; g; dom; succs_of; preds_of; machine_blk_tids; sub;
      needs }

(* The construction on a sub whose jmp effects are prepared. *)
let construct ~(synth : Hike_synth.table)
    ~(target : Bap_core_theory.Theory.Target.t) (sub : sub term) : sub term =
  if Seq.is_empty (Term.enum blk_t sub) then sub
  else
    let c = analyze ~synth ~target sub in
    let sub =
      place_phis ~preds_of:c.preds_of ~only:(Fun.const true) c.needs c.sub
    in
    let sub =
      rename_versions ~abi:c.abi ~sp:c.sp ~g:c.g ~dom:c.dom
        ~renamable:c.renamable ~succs_of:c.succs_of
        ~machine_blk_tids:c.machine_blk_tids sub
    in
    sub

(* The block back in its pre-SSA form: base names, no phis, no restore
   defs, no version stamps. *)
let unssa_blk (blk : blk term) : blk term =
  let base_exp =
    (object
      inherit Exp.mapper
      method! map_sym z = Var.base z
    end)#map_exp
  in
  blk
  |> Term.filter phi_t ~f:(Fun.const false)
  |> Term.filter def_t ~f:(fun d -> not (Term.has_attr d restore_tag))
  |> Term.map def_t ~f:(fun d ->
         Def.with_lhs (Def.with_rhs d (base_exp (Def.rhs d)))
           (Var.base (Def.lhs d)))
  |> Term.map jmp_t ~f:(fun j ->
         Jmp.map_exp ~f:base_exp j
         |> Model.map_effects ~read:Var.base ~write:Var.base)
  |> fun b -> Term.del_attr b versions_tag

let unssa_sub (sub : sub term) : sub term =
  Term.map blk_t sub ~f:unssa_blk

(* Up to a consistent renaming of versions per base var: each version is
   renumbered by first occurrence, then the terms are printed without
   their own tids. *)
let canonical (sub : sub term) : string =
  let seen : var Var.Table.t = Core.Hashtbl.create (module Var) in
  let counts : int Var.Table.t = Core.Hashtbl.create (module Var) in
  let name v =
    if Var.index v = 0 then v
    else
      match Core.Hashtbl.find seen v with
      | Some w -> w
      | None ->
          let b = Var.base v in
          let n = 1 + Base.Option.value (Core.Hashtbl.find counts b) ~default:0 in
          Core.Hashtbl.set counts ~key:b ~data:n;
          let w = Var.with_index b n in
          Core.Hashtbl.set seen ~key:v ~data:w;
          w
  in
  let exp =
    (object
      inherit Exp.mapper
      method! map_sym z = name z
    end)#map_exp
  in
  let vars l =
    String.concat "," (Base.List.map l ~f:(fun v -> Var.to_string (name v)))
  in
  let label = function
    | Direct t -> Tid.name t
    | Indirect e -> Exp.to_string (exp e)
  in
  let buf = Buffer.create 4096 in
  let line fmt = Printf.bprintf buf (fmt ^^ "\n") in
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun blk ->
         line "blk %s" (Tid.name (Term.tid blk));
         Term.enum phi_t blk |> Seq.to_list
         |> Base.List.sort ~compare:(fun p q ->
                Var.compare (Var.base (Phi.lhs p)) (Var.base (Phi.lhs q)))
         |> Base.List.iter ~f:(fun p ->
                let lhs = name (Phi.lhs p) in
                let ins =
                  Phi.values p |> Seq.to_list
                  |> Base.List.sort ~compare:(fun (a, _) (b, _) ->
                         Tid.compare a b)
                  |> Base.List.map ~f:(fun (s, e) ->
                         Tid.name s ^ ":" ^ Exp.to_string (exp e))
                in
                line "phi %s = %s" (Var.to_string lhs) (String.concat ";" ins));
         Term.enum def_t blk
         |> Seq.iter ~f:(fun d ->
                let rhs = exp (Def.rhs d) in
                line "def %s = %s" (Var.to_string (name (Def.lhs d)))
                  (Exp.to_string rhs));
         Term.enum jmp_t blk
         |> Seq.iter ~f:(fun j ->
                let cond = exp (Jmp.cond j) in
                let kind =
                  match Jmp.kind j with
                  | Goto l -> "goto " ^ label l
                  | Ret l -> "ret " ^ label l
                  | Int (n, t) -> Printf.sprintf "int %d %s" n (Tid.name t)
                  | Call c ->
                      Printf.sprintf "call %s -> %s" (label (Call.target c))
                        (Base.Option.value_map (Call.return c) ~default:"-"
                           ~f:label)
                in
                let eff = Model.effects j in
                line "jmp when %s %s r[%s] w[%s]" (Exp.to_string cond) kind
                  (vars eff.Model.Term_effects.reads)
                  (vars eff.Model.Term_effects.writes));
         match Term.get_attr blk versions_tag with
         | None -> ()
         | Some st ->
             let pairs l =
               String.concat ","
                 (Base.List.sort l ~compare:(fun (a, _) (b, _) -> Var.compare a b)
                 |> Base.List.map ~f:(fun (a, b) ->
                      Var.to_string (name a) ^ "=" ^ Var.to_string (name b)))
             in
             line "stamp a[%s] r[%s]" (pairs st.Versions.args)
               (pairs st.Versions.rets));
  Buffer.contents buf

let equivalent (a : sub term) (b : sub term) : bool =
  String.equal (canonical a) (canonical b)

(* The affected region is every block that is new, has changed defs or
   predecessors, needs a different phi set, or is reachable from one:
   the other blocks keep their reaching definitions, so they keep their
   variables.  A block that only gained or lost pure jmps keeps them too,
   resolving the new jmps' reads in place. *)
let update_sub_woken ~(synth : Hike_synth.table)
    ~(target : Bap_core_theory.Theory.Target.t) ~(old : sub term)
    (sub : sub term) : sub term * Tid.Set.t =
  if Seq.is_empty (Term.enum blk_t sub) then (sub, Tid.Set.empty)
  else
    let c = analyze ~synth ~target (unssa_sub sub) in
    let old_g = Sub.to_graph old in
    let old_preds tid =
      Graphs.Tid.Node.preds tid old_g |> Seq.to_list
      |> Base.List.filter ~f:is_real |> Tid.Set.of_list
    in
    let tids f b = Seq.to_list (Seq.map (f b) ~f:Term.tid) in
    let phi_bases b =
      Term.enum phi_t b |> Seq.to_list
      |> Base.List.map ~f:(fun p -> Var.base (Phi.lhs p))
      |> Var.Set.of_list
    in
    (* A block whose only change is new pure jmps keeps its names; the
       jmps' reads are resolved in place. *)
    let kind b =
      let tid = Term.tid b in
      let needed =
        Base.Option.value (Core.Map.find c.needs tid) ~default:Var.Set.empty
      in
      match Term.find blk_t old tid with
      | None -> Full
      | Some ob ->
          let changed_jmps = tids (Term.enum jmp_t) ob <> tids (Term.enum jmp_t) b in
          let pure j =
            Core.Set.is_empty (Model.writes (`Jmp j))
            && Base.Option.is_none (call_of_jmp j)
          in
          let differing x y =
            Term.enum jmp_t x
            |> Seq.filter ~f:(fun j -> Base.Option.is_none (Term.find jmp_t y (Term.tid j)))
          in
          if
            not (Core.Set.equal (old_preds tid) (Tid.Set.of_list (c.preds_of tid)))
            || not (Base.List.equal (fun a b -> Tid.equal (Term.tid a) (Term.tid b)
                            && Var.equal (Def.lhs a) (Def.lhs b)
                            && Exp.equal (Def.rhs a) (Def.rhs b))
                      (Term.enum def_t ob |> Seq.to_list)
                      (Term.enum def_t b |> Seq.to_list))
            || Seq.exists (Term.enum jmp_t b) ~f:(fun j ->
                 match Term.find jmp_t ob (Term.tid j) with
                 | None -> false
                 | Some oj ->
                   not (Core.Set.equal (Model.reads (`Jmp oj)) (Model.reads (`Jmp j)))
                   || not (Core.Set.equal (Model.writes (`Jmp oj)) (Model.writes (`Jmp j)))
                   || not (Exp.equal (Jmp.cond oj) (Jmp.cond j))
                   || Jmp.kind oj <> Jmp.kind j)
            || not (Core.Set.equal needed (phi_bases b))
          then Full
          else if changed_jmps then
            if Seq.for_all (differing b ob) ~f:pure
               && Seq.for_all (differing ob b) ~f:pure
            then Reread
            else Full
          else Fixed
    in
    let kinds =
      Term.enum blk_t sub |> Seq.to_list
      |> Base.List.fold ~init:Tid.Map.empty ~f:(fun m b ->
             Core.Map.set m ~key:(Term.tid b) ~data:(kind b))
    in
    let roots =
      Core.Map.fold kinds ~init:[] ~f:(fun ~key ~data acc ->
          if data = Full then key :: acc else acc)
    in
    let rec close seen = function
      | [] -> seen
      | t :: rest ->
          if Core.Set.mem seen t then close seen rest
          else close (Core.Set.add seen t) (c.succs_of t @ rest)
    in
    let affected = close Tid.Set.empty roots in
    let is_affected tid = Core.Set.mem affected tid in
    let mode tid =
      if is_affected tid then Full
      else Base.Option.value (Core.Map.find kinds tid) ~default:Fixed
    in
    (* Fresh versions continue above every index ever used. *)
    let floor =
      let note acc v =
        if Var.index v = 0 then acc
        else
          Core.Map.update acc (Var.base v) ~f:(function
            | Some k when k >= Var.index v -> k
            | _ -> Var.index v)
      in
      let scan acc s =
        Term.enum blk_t s
        |> Seq.fold ~init:acc ~f:(fun acc blk ->
               let acc =
                 Blk.elts blk
                 |> Seq.fold ~init:acc ~f:(fun acc t ->
                        Core.Set.fold (Model.writes t)
                          ~init:
                            (Core.Set.fold (Model.reads t) ~init:acc ~f:note)
                          ~f:note)
               in
               match Term.get_attr blk versions_tag with
               | None -> acc
               | Some st ->
                   Base.List.fold (st.Versions.args @ st.Versions.rets)
                     ~init:acc ~f:(fun acc (a, b) -> note (note acc a) b))
      in
      let history = Core.Map.of_alist_exn (module Var) (high_water old) in
      let current = scan (scan Var.Map.empty old) sub in
      Core.Map.merge history current ~f:(fun ~key:_ -> function
          | `Left k | `Right k -> Some k
          | `Both (a, b) -> Some (max a b))
    in
    let base =
      Term.map blk_t sub ~f:(fun b ->
          if is_affected (Term.tid b) then
            Base.Option.value (Term.find blk_t c.sub (Term.tid b)) ~default:b
          else b)
    in
    let base =
      place_phis ~preds_of:c.preds_of ~only:is_affected c.needs base
    in
    let result =
      rename_versions ~mode ~floor ~abi:c.abi
        ~sp:c.sp ~g:c.g ~dom:c.dom ~renamable:c.renamable
        ~succs_of:c.succs_of ~machine_blk_tids:c.machine_blk_tids base
    in
#ifdef VSA_DEBUG
    let fresh = construct ~synth ~target (unssa_sub sub) in
    if not (equivalent result fresh) then
      failwith "Hike_ssa.update_sub: differs from fresh construction";
#endif
    let woken = Core.Map.fold kinds ~init:affected ~f:(fun ~key ~data acc ->
        if data = Reread then Core.Set.add acc key else acc) in
    (result, woken)

let update_sub ~synth ~target ~old sub =
  fst (update_sub_woken ~synth ~target ~old sub)

(* Under SSA the sub's input lanes are its index-0 reads: every
   versioned read is dominated by its def.  The model's memory vars and
   storage bases are not lanes; a Mem-typed pointer value is. *)
let free_regs_ssa ~(synth : Hike_synth.table) ~(abi : Abi.t) (sub : sub term) :
    var list =
  Term.enum blk_t sub
  |> Seq.fold ~init:Var.Set.empty ~f:(fun acc blk ->
      Blk.elts blk |> Seq.fold ~init:acc ~f:(fun acc term ->
          Core.Set.union acc (Model.reads term
              |> Core.Set.filter ~f:(fun v -> Var.index v = 0))))
  |> Core.Set.filter ~f:(fun v ->
         not
           (Model.is_model_storage synth v
          || Model.is_window_var synth v || Abi.is_sp abi (Var.base v)
          || Hike_synth.is_address_var synth v))
  |> Core.Set.to_list

(* The highest version index each base variable reaches in the sub. *)
let version_ceiling (sub : sub term) : int Var.Map.t =
  let note acc v =
    Core.Map.update acc (Var.base v) ~f:(function
      | Some k when k >= Var.index v -> k
      | _ -> Var.index v)
  in
  Term.enum blk_t sub
  |> Seq.fold ~init:(Core.Map.of_alist_exn (module Var) (high_water sub)) ~f:(fun acc blk ->
      let acc =
        Blk.elts blk
        |> Seq.fold ~init:acc ~f:(fun acc t ->
            Core.Set.fold (Model.writes t) ~f:note
              ~init:(Core.Set.fold (Model.reads t) ~f:note ~init:acc))
      in
      match Term.get_attr blk versions_tag with
      | None -> acc
      | Some vs ->
          Base.List.fold (vs.Versions.args @ vs.Versions.rets)
            ~init:acc ~f:(fun acc (a, b) -> note (note acc a) b))

(* Derived views may mint versions too; the canonical body reserves them
   even though its claims and matching warm solution stay unchanged. *)
let retain_history ~from sub =
  let versions = Core.Map.merge (version_ceiling from) (version_ceiling sub)
      ~f:(fun ~key:_ -> function
          | `Left n | `Right n -> Some n
          | `Both (a, b) -> Some (max a b)) in
  Term.set_attr sub high_water_tag (Core.Map.to_alist versions)

let is_call_jmp (j : jmp term) : bool =
  match Jmp.kind j with
  | Call _ -> not (Hike_return.is_jmp j)
  | _ -> false

(* The lanes of the call jmps [select] accepts are re-derived under
   [callee].  Each lane keeps the version the call had; a lane the call
   gains reads the block's live version, or the base, and mints a fresh
   version above the sub's highest; a lane it loses leaves the block's
   result stamp. *)
let refresh_calls ~(synth : Hike_synth.table) ~(abi : Abi.t)
    ~(callee : Tid.t -> sub term option) ~(select : jmp term -> bool)
    (sub : sub term) : sub term =
  if
    not
      (Term.enum blk_t sub
       |> Seq.exists ~f:(fun blk -> Term.enum jmp_t blk |> Seq.exists ~f:select))
  then sub
  else
    let derived = Model.prepare_effects ~synth ~abi ~callee sub in
    let ceiling = ref (version_ceiling sub) in
    let fresh w =
      let b = Var.base w in
      let k = 1 + Core.Option.value (Core.Map.find !ceiling b) ~default:0 in
      ceiling := Core.Map.set !ceiling ~key:b ~data:k;
      Var.with_index b k
    in
    let assoc_base lanes v =
      Base.List.find lanes ~f:(fun l -> Var.same (Var.base l) (Var.base v))
    in
    Term.map blk_t sub ~f:(fun blk ->
        if not (Term.enum jmp_t blk |> Seq.exists ~f:select) then blk
        else
        let vs =
          Base.Option.value_exn (Term.get_attr blk versions_tag)
            ~message:
              ("Hike_ssa.refresh_calls: block " ^ Tid.name (Term.tid blk)
               ^ " has no version stamp")
        in
        let minted = ref [] in
        let prepared = Term.find_exn blk_t derived (Term.tid blk) in
        let blk =
          Term.map jmp_t blk ~f:(fun j ->
              if not (select j) then j
              else
                let old = Model.effects j in
                let read r =
                  match assoc_base old.Model.Term_effects.reads r with
                  | Some v -> v
                  | None ->
                      Base.List.Assoc.find vs.Versions.args r ~equal:Var.same
                      |> Core.Option.value ~default:r
                in
                let write w =
                  let v =
                    match assoc_base old.Model.Term_effects.writes w with
                    | Some v -> v
                    | None -> fresh w
                  in
                  minted := (w, v) :: !minted;
                  v
                in
                Term.find_exn jmp_t prepared (Term.tid j)
                |> Model.map_effects ~read ~write)
        in
        let written =
          Term.enum jmp_t blk
          |> Seq.fold ~init:Var.Set.empty ~f:(fun acc j ->
              Core.Set.union acc (Model.writes (`Jmp j)))
        in
        let kept =
          Base.List.filter vs.Versions.rets ~f:(fun (_, v) ->
              Core.Set.mem written v)
        in
        let added =
          Base.List.filter !minted ~f:(fun (w, _) ->
              not (Base.List.Assoc.mem kept w ~equal:Var.same))
        in
        Term.set_attr blk versions_tag { vs with Versions.rets = kept @ added })

(* Read-only lane narrowing leaves register definitions and their VSA facts
   intact. A gained live merge or changed result needs a real SSA update. *)
let relane_sub ~synth ~target ~callee sub =
  if Seq.is_empty (Term.enum blk_t sub) then sub else
  let abi = Abi.of_target target in
  let refreshed = refresh_calls ~synth ~abi ~callee ~select:is_call_jmp sub in
  let changed_writes = Term.enum blk_t refreshed |> Seq.exists ~f:(fun b ->
      Term.enum jmp_t b |> Seq.exists ~f:(fun j ->
          let before = Term.find_exn blk_t sub (Term.tid b)
            |> fun b -> Term.find_exn jmp_t b (Term.tid j) in
          not (Core.Set.equal (Model.writes (`Jmp before)) (Model.writes (`Jmp j))))) in
  let c = analyze ~synth ~target (unssa_sub refreshed) in
  let needed b = Base.Option.value (Core.Map.find c.needs (Term.tid b))
      ~default:Var.Set.empty in
  let missing = Term.enum blk_t refreshed |> Seq.exists ~f:(fun b ->
      let existing = Term.enum phi_t b |> Seq.map ~f:(fun p -> Var.base (Phi.lhs p))
        |> Seq.to_list |> Var.Set.of_list in
      not (Core.Set.is_subset (needed b) ~of_:existing)) in
  if changed_writes || missing then update_sub ~synth ~target ~old:sub refreshed
  else
    let dead = ref Var.Set.empty in
    let result = Term.map blk_t refreshed ~f:(fun b ->
        Term.filter phi_t b ~f:(fun p ->
            let keep = Core.Set.mem (needed b) (Var.base (Phi.lhs p)) in
            if not keep then dead := Core.Set.add !dead (Phi.lhs p);
            keep)) in
    Term.map blk_t result ~f:(fun b ->
        match Term.get_attr b versions_tag with
        | None -> b
        | Some vs ->
          let live (_, v) = not (Core.Set.mem !dead v) in
          Term.set_attr b versions_tag
            { Versions.args = Base.List.filter vs.Versions.args ~f:live;
              rets = Base.List.filter vs.Versions.rets ~f:live })

(* The SSA of a lifted sub: its calls read and write the machine
   convention and its returns the ABI's return lanes. *)
let prepare_sub ~(synth : Hike_synth.table)
    ~(target : Bap_core_theory.Theory.Target.t) (sub : sub term) : sub term =
  let abi = Abi.of_target target in
  let lanes = Term.enum arg_t sub |> Seq.to_list in
  (if Model.is_emittable_intrinsic sub then sub
   else Model.set_sig sub (Model.return_lanes ~target sub @ Model.sig_args sub))
  |> Model.prepare_effects ~synth ~abi ~callee:(fun _ -> None)
  |> (fun sub -> Model.set_sig sub lanes)

let ssa_sub ~synth ~target sub =
  prepare_sub ~synth ~target sub |> construct ~synth ~target

let ssa_program ~(synth : Hike_synth.table)
    ~(target : Bap_core_theory.Theory.Target.t)
    (prog : program term) : program term =
  Term.map sub_t prog ~f:(ssa_sub ~synth ~target)
