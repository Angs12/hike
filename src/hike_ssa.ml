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
          if Bil2llvm_env.is_interrupt_name (Tid.name target) then None
          else if
            Bil2llvm_fp.native_fp_op (Tid.name target) = Some Bil2llvm_fp.FHLT
          then None
          else Some c
      | Indirect _ -> Some c)
  | _ -> None

(* The machine calls: a mapped intrinsic is a soft-float helper, not a
   call — no return address is pushed, so no SP restore rides it. *)
let machine_call (j : jmp term) : bool =
  match Jmp.kind j with
  | Call c -> (
      match Call.target c with
      | Direct target ->
          Base.Option.is_none (Bil2llvm_fp.native_fp_op (Tid.name target))
      | Indirect _ -> true)
  | _ -> false

(* The call's ret lanes: a mapped intrinsic versions its own ret temps;
   an in-program sub its own Out intents; every other target (externs,
   excluded intrinsic placeholders, the synthetic conventions) the ABI
   return registers. *)
let ret_lanes_of ~(subs : sub term Tid.Map.t) ~(abi : Abi.t) (target : Tid.t) :
    var list =
  match Bil2llvm_fp.native_fp_op (Tid.name target) with
  | Some op ->
      let w =
        Base.Option.value
          (Bil2llvm_fp.fp_width_of_name (Tid.name target))
          ~default:(8 * abi.Abi.word)
      in
      Bil2llvm_fp.(fp_sig_of op ~w).fp_rets
  | None -> (
      match Core.Map.find subs target with
      | Some sub -> Base.List.map (Model.sig_rets sub) ~f:Arg.lhs
      | None -> abi.Abi.return_regs)

let restore_word ~(abi : Abi.t) : exp =
  Bil.Int
    (Cbat_word.to_word (Cbat_word.of_int ~width:(8 * abi.Abi.word) abi.Abi.word))

(* The SP restore def at a call's single-pred continuation. *)
let with_top_def (blk : blk term) (d : def term) : blk term =
  let b = Blk.Builder.init ~copy_phis:true ~copy_jmps:true blk in
  Blk.Builder.add_def b d;
  Term.enum def_t blk |> Seq.iter ~f:(fun d0 -> Blk.Builder.add_def b d0);
  Blk.Builder.result b

(* One phi rewrite: the incoming from [src] becomes [exp]. *)
let set_incoming (phi : phi term) ~(src : Tid.t) (exp : exp) : phi term =
  Phi.of_list (Phi.lhs phi)
    (Phi.values phi
    |> Seq.map ~f:(fun (s, e) -> if Tid.equal s src then (s, exp) else (s, e))
    |> Seq.to_list)

let ssa_sub ~(target : Bap_core_theory.Theory.Target.t)
    ~(subs : sub term Tid.Map.t) (sub : sub term) : sub term =
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
      not (Model.is_region_mem v)
      && not (Model.is_window_mem v)
      && not (Model.is_sec_comp_mem v)
      && not (Model.is_storage_base v)
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
    let call_blk_tids =
      Base.List.map call_blocks ~f:(fun (blk, _) -> Term.tid blk)
      |> Core.Set.of_list (module Tid)
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
    let sub =
      Base.List.fold call_blocks ~init:sub ~f:(fun acc (blk, cs) ->
          Base.List.fold cs ~init:acc ~f:(fun acc site ->
              match continuation_of site with
              | Some ft when
                  Core.Set.mem machine_blk_tids (Term.tid blk)
                  && preds_of ft = [ Term.tid blk ] ->
                  Term.map blk_t acc ~f:(fun b ->
                      if Tid.equal (Term.tid b) ft then
                        with_top_def b
                          (Def.create sp
                             (Bil.BinOp (Bil.PLUS, Bil.Var sp, restore_word ~abi)))
                      else b)
              | _ -> acc))
    in
    let blks = Term.enum blk_t sub |> Seq.to_list in
    (* The mint plan per call block: the ret lanes it versions. *)
    let mint_of (cs : (jmp term * Call.t) list) =
      Base.List.concat_map cs ~f:(fun (_, c) ->
          match Call.target c with
          | Direct t -> ret_lanes_of ~subs ~abi t
          | Indirect _ -> abi.Abi.return_regs)
      |> Base.List.dedup_and_sort ~compare:Var.compare
    in
    (* The dom/phi machinery walks the BIR's own CFG ([g] above). *)
#ifdef VSA_DEBUG
    let () =
      Graphs.Tid.nodes g
      |> Seq.iter ~f:(fun n ->
             Format.eprintf "SSA-DBG %s -> [%s]@." (Tid.name n)
               (String.concat ","
                  (Graphs.Tid.Node.succs n g |> Seq.to_list
                  |> Base.List.map ~f:Tid.name)))
    in
#endif
    let dom =
      Graphlib.Std.Graphlib.dominators (module Graphs.Tid) g Graphs.Tid.start
    in
    let frontier = Graphlib.Std.Graphlib.dom_frontier (module Graphs.Tid) g dom in
#ifdef VSA_DEBUG
    let () =
      Format.eprintf "SSA-DBG dom-tree: %d nodes; frontiers: %s@."
        (Base.List.length (Graphs.Tid.nodes g |> Seq.to_list))
        (String.concat ","
           (Graphs.Tid.nodes g
            |> Seq.to_list
            |> Base.List.filter_map ~f:(fun n ->
                   let fr =
                     Graphlib.Std.Frontier.enum frontier n |> Seq.to_list
                   in
                   if Base.List.is_empty fr then None
                   else
                     Some
                       (Tid.name n ^ "=>"
                        ^ String.concat ","
                            (Base.List.map fr ~f:Tid.name)))))
    in
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
    (* The emitter reads call lanes at their sites (arguments) and at
       returns (results) with no BIR use — they join [vars] so the
       joins where their defs meet still materialize a phi. *)
    let call_lanes =
      Base.List.concat_map call_blocks ~f:(fun (_, cs) ->
          Base.List.concat_map cs ~f:(fun (_, c) ->
              match Call.target c with
              | Direct t ->
                  ret_lanes_of ~subs ~abi t
                  @ (match Core.Map.find subs t with
                    | Some sub ->
                        Base.List.filter_map (Model.sig_args sub) ~f:(fun a ->
                            match Arg.intent a with
                            | Some Out -> None
                            | _ -> Some (Arg.lhs a))
                    | None -> abi.Abi.int_param_regs)
              | Indirect _ ->
                  abi.Abi.return_regs @ abi.Abi.int_param_regs))
      |> Core.Set.of_list (module Var)
    in
    let vars =
      Base.List.fold blks ~init:call_lanes ~f:(fun acc blk ->
          Core.Set.union acc (Blk.free_vars blk))
      |> Core.Set.filter ~f:renamable
    in
    let defines (v : var) (blk : blk term) =
      Blk.elts blk
      |> Seq.exists ~f:(fun elt ->
             match elt with
             | `Def d -> Var.same (Def.lhs d) v
             | `Phi p -> Var.same (Phi.lhs p) v
             | _ -> false)
    in
    let insert_phi ~(preds : Tid.t list) (blk : blk term) (v : var) =
      if
        Term.enum phi_t blk |> Seq.exists ~f:(fun p -> Var.same (Phi.lhs p) v)
      then blk
      else Term.append phi_t blk (Phi.of_list v (Base.List.map preds ~f:(fun p -> (p, Bil.Var v))))
    in
#ifdef VSA_DEBUG
    let () =
      Format.eprintf "SSA-DBG vars(%d): [%s]@." (Core.Set.length vars)
        (String.concat ","
           (Core.Set.to_list vars |> Base.List.map ~f:Var.name))
    in
#endif
    let sub =
      Core.Set.to_list vars
      |> Base.List.fold ~init:sub ~f:(fun sub v ->
#ifdef VSA_DEBUG
          let dbg_sites =
            Base.List.filter_map blks ~f:(fun blk ->
                if defines v blk then Some (Tid.name (Term.tid blk)) else None)
          in
          let dbg_bs =
            Graphs.Tid.start :: Base.List.filter_map blks ~f:(fun blk ->
                if defines v blk then Some (Term.tid blk) else None)
            |> Core.Set.of_list (module Tid)
          in
          Format.eprintf "SSA-DBG var %s sites=[%s] idf=[%s]@." (Var.name v)
            (String.concat "," dbg_sites)
            (String.concat ","
               (Core.Set.to_list (iterated_frontier dbg_bs)
                |> Base.List.map ~f:Tid.name));
#endif

          let sites =
            Base.List.filter_map blks ~f:(fun blk ->
                if defines v blk then Some (Term.tid blk) else None)
          in
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
          |> Base.List.fold ~init:sub ~f:(fun sub tid ->
                 match Term.find blk_t sub tid with
                 | None -> sub
                 | Some blk ->
                     Term.update blk_t sub
                       (insert_phi ~preds:(preds_of tid) blk v)))
    in
    (* The rename walk, dominator-tree ordered from [start]. *)
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
    let children tid =
      Graphs.Tid.nodes g |> Seq.filter ~f:(Graphlib.Std.Tree.is_child_of ~parent:tid dom)
    in
    let rec walk sub' tid =
      let minted = ref [] in
      let entry_vers = ref [] in
      let sub' =
        match Term.find blk_t sub' tid with
        | None -> sub'
        | Some blk ->
            (* The entry map reads BEFORE this block's own defs. *)
            entry_vers := live_vers ();
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
            let blk = Term.map jmp_t blk ~f:(Jmp.map_exp ~f:substitute) in
            (* The argument map reads BEFORE the call's ret mints: an
               argument lane passes the machine's current value, not
               the callee's future result. *)
            let arg_vers = live_vers () in
            if Core.Set.mem call_blk_tids tid then
              Base.List.iter (mint_of (call_info blk)) ~f:(fun v ->
                  minted := (v, new_name v) :: !minted);
            stamps :=
              Core.Map.set !stamps ~key:tid
                ~data:
                  { Versions.args = arg_vers;
                    rets = !minted;
                    entry = !entry_vers };
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
      let sub' = children tid |> Seq.fold ~init:sub' ~f:walk in
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
           Base.List.iter !minted ~f:(fun (v, _) -> pop (Var.base v) |> ignore)
       | None -> ());
      sub'
    in
    let sub = walk sub Graphs.Tid.start in
    let sub =
      !stamps
      |> Core.Map.fold ~init:sub ~f:(fun ~key ~data sub ->
             match Term.find blk_t sub key with
             | None -> sub
             | Some blk ->
                 Term.update blk_t sub (Term.set_attr blk versions_tag data))
    in
    Term.set_attr sub ssa_tag ()

(* Under SSA the sub's input lanes are its index-0 reads: every
   versioned read is dominated by its def.  The model's memory vars and
   storage bases are not lanes; a Mem-typed pointer value is. *)
let free_regs_ssa (sub : sub term) : var list =
  Term.enum blk_t sub
  |> Seq.fold ~init:Var.Set.empty ~f:(fun acc blk ->
        Core.Set.union acc
          (Blk.free_vars blk
           |> Core.Set.filter ~f:(fun v -> Var.index v = 0)))
  |> Core.Set.filter ~f:(fun v ->
         not
           (Model.is_region_mem v || Model.is_window_mem v
          || Model.is_sec_comp_mem v || Model.is_storage_base v
          || Model.is_window_var v))
  |> Core.Set.to_list

let ssa_program ~(target : Bap_core_theory.Theory.Target.t)
    (prog : program term) : program term =
  let subs =
    Term.enum sub_t prog
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m s ->
          Core.Map.set m ~key:(Term.tid s) ~data:s)
  in
  Term.map sub_t prog ~f:(ssa_sub ~target ~subs)
