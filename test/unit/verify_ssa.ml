(* The SSA property verifier: a test/vsa-debug oracle, never a
   production check.  It answers the six properties the edit seam must
   maintain:

   1. every versioned use has one definition that dominates it;
   2. no version has two definitions;
   3. every renamable call-jmp write is versioned;
   4. no renamable definition is version 0;
   5. every phi incoming is a real predecessor or the synthetic entry;
   6. the retained high-water covers every version in the sub. *)

open Bap.Std
module Model = Hike_stack_model
module Abi = Hike_abi

let fail what fmt =
  Printf.ksprintf (fun msg -> failwith (what ^ ": " ^ msg)) fmt

let renamable ~synth ~target ~abi v =
  not (Model.is_mem v)
  && not (Model.is_model_storage synth v)
  && not (Hike_synth.is_address_var synth v)
  && not (Var.same v (Abi.pc target))
  && not (Var.same v (Model.hike_window_var ~word:abi.Abi.word))
  && not (Model.is_arg_slot synth (Var.base v))
  && not (Model.is_call_arg synth (Var.base v))

let dominators sub =
  let graph = Sub.to_graph sub in
  let tids =
    Term.enum blk_t sub |> Seq.map ~f:Term.tid |> Seq.to_list
  in
  let all = Tid.Set.of_list tids in
  let in_sub t = Base.List.exists tids ~f:(Tid.equal t) in
  let preds t =
    Graphs.Tid.Node.preds t graph |> Seq.to_list
    |> Base.List.filter ~f:in_sub
  in
  match tids with
  | [] -> Tid.Map.empty
  | entry :: _ ->
    let dom =
      ref
        (Tid.Map.of_alist_exn
           (Base.List.map tids ~f:(fun t ->
                (t, if Tid.equal t entry then Tid.Set.singleton t else all))))
    in
    let changed = ref true in
    while !changed do
      changed := false;
      Base.List.iter tids ~f:(fun t ->
          let ps = preds t in
          let meet =
            match ps with
            | [] -> Tid.Set.singleton t
            | p :: rest ->
              Base.List.fold rest ~init:(Core.Map.find_exn !dom p)
                ~f:(fun acc q ->
                  Core.Set.inter acc (Core.Map.find_exn !dom q))
          in
          let next = Core.Set.add meet t in
          if not (Core.Set.equal next (Core.Map.find_exn !dom t)) then begin
            dom := Core.Map.set !dom ~key:t ~data:next;
            changed := true
          end);
    done;
    !dom

(* Check an SSA sub. [what] names the producer/stage in the failure. *)
let sub ~synth ~target ~what (s : sub term) : unit =
  let abi = Abi.of_target target in
  let renamable = renamable ~synth ~target ~abi in
  let defs : Tid.Set.t Var.Table.t = Core.Hashtbl.create (module Var) in
  let uses : Tid.Set.t Var.Table.t = Core.Hashtbl.create (module Var) in
  let add tbl v tid =
    Core.Hashtbl.update tbl v ~f:(function
      | None -> Tid.Set.singleton tid
      | Some s -> Core.Set.add s tid)
  in
  let def v tid = if Var.index v > 0 then add defs v tid in
  let use v tid = if Var.index v > 0 then add uses v tid in
  let exp_uses e tid = Core.Set.iter (Exp.free_vars e) ~f:(fun v -> use v tid) in
  let blocks = Term.enum blk_t s |> Seq.to_list in
  let block_tids = Tid.Set.of_list (Base.List.map blocks ~f:Term.tid) in
  (* Definitions and version-0 definition violations. *)
  Base.List.iter blocks ~f:(fun b ->
      let tid = Term.tid b in
      Term.enum def_t b |> Seq.iter ~f:(fun d ->
          let v = Def.lhs d in
          if Var.index v = 0 && renamable v then
            fail what "block %s defines a renamable name %s at version 0"
              (Tid.name tid) (Var.to_string v);
          def v tid;
          exp_uses (Def.rhs d) tid);
      Term.enum phi_t b |> Seq.iter ~f:(fun p ->
          let v = Phi.lhs p in
          if Var.index v = 0 && renamable v then
            fail what "block %s has a renamable phi %s at version 0"
              (Tid.name tid) (Var.to_string v);
          def v tid);
      Term.enum jmp_t b |> Seq.iter ~f:(fun j ->
          exp_uses (Jmp.cond j) tid;
          let e = Model.effects j in
          Base.List.iter e.Model.Term_effects.reads ~f:(fun v -> use v tid);
          Base.List.iter e.Model.Term_effects.writes ~f:(fun v ->
              if renamable v && Var.index v = 0 then
                fail what
                  "block %s jmp %s writes renamable name %s at version 0"
                  (Tid.name tid) (Tid.name (Term.tid j)) (Var.to_string v);
              (* A base lane's write is a version-0 definition too. *)
              if Var.index v > 0 then add defs v tid)));
  (* Phi incoming values are used at their source block. *)
  Base.List.iter blocks ~f:(fun b ->
      Term.enum phi_t b |> Seq.iter ~f:(fun p ->
          Phi.values p
          |> Seq.iter ~f:(fun (src, e) ->
                 if Core.Set.mem block_tids src then exp_uses e src)));
  (* Predecessor set for the phi-edge property. *)
  let preds tid =
    let graph = Sub.to_graph s in
    Graphs.Tid.Node.preds tid graph |> Seq.to_list
    |> Base.List.filter ~f:(fun t -> Core.Set.mem block_tids t)
    |> Tid.Set.of_list
  in
  Base.List.iter blocks ~f:(fun b ->
      let ps = preds (Term.tid b) in
      Term.enum phi_t b |> Seq.iter ~f:(fun p ->
          Phi.values p
          |> Seq.iter ~f:(fun (src, _) ->
                 if not (Core.Set.mem ps src) then
                   fail what
                     "block %s phi %s has an incoming from %s, not a \
                      predecessor"
                     (Tid.name (Term.tid b)) (Var.to_string (Phi.lhs p))
                     (Tid.name src))));
  (* Dominance, single definition. *)
  let dom = dominators s in
  Core.Hashtbl.iteri uses ~f:(fun ~key:v ~data:tids ->
      let ds =
        Base.Option.value (Core.Hashtbl.find defs v) ~default:Tid.Set.empty
      in
      if Core.Set.is_empty ds then
        fail what "versioned name %s has no definition" (Var.to_string v);
      if Core.Set.length ds > 1 then
        fail what "versioned name %s has %d definitions [%s]"
          (Var.to_string v) (Core.Set.length ds)
          (String.concat "," (Core.Set.to_list ds |> Base.List.map ~f:Tid.name));
      Core.Set.iter tids ~f:(fun b ->
          let dominated =
            Core.Set.exists ds ~f:(fun d ->
                match Core.Map.find dom b with
                | Some doms -> Core.Set.mem doms d
                | None -> false)
          in
          if not dominated then
            fail what "definition of %s does not dominate block %s"
              (Var.to_string v) (Tid.name b)));
  (* High-water. *)
  let high =
    Base.List.fold (Hike.Ssa.high_water s)
      ~init:(Var.Map.empty)
      ~f:(fun m (k, n) -> Core.Map.set m ~key:(Var.base k) ~data:n)
  in
  Core.Hashtbl.iteri defs ~f:(fun ~key:v ~data:_ ->
      let hi =
        Base.Option.value (Core.Map.find high (Var.base v)) ~default:0
      in
      if Var.index v > hi then
        fail what "version %s exceeds the retained high-water %d"
          (Var.to_string v) hi)
