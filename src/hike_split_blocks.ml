(* The block/jmp split: a 3+-jmp direct-goto series becomes one block per
   jmp — piece 1 keeps the tid, defs, phis, and attrs; every piece carries
   an explicit Goto to the next.  The guards' false edges are already
   explicit by then (the completion writes them), so the BIR's edges are
   the jmps themselves: every later pass (the emitter included) reads the
   BIR, never a term order.  A series that is not all direct gotos stays
   whole, named on the channel. *)

open Bap.Std
module Model = Hike_stack_model

(* A compilable series: every jmp a direct Goto to a non-interrupt. *)
let compilable_series (jmps : jmp term list) : bool =
  Base.List.for_all jmps ~f:(fun j ->
      match Jmp.kind j with
      | Goto (Direct tid) ->
          not (Bil2llvm_env.is_interrupt_name (Tid.name tid))
      | _ -> false)

(* One block per jmp: piece 1 is the original block minus the later
   jmps; each later jmp becomes a fresh block of its own.  Every piece
   but the last carries an explicit [Goto] to the next piece, so a
   guard's false edge is a jmp target — the BIR carries its own edges
   and no pass reads the term order. *)
let pieces (blk : blk term) : blk term list =
  match Term.enum jmp_t blk |> Seq.to_list with
  | [] | [ _ ] -> [ blk ]
  | jmps ->
      let tids =
        match jmps with
        | _ :: rest ->
            Term.tid blk :: Base.List.map rest ~f:(fun _ -> Tid.create ())
        | [] -> []
      in
      let n = Base.List.length jmps in
      Base.List.mapi jmps ~f:(fun i j ->
          let blk_i =
            if Int.equal i 0 then
              Term.filter jmp_t blk ~f:(fun x ->
                  Tid.equal (Term.tid x) (Term.tid j))
            else Blk.create ~tid:(Base.List.nth_exn tids i) ~jmps:[ j ] ()
          in
          if i + 1 < n then
            Term.append jmp_t blk_i
              (Jmp.create (Goto (Direct (Base.List.nth_exn tids (i + 1)))))
          else blk_i)

let split_sub (sub : sub term) : sub term =
  (* A 3+-jmp block becomes one piece per jmp, each carrying an explicit
     Goto to the next. *)
  let multi =
    Term.enum blk_t sub
    |> Seq.filter ~f:(fun blk ->
           Base.List.length (Term.enum jmp_t blk |> Seq.to_list) > 2)
    |> Seq.to_list
  in
  if Base.List.is_empty multi then sub
  else begin
    let splittable =
      Base.List.filter_map multi ~f:(fun blk ->
          let jmps = Term.enum jmp_t blk |> Seq.to_list in
          if compilable_series jmps then Some (Term.tid blk)
          else begin
            let shape =
              Base.String.concat ~sep:","
                (Base.List.map jmps ~f:(fun j ->
                     match Jmp.kind j with
                     | Goto (Direct _) -> "goto"
                     | Goto (Indirect _) -> "goto*"
                     | Ret _ -> "ret"
                     | Call _ -> "call"
                     | Int _ -> "int"))
            in
            Hike_diag.warn
              "split-blocks: sub %s: block %s: multi-jmp series [%s] not all \
               direct gotos; left unsplit"
              (Sub.name sub) (Tid.name (Term.tid blk)) shape;
            None
          end)
    in
    if Base.List.is_empty splittable then sub
    else begin
      let splittable = Core.Set.of_list (module Tid) splittable in
      Term.concat_map blk_t sub ~f:(fun blk ->
          if Core.Set.mem splittable (Term.tid blk) then pieces blk
          else [ blk ])
    end
  end

let normalize (prog : program term) : program term =
  Term.map sub_t prog ~f:split_sub

(* The sub's free registers, read at its own entries over the BIR's
   explicit edges.  A split piece carries no defs; its entering edge is
   the previous piece's explicit Goto, so liveness does not transport a
   target's live set to the sub entry. *)
let free_regs ~(abi : Hike_abi.t) (sub : sub term) : var list =
  let blks = Term.enum blk_t sub |> Seq.to_list in
  (* The exit seed mirrors BAP's liveness: outgoing lanes read their
     value at the return. *)
  let exit_seed =
    Term.enum arg_t sub
    |> Seq.fold ~init:Var.Set.empty ~f:(fun acc arg ->
           match Arg.intent arg with
           | Some (Out | Both) ->
               Core.Set.union acc (Exp.free_vars (Arg.rhs arg))
           | _ -> acc)
  in
  let def live d =
    Core.Set.union
      (Core.Set.diff live (Model.def_writes d))
      (Model.def_reads d)
  in
  let phi live p =
    Core.Set.union (Core.Set.diff live (Model.phi_writes p))
      (Model.phi_reads p)
  in
  let jmp live j = Core.Set.union live (Model.jmp_reads ~abi j) in
  let graph = Sub.to_graph sub in
  let block_ids =
    Base.List.map blks ~f:Term.tid |> Core.Set.of_list (module Tid)
  in
  let live =
    Hike_bir_flow.run ~graph ~sub ~rev:true
      ~initial:(Tid.Map.singleton Graphs.Tid.exit exit_seed)
      ~default:Var.Set.empty ~equal:Core.Set.equal ~merge:Core.Set.union
      ~def ~phi ~jmp
  in
  Base.List.fold blks ~init:Var.Set.empty ~f:(fun acc blk ->
      let tid = Term.tid blk in
      let has_block_pred =
        Graphs.Tid.Node.preds tid graph
        |> Seq.exists ~f:(Core.Set.mem block_ids)
      in
      if has_block_pred then acc
      else
        Core.Set.union acc
          (Option.value (Core.Map.find live.before tid)
             ~default:Var.Set.empty))
  |> Core.Set.filter ~f:(fun v ->
         not (Hike_abi.is_sp abi (Var.base v))
         && match Var.typ v with Type.Mem _ -> false | _ -> true)
  |> Core.Set.to_list
