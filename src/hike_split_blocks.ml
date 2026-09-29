(* The block/jmp split: every guard's false edge becomes an explicit
   Goto (BAP's lifting leaves it implicit in the term order), and a
   3+-jmp direct-goto series becomes one block per jmp — piece 1 keeps
   the tid, defs, phis, and attrs; every piece carries an explicit Goto
   to the next.  The BIR's edges are then the jmps themselves, so every
   later pass (the emitter included) reads the BIR, never a term order.
   A series that is not all direct gotos stays whole, named on the
   channel. *)

open Bap.Std

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

(* The block that follows [blk] in [sub]'s term order: the false target of
   a guard whose block has no later jmp. *)
let fallthrough (sub : sub term) (blk : blk term) : Tid.t option =
  let tid = Term.tid blk in
  let rec go seen = function
    | [] -> None
    | b :: rest ->
        if seen then Some (Term.tid b)
        else go (Tid.equal (Term.tid b) tid) rest
  in
  go false (Term.enum blk_t sub |> Seq.to_list)

let split_sub (sub : sub term) : sub term =
  (* Every guard's false edge becomes an explicit Goto.  BAP's lifting
     leaves it implicit (the term-order successor); materializing it here
     means no later pass — the emitter included — reads a term order. *)
  let sub =
    Term.map blk_t sub ~f:(fun blk ->
        match Base.List.last (Term.enum jmp_t blk |> Seq.to_list) with
        | Some j when not (Hike_stack_model.is_true_cond (Jmp.cond j)) -> (
            match fallthrough sub blk with
            | Some succ ->
                Term.append jmp_t blk (Jmp.create (Goto (Direct succ)))
            | None -> blk)
        | _ -> blk)
  in
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

(* The rendered CFG's edge set: every jmp target, explicit in the BIR.
   The liveness and SSA passes read the CFG from here — one successor
   relation, no term-order fallthrough. *)
let succs_of_sub (sub : sub term) : Tid.t list Tid.Map.t =
  Term.enum blk_t sub
  |> Seq.fold ~init:Tid.Map.empty ~f:(fun m blk ->
      let succs =
        Term.enum jmp_t blk
        |> Seq.filter_map ~f:(fun j ->
               match Jmp.kind j with
               | Goto (Direct tid) | Int (_, tid) -> Some tid
               | Call c -> (
                   match Call.return c with
                   | Some (Direct tid) -> Some tid
                   | _ -> None)
               | _ -> None)
        |> Seq.to_list
      in
      Core.Map.set m ~key:(Term.tid blk) ~data:succs)

(* The sub's free registers, read at its own entries over the BIR's
   explicit edges.  A split piece carries no defs; its entering edge is
   the previous piece's explicit Goto, so liveness does not transport a
   target's live set to the sub entry. *)
let free_regs (sub : sub term) : var list =
  let blks = Term.enum blk_t sub |> Seq.to_list in
  let succs = succs_of_sub sub in
  let uses_and_defs (blk : blk term) =
    let defs =
      Blk.elts blk
      |> Seq.fold ~init:Var.Set.empty ~f:(fun acc elt ->
             match elt with
             | `Def d -> Core.Set.add acc (Def.lhs d)
             | `Phi p -> Core.Set.add acc (Phi.lhs p)
             | _ -> acc)
    in
    (Blk.free_vars blk, defs)
  in
  let trans =
    Base.List.fold blks ~init:Tid.Map.empty ~f:(fun m blk ->
        let uses, defs = uses_and_defs blk in
        Core.Map.set m ~key:(Term.tid blk) ~data:(uses, defs))
  in
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
  let has_succs tid =
    match Core.Map.find succs tid with
    | Some (_ :: _) -> true
    | _ -> false
  in
  let live_in = ref Tid.Map.empty in
  let get_in tid =
    Core.Map.find !(live_in) tid |> Option.value ~default:Var.Set.empty
  in
  let changed = ref true in
  while !changed do
    changed := false;
    Base.List.iter blks ~f:(fun blk ->
        let tid = Term.tid blk in
        let out =
          if has_succs tid then
            Core.Map.find succs tid
            |> Option.value ~default:[]
            |> Base.List.fold ~init:Var.Set.empty
                 ~f:(fun acc s -> Core.Set.union acc (get_in s))
          else exit_seed
        in
        let uses, defs =
          Core.Map.find trans tid |> Option.value ~default:(Var.Set.empty, Var.Set.empty)
        in
        let inn =
          Core.Set.union uses (Core.Set.diff out defs)
        in
        if not (Core.Set.equal inn (get_in tid)) then begin
          live_in := Core.Map.set !(live_in) ~key:tid ~data:inn;
          changed := true
        end)
  done;
  (* Roots: no in-edge under the rendered edge set (dead blocks join
     the real entry, exactly as the BAP glue does). *)
  let with_pred =
    Core.Map.fold succs ~init:Tid.Set.empty ~f:(fun ~key:_ ~data acc ->
        Base.List.fold data ~init:acc ~f:(fun acc t -> Core.Set.add acc t))
  in
  Base.List.fold blks ~init:Var.Set.empty ~f:(fun acc blk ->
      let tid = Term.tid blk in
      if Core.Set.mem with_pred tid then acc
      else Core.Set.union acc (get_in tid))
  |> Core.Set.filter ~f:(fun v ->
         match Var.typ v with Type.Mem _ -> false | _ -> true)
  |> Core.Set.to_list
