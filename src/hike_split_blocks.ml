(* The block/jmp-series split: a block whose jmps are all direct Gotos
   (none naming an interrupt sub) becomes one block per jmp, the pieces
   consecutive in term order — piece 1 keeps the tid, defs, phis, and
   attrs.  The BIR CFG then equals the CFG the emitter renders: the
   implicit fallthrough of a piece is its guard's false edge.  Any other
   multi-jmp block stays whole, named on the channel. *)

open Bap.Std

(* The block that follows [blk] in [sub]'s term order: where an implicit
   fallthrough edge lands. *)
let fallthrough (sub : sub term) (blk : blk term) : Tid.t option =
  let tid = Term.tid blk in
  let rec go seen = function
    | [] -> None
    | b :: rest ->
        if seen then Some (Term.tid b)
        else go (Tid.equal (Term.tid b) tid) rest
  in
  go false (Term.enum blk_t sub |> Seq.to_list)

(* A compilable series: every jmp a direct Goto to a non-interrupt. *)
let compilable_series (jmps : jmp term list) : bool =
  Base.List.for_all jmps ~f:(fun j ->
      match Jmp.kind j with
      | Goto (Direct tid) ->
          not (Bil2llvm_env.is_interrupt_name (Tid.name tid))
      | _ -> false)

(* One block per jmp: piece 1 is the original block minus the later
   jmps; each later jmp becomes a fresh block of its own. *)
let pieces (blk : blk term) : blk term list =
  match Term.enum jmp_t blk |> Seq.to_list with
  | [] | [ _ ] -> [ blk ]
  | first :: rest ->
      let first_tid = Term.tid first in
      Term.filter jmp_t blk ~f:(fun j -> Tid.equal (Term.tid j) first_tid)
      :: Base.List.map rest ~f:(fun j -> Blk.create ~jmps:[ j ] ())

let split_sub (sub : sub term) : sub term =
  let multi =
    Term.enum blk_t sub
    |> Seq.filter ~f:(fun blk ->
           Base.List.length (Term.enum jmp_t blk |> Seq.to_list) > 1)
    |> Seq.to_list
  in
  if Base.List.is_empty multi then sub
  else begin
    let splittable =
      Base.List.filter_map multi ~f:(fun blk ->
          let jmps = Term.enum jmp_t blk |> Seq.to_list in
          if compilable_series jmps then Some (Term.tid blk)
          else begin
            Hike_diag.warn
              "split-blocks: sub %s: block %s: multi-jmp series not all \
               direct gotos; left unsplit"
              (Sub.name sub) (Tid.name (Term.tid blk));
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

(* The rendered CFG's edge set: every explicit jmp target, plus the
   term-order successor of a guarded goto terminal (its false edge).
   The liveness and SSA passes read the CFG from here — one successor
   relation. *)
let succs_of_sub (sub : sub term) : Tid.t list Tid.Map.t =
  let blks = Term.enum blk_t sub |> Seq.to_list in
  Base.List.fold blks ~init:Tid.Map.empty ~f:(fun m blk ->
      let explicit =
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
      let last_guarded =
        let jmps = Term.enum jmp_t blk |> Seq.to_list in
        match Base.List.last jmps with
        | Some j when not (Hike_stack_model.is_true_cond (Jmp.cond j)) -> (
            match Jmp.kind j with Goto (Direct _) -> true | _ -> false)
        | _ -> false
      in
      let succs =
        match (last_guarded, fallthrough sub blk) with
        | true, Some succ -> succ :: explicit
        | _ -> explicit
      in
      Core.Map.set m ~key:(Term.tid blk) ~data:succs)

(* The sub's free registers, read at its own entries over the rendered
   CFG.  A split piece carries no defs, so the BAP tid graph's
   in-degree-0 glue would transport its jmp target's live set to the
   sub entry and fatten the signature with registers never read there;
   the fallthrough edge gives the piece its real predecessor. *)
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
