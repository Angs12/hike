(* The transfer-target vocabulary: the memory slot an indirect transfer
   reads its destination through.  A target whose value is a LOAD from a
   constant address names the dynamic linker's slot at that address; a
   Var target or a Var load address resolves through the sub's own defs
   (the def may sit in any block; the last def in term order is the one
   the transfer reads).  Consumers decide membership: the emitter names
   the external the slot binds, the completion and the prune classify
   the transfer as a foreign boundary. *)

open Bap.Std

(* The defining rhs of [v]: the last def of the var in term order (under
   SSA that is the one def). *)
let def_rhs ~(sub : sub term) (v : var) : exp option =
  Term.enum blk_t sub
  |> Seq.concat_map ~f:(Term.enum def_t)
  |> Seq.fold ~init:None ~f:(fun found d ->
      if Var.equal (Def.lhs d) v then Some (Def.rhs d) else found)

(* Var-links resolved through the sub's defs; [seen] keeps a copy cycle
   from looping. *)
let rec resolve ~(sub : sub term option) ~(seen : var list) (e : exp) : exp =
  match e with
  | Bil.Var v ->
    if Base.List.exists ~f:(Var.equal v) seen then e
    else
      (match sub with
       | None -> e
       | Some sub -> (
         match def_rhs ~sub v with
         | Some rhs -> resolve ~sub:(Some sub) ~seen:(v :: seen) rhs
         | None -> e))
  | e -> e

(* The linker slot the transfer's target reads, if any.  [origin] maps a
   storage base var to its module byte origin, so a resolved
   component-relative access recovers its absolute slot. *)
let slot_of_target ?(synth = Hike_synth.empty)
    ?(origin : (var -> int64 option) option) ?(sub : sub term option)
    (target : exp) : int64 option =
  match resolve ~sub ~seen:[] target with
  | Bil.Load (mem, addr, _, _) -> (
    let addr = resolve ~sub ~seen:[] addr in
    match mem with
    | Bil.Var mv -> Hike_synth.access_address ?origin synth mv addr
    | _ -> Hike_synth.address_of_exp synth addr)
  | _ -> None
