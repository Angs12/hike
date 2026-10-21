(* The transfer-target vocabulary: the memory slot an indirect transfer
   reads its destination through.  A target whose value is a LOAD from a
   constant address names the dynamic linker's slot at that address; a
   Var target or a Var load address resolves through definitions and
   phis whose incoming expressions resolve to the same value.  Consumers decide membership: the emitter names
   the external the slot binds, the completion and the prune classify
   the transfer as a foreign boundary. *)

open Bap.Std

(* The sub's definitions and phi operands, built once: var-link resolution
   follows links through it, so a loop that resolves many targets for
   one sub shares one scan. *)
type index = exp list Var.Map.t

let index_of_sub (sub : sub term) : index =
  Term.enum blk_t sub
  |> Seq.fold ~init:Var.Map.empty ~f:(fun m blk ->
      let m = Term.enum phi_t blk |> Seq.fold ~init:m ~f:(fun m p ->
          Core.Map.set m ~key:(Phi.lhs p)
            ~data:(Phi.values p |> Seq.map ~f:snd |> Seq.to_list)) in
      Term.enum def_t blk |> Seq.fold ~init:m ~f:(fun m d ->
          Core.Map.update m (Def.lhs d) ~f:(function
            | Some rhs -> rhs @ [ Def.rhs d ]
            | None -> [ Def.rhs d ])))

(* Var-links resolved through [index]; [seen] keeps a copy cycle from
   looping. *)
let rec resolve_index ~(index : index) ~(seen : var list) (e : exp) : exp =
  match e with
  | Bil.Var v ->
    if Base.List.exists ~f:(Var.equal v) seen then e
    else (
      match Core.Map.find index v with
      | Some (rhs :: rest) ->
        let resolve = resolve_index ~index ~seen:(v :: seen) in
        let rhs = resolve rhs in
        if Base.List.for_all rest ~f:(fun r -> Exp.equal rhs (resolve r))
        then rhs else e
      | Some [] | None -> e)
  | e -> e

(* The linker slot the transfer's target reads, if any.  [origin] maps a
   storage base var to its module byte origin, so a resolved
   component-relative access recovers its absolute slot.  [index] shares
   one per-sub def scan across many resolutions; without it (and with
   [sub]) each call builds its own. *)
let slot_of_target ?index ~synth
    ?(origin : (var -> int64 option) option) ?(sub : sub term option)
    (target : exp) : int64 option =
  let index =
    match index with
    | Some index -> Some index
    | None -> Base.Option.map sub ~f:index_of_sub
  in
  let resolve e =
    match index with
    | Some index -> resolve_index ~index ~seen:[] e
    | None -> e
  in
  match resolve target with
  | Bil.Load (mem, addr, _, _) -> (
    let addr = resolve addr in
    match mem with
    | Bil.Var mv -> Hike_synth_addr.access_address ?origin synth mv addr
    | _ -> Hike_synth_addr.address_of_exp synth addr)
  | _ -> None
