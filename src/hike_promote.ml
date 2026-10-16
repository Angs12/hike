(* The Stack-Arg promotion: the layout's slots become the sub's
   promoted parameters, call sites bind the stored values, and
   promoted-slot loads read the args. *)

open Bap.Std
open Bap.Std.Bil.Types
module Model = Hike_stack_model
module Vsa = Cbat_vsa
module Tag = Hike_stack_model.Tag
module Sections = Hike_sections

(* The call-site correspondence: a store's singleton aligned start [a]
   against the block's call-time SP [d_sp] is slot
   [(a - d_sp - word) / word]. *)
type site_binding = {
  sb_slot : int;
  sb_def : def term;
}

let site_bindings_of_sub_with_blocks ~(word : int) ~(sp : var)
    ~(denote : blk:blk term -> ?def:def term -> exp ->
                (Vsa.WordSet.t, Type.error) Result.t)
    (sub : sub term) : (site_binding list * blk term) Tid.Map.t =
  let w64 = Stdlib.Int64.of_int word in
  let singleton_at ?(def : def term option) ~(blk : blk term) (e : exp) :
      int64 option =
    match denote ~blk ?def e with
    | Error _ -> None
    | Ok ws -> Model.singleton_stack_position ws
  in
  let slot_of_start (a : int64) (d_sp : int64) : int option =
    let rel = Stdlib.Int64.sub a d_sp in
    if
      Stdlib.Int64.compare rel w64 >= 0
      && Stdlib.Int64.equal (Stdlib.Int64.rem rel w64) 0L
    then Some (Model.slot_index_of_offset ~word rel)
    else None
  in
  Term.enum blk_t sub
  |> Seq.fold ~init:Tid.Map.empty ~f:(fun sites blk ->
         let btid = Term.tid blk in
         let has_call =
           Term.enum jmp_t blk
           |> Seq.exists ~f:Hike_stack_model.machine_call
         in
         if not has_call then sites
         else
           match singleton_at ~blk (Bil.Var sp) with
           | None -> Core.Map.set sites ~key:btid ~data:([], blk)
           | Some d_sp ->
               let bindings =
                 Term.enum def_t blk
                 |> Seq.fold ~init:Core.Int.Map.empty ~f:(fun acc d ->
                        match
                          ( Model.addr_of_rhs (Def.rhs d),
                            Model.store_data_of_rhs (Def.rhs d) )
                        with
                        | Some (addr, _size), Some _ -> (
                            match singleton_at ~def:d ~blk addr with
                            | Some a -> (
                                match slot_of_start a d_sp with
                                | Some i ->
                                    Core.Map.set acc ~key:i
                                      ~data:{ sb_slot = i; sb_def = d }
                                | None -> acc)
                            | None -> acc)
                        | _ -> acc)
               in
               Core.Map.set sites ~key:btid
                 ~data:
                   (Core.Map.data bindings, blk))

let site_bindings_of_sub ~(word : int) ~(sp : var)
    ~(denote : blk:blk term -> ?def:def term -> exp ->
                (Vsa.WordSet.t, Type.error) Result.t)
    (sub : sub term) : site_binding list Tid.Map.t =
  site_bindings_of_sub_with_blocks ~word ~sp ~denote sub
  |> Core.Map.map ~f:fst

(* ---- The one address map: every address def's value is its storage's
   base plus the storage-relative displacement. ---- *)

(* Each binding's [hike_argN] def goes just before its storing def. *)
let bind_site_args ~(addr_bits : int) (bindings : site_binding list)
    (blk : blk term) : blk term =
  Base.List.fold bindings ~init:blk ~f:(fun blk b ->
      (* [b.sb_def] is the PRE-rewrite term; its address is read off the
         rewritten block, whose mapper has already run. *)
      let addr =
        match Term.find def_t blk (Term.tid b.sb_def) with
        | Some d -> (
            match Model.addr_of_rhs (Def.rhs d) with
            | Some (a, _) -> a
            | None ->
                failwith
                  ("hike-promote: call-arg binding: slot "
                  ^ Int.to_string b.sb_slot
                  ^ "'s store address is not readable after the rewrite"))
        | None ->
            failwith
              ("hike-promote: call-arg binding: slot "
             ^ Int.to_string b.sb_slot
             ^ "'s storing def is not in its block")
      in
      let arg = Def.create (Model.call_arg ~addr_bits b.sb_slot) addr in
      match Term.next def_t blk (Term.tid b.sb_def) with
      | Some next -> Term.prepend def_t blk ~before:(Term.tid next) arg
      | None -> Term.append def_t blk arg)

(* The promotion's per-sub input facts. *)
type facts = {
  prom_arity : int;
  prom_resolved : Tid.t option Tid.Map.t;
}

(* Resolves each indirect call's target through its denotation: the
   caller-side half of the promotion. *)
let call_resolution ~(denote : blk:blk term -> ?def:def term -> exp ->
                  (Vsa.WordSet.t, Type.error) Result.t)
    ~(lookup : int64 -> Tid.t option)
    (sub : sub term) : Tid.t option Tid.Map.t =
  Term.enum blk_t sub
  |> Seq.fold ~init:Tid.Map.empty ~f:(fun acc blk ->
      Term.enum jmp_t blk
      |> Seq.fold ~init:acc ~f:(fun acc j ->
          match Jmp.kind j with
          | Call c -> (
              match Call.target c with
              | Indirect texp -> (
                  match denote ~blk texp with
                  | Error _ -> Core.Map.set acc ~key:(Term.tid j) ~data:None
                  | Ok ws ->
                      Core.Map.set acc ~key:(Term.tid j)
                        ~data:(Hike_resolve.resolve_target ~lookup ws))
              | Direct _ -> acc)
          | _ -> acc))

(* The caller side: a resolved target becomes direct; the jmp keeps
   its tid, guard, and tag. *)
let resolve_targets ~(resolved : Tid.t option Tid.Map.t)
    (sub : sub term) : sub term =
  Term.map blk_t sub ~f:(fun blk ->
      Term.map jmp_t blk ~f:(fun j ->
          match Core.Map.find resolved (Term.tid j) with
          | Some (Some t) -> (
              match Jmp.kind j with
              | Call c -> Jmp.with_kind j (Call (Call.with_target c (Direct t)))
              | _ -> j)
          | _ -> j))

(* The promotion rewrite: the sub gains its promoted parameters as
   real BIR args, the sites' outgoing stores gain [hike_argN] defs,
   and singleton-resolved indirect targets become direct.
   Fixed-signature subs (the intrinsics, @main) get no callee-side
   rewrite; the caller side runs for every sub. *)
let promote_sub ~(addr_bits : int) (facts : facts)
    (sub : sub term) : sub term =
  let with_signature sub =
    if Hike_stack_model.fixed_signature sub then sub
    else
      (* Promotion defines the sub's whole argument convention: the
         slots in signature order replace the sub's args.  A slot is the
         caller's cell ADDRESS, so the parameter is a pointer. *)
      let slots =
        Base.List.init facts.prom_arity ~f:(fun i ->
            Arg.create ~intent:In (Model.arg_slot ~addr_bits i)
              (Bil.Var (Model.arg_slot ~addr_bits i)))
      in
      Model.set_sig sub slots
  in
  resolve_targets ~resolved:facts.prom_resolved (with_signature sub)


(* The per-sub rewrite: promotion, the storage rewrite, and the layout
   stamp.  [sites]/[resolved] are the call-site and resolution
   products. *)
let rewrite_sub ~(word : int) ~(entry : int64) ~(addr_bits : int)
    ~(abi : Hike_abi.t)
    ~(spans : Sections.data_span list)
    ~(denote : blk:blk term -> ?def:def term -> exp ->
                (Vsa.WordSet.t, Type.error) Result.t)
    ~(ctx : Sections.ctx)
    ~(sites : (site_binding list * blk term) Tid.Map.t)
    ~(resolved : Tid.t option Tid.Map.t)
    ~(callee_exempt : bool)
    (sub : sub term) : sub term =
  let tree =
    Core.Map.find ctx.sub_trees (Term.tid sub)
    |> Core.Option.value ~default:Sections.Tree.empty
  in
  let arity = Sections.slot_arity ~word ~entry tree in
  let arity = if callee_exempt then 0 else arity in
  let facts = { prom_arity = arity; prom_resolved = resolved } in
  let sub = promote_sub ~addr_bits facts sub in
  (* A non-memory def whose value is a caller-window address — the
     model's one window denotation — is stamped; the emitter re-bases
     its integer to the window parameter. *)
  let window_values =
    Term.enum blk_t sub
    |> Seq.fold ~init:Tid.Set.empty ~f:(fun acc blk ->
        Term.enum def_t blk
        |> Seq.fold ~init:acc ~f:(fun acc d ->
            if Core.Option.is_some (Model.addr_of_rhs (Def.rhs d)) then acc
            else
              match denote ~blk ~def:d (Def.rhs d) with
              | Error _ -> acc
              | Ok ws ->
                  if Model.is_window_denotation ~entry ~word ws then
                    Core.Set.add acc (Term.tid d)
                  else acc))
  in
  let sub = Hike_def_slots.stamp_window_values ~window_values sub in
  (* The layout precedes the rewrite: each storage's base offset [rel]
     reads off it, and the rewrite's value forms must not perturb the
     region geometry the layout measures. *)
  let layout = Sections.layout_of_tree ~word ~entry ~abi ~sub tree in
  let storages = Sections.spans_of_layout ~word layout in
  (* The window forms need the signature's window parameter: a
     fixed-signature sub (@main, the intrinsics) never carries it.  A
     window-VALUE def forces the parameter (the layout is stamped with it
     below), so the forms are available for it too. *)
  let window_ok =
    (layout.Hike_stack_model.window_param
    || not (Core.Set.is_empty window_values))
    && not callee_exempt
  in
  let facts =
    Sections.def_facts ~word ~entry ~abi ~tree ~data:ctx.data_tree
      ~projections:ctx.projections ~conversions:ctx.conversions ~storages
      ~window_param:window_ok ~spans ~denote sub
  in
  (* The second pass: one general [Term.mapper] over the sub.  Every def
     (and phi) the attribution proved is rewritten to its owning
     storage — no ad-hoc def filtering. *)
  let rewrite =
    object
      inherit Term.mapper as super

      method! map_def d =
        let d = super#map_def d in
        match Core.Map.find facts (Term.tid d) with
        | None -> d
        | Some f -> (
            match f.Sections.fr_rhs with
            | Some rhs -> Def.with_rhs d rhs
            | None ->
                (* The conversion names the address's own alloca; carry
                   it on the def so the emitter materializes into that
                   region, never the operand's. *)
                Hike_synth_addr.rewrite_storage ~addr_bits ~conv:f.Sections.fr_conv ~bits:f.Sections.fr_bits
                  ?addr:f.Sections.fr_addr d)

      method! map_blk blk =
        let blk = super#map_blk blk in
        match Core.Map.find sites (Term.tid blk) with
        | Some (bs, _) -> bind_site_args ~addr_bits bs blk
        | None -> blk
    end
  in
  let sub = rewrite#map_sub sub in
  (* The signature carries the window parameter whenever a
     window-value def exists. *)
  let layout =
    if Core.Set.is_empty window_values then layout
    else { layout with Hike_stack_model.window_param = true }
  in
  Hike_stack_model.set_layout layout sub

(* The program driver: per-sub sites and resolution, the rewrite. *)
let rewrite_program ~(word : int) ~(entry : int64) ~(facts : Hike_kb.facts)
    ~(spans : Sections.data_span list)
    ~(ctx : Sections.ctx)
    (prog : program term) : program term =
  let abi = facts.abi in
  let denote = facts.denote in
  let sp = abi.Hike_abi.sp in
  let lookup = facts.lookup in
  (* The slot vars are address lanes: the run's target address width,
     the same fact the emitter threads. *)
  let addr_bits = Bap_core_theory.Theory.Target.bits facts.target in
  let callee_exempt = Hike_stack_model.fixed_signature in
  let exempt =
    Term.enum sub_t prog
    |> Seq.fold ~init:Tid.Set.empty ~f:(fun acc s ->
           if callee_exempt s then Core.Set.add acc (Term.tid s) else acc)
  in
  let sides =
    Term.enum sub_t prog
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun acc sub ->
           let sites =
             site_bindings_of_sub_with_blocks ~word ~sp ~denote sub
           in
           let resolved = call_resolution ~denote ~lookup sub in
           Core.Map.set acc ~key:(Term.tid sub) ~data:(sites, resolved))
  in
  Term.map sub_t prog ~f:(fun sub ->
      let sites, resolved =
        Core.Map.find sides (Term.tid sub)
        |> Core.Option.value ~default:(Tid.Map.empty, Tid.Map.empty)
      in
      rewrite_sub ~word ~entry ~addr_bits ~abi ~spans ~denote ~ctx ~sites
        ~resolved
        ~callee_exempt:(Core.Set.mem exempt (Term.tid sub))
        sub)
