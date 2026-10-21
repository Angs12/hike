(* The Stack-Arg promotion: the layout's slots become the sub's
   promoted parameters, call sites bind the stored values, and
   promoted-slot loads read the args. *)

open Bap.Std
open Bap.Std.Bil.Types
module Model = Hike_stack_model
module Vsa = Cbat_vsa
module Tag = Hike_stack_model.Tag
module Sections = Hike_sections

type site_binding = Hike_stack_model.call_arg_store = {
  sb_slot : int;
  sb_def : def term;
}

let site_bindings_of_sub_with_blocks ~(word : int) ~(sp : var)
    ~(denote : blk:blk term -> ?def:def term -> exp ->
                (Vsa.WordSet.t, Type.error) Result.t)
    (sub : sub term) : (site_binding list * blk term) Tid.Map.t =
  Model.site_bindings_of_sub_with_blocks ~word ~sp ~denote sub

let site_bindings_of_sub ~(word : int) ~(sp : var)
    ~(denote : blk:blk term -> ?def:def term -> exp ->
                (Vsa.WordSet.t, Type.error) Result.t)
    (sub : sub term) : site_binding list Tid.Map.t =
  site_bindings_of_sub_with_blocks ~word ~sp ~denote sub
  |> Core.Map.map ~f:fst

(* ---- The one address map: every address def's value is its storage's
   base plus the storage-relative displacement. ---- *)

(* Each binding's [hike_argN] def goes just before its storing def. *)
let bind_site_args ~(synth : Hike_synth.table ref) ~(addr_bits : int)
    (bindings : site_binding list) (blk : blk term) : blk term =
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
      let call_arg =
        Hike_synth.record synth
          (Hike_synth.mint_base ~addr_bits (Hike_synth.Argument b.sb_slot)) in
      let arg = Def.create call_arg addr in
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
   its tid, guard, and tag.  The direct call's lanes are re-derived
   ([Hike_ssa.refresh_calls]): each keeps the version the indirect call
   had. *)
let resolve_targets ~(synth : Hike_synth.table) ~(abi : Hike_abi.t)
    ~(resolved : Tid.t option Tid.Map.t) (sub : sub term) : sub term =
  let is_retargeted j =
    match Core.Map.find resolved (Term.tid j), Jmp.kind j with
    | Some (Some _), Call _ -> true
    | _ -> false
  in
  Term.map blk_t sub ~f:(fun blk ->
      Term.map jmp_t blk ~f:(fun j ->
          match Core.Map.find resolved (Term.tid j), Jmp.kind j with
          | Some (Some t), Call c ->
              Jmp.with_kind j (Call (Call.with_target c (Direct t)))
          | _ -> j))
  |> Hike_ssa.refresh_calls ~synth ~abi ~callee:(fun _ -> None)
       ~select:is_retargeted

(* The promotion rewrite: the sub gains its promoted parameters as
   real BIR args, the sites' outgoing stores gain [hike_argN] defs,
   and singleton-resolved indirect targets become direct.
   Fixed-signature subs (the intrinsics, @main) get no callee-side
   rewrite; the caller side runs for every sub. *)
let promote_sub ~(synth : Hike_synth.table ref) ~(addr_bits : int)
    ~(abi : Hike_abi.t) (facts : facts) (sub : sub term) : sub term =
  let with_signature sub =
    if Hike_stack_model.fixed_signature sub then sub
    else
      (* Promotion defines the sub's whole argument convention: the
         slots in signature order replace the sub's args.  A slot is the
         caller's cell ADDRESS, so the parameter is a pointer. *)
      let slots =
        Base.List.init facts.prom_arity ~f:(fun i ->
            let slot =
              Hike_synth.record synth
                (Hike_synth.mint_base ~addr_bits (Hike_synth.Slot i)) in
            Arg.create ~intent:In slot (Bil.Var slot))
      in
      Model.set_sig sub slots
  in
  resolve_targets ~synth:!synth ~abi ~resolved:facts.prom_resolved
    (with_signature sub)


(* The per-sub rewrite: promotion, the storage rewrite, and the layout
   stamp.  [sites]/[resolved] are the call-site and resolution
   products. *)
let rewrite_sub ~(synth : Hike_synth.table ref) ~(word : int)
    ~(entry : int64) ~(addr_bits : int) ~(abi : Hike_abi.t)
    ~(spans : Sections.data_span list)
    ~(denote : blk:blk term -> ?def:def term -> exp ->
                (Vsa.WordSet.t, Type.error) Result.t)
    ~(ctx : Sections.ctx)
    ~(sites : (site_binding list * blk term) Tid.Map.t)
    ~(resolved : Tid.t option Tid.Map.t)
    ~(callee_exempt : bool)
    (sub : sub term) : sub term =
  let tree = Core.Map.find_exn ctx.sub_trees (Term.tid sub) in
  let arity = Sections.slot_arity ~word ~entry tree in
  let arity = if callee_exempt then 0 else arity in
  let facts = { prom_arity = arity; prom_resolved = resolved } in
  let sub = promote_sub ~synth ~addr_bits ~abi facts sub in
  (* Keep the window-value stamp for denotations at/above entry. The
     layout decides whether an actual Args-space memory access needs an
     incoming window parameter. *)
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
  let storages = Sections.spans_of_layout ~synth ~word layout in
  (* The window forms need an Args-space access, including the overflow
     area consumed by a recognized va_list construction. A dead
     SP-derived value does not need the incoming lane. *)
  let window_ok =
    layout.Hike_stack_model.window_param && not callee_exempt
  in
  let facts =
    Sections.def_facts ~synth ~word ~entry ~abi ~tree ~data:ctx.data_tree
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
                Hike_synth_addr.rewrite_storage ~synth ~addr_bits ~conv:f.Sections.fr_conv ~bits:f.Sections.fr_bits
                  ?addr:f.Sections.fr_addr d)

      method! map_blk blk =
        let blk = super#map_blk blk in
        match Core.Map.find sites (Term.tid blk) with
        | Some (bs, _) -> bind_site_args ~synth ~addr_bits bs blk
        | None -> blk
    end
  in
  let sub = rewrite#map_sub sub in
  Hike_stack_model.set_layout layout sub

(* The program driver: per-sub sites and resolution, the rewrite. *)
let rewrite_program ~(word : int) ~(entry : int64) ~(facts : Hike_kb.facts)
    ~(spans : Sections.data_span list)
    ~(ctx : Sections.ctx)
    (prog : program term) : Hike_synth.table * program term =
  let synth = ref facts.synth in
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
  let prog =
    Term.map sub_t prog ~f:(fun sub ->
        let sites, resolved = Core.Map.find_exn sides (Term.tid sub) in
        rewrite_sub ~synth ~word ~entry ~addr_bits ~abi ~spans ~denote ~ctx
          ~sites ~resolved
          ~callee_exempt:(Core.Set.mem exempt (Term.tid sub))
          sub)
  in
  (!synth, prog)
