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

let site_bindings_of_sub_with_blocks ~(word : int) ~(abi : Hike_abi.t) ~(sp : var)
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
                 |> Seq.fold ~init:[] ~f:(fun acc d ->
                        match
                          ( Model.addr_of_rhs (Def.rhs d),
                            Model.store_data_of_rhs (Def.rhs d) )
                        with
                        | Some (addr, _size), Some _ -> (
                            match singleton_at ~def:d ~blk addr with
                            | Some a -> (
                                match slot_of_start a d_sp with
                                | Some i ->
                                    { sb_slot = i; sb_def = d }
                                    :: Base.List.filter acc ~f:(fun b ->
                                           not (Int.equal b.sb_slot i))
                                | None -> acc)
                            | None -> acc)
                        | _ -> acc)
               in
               Core.Map.set sites ~key:btid
                 ~data:
                   ( Base.List.sort bindings ~compare:(fun a b ->
                        Int.compare a.sb_slot b.sb_slot),
                     blk ))

let site_bindings_of_sub ~(word : int) ~(abi : Hike_abi.t) ~(sp : var)
    ~(denote : blk:blk term -> ?def:def term -> exp ->
                (Vsa.WordSet.t, Type.error) Result.t)
    (sub : sub term) : site_binding list Tid.Map.t =
  site_bindings_of_sub_with_blocks ~word ~abi ~sp ~denote sub
  |> Core.Map.map ~f:fst

(* ---- The one address map: every address def's value is its storage's
   base plus the storage-relative displacement. ---- *)

(* Every var leaf's kind: [ `Static k ] an address whose offset is
   provably k, [ `Addr ] an address whose offset is not static, [ `Int ]
   a visible non-address (a runtime piece).  A var the denotation cannot
   see is absent — unknown may be a pointer at emission, so it never
   enters a displacement. *)
(* One def's rewrite facts: the access's conversion (the mem re-point)
   plus the storage-relative address forms — a value def's whole rhs,
   an access def's mem-node address. *)
type def_fact = {
  fr_conv : Sections.conv;
  fr_bits : int;
  fr_addr : exp option;
  fr_rhs : exp option;
}

let no_fact = { fr_conv = Sections.Keep; fr_bits = 0; fr_addr = None; fr_rhs = None }

(* The sub's storage spans: the layout's regions in the synth fact
   shape, built once and read by every consumer. *)
let spans_of_layout ~(word : int) (layout : Hike_stack_model.sub_layout) :
    Hike_synth.storage_span list =
  Base.List.map layout.Hike_stack_model.regions
    ~f:(fun { Model.Sub_layout.r_id = id; r_lo = lo; r_hi = hi; _ } ->
        Hike_synth.storage_span ~addr_bits:(Model.word_bits word)
          (Hike_synth.Stack id) ~lo ~hi)

(* The per-def rewrite facts of one sub: every access keeps its
   conversion; every address def whose value routes to a storage takes
   the base + displacement form. *)
let def_facts ~(word : int) ~(entry : int64) ~(abi : Hike_abi.t)
    ~(tree : Sections.sub_tree) ~(data : Sections.data_tree)
    ~(projections : Sections.projection option Tid.Map.t)
    ~(conversions : Sections.conv Tid.Map.t)
    ~(storages : Hike_synth.storage_span list)
    ~(window_param : bool) ~(vla_tids : Tid.Set.t)
    ~(spans : Sections.data_span list)
    ~(denote : blk:blk term -> ?def:def term -> exp ->
                (Vsa.WordSet.t, Type.error) Result.t)
    (sub : sub term) : def_fact Tid.Map.t =
#ifdef VSA_DEBUG
  let census key = Cbat_vsa.Cbat_attr_census.bump key in
#else
  let census _ = () in
#endif
  let addr_bits = Model.word_bits word in
  (* The rewrite's admissibility: the address's whole range lies inside
     the storage's allocated extent — a value or access outside it names
     no storage, and the model arithmetic keeps it. *)
  Term.enum blk_t sub
  |> Seq.fold ~init:Tid.Map.empty ~f:(fun acc blk ->
         Term.enum def_t blk
         |> Seq.fold ~init:acc ~f:(fun acc d ->
                if
                  Hike_def_slots.def_is_dyn_alloc d
                then acc
                else
                  let leaves = Hike_synth_addr.address_leaves ~denote ~storages ~blk ~def:d (Def.rhs d) in
                  let fact = no_fact in
                  match Sections.access_of d with
                  | Some (addr, w, _) -> (
                      let projected =
                        Base.Option.join
                          (Core.Map.find projections (Term.tid d))
                      in
                      let conv =
                        Base.Option.value
                          (Core.Map.find conversions (Term.tid d))
                          ~default:Sections.Keep
                      in
                      let addr_range () =
                        Base.Option.bind projected
                          ~f:(fun p -> p.Sections.offsets)
                      in
                      match conv with
                      | Sections.Conv_region id when
                          Base.Option.value_map (addr_range ())
                            ~default:false ~f:(fun (lo, hi) ->
                              Hike_synth_addr.fits_span ~storages (Hike_synth.Stack id) lo hi)
                          -> (
                          let folded = Hike_synth_addr.offset_of ~leaves addr in

                          census
                            (if Int.equal id Model.residue_id then
                               (match folded with
                                | Some _ -> "rw.access.residue.folded"
                                | None -> "rw.access.residue.geom")
                             else
                               (match folded with
                                | Some _ -> "rw.access.region.folded"
                                | None -> "rw.access.region.geom"));
                          let f =
                            match Hike_synth_addr.span_base ~storages (Hike_synth.Stack id) folded with
                            | Some a -> { fact with fr_addr = Some a }
                            | None -> fact
                          in
                          Core.Map.set acc ~key:(Term.tid d)
                            ~data:{ f with fr_conv = conv; fr_bits = 8 * w })
                      | Sections.Conv_region id ->
                          census
                            (if Int.equal id Model.residue_id then
                               "rw.access.residue.outside"
                             else "rw.access.region.outside");
                          Core.Map.set acc ~key:(Term.tid d)
                            ~data:{ fact with fr_conv = conv; fr_bits = 8 * w }
                      | Sections.Conv_window ->
                          census "rw.access.window";
                          (* The window's base is the parameter; its
                             coordinate IS the entry-relative offset. *)
                          let f =
                            match
                              Hike_synth_addr.base_form ~leaves
                                ~base:(Model.hike_window_var ~word) ~rel:0L addr
                            with
                            | Some a -> { fact with fr_addr = Some a }
                            | None -> fact
                          in
                          Core.Map.set acc ~key:(Term.tid d)
                            ~data:{ f with fr_conv = conv; fr_bits = 8 * w }
                      | Sections.Conv_global _ ->
                          census "rw.access.section";
                          Core.Map.set acc ~key:(Term.tid d)
                            ~data:{ fact with fr_conv = conv; fr_bits = 8 * w }
                      | _ ->
                          census "rw.access.keep";
                          Core.Map.set acc ~key:(Term.tid d)
                            ~data:
                              { fact with fr_conv = conv;
                                fr_bits = 8 * w })
                  | None -> (
                      let v = Def.lhs d in
                      if
                        Model.is_mem v
                        || Hike_abi.is_sp abi (Var.base v)
                        || not
                             (match Var.typ v with
                              | Type.Imm n -> Int.equal n addr_bits
                              | _ -> false)
                      then acc
                      else
                        match denote ~blk ~def:d (Def.rhs d) with
                        | Error _ -> acc
                        | Ok ws
                          when not (Vsa.WordSet.in_stack_segment ws)
                               && not (Vsa.WordSet.is_top ws)
                               && not (Vsa.WordSet.is_bottom ws) -> (
                            (* A plain constant address routes to its
                               component's base: the binding wholly
                               owning it, minus the component's own low
                               bound.  A constant at a copy-relocated
                               slot is externally owned — it keeps the
                               raw lane. *)
                            match Model.singleton_i64 ws with
                            | None -> census "rw.value.raw"; acc
                            | Some c -> (
                                let at_slot =
                                  Base.List.exists spans ~f:(fun sp ->
                                      Sections.equal_sec sp.Sections.ds_sec
                                        (Sections.point Rodata c).p_sec
                                      && Base.List.exists sp.Sections.ds_slots
                                           ~f:(fun sl ->
                                             Stdlib.Int64.equal sl c))
                                in
                                match
                                  (at_slot,
                                   Sections.owning_data_binding data c)
                                with
                                | false, Some (id, comp_lo) -> (
                                    (* A pure constant address materializes
                                       at this def: the component's pointer
                                       base plus its own constant.  A value
                                       with var leaves composes over its
                                       operands' own pointers — the address
                                       defs carrying it already render the
                                       real bits, so a re-base here would
                                       materialize the address twice. *)
                                    match
                                      Hike_synth_addr.offset_of ~leaves (Def.rhs d)
                                    with
                                    | Some (Bil.Int w) ->
                                        census "rw.value.section";
                                        let rhs =
                                          match
                                            Cbat_word.to_int64
                                              (Cbat_word.of_word w)
                                          with
                                          | Ok k
                                            when Stdlib.Int64.equal k c ->
                                              Hike_synth_addr.base_plus
                                                (Model.sec_comp_ptr
                                                   ~addr_bits id)
                                                ~rel:comp_lo (Bil.Int w)
                                          | _ ->
                                              Bil.BinOp
                                                ( Bil.PLUS,
                                                  Bil.Var
                                                    (Model.sec_comp_ptr
                                                       ~addr_bits id),
                                                  Bil.BinOp
                                                    ( Bil.MINUS,
                                                      Bil.Int w,
                                                      Bil.Int
                                                        (Cbat_word.to_word
                                                           (Cbat_word
                                                              .of_int64
                                                              ~width:64
                                                              comp_lo))
                                                    ) )
                                        in
                                        Core.Map.set acc ~key:(Term.tid d)
                                          ~data:
                                            { fact with fr_rhs = Some rhs }
                                    | _ ->
                                        census "rw.value.section.carried";
                                        acc)
                                | _ -> census "rw.value.raw"; acc))
                        | Ok ws when Core.Map.is_empty leaves -> (
                            (* A pure constant is a machine constant, not
                               a synthesized address: the model's stack
                               line sits at 2^62, and a double's bits can
                               land inside it — only a value with var
                               leaves (an SP-derived address) routes to
                               the frame's storages. *)
                            census "rw.value.raw";
                            acc)
                        | Ok ws -> (
                            (* The routing of an address value: at/above
                               the args base it names the caller's window
                               (the parameter is the base); below the
                               entry line the tree's binding owns its
                               whole range. *)
                            match Vsa.WordSet.origin ws with
                            | Some (Vsa.WordSet.Origin.Vla tid)
                              when (not (Vsa.WordSet.is_infinite ws))
                                   && Core.Set.mem vla_tids tid -> (
                                (* The offsets are frame-relative: the
                                   allocation's base is byte zero, no
                                   position arithmetic applies. *)
                                match
                                  Base.Option.map
                                    (Hike_synth_addr.offset_of ~leaves (Def.rhs d))
                                    ~f:(Hike_synth_addr.base_plus (Model.vla_ptr ~addr_bits tid)
                                         ~rel:0L)
                                with
                                | Some rhs ->
                                    census "rw.value.vla";
                                    Core.Map.set acc ~key:(Term.tid d)
                                      ~data:{ fact with fr_rhs = Some rhs }
                                | None ->
                                    census "rw.value.vla.unfoldable"; acc)
                            | Some (Vsa.WordSet.Origin.Vla _) ->
                                census "rw.value.vla"; acc
                            | _ -> (
                                let a_base = Model.args_base ~entry ~word in
                                match
                                  (not (Vsa.WordSet.is_infinite ws),
                                   Model.positions_of_offsets ws)
                                with
                                | true, Some (lo, hi)
                                  when Stdlib.Int64.compare lo hi <= 0
                                       && Stdlib.Int64.compare lo a_base >= 0
                                       && window_param -> (
                                    match
                                      Hike_synth_addr.base_form ~leaves
                                        ~base:(Model.hike_window_var ~word)
                                        ~rel:0L (Def.rhs d)
                                    with
                                    | Some rhs ->
                                        census "rw.value.window";
                                        Core.Map.set acc ~key:(Term.tid d)
                                          ~data:{ fact with fr_rhs = Some rhs }
                                    | None ->
                                        census "rw.value.window.unfoldable";
                                        acc)
                                | true, Some (lo, hi)
                                  when Stdlib.Int64.compare lo hi <= 0 -> (
                                    match Sections.owning_storage tree lo hi with
                                    | Some
                                        ((Stack_region _ | Stack_residue) as
                                        st)
                                      when Hike_synth_addr.fits_span ~storages
                                             (Hike_synth.Stack
                                                (Sections.region_id_of_storage st))
                                             lo hi
                                      -> (
                                        match
                                          Hike_synth_addr.span_base ~storages
                                            (Hike_synth.Stack
                                               (Sections.region_id_of_storage st))
                                            (Hike_synth_addr.offset_of ~leaves
                                               (Def.rhs d))
                                        with
                                        | Some rhs ->
                                            census "rw.value.region";
                                            Core.Map.set acc
                                              ~key:(Term.tid d)
                                              ~data:{ fact with fr_rhs = Some rhs }
                                        | None ->
                                            census "rw.value.region.unfoldable";
                                            acc)
                                    | Some _ -> census "rw.value.window"; acc
                                    | None -> census "rw.value.raw"; acc)
                                | _ -> census "rw.value.raw"; acc)))))

(* Every memory node of the expression re-points at [mem_var] — a
   converted def keeps no model-memory node — and takes [addr] as its
   address when the rewrite computed the storage-relative form.  The
   override receives children unmapped, so it maps the address and
   store data itself. *)
(* Each call site's stored slot gains its [hike_argN] def binding the
   caller's own slot ADDRESS: the store's address, which the rewrite
   above already re-pointed at the caller's storage.  A partial store
   passes its address too — the callee reads and writes the exact
   bytes. *)
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
  let resolved = ref Tid.Map.empty in
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun blk ->
      Term.enum jmp_t blk
      |> Seq.iter ~f:(fun j ->
          match Jmp.kind j with
          | Call c -> (
              match Call.target c with
              | Indirect texp -> (
                  match denote ~blk texp with
                  | Error _ ->
                      resolved :=
                        Core.Map.set !resolved ~key:(Term.tid j) ~data:None
                  | Ok ws ->
                      resolved :=
                        Core.Map.set !resolved ~key:(Term.tid j)
                          ~data:(Hike_resolve.resolve_target ~lookup ws))
              | Direct _ -> ())
          | _ -> ()));
  !resolved

(* The promotion rewrite: the sub gains its promoted parameters as
   real BIR args, the sites' outgoing stores gain [hike_argN] defs,
   and singleton-resolved indirect targets become direct.
   Fixed-signature subs (the intrinsics, @main) get no callee-side
   rewrite; the caller side runs for every sub. *)
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


(* The promoted slots' arity: one per word cell the tree's Arg_slot
   members name, derived from each member's own address — the binding is
   never the unit. *)
let slot_arity ~(word : int) ~(entry : int64) (tree : Sections.sub_tree) : int =
  let arity =
    Sections.Tree.to_sequence tree
    |> Seq.fold ~init:None ~f:(fun mx (_, rs) ->
           match rs.storage with
           | Arg_slot ->
               Base.List.fold rs.members ~init:mx ~f:(fun mx mm ->
                   match Sections.args_member_cell ~word ~entry mm with
                   | Some i -> (
                       match mx with
                       | Some n -> Some (Int.max n i)
                       | None -> Some i)
                   | None -> mx)
           | _ -> mx)
  in
  match arity with Some i -> i + 1 | None -> 0

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
    ~(vla_tids : Tid.Set.t)
    ~(callee_exempt : bool)
    (sub : sub term) : sub term =
  (* A fixed-signature sub (@main, an emittable intrinsic) carries a
     convention of its own, never the ABI's, so it is not a variadic
     definition however its body is built. *)
  let variadic =
    (not callee_exempt)
    && Model.is_variadic_construction ~abi ~entry ~denote sub
  in
  let tree =
    Core.Map.find ctx.sub_trees (Term.tid sub)
    |> Core.Option.value ~default:Sections.Tree.empty
  in
  let arity = slot_arity ~word ~entry tree in
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
  let storages = spans_of_layout ~word layout in
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
    def_facts ~word ~entry ~abi ~tree ~data:ctx.data_tree
      ~projections:ctx.projections ~conversions:ctx.conversions ~storages
      ~window_param:window_ok ~vla_tids ~spans ~denote sub
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
            match f.fr_rhs with
            | Some rhs -> Def.with_rhs d rhs
            | None ->
                let d =
                  Hike_synth_addr.rewrite_storage ~addr_bits ~conv:f.fr_conv ~bits:f.fr_bits
                    ?addr:f.fr_addr d
                in
                (* The conversion names the address's own alloca; carry
                   it on the def so the emitter materializes into that
                   region, never the operand's. *)
                match f.fr_conv with
                | Sections.Conv_region _ | Sections.Conv_window -> d
                | Sections.Conv_slot _ | Sections.Conv_global _ | Sections.Keep -> d)

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
  let sub = Hike_stack_model.set_layout layout sub in
  if variadic then Hike_stack_model.set_variadic sub else sub

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
             site_bindings_of_sub_with_blocks ~word ~abi ~sp ~denote sub
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
        ~vla_tids:(Core.Map.key_set facts.Hike_kb.vla_extents)
        ~callee_exempt:(Core.Set.mem exempt (Term.tid sub))
        sub)
