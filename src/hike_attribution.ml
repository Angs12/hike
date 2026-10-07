open Bap.Std

type result = {
  program : program term;
  facts : Hike_kb.facts;
}

let run ~(facts : Hike_kb.facts) ~(word : int) ~(entry : int64)
    ~(spans : Hike_sections.data_span list)
    ~(meta : Hike_sections.sec_meta option list)
    ~(tls : Hike_spec.tls_spec option)
    ~(relative : (int64 * int64) list) ~(externals : (int64 * string) list)
    (program : program term) : result =
  let program = Hike_split_blocks.materialize ~facts program in
  let addr_bits = Hike_abi.addr_size_bits facts.target in
  (* A copy-relocated slot's bytes are externally owned: the access keeps
     its absolute address so the emitter's relocation path renders it. *)
  let slots =
    Base.List.concat_map spans ~f:(fun span -> span.Hike_sections.ds_slots)
  in
  let layout ~synth program =
    let facts = { facts with Hike_kb.synth } in
    let dynamic_allocs =
      Term.enum sub_t program
      |> Seq.fold ~init:Tid.Map.empty ~f:(fun map sub ->
             Core.Map.set map ~key:(Term.tid sub)
               ~data:(Hike_sections.dynamic_alloc_tids_of ~facts sub))
    in
    let program =
      Term.map sub_t program ~f:(fun sub ->
          let tids =
            Core.Map.find dynamic_allocs (Term.tid sub)
            |> Option.value ~default:Tid.Set.empty
          in
          Hike_def_slots.stamp_dyn_allocs ~dynamic_alloc_tids:tids sub)
    in
    let sections =
      Hike_sections.attribute ~facts ~word ~entry ~spans program
    in
    let program =
      Term.map sub_t program ~f:(Hike_sections.stamp_tags sections)
      |> Hike_promote.rewrite_program ~word ~entry ~facts ~spans ~ctx:sections
    in
    let spec =
      Hike_sections.section_spec_of ~word
        ~comps:(Hike_sections.global_comps_of ~word ~spans sections)
        ~whole:(Hike_sections.whole_comps_of sections) ~meta ~tls ~relative
        ~externals
    in
    let regions =
      Base.List.map spec.spec_comps ~f:(fun comp ->
          let byte w = Int64.add comp.Hike_stack_model.sec_lo
              (Int64.of_int (w * word)) in
          { Hike_synth_addr.id = comp.comp_id;
            lo = byte comp.lo_w; hi = Int64.pred (byte (comp.hi_w + 1)) })
      @ Base.List.map spec.spec_whole ~f:(fun (id, lo, hi) ->
            { Hike_synth_addr.id; lo; hi })
    in
    let arities =
      Core.Map.map sections.sub_trees
        ~f:(Hike_sections.slot_arity ~word ~entry)
    in
    let window_readers =
      Term.enum sub_t program
      |> Seq.fold ~init:Tid.Set.empty ~f:(fun acc sub ->
             let reads_window =
               Hike_stack_model.is_variadic sub
               || Base.Option.value_map
                    (Core.Map.find sections.sub_trees (Term.tid sub))
                    ~default:false ~f:(fun tree ->
                      Hike_sections.Tree.to_sequence tree
                      |> Seq.exists ~f:(fun (_, range) ->
                             Base.List.exists range.Hike_sections.members
                               ~f:(fun member_ ->
                                 member_.Hike_sections.m_identity
                                 && Hike_sections.equal_sec
                                      member_.Hike_sections.m_sec
                                      Hike_stack_model.Args)))
             in
             if reads_window then Core.Set.add acc (Term.tid sub) else acc)
    in
    let escape_roots =
      Term.enum sub_t program
      |> Seq.fold ~init:Tid.Map.empty ~f:(fun map sub ->
             let tree =
               Core.Map.find sections.sub_trees (Term.tid sub)
               |> Option.value ~default:Hike_sections.Tree.empty
             in
             Core.Map.set map ~key:(Term.tid sub)
               ~data:
                 (Hike_sections.escape_roots_of_sub
                    ~addr_bits:(Hike_stack_model.word_bits facts.abi.word)
                    ~abi:facts.abi ~arities ~window_readers ~tree sub))
    in
    (program, regions, Hike_kb.with_attribution facts ~spec ~escape_roots)
  in
  let program, facts =
    Hike_rip.resolve_with_layout ~addr_bits ~slots ~layout program
  in
  { program; facts = { facts with Hike_kb.synth = Hike_synth.table_of_program program } }
