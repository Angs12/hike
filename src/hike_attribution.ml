open Bap.Std

type result = {
  program : program term;
  facts : Hike_kb.facts;
}

let run ~(facts : Hike_kb.facts) ~(word : int) ~(entry : int64)
    ~(spans : Hike_sections.data_span list)
    ~(meta : Hike_sections.sec_meta option list)
    ~(relative : (int64 * int64) list) ~(externals : (int64 * string) list)
    (program : program term) : result =
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
      ~whole:(Hike_sections.whole_comps_of sections) ~meta ~relative
      ~externals
  in
  let arities =
    Core.Map.map sections.sub_trees
      ~f:(Hike_promote.slot_arity ~word ~entry)
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
  { program;
    facts = Hike_kb.with_attribution facts ~spec ~escape_roots }
