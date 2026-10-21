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
  let synth, program = Hike_split_blocks.materialize ~facts program in
  let facts = Hike_kb.with_synth facts synth in
  let addr_bits = Bap_core_theory.Theory.Target.data_addr_size facts.target in
  let synth, program =
    Hike_tls.rewrite_program ~synth ~addr_bits ~tls ~denote:facts.denote program
  in
  let facts = Hike_kb.with_synth facts synth in
  (* A copy-relocated slot's bytes are externally owned: the access keeps
     its absolute address so the emitter's relocation path renders it. *)
  let slots =
    Base.List.concat_map spans ~f:(fun span -> span.Hike_sections.ds_slots)
  in
  let layout ~synth program =
    let facts = Hike_kb.with_synth facts synth in
    let sections =
      Hike_sections.attribute ~facts ~word ~entry ~spans program
    in
    let synth, program =
      Term.map sub_t program ~f:(Hike_sections.stamp_tags sections)
      |> Hike_promote.rewrite_program ~word ~entry ~facts ~spans ~ctx:sections
    in
    let facts = Hike_kb.with_synth facts synth in
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
    (program, regions, synth, Hike_kb.with_attribution facts ~spec)
  in
  let program, synth, facts =
    Hike_rip.resolve_with_layout ~addr_bits ~slots ~synth ~layout program
  in
  { program; facts = Hike_kb.with_synth facts (Hike_synth.restrict_to_program synth program) }
