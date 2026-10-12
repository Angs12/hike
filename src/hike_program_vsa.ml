(* Shared preparation and solving for discovery and final analysis. *)
open Bap.Std
open Bap_core_theory

type context = {
  target : Theory.Target.t;
  images : Cbat_vsa.section_image list;
  linker_slots : Core.Int64.Set.t;
  reserved_slots : Core.Int64.Set.t;
  text_range : (int64 * int64) option;
  data_spans : Hike_sections.data_span list;
}

type solution = {
  program : program term;
  subs : ((Cbat_vsa.AI.t * Cbat_vsa.AI.t) Tid.Map.t * sub term) Tid.Map.t;
  block_addrs : Tid.t Addr.Map.t;
  sub_addrs : Tid.t Addr.Map.t;
  lookup : int64 -> Tid.t option;
}

let prepare proj =
  let target = Project.target proj in
  let range_of_section name =
    match
      Hike_image.get_section_mem name proj |> Hike_image.get_section_data
    with
    | Some (_, lo, hi) -> Some (Word.to_int64_exn lo, Word.to_int64_exn hi)
    | None -> None
  in
  (* The linker-owned slot addresses: a slot's value the dynamic linker
     writes at startup — the file bytes there are not a value, and a
     transfer whose target reads one leaves the program.  The reserved
     head of .got.plt (the ABI's three words: the _DYNAMIC pointer, the
     link-map, the resolver) is the loader's own — no relocation names
     it, and the value is the loader's. *)
  let linker_slots =
    let reserved =
      match range_of_section ".got.plt" with
      | Some (lo, _) ->
        let w =
          Int64.of_int (Hike_abi.word_bits (Hike_abi.of_target target) / 8)
        in
        [ lo; Int64.add lo w; Int64.add lo (Int64.mul 2L w) ]
      | None -> []
    in
    Hike_image.external_references proj
    |> Base.List.map ~f:fst
    |> Base.List.append reserved
    |> Core.Int64.Set.of_list
  in
  (* The ABI-reserved .got.plt head: the dynamic linker's own protocol
     slots (the link map and the resolver entry).  A sub whose exits
     transfer through one is the loader's machinery — the resolver
     head — whatever calls reach it. *)
  let reserved_slots =
    match range_of_section ".got.plt" with
    | Some (lo, _) ->
      let w =
        Int64.of_int (Hike_abi.word_bits (Hike_abi.of_target target) / 8)
      in
      Core.Int64.Set.of_list [ lo; Int64.add lo w; Int64.add lo (Int64.mul 2L w) ]
    | None -> Core.Int64.Set.empty
  in
  (* Image-backed loads are sound only where the runtime content is
     known and fixed: never-written memory only, a relocated word as its
     RELATIVE runtime value, and a linker-owned slot's word as no value
     at all. *)
  let images =
    Hike_image.get_section_images proj
      ~page:(Hike_abi.of_target target).Hike_abi.page_size
    |> Base.List.map ~f:(fun (img_bytes, img_lo, img_hi) ->
           { Cbat_vsa.img_lo;
             img_hi;
             img_bytes;
             img_slots =
               Core.Set.filter linker_slots
                 ~f:(fun a ->
                     Int64.compare a img_lo >= 0
                     && Int64.compare a img_hi <= 0) })
  in
  let text_range = range_of_section ".text" in
  let data_spans =
    Hike_sections.attrib_spans
      ~meta:(Hike_sections.sec_meta
               ~word:(Hike_abi.of_target target).Hike_abi.word proj)
  in
  Hike_origin.Regions.install
    (Base.List.map data_spans ~f:(fun span ->
         (span.Hike_sections.ds_sec, span.ds_lo, span.ds_hi)));
  { target; images; linker_slots; reserved_slots; text_range; data_spans }

let normalize context program =
  let addr_bits = Hike_abi.word_bits (Hike_abi.of_target context.target) in
  let program = Hike_atomic.normalize ~addr_bits program in
  Term.map sub_t program ~f:(Hike_jump.compile_sub context.target)
  |> Hike_split_mem.normalize |> Hike_coerce.coerce_program
  |> Hike_fp.run_program

let solve context proj ~noreturn program =
  let program = normalize context program in
  let { target; images; linker_slots; data_spans; _ } = context in
  let block_addrs =
    Term.enum sub_t program
    |> Seq.concat_map ~f:(Term.enum blk_t)
    |> Seq.filter_map ~f:(fun b ->
           Base.Option.map (Term.get_attr b address)
             ~f:(fun a -> (a, Term.tid b)))
    |> Seq.to_list
    |> Core.Map.of_alist_exn (module Addr)
  in
  let entry_addrs =
    Term.enum sub_t program
    |> Seq.fold ~init:Core.Int64.Map.empty ~f:(fun m s ->
           match Term.first blk_t s with
           | Some b -> (
             match Term.get_attr b address with
             | Some a ->
               Core.Map.set m ~key:(Word.to_int64_exn a)
                 ~data:(Term.tid s)
             | None -> m)
           | None -> m)
  in
  let named =
    Hike_resolve.symtab_lookup
      ~symtab:(Some (Project.symbols proj))
      ~table:(Hike_resolve.name_table_of program)
      ~addr_bits:(Hike_abi.addr_size_bits target)
  in
  let lookup v =
    match named v with
    | Some t -> Some t
    | None -> Core.Map.find entry_addrs v
  in
  (* The rip tag is read once, here: a tagged literal naming a function
     entry or a data section becomes a module address, so every
     denotation of it carries its [Rip] anchor. *)
  let program =
    let is_address a =
      Option.is_some (lookup a)
      || Base.List.exists data_spans ~f:(fun span ->
          Int64.unsigned_compare span.Hike_sections.ds_lo a <= 0
          && Int64.unsigned_compare a span.ds_hi <= 0)
    in
    Hike_rip.prepare_program ~addr_bits:(Hike_abi.addr_size_bits target)
      ~is_address program
  in
  let sub_addrs =
    Core.Map.fold block_addrs ~init:Addr.Map.empty
      ~f:(fun ~key:addr ~data:_ m ->
        match lookup (Word.to_int64_exn addr) with
        | Some sub -> Core.Map.set m ~key:addr ~data:sub
        | None -> m)
  in
  let written =
    Hike_vsa.kill_summaries ~abi:(Hike_abi.of_target target) program
  in
  let subs_acc, block_addrs =
    Term.enum sub_t program
    |> Seq.fold ~init:(Tid.Map.empty, block_addrs)
         ~f:(fun (acc, ba) sub ->
           let envs, sub', ba' =
             Hike_vsa.fixpoint target ~lookup ~sub_addrs ~images
               ~written ~foreign_slots:linker_slots
               ~noreturn
               ~block_addrs:ba sub
           in
           (Core.Map.set acc ~key:(Term.tid sub) ~data:(envs, sub'),
            ba'))
  in
  let program =
    Term.map sub_t program ~f:(fun s ->
        match Core.Map.find subs_acc (Term.tid s) with
        | Some (_, s') -> s'
        | None -> s)
  in
  { program; subs = subs_acc; block_addrs; sub_addrs; lookup }

let install context solution =
  let envs =
    Core.Map.fold solution.subs ~init:Tid.Map.empty
      ~f:(fun ~key:_ ~data:(envs, _) acc ->
        Core.Map.fold envs ~init:acc
          ~f:(fun ~key ~data acc -> Core.Map.set acc ~key ~data))
  in
  Hike_kb.install
    { (Hike_kb.build ~block_envs:envs ~block_addrs:solution.block_addrs
         ~target:context.target ~lookup:solution.lookup) with
      Hike_kb.sub_addrs = solution.sub_addrs;
      images = context.images; foreign_slots = context.linker_slots }

let run context proj program =
  let rec settle remaining noreturn =
    let solution = solve context proj ~noreturn program in
    let next = Hike_noreturn.classify ~target:context.target solution.program in
    if Core.Set.equal noreturn next then solution
    else if remaining = 0 then begin
      Hike_diag.warn "vsa: noreturn analysis stopped at its round budget";
      solution
    end else settle (remaining - 1) next
  in
  settle 63 (Hike_noreturn.classify ~target:context.target program)
