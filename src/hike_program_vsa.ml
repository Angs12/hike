(* The analysis context of a discovery run and the per-function
   normalization every solve starts from. *)
open Bap.Std
open Bap_core_theory

type context = {
  target : Theory.Target.t;
  images : Cbat_vsa.section_image list;
  linker_slots : Core.Int64.Set.t;
  text_range : (int64 * int64) option;
  data_spans : Hike_sections.data_span list;
  signatures : Hike_signatures.t;
}

let prepare ~signatures proj =
  let target = Project.target proj in
  let abi = Hike_abi.of_target target in
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
          Int64.of_int (Hike_abi.word_bits abi / 8)
        in
        [ lo; Int64.add lo w; Int64.add lo (Int64.mul 2L w) ]
      | None -> []
    in
    Hike_image.external_references proj
    |> Base.List.map ~f:fst
    |> Base.List.append reserved
    |> Core.Int64.Set.of_list
  in
  (* Image-backed loads are sound only where the runtime content is
     known and fixed: never-written memory only, a relocated word as its
     RELATIVE runtime value, and a linker-owned slot's word as no value
     at all. *)
  let images =
    Hike_image.get_section_images proj
      ~page:abi.Hike_abi.page_size
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
               ~word:abi.Hike_abi.word proj)
  in
  Hike_origin.Regions.install
    (Base.List.map data_spans ~f:(fun span ->
         (span.Hike_sections.ds_sec, span.ds_lo, span.ds_hi)));
  let imports =
    Core.String.Map.of_alist_reduce (Hike_image.versioned_imports proj)
      ~f:(fun first _ -> first) in
  let signatures =
    Hike_signatures.create ~target signatures ~imports:(Core.Map.find imports) in
  { target; images; linker_slots; text_range; data_spans; signatures }

let normalize context ~synth program =
  let addr_bits = Hike_abi.word_bits (Hike_abi.of_target context.target) in
  let program = Hike_atomic.normalize ~addr_bits program in
  let cell = ref synth in
  let program =
    Term.map sub_t program ~f:(fun sub ->
        Hike_synth.record cell (fun synth ->
            Hike_jump.compile_sub ~synth context.target sub))
  in
  let synth, program = Hike_split_mem.normalize ~synth:!cell program in
  let program = Hike_coerce.coerce_program program in
  Hike_fp.run_program ~word_bits:addr_bits ~synth program

(* The rip tag is read once, here: a tagged literal naming a function
   entry or a data section becomes a module address, so every
   denotation of it carries its [Rip] anchor. *)
let tag_rip context ~synth ~(is_entry : int64 -> bool) program =
  let is_address a =
    is_entry a
    || Base.List.exists context.data_spans ~f:(fun span ->
        Int64.unsigned_compare span.Hike_sections.ds_lo a <= 0
        && Int64.unsigned_compare a span.ds_hi <= 0)
  in
  Hike_rip.prepare_program ~synth
    ~addr_bits:(Bap_core_theory.Theory.Target.data_addr_size context.target) ~is_address program

(* A transfer that is not a goto (a call, a trap) shares its block with
   other jmps: it moves to a block of its own, entered under its guard, so
   that the results a call defines lie on the call's own edge.  The new
   blocks follow the existing ones, which keeps every implicit
   fall-through. *)
let isolate_block (blk : blk term) : blk term * blk term list =
  let moved = ref [] in
  let is_goto j = match Jmp.kind j with Goto _ -> true | _ -> false in
  let jmps = Term.enum jmp_t blk |> Seq.to_list in
  if Base.List.length jmps < 2 || Base.List.for_all jmps ~f:is_goto then
    (blk, [])
  else
    let blk =
      Term.concat_map jmp_t blk ~f:(fun j ->
          if is_goto j then [ j ]
          else begin
            let own =
              Blk.create ~jmps:[ Jmp.with_cond j (Bil.Int (Word.one 1)) ] ()
            in
            moved := own :: !moved;
            [ Jmp.create_goto ~cond:(Jmp.cond j) (Direct (Term.tid own)) ]
          end)
    in
    (blk, Base.List.rev !moved)

let isolate_transfers (sub : sub term) : sub term =
  let moved = ref [] in
  let sub =
    Term.map blk_t sub ~f:(fun blk ->
        let blk, own = isolate_block blk in
        moved := Base.List.rev_append own !moved;
        blk)
  in
  Base.List.fold (Base.List.rev !moved) ~init:sub ~f:(Term.append blk_t)

(* The function's normalized body in SSA and the table grown by its
   minted vars.  The returns read the ABI's return lanes and the calls the
   machine convention; signing narrows the calls later. *)
let normalize_function context ~synth ~is_entry sub =
  let program = Term.append sub_t (Program.create ()) sub in
  let synth, program = normalize context ~synth program in
  let synth, program = tag_rip context ~synth ~is_entry program in
  let sub = Base.Option.value_exn (Term.first sub_t program) in
  let sub = isolate_transfers sub in
  (sub, synth)

let prepare_function context ~synth ~is_entry sub =
  let sub, synth = normalize_function context ~synth ~is_entry sub in
  let sub = Hike_ssa.ssa_sub ~synth ~target:context.target sub in
  (Hike_dce.dce_sub ~synth ~target:context.target sub, synth)
