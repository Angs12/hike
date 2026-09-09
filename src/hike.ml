open Bap.Std
open Bap_main
open Bap_core_theory
open Convutils
open Hike_abi
module Abi = Hike_abi
open Hike_filter
open Hike_sections


(* Public re-exports; consumers use [Hike.Abi], etc. *)
module Vsa = Hike_vsa
module Dce = Hike_dce
module Stack_model = Hike_stack_model
module Stack_to_locals = Hike_stack_to_locals
module Kb = Hike_kb
module Convutils = Convutils
module Bil2llvm = Bil2llvm

(* Setup and filter form their own pass. *)

(* Re-exported for the seam's direct fixture tests (see hike.mli). *)
let copy_reloc_slots = Hike_sections.copy_reloc_slots

let setup proj =
  let target = Project.target proj in
  (* Forwards the address width. *)
  Hike_vsa.set_addr_bits (addr_size_bits target)

let convert_binary output_program proj =
  let llvm_ctx = Llvm.create_context () in
  let llvm_module = Llvm.create_module llvm_ctx "Convlir" in
  setup proj;
  let target = Project.target proj in
  let ptrsize = Theory.Target.bits target in
  let regions = get_named_region_info proj in
  (* Pass 1: data-section globals. *)
  let mk_section section_type ~is_const =
    let llvm_name = section_type_to_string section_type in
    let name = "." ^ llvm_name in
    get_section_mem name proj |> get_section_data
    |> Option.map (fun (arr, min_addr, max_addr) ->
        let base =
          Bil2llvm.create_section_global llvm_ctx llvm_module
            (Array.length arr) llvm_name ~is_const
        in
        (arr, min_addr, max_addr, base))
  in
  let data_section = mk_section DATA ~is_const:false in
  let rodata_section = mk_section RODATA ~is_const:true in
  let bss_region =
    Seq.find regions ~f:(fun { info; _ } -> String.equal info ".bss")
  in
  let copy_relocs =
    match bss_region with
    | Some { addr; size; _ } ->
        get_copy_relocations proj ~bss_addr:addr ~bss_size:size
    | None -> []
  in
  let bss_section =
    create_uninitialized_section llvm_ctx llvm_module proj BSS regions
      copy_relocs
  in
  let copy_reloc_addrs_val =
    match bss_region with
    | Some { addr; _ } ->
        copy_reloc_slots ~bss_addr:addr copy_relocs (Project.program proj)
    | None -> []
  in
  let got_section = mk_section GOT ~is_const:true in
  let gotplt_section = mk_section GOTPLT ~is_const:true in
  let rodata_rel_section = mk_section RODATA_REL ~is_const:true in
  (* Stashes .text bytes for compile-time loads. *)
  let text_section = mk_section TEXT ~is_const:true in
  let text_section_val =
    Base.Option.map text_section ~f:(fun (arr, min, max, _base) ->
      (arr, Word.to_int64_exn min, Word.to_int64_exn max))
  in
  (* Maps native function addresses to lifted functions. *)
  let symtab_val = Some (Project.symbols proj) in
  (* Maps native section addresses to lifted globals. *)
  let sec_lo_hi_base sec =
    Base.Option.map sec ~f:(fun (arr, min_addr, max_addr, base) ->
        let lo = Word.to_int64_exn min_addr in
        let hi = Word.to_int64_exn max_addr in
        ignore arr;
        (lo, hi, base))
  in
  let bss_lo_hi_base =
    match bss_section with
    | Some { base; min_addr; max_addr; _ } ->
        Some
          (Word.to_int64_exn min_addr, Word.to_int64_exn max_addr, base)
    | None -> None
  in
  let section_remap_val =
    Base.List.filter_map
      [
        sec_lo_hi_base data_section;
        sec_lo_hi_base rodata_section;
        bss_lo_hi_base;
        sec_lo_hi_base got_section;
        sec_lo_hi_base gotplt_section;
        sec_lo_hi_base rodata_rel_section;
      ]
      ~f:(fun x -> x)
  in
  let section_of_sec sec =
    Base.Option.map sec ~f:(fun (_, min_addr, max_addr, base) ->
        { base; min_addr; max_addr })
  in
  let section_list =
    Base.List.filter_mapi
      ~f:(fun i section ->
        match section with
        | None ->
            Hike_diag.warn "section %d was not found in binary" i;
            None
        | Some s -> Some s)
      [
        section_of_sec data_section;
        section_of_sec rodata_section;
        bss_section;
        section_of_sec got_section;
        section_of_sec gotplt_section;
        section_of_sec rodata_rel_section;
      ]
  in
  let ctx =
    (* Only the section facts are read here; emit_program builds its own
       full context from the seam arguments. *)
    {
      (Convutils.empty_emit_ctx ()) with
      Convutils.symtab = symtab_val;
      text_section = text_section_val;
      section_remap = section_remap_val;
      copy_relocs = copy_reloc_addrs_val;
    }
  in
  Bil2llvm.emit_program llvm_ctx llvm_module
    ~target ~ptrsize
    ~symtab:symtab_val
    ~text_section:text_section_val
    ~section_remap:section_remap_val
    ~copy_relocs:copy_reloc_addrs_val
    section_list (Project.program proj);
  (* Pass 2: data-section initializers — AFTER [emit_program]. Every
     8-byte word renders through [remap_native_addr]: the symtab arm
     (a word that names a lifted sub renders as [ptrtoint @sub]) needs
     the sub's LLVM function to EXIST in the module, so populating the
     initializers before the emission left that arm structurally dead
     and rendered every function-valued relocated addend as the raw
     input-world vaddr (the fptr_table class: an indirect call through
     a data table landed on an address meaningless in the lifted
     executable). One rule for every section, no per-word special
     cases; words that name no lifted world keep the identity (raw). *)
  Base.List.iter
    [
      data_section;
      rodata_section;
      got_section;
      gotplt_section;
      rodata_rel_section;
    ]
    ~f:(fun sec ->
        Base.Option.iter sec ~f:(fun (arr, min_addr, _, base) ->
            Bil2llvm.set_section_initializer ctx llvm_ctx llvm_module base arr
              (Word.to_int64_exn min_addr)));
  Llvm.print_module output_program llvm_module;
  Llvm.dispose_module llvm_module;
  Llvm.dispose_context llvm_ctx

let output =
  Extension.Configuration.parameter ~aliases:[ "o"; "output" ]
    Extension.Type.("output file" %: string)
    "output-file" ~doc:"File to output LLVM IR"

let () =
  Extension.declare (fun ctx ->
      let output_file = Extension.Configuration.get ctx output in
      Project.register_pass ~name:"filter" ~runonce:true
        (fun proj ->
           setup proj;
           (* Setup and filter run first. *)
           filter_subs proj);
      (* VSA tag pass; depends on the filter only (spec §2.1). *)
      Project.register_pass ~name:"vsa" ~deps:[ "hike-filter" ] ~runonce:true
        (fun proj ->
           (* Per-sub computation is pure; the map folds before the one
              KB write (no monad-iter-plus-ref shape). *)
           let acc =
             Term.enum sub_t (Project.program proj)
             |> Seq.fold ~init:Tid.Map.empty ~f:(fun acc sub ->
                 (* Computes tags and plan on the pre-rewrite sub. *)
                 let info =
                   Hike_vsa.offsets_of_sub (Project.target proj)
                     (sp (Project.target proj)) sub
                 in
#ifdef VSA_DEBUG
                 Printf.eprintf "hike: vsa: %s -> %d tag(s)\n"
                   (Sub.name sub) (Core.Map.length info.Convutils.offsets);
#endif
                 Core.Map.set acc ~key:(Term.tid sub) ~data:info)
           in
           (* Provides all tags in one write. *)
           Hike_kb.provide acc;
           proj);
      (* Rewrite pass: the fission rewrite and its DCE — one registration
         (the DCE's load-roots rule is defined over the vars the rewrite
         creates; neither runs without the other). *)
       Project.register_pass ~name:"stack-to-locals" ~runonce:true
        ~deps:[ "hike-vsa" ]
        (fun proj ->
           let target = Project.target proj in
           let proj =
             Project.map_program proj ~f:(fun prog ->
                 Term.map sub_t prog
                   ~f:(Hike_stack_to_locals.stack_to_locals
                         target (sp target)))
           in
           let proj =
             Project.map_program proj ~f:(fun prog ->
                 Term.map sub_t prog ~f:(Hike_dce.dce ~target))
           in
#ifdef VSA_DEBUG
           Core.Map.iter (Hike_kb.vsa_info ()) ~f:(fun info ->
               Printf.eprintf "hike: stl: %d tag(s)\n"
                 (Core.Map.length info.Convutils.offsets));
#endif
           proj);
      Project.register_pass' ~name:"convlir" ~runonce:true
        ~deps:[ "hike-stack-to-locals" ]
        (convert_binary output_file);
      Ok ())
