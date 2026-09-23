open Bap.Std
open Bap_main
open Bap_core_theory
open Bil2llvm_env
module Abi = Hike_abi
open Hike_filter


(* Public re-exports; consumers use [Hike.Abi], etc. *)
module Vsa = Hike_vsa
module Diag = Hike_diag
module Cfg_complete = Hike_cfg_complete
module Resolve = Hike_resolve
module Dce = Hike_dce
module Jump = Hike_jump
module Split_mem = Hike_split_mem
module Stack_model = Hike_stack_model
module Sections = Hike_sections
module Image = Hike_image
module Promote = Hike_promote
module Filter = Hike_filter
module Kb = Hike_kb
module Types = Hike_types
module Strip_canaries = Hike_strip_canaries
module Bil2llvm = Bil2llvm

(* The section metadata rows, in the fixed table order; the spans,
   emitter spec, and copy-reloc slots all project from this builder. *)
type sec_meta = {
  sm_type : section_type;
  sm_const : bool;
  sm_lo : int64;
  sm_hi : int64;
  sm_words : int;
  sm_image : Bytes.t option;  (* None = the bss region *)
  sm_copy_relocs : (int * string) list;  (* bss: (byte offset, symbol) *)
}

let bss_region proj =
  let regions = Hike_image.get_named_region_info proj in
  Base.Option.map (Seq.find regions ~f:(fun { info; _ } -> String.equal info ".bss"))
    ~f:(fun { addr; size; _ } ->
      (addr, size, Hike_image.get_copy_relocations proj ~bss_addr:addr ~bss_size:size))

let sec_meta ~(word : int) (proj : Project.t) : sec_meta option list =
  let byte_row section_type ~is_const =
    let llvm_name = section_type_to_string section_type in
    Hike_image.get_section_mem ("." ^ llvm_name) proj |> Hike_image.get_section_data
    |> Base.Option.map ~f:(fun (arr, min_addr, max_addr) ->
        { sm_type = section_type;
          sm_const = is_const;
          sm_lo = Word.to_int64_exn min_addr;
          sm_hi = Word.to_int64_exn max_addr;
          sm_words = (Bytes.length arr + word - 1) / word;
          sm_image = Some arr;
          sm_copy_relocs = [] })
  in
  let bss_row =
    Base.Option.map (bss_region proj) ~f:(fun (addr, size, copy_relocs) ->
        { sm_type = BSS;
            sm_const = false;
            sm_lo = addr;
            sm_hi = Int64.sub (Int64.add addr size) 1L;
            sm_words =
              Int64.to_int
                (Int64.div (Int64.add size (Int64.of_int (word - 1)))
                   (Int64.of_int word));
            sm_image = None;
            sm_copy_relocs = copy_relocs })
  in
  [ byte_row DATA ~is_const:false;
    byte_row RODATA ~is_const:true;
    bss_row;
    byte_row GOT ~is_const:true;
    byte_row GOTPLT ~is_const:true;
    byte_row RODATA_REL ~is_const:true;
    byte_row TEXT ~is_const:true ]

(* Every copy-relocated slot address (absolute): loads and stores at a
   slot go through the slot's relocated pointer. *)
let copy_reloc_slot_addrs proj =
  Base.Option.value
    (Base.Option.map (bss_region proj) ~f:(fun (addr, _, copy_relocs) ->
         Base.List.map copy_relocs
           ~f:(fun (off, _) -> Int64.add addr (Int64.of_int off))))
    ~default:[]

let attrib_spans ~(word : int) (proj : Project.t) : Hike_sections.data_span list =
  let sec_of_type = function
    | DATA -> Hike_stack_model.Data
    | RODATA -> Hike_stack_model.Rodata
    | BSS -> Hike_stack_model.Bss
    | GOT -> Hike_stack_model.Got
    | GOTPLT -> Hike_stack_model.Gotplt
    | RODATA_REL -> Hike_stack_model.Datarelro
    | TEXT -> Hike_stack_model.Text
  in
  Base.List.filter_map (sec_meta ~word proj)
    ~f:(Base.Option.map ~f:(fun m ->
            { Hike_sections.ds_sec = sec_of_type m.sm_type;
              Hike_sections.ds_lo = m.sm_lo;
              Hike_sections.ds_hi = m.sm_hi;
              Hike_sections.ds_slots =
                Base.List.map m.sm_copy_relocs ~f:(fun (off, _) ->
                    Int64.add m.sm_lo (Int64.of_int off)) }))

(* The emitter's section spec; a [whole] entry (id, lo, hi) is a span
   served whole — the section's own image global is the id's storage. *)
let section_spec_of ~(word : int) ~(comps : Hike_stack_model.sec_comp list)
    ~(whole : (int * int64 * int64) list) (proj : Project.t) :
    Bil2llvm.section_spec =
  let spec_section (m : sec_meta) =
    match m.sm_image with
    | Some arr ->
        Sec_bytes
          { si_type = m.sm_type;
            si_lo = m.sm_lo;
            si_hi = m.sm_hi;
            si_words = m.sm_words;
            si_const = m.sm_const;
            si_image = arr }
    | None ->
        Sec_bss
          { si_lo = m.sm_lo;
            si_hi = m.sm_hi;
            si_words = m.sm_words;
            si_copy_relocs = m.sm_copy_relocs }
  in
  { spec_comps = comps;
    spec_whole = whole;
    spec_word = word;
    spec_sections =
      Base.List.map (sec_meta ~word proj)
        ~f:(Base.Option.map ~f:spec_section) }


let section_spec_stash : Bil2llvm.section_spec option ref = ref None

let convert_binary output_program proj =
  let llvm_ctx = Llvm.create_context () in
  let llvm_module = Llvm.create_module llvm_ctx "Convlir" in
  let target = Project.target proj in
  let ptrsize = Theory.Target.bits target in
  let word = ptrsize / 8 in
  let spec =
    match !section_spec_stash with
    | Some spec when spec.Bil2llvm.spec_word = word -> spec
    | _ ->
        (* No attribution ran: the sections emit with no components. *)
        section_spec_of ~word ~comps:[] ~whole:[] proj
  in
  let copy_reloc_addrs_val = copy_reloc_slot_addrs proj in
  let symtab_val = Some (Project.symbols proj) in
  Bil2llvm.emit_program llvm_ctx llvm_module
    ~target ~ptrsize
    ~symtab:symtab_val
    ~copy_relocs:copy_reloc_addrs_val
    spec (Project.program proj);
  Llvm.print_module output_program llvm_module;
  Llvm.dispose_module llvm_module;
  Llvm.dispose_context llvm_ctx

let output =
  Extension.Configuration.parameter ~aliases:[ "o"; "output" ]
    Extension.Type.("output file" %: string)
    "output-file" ~doc:"File to output LLVM IR"

(* Registers the pass and returns its name for the next link's deps:
   the chain is linear, each pass depending on its predecessor. *)
let chain ~name ~prev run =
  Project.register_pass ~name ~deps:[ "hike-" ^ prev ] ~runonce:true run;
  name

let map_subs f proj =
  Project.map_program proj ~f:(fun prog -> Term.map sub_t prog ~f)

let pass_filter proj =
  filter_subs proj

let pass_jump proj = map_subs (Hike_jump.compile_sub (Project.target proj)) proj

let pass_split_mem proj = Project.map_program proj ~f:Hike_split_mem.normalize

let pass_vsa proj =
  let target = Project.target proj in
  (* Image-backed loads are sound only where the runtime content IS
     the static image: .rodata is read-only and a valid PIE never
     relocates it (relocated data lands in .data.rel.ro). *)
  let images =
    Hike_image.get_section_mem ("." ^ section_type_to_string RODATA) proj
    |> Hike_image.get_section_data
    |> Base.Option.map ~f:(fun (arr, min_addr, max_addr) ->
           [ { Cbat_vsa.img_lo = Word.to_int64_exn min_addr;
               img_hi = Word.to_int64_exn max_addr;
               img_bytes = arr } ])
    |> Base.Option.value ~default:[]
  in
  (* The re-lift seam: decode and lift the case body at a dispatch word
     the lift never made a block.  The view starts at the word so the
     body's first block is aligned there; only the blocks reachable from
     it are kept (the sweep's tail past the terminator is dropped). *)
  let lift_at (a : Addr.t) : blk term list option =
    match Seq.to_list (Memmap.lookup (Project.memory proj) a) with
    | [] -> None
    | (seg, _) :: _ -> (
        let view = Memory.view_exn ~from:a seg in
        match Disasm_expert.Recursive.run (Project.arch proj) view with
        | Error _ -> None
        | Ok rec_t ->
          let cfg = Disasm_expert.Recursive.cfg rec_t in
          let root =
            Graphs.Cfg.nodes cfg
            |> Seq.find ~f:(fun b -> Addr.equal (Block.addr b) a)
          in
          Base.Option.map root ~f:(fun root ->
              let nodes =
                Graphlib.Std.Graphlib.fold_reachable (module Graphs.Cfg) cfg
                  ~init:[] ~f:(fun acc n -> n :: acc) root
              in
              let others =
                Base.List.filter nodes ~f:(fun n ->
                    not (Addr.equal (Block.addr n) a))
              in
              Base.List.concat_map (root :: others) ~f:(Blk.lift cfg)))
  in
  (* The run's block-address map, read off the terms at this boundary:
     each block's own address stamp.  A block the lift created unnamed
     carries no stamp and names no case entry. *)
  let block_addrs =
    Term.enum sub_t (Project.program proj)
    |> Seq.concat_map ~f:(Term.enum blk_t)
    |> Seq.filter_map ~f:(fun b ->
           Base.Option.map (Term.get_attr b address)
             ~f:(fun a -> (a, Term.tid b)))
    |> Seq.to_list
    |> Core.Map.of_alist_exn (module Addr)
  in
  let written =
    Hike_vsa.kill_summaries ~abi:(Hike_abi.of_target target)
      (Project.program proj)
  in
  let subs_acc, block_addrs =
    Term.enum sub_t (Project.program proj)
    |> Seq.fold ~init:(Tid.Map.empty, block_addrs)
         ~f:(fun (acc, block_addrs) sub ->
        Option.value
          (Base.Option.map
             (Hike_vsa.fixpoint target
                ~prog:(Project.program proj)
                ~symtab:(Some (Project.symbols proj)) ~images ~written
                ~lift_at ~block_addrs sub)
             ~f:(fun (envs, sub', block_addrs') ->
               (Core.Map.set acc ~key:(Term.tid sub) ~data:(envs, sub'),
                block_addrs')))
          ~default:(acc, block_addrs))
  in
  let all_envs =
    Core.Map.fold subs_acc ~init:Tid.Map.empty
      ~f:(fun ~key:_ ~data:(envs, _) m ->
        Core.Map.fold envs ~init:m
          ~f:(fun ~key ~data m' -> Core.Map.set m' ~key ~data))
  in
  Hike_kb.install
    (Hike_kb.build ~block_envs:all_envs ~block_addrs ~target);
  (* The rewritten subs are the program from here on. *)
  Project.map_program proj ~f:(fun prog ->
      Term.map sub_t prog ~f:(fun sub ->
          Option.value (Base.Option.map (Core.Map.find subs_acc (Term.tid sub)) ~f:snd)
            ~default:sub))

(* The canary strip runs before the fission: a proven canary
   composition is deleted before emission. *)
let pass_strip_canaries proj =
  let facts = Hike_kb.facts () in
  let names =
    Term.enum sub_t (Project.program proj)
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m s ->
        Core.Map.set m ~key:(Term.tid s) ~data:(Sub.name s))
  in
  map_subs (Hike_strip_canaries.strip_sub ~facts ~names) proj
(* The sections pass; the emitter spec reaches the emitter through the
   run-scoped stash (the pass registry has no return channel). *)
let pass_attrib proj =
  let facts = Hike_kb.facts () in
  let target = facts.target in
  let word = Theory.Target.bits target / 8 in
  let spans = attrib_spans ~word proj in
  let dyn_allocs =
    Term.enum sub_t (Project.program proj)
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m sub ->
           Core.Map.set m ~key:(Term.tid sub)
             ~data:(Hike_promote.dynamic_alloc_tids_of ~facts sub))
  in
  Project.map_program proj ~f:(fun prog ->
      let prog =
        Term.map sub_t prog ~f:(fun sub ->
            Hike_stack_model.stamp_dyn_allocs
              ~dynamic_alloc_tids:(Core.Map.find dyn_allocs (Term.tid sub)
                                   |> Option.value ~default:Tid.Set.empty)
              sub)
      in
      let ctx =
        Hike_sections.attribute ~facts ~word ~entry:Hike_stack_model.segment_base
          ~spans prog
      in
      Term.map sub_t prog ~f:(Hike_sections.stamp_tags ctx)
      |> Hike_promote.rewrite_program ~word ~entry:Hike_stack_model.segment_base
            ~facts ~symtab:(Some (Project.symbols proj)) ~spans
            ~ctx
      |> fun prog ->
        (* The DCE's load roots are the vars the rewrite created; its
           escape roots are the storages carrying identity members. *)
        section_spec_stash :=
          Some
            (section_spec_of ~word
               ~comps:(Hike_sections.global_comps_of ~word ~spans ctx)
               ~whole:(Hike_sections.whole_comps_of ~word ~spans ctx)
               proj);
        Term.map sub_t prog ~f:(fun sub ->
            let roots =
              Core.Map.find ctx.Hike_sections.sub_trees (Term.tid sub)
              |> Option.value ~default:Hike_sections.Tree.empty
              |> Hike_sections.escape_roots_of_tree
            in
            Hike_dce.dce ~roots ~target sub))

let pass_convlir ~output proj = convert_binary output proj

let pass_types proj = Hike_types.run proj

let () =
  Extension.declare (fun ctx ->
      let output_file = Extension.Configuration.get ctx output in
      section_spec_stash := None;
      Project.register_pass ~name:"filter" ~runonce:true pass_filter;
      let jump = chain ~name:"jump" ~prev:"filter" pass_jump in
      let split_mem = chain ~name:"split-mem" ~prev:jump pass_split_mem in
      let vsa = chain ~name:"vsa" ~prev:split_mem pass_vsa in
      let strip_canaries =
        chain ~name:"strip-canaries" ~prev:vsa pass_strip_canaries
      in
      let sections = chain ~name:"sections" ~prev:strip_canaries pass_attrib in
      let types = chain ~name:"types" ~prev:sections pass_types in
      Project.register_pass' ~name:"convlir" ~runonce:true
        ~deps:[ "hike-" ^ types ]
        (pass_convlir ~output:output_file);
      Ok ())
