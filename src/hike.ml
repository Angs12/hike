open Bap.Std
open Bap_main
open Bap_core_theory
open Bil2llvm_env
open Hike_abi
module Abi = Hike_abi
open Hike_filter
open Hike_sections


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
module Kb = Hike_kb
module Strip_canaries = Hike_strip_canaries
module Bil2llvm = Bil2llvm

(* Setup and filter form their own pass. *)

(* The ONE section metadata builder: every reserved data section of
   the binary, in the fixed table order (Data, Rodata, Bss, Got,
   Gotplt, Datarelro) — the attribution spans, the emitter spec's
   input sections, and the copy-reloc slot set all project from it.
   [word] is the target's word size in bytes — the section word
   grid. *)
type sec_meta = {
  sm_type : section_type;       (* Bss = the zeroed region *)
  sm_const : bool;
  sm_lo : int64;
  sm_hi : int64;
  sm_words : int;
  sm_image : int array option;  (* None = the bss region *)
  sm_copy_relocs : (int * string) list;  (* bss: (byte offset, symbol) *)
}

let bss_region proj =
  let regions = get_named_region_info proj in
  match Seq.find regions ~f:(fun { info; _ } -> String.equal info ".bss") with
  | None -> None
  | Some { addr; size; _ } ->
    Some (addr, size, get_copy_relocations proj ~bss_addr:addr ~bss_size:size)

let sec_meta ~(word : int) (proj : Project.t) : sec_meta option list =
  let byte_row section_type ~is_const =
    let llvm_name = section_type_to_string section_type in
    get_section_mem ("." ^ llvm_name) proj |> get_section_data
    |> Base.Option.map ~f:(fun (arr, min_addr, max_addr) ->
        { sm_type = section_type;
          sm_const = is_const;
          sm_lo = Word.to_int64_exn min_addr;
          sm_hi = Word.to_int64_exn max_addr;
          sm_words = (Array.length arr + word - 1) / word;
          sm_image = Some arr;
          sm_copy_relocs = [] })
  in
  let bss_row =
    match bss_region proj with
    | None -> None
    | Some (addr, size, copy_relocs) ->
        Some
          { sm_type = BSS;
            sm_const = false;
            sm_lo = addr;
            sm_hi = Int64.sub (Int64.add addr size) 1L;
            sm_words =
              Int64.to_int
                (Int64.div (Int64.add size (Int64.of_int (word - 1)))
                   (Int64.of_int word));
            sm_image = None;
            sm_copy_relocs = copy_relocs }
  in
  [ byte_row DATA ~is_const:false;
    byte_row RODATA ~is_const:true;
    bss_row;
    byte_row GOT ~is_const:true;
    byte_row GOTPLT ~is_const:true;
    byte_row RODATA_REL ~is_const:true;
    byte_row TEXT ~is_const:true ]

(* Every copy-relocated slot address (absolute) — the through lane's
   slot set, unfiltered: loads AND stores at a slot go through the
   slot's relocated pointer. *)
let copy_reloc_slot_addrs proj =
  match bss_region proj with
  | Some (addr, _, copy_relocs) ->
      Base.List.map copy_relocs
        ~f:(fun (off, _) -> Int64.add addr (Int64.of_int off))
  | None -> []

(* The attribution's data spans, from the section metadata: each
   reserved span's section, native bounds, and copy-relocated slot
   addresses. *)
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

(* The emitter's section spec: the images from the project, the Global
   components from the finalized data tree, and the spans served whole
   (each (id, lo, hi) — the section's own image global is the id's
   storage), all values threaded from the attribution. *)
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
  (* The target's word size in bytes — the section word grid's cell. *)
  let word = ptrsize / 8 in
  let spec =
    match !section_spec_stash with
    | Some spec when spec.Bil2llvm.spec_word = word -> spec
    | _ ->
        (* No attribution ran (a probe calling convert_binary alone):
           the sections emit with no components — every span stays the
           identity array. *)
        section_spec_of ~word ~comps:[] ~whole:[] proj
  in
  let copy_reloc_addrs_val = copy_reloc_slot_addrs proj in
  (* Maps native function addresses to lifted functions. *)
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

(* The pass chain is linear: every pass runs once and depends on its
   predecessor. [chain] registers the pass and returns its bare name
   for the next link's deps. *)
let chain ~name ~prev run =
  Project.register_pass ~name ~deps:[ "hike-" ^ prev ] ~runonce:true run;
  name

(* Maps every sub of the project's program with [f]. *)
let map_subs f proj =
  Project.map_program proj ~f:(fun prog -> Term.map sub_t prog ~f)

(* The pass bodies in chain order; the plugin registers each as a
   pass with its predecessor as dependency. *)
let pass_filter proj =
  (* The filter runs first; the analysis entries self-arm their address
     width from the targets they carry. *)
  filter_subs proj

let pass_jump proj = map_subs (Hike_jump.compile_sub (Project.target proj)) proj

let pass_split_mem proj = Project.map_program proj ~f:Hike_split_mem.normalize

let pass_vsa proj =
  let target = Project.target proj in
  (* Image-backed loads read only sections whose runtime
     content IS the static image — .rodata: read-only, and a
     valid PIE never relocates it (relocated data lands in
     .data.rel.ro, whose image bytes differ from runtime). *)
  let images =
    get_section_mem ("." ^ section_type_to_string RODATA) proj
    |> get_section_data
    |> Base.Option.map ~f:(fun (arr, min_addr, max_addr) ->
           [ { Cbat_vsa.img_lo = Word.to_int64_exn min_addr;
               img_hi = Word.to_int64_exn max_addr;
               img_bytes = arr } ])
    |> Base.Option.value ~default:[]
  in
  (* The run's block-address map: every lifted block's own address
     stamp — the tid<->address bijection the lift establishes — read
     off the terms at this boundary.  Blocks the lift created unnamed
     carry no stamp and name no case entry. *)
  let block_addrs =
    Term.enum sub_t (Project.program proj)
    |> Seq.concat_map ~f:(Term.enum blk_t)
    |> Seq.filter_map ~f:(fun b ->
           Base.Option.map (Term.get_attr b address)
             ~f:(fun a -> (a, Term.tid b)))
    |> Seq.to_list
    |> Core.Map.of_alist_exn (module Addr)
  in
  Hike_kb.install_block_addrs block_addrs;
  (* The producer, composed per sub: the fixpoint's products are the
     block environments (the one cross-pass fact) and the REWRITTEN
     SUB (the CFG completion's terms). *)
  let acc =
    Term.enum sub_t (Project.program proj)
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun acc sub ->
        match
          Hike_vsa.fixpoint target (sp target)
            ~prog:(Project.program proj) ~images sub
        with
        | None -> acc
        | Some (envs, sub') ->
          Core.Map.set acc ~key:(Term.tid sub) ~data:(envs, sub'))
  in
  let all_envs =
    Core.Map.fold acc ~init:Tid.Map.empty
      ~f:(fun ~key:_ ~data:(envs, _) m ->
        Core.Map.fold envs ~init:m
          ~f:(fun ~key ~data m' -> Core.Map.set m' ~key ~data))
  in
  (* The run's table installs in one write. *)
  Hike_kb.install_run ~block_envs:all_envs;
  (* The rewritten subs are the program from here on; the
     dynamic-allocation stamp, the promotion, the storage rewrite, and
     the layout are the attribution pass's (over the finalized
     trees). *)
  Project.map_program proj ~f:(fun prog ->
      Term.map sub_t prog ~f:(fun sub ->
          match Core.Map.find acc (Term.tid sub) with
          | Some (_, sub') -> sub'
          | None -> sub))

(* The canary strip: the proven canary composition (the TLS read, the
   same-cell store/reload, the not-equal edge to __stack_chk_fail)
   deletes before the fission — the emission loses the TLS reads, the
   second exit, and the foreign fail-call shape; the FS/anchor render
   stays in the emitter for the residual reads. *)
let pass_strip_canaries proj =
  let names =
    Term.enum sub_t (Project.program proj)
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m s ->
        Core.Map.set m ~key:(Term.tid s) ~data:(Sub.name s))
  in
  map_subs
    (Hike_strip_canaries.strip_sub
       ~abi:(Hike_abi.of_target (Project.target proj))
       ~names)
    proj
(* The sections pass: the ownership trees and slim tags, then the
   promotion, the storage rewrite (Stack, Args, and Global), the DCE,
   and the emitter spec — the ctx is a value threaded through this one
   pass; the spec threads to the emitter as a value through the one
   run-scoped stash below (the pass registry has no return channel). *)
let pass_attrib proj =
  let target = Project.target proj in
  let abi = Hike_abi.of_target target in
  let word = Theory.Target.bits target / 8 in
  let sp = sp target in
  let spans = attrib_spans ~word proj in
  let dyn_allocs =
    Term.enum sub_t (Project.program proj)
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m sub ->
           Core.Map.set m ~key:(Term.tid sub)
             ~data:
              (Hike_sections.dynamic_alloc_tids_of ~sp
                 ~denote:Hike_vsa.denote_exp_at sub))
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
        Hike_sections.attribute ~word ~entry:Hike_stack_model.segment_base ~abi
          ~spans ~denote:Hike_vsa.denote_exp_at prog
      in
      Term.map sub_t prog ~f:(Hike_sections.stamp_tags ctx)
      |> Hike_sections.rewrite_program ~word ~entry:Hike_stack_model.segment_base
            ~abi ~sp ~symtab:(Some (Project.symbols proj)) ~spans
            ~denote:Hike_vsa.denote_exp_at ~ctx
      |> fun prog ->
        (* The DCE's load roots are the vars the rewrite created; its
           escape roots are the storages carrying identity members; the
           spec's Global components project from the finalized tree. *)
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

(* The registrations mirror the chain order: each pass's deps are its
   predecessor. The DCE and the emitter spec belong to attrib (the DCE's
   load roots are the rewrite's vars). *)
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
      Project.register_pass' ~name:"convlir" ~runonce:true
        ~deps:[ "hike-" ^ sections ]
        (pass_convlir ~output:output_file);
      Ok ())
