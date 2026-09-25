open Bap.Std
open Bap_main
open Bap_core_theory
module Abi = Hike_abi


(* Public re-exports; consumers use [Hike.Abi], etc. *)
module Vsa = Hike_vsa
module Diag = Hike_diag
module Cfg_complete = Hike_cfg_complete
module Resolve = Hike_resolve
module Dce = Hike_dce
module Jump = Hike_jump
module Split_mem = Hike_split_mem
module Coerce = Hike_coerce
module Stack_model = Hike_stack_model
module Def_slots = Hike_def_slots
module Sections = Hike_sections
module Image = Hike_image
module Promote = Hike_promote
module Kb = Hike_kb
module Types = Hike_types
module Strip_canaries = Hike_strip_canaries
module Bil2llvm = Bil2llvm

let convert_binary output_program proj =
  let llvm_ctx = Llvm.create_context () in
  let llvm_module = Llvm.create_module llvm_ctx "Convlir" in
  let target = Project.target proj in
  let abi = Abi.of_target target in
  let word = abi.Abi.word in
  let addr_bits = Theory.Target.bits target in
  let spec =
    match (Hike_kb.facts ()).Hike_kb.spec with
    | Some spec -> spec
    | None ->
        (* No attribution ran: the sections emit with no components. *)
        let meta = Hike_sections.sec_meta ~word proj in
        Hike_sections.section_spec_of ~word ~comps:[] ~whole:[] ~meta
  in
  Bil2llvm.emit_program llvm_ctx llvm_module
    ~target ~addr_bits
    ~symtab:(Some (Project.symbols proj))
    spec (Project.program proj);
  Llvm.print_module output_program llvm_module;
  Llvm.dispose_module llvm_module;
  Llvm.dispose_context llvm_ctx

let output =
  Extension.Configuration.parameter ~aliases:[ "o"; "output" ]
    Extension.Type.("output file" %: string)
    "output-file" ~doc:"File to output LLVM IR"

(* Registers the pass and returns its name for the next link's deps:
   the chain is linear, each pass depending on its predecessor.  [chain']
   is the parameter-passing registrar's twin (the emitting last link). *)
let chain ~name ~prev run =
  Project.register_pass ~name ~deps:[ "hike-" ^ prev ] ~runonce:true run;
  name

let chain' ~name ~prev run =
  Project.register_pass' ~name ~deps:[ "hike-" ^ prev ] ~runonce:true run;
  name

let map_subs f proj =
  Project.map_program proj ~f:(fun prog -> Term.map sub_t prog ~f)

let pass_filter proj = Hike_filter.filter_subs proj

let pass_jump proj = map_subs (Hike_jump.compile_sub (Project.target proj)) proj

let pass_split_mem proj = Project.map_program proj ~f:Hike_split_mem.normalize

(* The one width-coercion point: every later consumer reads uniform widths. *)
let pass_coerce proj = Project.map_program proj ~f:Hike_coerce.coerce_program

let pass_vsa proj =
  let target = Project.target proj in
  (* Image-backed loads are sound only where the runtime content IS
     the static image: .rodata is read-only and a valid PIE never
     relocates it (relocated data lands in .data.rel.ro). *)
  let images =
    Hike_image.get_section_mem
      ("." ^ Hike_stack_model.sec_name Hike_stack_model.Rodata) proj
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
  let lift_at (a : Addr.t) ~(block_addrs : Tid.t Addr.Map.t) :
      blk term list option =
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
              (* A block the run already names is not lifted again; the
                 retarget resolves references to it. *)
              let others =
                Base.List.filter others ~f:(fun n ->
                    not (Core.Map.mem block_addrs (Block.addr n)))
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
  (* The program-wide resolution lookup: one name table for the run. *)
  let lookup =
    Hike_resolve.symtab_lookup ~symtab:(Some (Project.symbols proj))
      ~table:(Hike_resolve.name_table_of (Project.program proj))
  in
  let subs_acc, block_addrs =
    Term.enum sub_t (Project.program proj)
    |> Seq.fold ~init:(Tid.Map.empty, block_addrs)
         ~f:(fun (acc, block_addrs) sub ->
        let envs, sub', block_addrs' =
          Hike_vsa.fixpoint target ~lookup ~images ~written ~lift_at
            ~block_addrs sub
        in
        (Core.Map.set acc ~key:(Term.tid sub) ~data:(envs, sub'), block_addrs'))
  in
  let all_envs =
    Core.Map.fold subs_acc ~init:Tid.Map.empty
      ~f:(fun ~key:_ ~data:(envs, _) m ->
        Core.Map.fold envs ~init:m
          ~f:(fun ~key ~data m' -> Core.Map.set m' ~key ~data))
  in
  Hike_kb.install
    (Hike_kb.build ~block_envs:all_envs ~block_addrs ~target ~lookup);
  (* The rewritten subs are the program from here on. *)
  Project.map_program proj ~f:(fun prog ->
      Term.map sub_t prog ~f:(fun sub ->
          Option.value (Base.Option.map (Core.Map.find subs_acc (Term.tid sub)) ~f:snd)
            ~default:sub))

(* The canary strip runs after the solve, before the attribution: a
   proven canary composition is deleted before emission. *)
let pass_strip_canaries proj =
  let facts = Hike_kb.facts () in
  let names =
    Term.enum sub_t (Project.program proj)
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m s ->
        Core.Map.set m ~key:(Term.tid s) ~data:(Sub.name s))
  in
  map_subs (Hike_strip_canaries.strip_sub ~facts ~names) proj

(* The sections pass: attribution, promotion, DCE; the emitter spec is
   installed into the KB facts for convert_binary. *)
let pass_attrib proj =
  let facts = Hike_kb.facts () in
  let target = facts.target in
  let word = facts.abi.Hike_abi.word in
  let meta = Hike_sections.sec_meta ~word proj in
  let spans = Hike_sections.attrib_spans ~meta in
  let dyn_allocs =
    Term.enum sub_t (Project.program proj)
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m sub ->
           Core.Map.set m ~key:(Term.tid sub)
             ~data:(Hike_sections.dynamic_alloc_tids_of ~facts sub))
  in
  let program =
    Term.map sub_t (Project.program proj) ~f:(fun sub ->
        Hike_def_slots.stamp_dyn_allocs
          ~dynamic_alloc_tids:(Core.Map.find dyn_allocs (Term.tid sub)
                               |> Option.value ~default:Tid.Set.empty)
          sub)
  in
  let ctx =
    Hike_sections.attribute ~facts ~word ~entry:Hike_stack_model.segment_base
      ~spans program
  in
  let program =
    Term.map sub_t program ~f:(Hike_sections.stamp_tags ctx)
    |> Hike_promote.rewrite_program ~word ~entry:Hike_stack_model.segment_base
          ~facts ~spans ~ctx
  in
  let spec =
    Hike_sections.section_spec_of ~word
      ~comps:(Hike_sections.global_comps_of ~word ~spans ctx)
      ~whole:(Hike_sections.whole_comps_of ctx)
      ~meta
  in
  (* The DCE's load roots are the vars the rewrite created; its
     escape roots are the storages carrying identity members. *)
  let program =
    Term.map sub_t program ~f:(fun sub ->
        let roots =
          Core.Map.find ctx.Hike_sections.sub_trees (Term.tid sub)
          |> Option.value ~default:Hike_sections.Tree.empty
          |> Hike_sections.escape_roots_of_tree
        in
        Hike_dce.dce ~roots ~target sub)
  in
  Hike_kb.install (Hike_kb.with_spec facts spec);
  Project.with_program proj program

let pass_convlir ~output proj = convert_binary output proj

let pass_types proj = Hike_types.run proj

let () =
  Extension.declare (fun ctx ->
      let output_file = Extension.Configuration.get ctx output in
      Project.register_pass ~name:"filter" ~runonce:true pass_filter;
      let jump = chain ~name:"jump" ~prev:"filter" pass_jump in
      let split_mem = chain ~name:"split-mem" ~prev:jump pass_split_mem in
      let coerce = chain ~name:"coerce" ~prev:split_mem pass_coerce in
      let vsa = chain ~name:"vsa" ~prev:coerce pass_vsa in
      let strip_canaries =
        chain ~name:"strip-canaries" ~prev:vsa pass_strip_canaries
      in
      let sections = chain ~name:"sections" ~prev:strip_canaries pass_attrib in
      let types = chain ~name:"types" ~prev:sections pass_types in
      let convlir = chain' ~name:"convlir" ~prev:types (pass_convlir ~output:output_file) in
      ignore convlir;
      Ok ())
