open Bap.Std
open Bap_main
open Bap_core_theory
module Atomic = Hike_atomic
module Abi = Hike_abi

(* Public re-exports; consumers use [Hike.Abi], etc. *)
module Vsa = Hike_vsa
module Summary = Hike_summary
module Worklist = Hike_worklist
module Decode = Hike_decode
module Diag = Hike_diag
module Cfg_complete = Hike_cfg_complete

module Resolve = Hike_resolve
module Rip = Hike_rip
module Synth = Hike_synth
module Dce = Hike_dce
module Jump = Hike_jump
module Split_mem = Hike_split_mem
module Split_blocks = Hike_split_blocks
module Coerce = Hike_coerce
module Fp = Hike_fp
module Stack_model = Hike_stack_model
module Variadic = Hike_variadic
module Def_slots = Hike_def_slots
module Sections = Hike_sections
module Image = Hike_image
module Promote = Hike_promote
module Attribution = Hike_attribution
module Kb = Hike_kb
module Types = Hike_types
module Ssa = Hike_ssa
module Bil2llvm = Bil2llvm

let convert_binary output_program proj =
  let llvm_ctx = Llvm.create_context () in
  let llvm_module = Llvm.create_module llvm_ctx "Convlir" in
  let target = Project.target proj in
  let abi = Abi.of_target target in
  let word = abi.Abi.word in
  let addr_bits = Theory.Target.bits target in
  let relative, externals =
    match (Hike_kb.facts ()).Hike_kb.spec with
    | Some spec ->
      (spec.Bil2llvm_env.spec_relative, spec.Bil2llvm_env.spec_externals)
    | None ->
      let bias = Hike_image.get_bias proj in
      (Hike_image.relative_values proj ~bias,
       Hike_image.external_references proj)
  in
  let spec =
    match (Hike_kb.facts ()).Hike_kb.spec with
    | Some spec -> spec
    | None ->
        (* No attribution ran: the sections emit with no components. *)
        let meta = Hike_sections.sec_meta ~word proj in
        Hike_sections.section_spec_of ~word ~comps:[] ~whole:[] ~meta
          ~tls:(Hike_image.tls_spec proj)
          ~relative ~externals
  in
  let prog = Project.program proj in
  Bil2llvm.emit_program llvm_ctx llvm_module
    ~target ~addr_bits
    ~symtab:(Some (Project.symbols proj))
    ~synth:(Hike_kb.facts ()).synth
    spec prog;
  Llvm.print_module output_program llvm_module;
  Llvm.dispose_module llvm_module;
  Llvm.dispose_context llvm_ctx

let output =
  Extension.Configuration.parameter ~aliases:[ "o"; "output" ]
    Extension.Type.("output file" %: string)
    "output-file" ~doc:"File to output LLVM IR"

(* The previous pass's ACTUAL registered name: BAP prefixes every pass
   with the bundle name, so the chain reads back the registered name
   instead of assuming a bundle prefix. *)
let last_pass () = Project.Pass.name (Core.List.last_exn (Project.passes ()))

let chain ~name ~deps run =
  Project.register_pass ~name ~deps ~runonce:true run;
  last_pass ()

let chain' ~name ~deps run =
  Project.register_pass' ~name ~deps ~runonce:true run;
  last_pass ()

(* Discovery: the worklist's program and the analysis facts every later
   pass reads. *)
let pass_discover proj =
  let target = Project.target proj in
  if Hike_abi.is_known_foreign target then
    Hike_diag.warn
      "target %s is not x86_64-gnu-elf; the x86-64 SysV convention record serves it"
      (KB.Name.to_string (Theory.Target.name target));
  let result = Hike_worklist.run proj in
  Hike_kb.install result.facts;
  Project.with_program proj result.program

(* ELF facts are read here; attribution owns the BIR and facts protocol. *)
let pass_attrib proj =
  let facts = Hike_kb.facts () in
  let word = facts.abi.Hike_abi.word in
  let meta = Hike_sections.sec_meta ~word proj in
  let spans = Hike_sections.attrib_spans ~meta in
  let tls =
    Hike_image.tls_spec proj
  in
  let result =
    Hike_attribution.run ~facts ~word
      ~entry:Hike_stack_model.segment_base ~spans ~meta ~tls
      ~relative:(Hike_image.relative_values proj ~bias:(Hike_image.get_bias proj))
      ~externals:(Hike_image.external_references proj) (Project.program proj)
  in
  Hike_kb.install result.facts;
  Project.with_program proj result.program

(* The variadic stamp reads the analysis denotation on the discovered
   program, before attribution rewrites its blocks. *)
let pass_variadic proj =
  let facts = Hike_kb.facts () in
  Project.map_program proj
    ~f:(Hike_variadic.stamp ~abi:facts.abi ~entry:Hike_stack_model.segment_base
          ~denote:facts.denote)

let pass_convlir ~output proj = convert_binary output proj

let pass_split_blocks proj =
  Project.map_program proj ~f:Hike_split_blocks.normalize

let pass_ssa proj =
  let target = Project.target proj in
  Project.map_program proj ~f:(Hike_ssa.ssa_program ~target)

let () =
  Extension.declare ~provides:["pass"; "hike"] (fun ctx ->
      let output_file = Extension.Configuration.get ctx output in
      let discover = chain ~name:"discover" ~deps:[] pass_discover in
      let variadic = chain ~name:"variadic" ~deps:[ discover ] pass_variadic in
      let sections = chain ~name:"sections" ~deps:[ variadic ] pass_attrib in
      let split_blocks =
        chain ~name:"split-blocks" ~deps:[ sections ] pass_split_blocks
      in
      let sign = chain ~name:"sign" ~deps:[ split_blocks ] Hike_types.sign_run in
      let ssa = chain ~name:"ssa" ~deps:[ sign ] pass_ssa in
      let types = chain ~name:"types" ~deps:[ ssa ] Hike_types.run in
      let convlir = chain' ~name:"convlir" ~deps:[ types ] (pass_convlir ~output:output_file) in
      ignore convlir;
      Ok ())
