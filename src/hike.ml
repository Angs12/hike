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
module Drive = Hike_drive
module Diag = Hike_diag
module Signatures = Hike_signatures
module Cfg_complete = Hike_cfg_complete

module Resolve = Hike_resolve
module Rip = Hike_rip
module Tls = Hike_tls
module Synth = Hike_synth
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
module Dce = Hike_dce
module Bil2llvm = Bil2llvm

let emit output_program proj =
  let llvm_ctx = Llvm.create_context () in
  let llvm_module = Llvm.create_module llvm_ctx "Convlir" in
  let target = Project.target proj in
  let addr_bits = Theory.Target.bits target in
  let facts = Hike_kb.facts () in
  let spec =
    match facts.Hike_kb.spec with
    | Some spec -> spec
    | None ->
        failwith
          "hike-emit: no section spec installed; run Hike.lift before \
           Hike.emit"
  in
  let prog = Project.program proj in
  Bil2llvm.emit_program llvm_ctx llvm_module
    ~target ~addr_bits
    ~symtab:(Some (Project.symbols proj))
    ~synth:facts.synth
    ~signatures:facts.signatures
    spec prog;
  Llvm.print_module output_program llvm_module;
  Llvm.dispose_module llvm_module;
  Llvm.dispose_context llvm_ctx

let output =
  Extension.Configuration.parameter ~aliases:[ "o"; "output" ]
    Extension.Type.("output file" %: string)
    "output-file" ~doc:"File to output LLVM IR"

let signatures_files =
  Extension.Configuration.parameter
    Extension.Type.(list string) "signatures"
    ~doc:"Signature files (S-expression) describing the external library \
          functions; a later file overrides an earlier entry"

(* The user's signature files, read when the pass first needs them: the
   extension is registered whenever BAP starts, so a missing or bad file
   must fail the lift, not BAP's initialization.  Without signatures the
   lift cannot tell which imports never return, and would follow their
   fallthroughs. *)
let load_signatures files =
  lazy
    (if Base.List.is_empty files then
       failwith "hike: no signatures: pass --signatures FILE (data/glibc.sexp)";
     match Hike_signatures.load files with
     | Ok db -> db
     | Error err ->
       failwith
         (Printf.sprintf "hike: signatures: %s" (Core.Error.to_string_hum err)))

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

(* Discovery: the drive's program and symbol table, and the analysis
   facts every later pass reads. *)
let pass_discover ~(signatures : Hike_signatures.db Lazy.t) proj =
  let target = Project.target proj in
  if not (Hike_abi.is_primary_target target) then
    failwith
      (Printf.sprintf "hike: target %s is not x86_64-gnu-elf"
         (KB.Name.to_string (Theory.Target.name target)));
  let result = Hike_drive.run ~signatures:(Lazy.force signatures) proj in
  Hike_kb.install result.facts;
  Project.with_program (Project.with_symbols proj result.symtab) result.program

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

let pass_split_blocks proj =
  let synth = (Hike_kb.facts ()).synth in
  Project.map_program proj
    ~f:(Hike_split_blocks.normalize ~synth ~target:(Project.target proj))

(* The pass chain in order: the plugin registers each stage as a pass
   and [lift] runs them in sequence, so the two entries cannot drift. *)
let stages ~signatures () = [
  ("discover", pass_discover ~signatures);
  ("variadic", pass_variadic);
  ("sections", pass_attrib);
  ("split-blocks", pass_split_blocks);
  ("sign", Hike_types.sign_run);
  ("types", Hike_types.run);
]

let lift ~signatures proj =
  Base.List.fold (stages ~signatures:(Lazy.from_val signatures) ()) ~init:proj ~f:(fun proj (_, run) -> run proj)

let () =
  Extension.declare ~provides:["pass"; "hike"] (fun ctx ->
      let output_file = Extension.Configuration.get ctx output in
      let signatures =
        load_signatures (Extension.Configuration.get ctx signatures_files) in
      let last =
        Base.List.fold (stages ~signatures ()) ~init:[] ~f:(fun deps (name, run) -> [ chain ~name ~deps run ])
      in
      ignore (chain' ~name:"convlir" ~deps:last (emit output_file));
      Ok ())
