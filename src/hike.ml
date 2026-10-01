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
module Split_blocks = Hike_split_blocks
module Coerce = Hike_coerce
module Fp = Hike_fp
module Stack_model = Hike_stack_model
module Def_slots = Hike_def_slots
module Sections = Hike_sections
module Image = Hike_image
module Promote = Hike_promote
module Kb = Hike_kb
module Types = Hike_types
module Ssa = Hike_ssa
module Strip_canaries = Hike_strip_canaries
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
          ~relative ~externals
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

let map_subs f proj =
  Project.map_program proj ~f:(fun prog -> Term.map sub_t prog ~f)

let pass_filter proj = Hike_filter.filter_subs proj

let pass_jump proj = map_subs (Hike_jump.compile_sub (Project.target proj)) proj

let pass_split_mem proj = Project.map_program proj ~f:Hike_split_mem.normalize

(* The one width-coercion point: every later consumer reads uniform widths. *)
let pass_coerce proj = Project.map_program proj ~f:Hike_coerce.coerce_program

(* The FP temp identity carries its width; after the coercion point the
   lifter's widths are honest, so every later pass reads the qualified
   names. *)
let pass_fp proj = Project.map_program proj ~f:Hike_fp.run_program

let pass_vsa proj =
  let target = Project.target proj in
  if Hike_abi.is_known_foreign target then
    Hike_diag.warn
      "target %s is not x86_64-gnu-elf; the x86-64 SysV convention record serves it"
      (KB.Name.to_string (Theory.Target.name target));
  (* Image-backed loads are sound only where the runtime content is
     known: a relocation-free section is its file bytes, and a section
     holding relocated words is its RELATIVE words' runtime values plus
     the bytes no relocation names. *)
  let images =
    Hike_image.get_section_images proj
    |> Base.List.map ~f:(fun (img_bytes, img_lo, img_hi) ->
           { Cbat_vsa.img_lo; img_hi; img_bytes })
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
      ~addr_bits:(Hike_abi.addr_size_bits target)
  in
  (* The run's sub-entry index: the symtab resolves every block address
     that names a lifted subroutine to that subroutine's tid — the
     target a re-lifted direct call lands on. *)
  let sub_addrs =
    Core.Map.fold block_addrs ~init:Addr.Map.empty
      ~f:(fun ~key:addr ~data:_ m ->
          match lookup (Word.to_int64_exn addr) with
          | Some sub -> Core.Map.set m ~key:addr ~data:sub
          | None -> m)
  in
  let subs_acc, block_addrs =
    Term.enum sub_t (Project.program proj)
    |> Seq.fold ~init:(Tid.Map.empty, block_addrs)
         ~f:(fun (acc, block_addrs) sub ->
        let envs, sub', block_addrs' =
          Hike_vsa.fixpoint target ~lookup ~sub_addrs ~images ~written ~lift_at
            ~block_addrs sub
        in
        (Core.Map.set acc ~key:(Term.tid sub) ~data:(envs, sub'), block_addrs'))
  in
  (* The program's main: the address the entry passes to the runtime.
     The entry's call block sets the argument register; the block's
     postcondition denotates the address as a singleton.  A named sub
     sits there (the symtab names it); a stripped binary has no sub at
     the address — the re-lift seam decodes and lifts it, and the run
     solves it like any other sub. *)
  let main_addr =
    let entry =
      Term.enum sub_t (Project.program proj)
      |> Seq.find ~f:(fun s -> Term.has_attr s Sub.entry_point)
    in
    match entry with
    | None -> None
    | Some entry -> (
      match Core.Map.find subs_acc (Term.tid entry) with
      | None -> None
      | Some (envs, _) ->
        let arg0 = Abi.argc_argv_regs (Hike_abi.of_target target) |> fst in
        Term.enum blk_t entry
        |> Seq.filter_map ~f:(fun blk ->
            let has_call =
              Term.enum jmp_t blk
              |> Seq.exists ~f:(fun j ->
                  match Jmp.kind j with Call _ -> true | _ -> false)
            in
            if not has_call then None
            else
              Core.Map.find envs (Term.tid blk)
              |> Base.Option.bind ~f:(fun (_, post) ->
                  match
                    Cbat_vsa.denote_exp_at ~pre:post ~post ~blk (Bil.Var arg0)
                  with
                  | Error _ -> None
                  | Ok ws -> (
                    match
                      Cbat_word.to_int64 (Cbat_vsa.WordSet.cardinality ws)
                    with
                    | Ok 1L ->
                      Base.Option.bind (Cbat_vsa.WordSet.min_elem ws)
                        ~f:(fun w -> Result.to_option (Cbat_word.to_int64 w))
                    | _ -> None)))
        |> Seq.hd)
  in
  let main_tid, subs_acc, block_addrs =
    match main_addr with
    | None -> (None, subs_acc, block_addrs)
    | Some addr -> (
      match lookup addr with
      | Some t -> (Some t, subs_acc, block_addrs)
      | None -> (
        match lift_at (Addr.of_int64 addr) ~block_addrs with
        | None | Some [] -> (None, subs_acc, block_addrs)
        | Some blks ->
          let tid = Tid.for_name "main" in
          let sb = Sub.Builder.create ~tid ~name:"main" () in
          (* The lifted blocks take the same normalization a dispatch
             materialization gives its own: one inline memory node per
             def, and width-honest operands. *)
          Base.List.iter blks ~f:(fun b ->
              let b =
                Term.concat_map def_t b ~f:Hike_split_mem.split_def
              in
              Sub.Builder.add_blk sb (Hike_coerce.coerce_block b));
          let main_sub = Sub.Builder.result sb in
          let envs, stamped, block_addrs' =
            Hike_vsa.fixpoint target ~lookup ~sub_addrs ~images ~written
              ~lift_at ~block_addrs main_sub
          in
          ( Some tid,
            Core.Map.set subs_acc ~key:tid ~data:(envs, stamped),
            Core.Map.fold block_addrs' ~init:block_addrs
              ~f:(fun ~key ~data m -> Core.Map.set m ~key ~data) )))
  in
  let all_envs =
    Core.Map.fold subs_acc ~init:Tid.Map.empty
      ~f:(fun ~key:_ ~data:(envs, _) m ->
        Core.Map.fold envs ~init:m
          ~f:(fun ~key ~data m' -> Core.Map.set m' ~key ~data))
  in
  Hike_kb.install
    (Hike_kb.build ~block_envs:all_envs ~block_addrs ~target ~lookup);
  let facts = Hike_kb.facts () in
  (* The rewritten subs are the program from here on, plus a main the
     lift never discovered. *)
  let program =
    let rewritten =
      Term.map sub_t (Project.program proj) ~f:(fun sub ->
          Option.value
            (Base.Option.map (Core.Map.find subs_acc (Term.tid sub)) ~f:snd)
            ~default:sub)
    in
    match main_tid with
    | None -> rewritten
    | Some tid -> (
      let present =
        Term.enum sub_t rewritten
        |> Seq.exists ~f:(fun s -> Tid.equal (Term.tid s) tid)
      in
      if present then rewritten
      else
        match Core.Map.find subs_acc tid with
        | Some (_, sub) -> Term.append sub_t rewritten sub
        | None -> rewritten)
  in
  (* The runtime's own stubs drop by reachability from the program's
     root (main), never by spelling.  The closure follows direct call
     targets and every target a bounded denotation names; an unbounded
     target or a relocated-slot read names no in-module sub and
     contributes no edge.  Without a root the prune does not run: the
     identity keeps every sub. *)
  let pruned_program =
    match main_tid with
    | None -> program
    | Some root -> (
      let sub_of_tid =
        Term.enum sub_t program
        |> Seq.fold ~init:Tid.Map.empty ~f:(fun m s ->
            Core.Map.set m ~key:(Term.tid s) ~data:s)
      in
      (* The external-symbol slots: a jump whose target is read through
         one of these leaves the program — the dynamic linker owns the
         value.  A RELATIVE slot's value is the module's own address;
         the denotation reads it from the image and the edge follows it
         like any other. *)
      let relocated =
        Hike_image.external_references proj
        |> Base.List.map ~f:fst
        |> Core.Int64.Set.of_list
      in
      (* The set's own words of a bounded target denotation; [None] when
         the target is unbounded or the set is too wide to enumerate. *)
      let target_words ~blk e =
        match facts.Hike_kb.denote ~blk e with
        | Ok ws when not (Cbat_vsa.WordSet.is_top ws) -> (
          match Cbat_word.to_int64 (Cbat_vsa.WordSet.cardinality ws) with
          | Ok n when Stdlib.Int64.compare n 64L <= 0 ->
            Some (Cbat_vsa.WordSet.iter ws)
          | _ -> None)
        | _ -> None
      in
      (* A target read through a relocated slot names no lifted sub.  The
         target exp may name the temp the block loaded the slot into; the
         last def of the same var in the block puts the slot read back in
         view (the state the jmp reads). *)
      let is_foreign_boundary ~blk e =
        let e =
          match e with
          | Bil.Var v ->
            Term.enum def_t blk
            |> Seq.fold ~init:e ~f:(fun found d ->
                if Var.equal (Def.lhs d) v then Def.rhs d else found)
          | _ -> e
        in
        match e with
        | Bil.Load (_, addr_e, _, _) -> (
          match facts.Hike_kb.denote ~blk addr_e with
          | Ok ws -> (
            match Cbat_word.to_int64 (Cbat_vsa.WordSet.cardinality ws) with
            | Ok 1L ->
              Base.Option.value_map
                (Base.Option.bind (Cbat_vsa.WordSet.min_elem ws)
                   ~f:(fun w -> Result.to_option (Cbat_word.to_int64 w)))
                ~default:false
                ~f:(fun a -> Core.Set.mem relocated a)
            | _ -> false)
          | Error _ -> false)
        | _ -> false
      in
      let resolve_word w =
        match Cbat_word.to_int64 w with
        | Ok v -> Core.Map.find sub_addrs (Addr.of_int64 v)
        | Error _ -> None
      in
      (* The blocks the sub's own execution reaches: the entry block's
         DFS over the BIR's edges.  A no-return call or a terminator
         ends the walk — the body folded after it is dead code and
         contributes no edges.  An unresolvable indirect transfer keeps
         every block: the walk claims no deadness it cannot prove.  A
         sub with no entry block (an empty body) serves whole. *)
      let reachable_tids sub : Tid.Set.t =
        let blocks = Term.enum blk_t sub |> Seq.to_list in
        match Cbat_vsa.entry_block_of sub with
        | None ->
          Core.Set.of_list (module Tid) (Base.List.map blocks ~f:Term.tid)
        | Some eb -> (
          let by_tid =
            Core.Map.of_alist_exn (module Tid)
              (Base.List.map blocks ~f:(fun b -> (Term.tid b, b)))
          in
          let rec nexts = function
            | [] -> []
            | b :: tl -> (
                let nx = match tl with b2 :: _ -> Some (Term.tid b2) | [] -> None in
                (Term.tid b, nx) :: nexts tl)
          in
          let fall_tbl = Core.Map.of_alist_exn (module Tid) (nexts blocks) in
          let all =
            Core.Set.of_list (module Tid) (Base.List.map blocks ~f:Term.tid)
          in
          let rec go seen tid =
            if Core.Set.mem seen tid then seen
            else
              match Core.Map.find by_tid tid with
              | None -> seen
              | Some blk -> (
                  let seen = Core.Set.add seen tid in
                  let js = Term.enum jmp_t blk |> Seq.to_list in
                  match js with
                  | [] -> (
                      match Core.Map.find fall_tbl tid with
                      | Some (Some t) -> go seen t
                      | _ -> seen)
                  | _ ->
                    let keeps_all = ref false in
                    let seen =
                      Base.List.fold js ~init:seen ~f:(fun seen j ->
                          match Jmp.kind j with
                          | Goto (Direct t) -> go seen t
                          | Int (_, t) -> go seen t
                          | Call c -> (
                              match Call.return c with
                              | Some (Direct l) -> go seen l
                              | _ -> seen)
                          | Ret _ -> seen
                          | Goto (Indirect _) ->
                            keeps_all := true;
                            seen)
                    in
                    if !keeps_all then Core.Set.union seen all else seen)
          in
          go (Core.Set.empty (module Tid)) (Term.tid eb))
      in
      let edges_of_sub sub : Tid.t list =
        let reach = reachable_tids sub in
        Term.enum blk_t sub
        |> Seq.filter ~f:(fun blk -> Core.Set.mem reach (Term.tid blk))
        |> Seq.concat_map ~f:(fun blk ->
            Term.enum jmp_t blk
            |> Seq.filter_map ~f:(fun j ->
                let indirect e =
                  if is_foreign_boundary ~blk e then None
                  else
                    match target_words ~blk e with
                    | None -> None
                    | Some ws ->
                      let ts = Base.List.filter_map ws ~f:resolve_word in
                      if ts = [] then None else Some ts
                in
                match Jmp.kind j with
                | Call c -> (
                  match Call.target c with
                  | Direct t -> Some [ t ]
                  | Indirect e -> indirect e)
                | Goto g -> (
                  match g with
                  | Direct _ -> None
                  | Indirect e -> indirect e)
                | Ret _ | Int _ -> None))
        |> Seq.to_list
        |> List.concat
      in
      let rec closure seen work =
        match work with
        | [] -> seen
        | t :: rest ->
          if Core.Set.mem seen t then closure seen rest
          else
            let seen = Core.Set.add seen t in
            match Core.Map.find sub_of_tid t with
            | None -> closure seen rest
            | Some s ->
              (* The entry is analysed, not executed: its folded body is
                 the runtime boundary — the code the native crt1 runs
                 before main — and contributes no edges to the module's
                 call graph. *)
              let more =
                if Term.has_attr s Sub.entry_point then []
                else edges_of_sub s
              in
              closure seen (more @ rest)
      in
      let closure =
        closure (Core.Set.empty (module Tid)) [ root ]
      in
            Term.filter sub_t program ~f:(fun s -> Core.Set.mem closure (Term.tid s)))
  in
  (* The main sub earns the C ABI: the native crt1 calls it directly. *)
  let program =
    match main_tid with
    | None -> pruned_program
    | Some tid ->
      Term.map sub_t pruned_program ~f:(fun s ->
          if Tid.equal (Term.tid s) tid then
            Term.set_attr s Hike_stack_model.main_role ()
          else s)
  in
  Project.with_program proj program

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

(* The sections pass: attribution and promotion; the emitter spec and the
   sweep's escape roots are installed into the KB facts. *)
let pass_attrib proj =
  let facts = Hike_kb.facts () in
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
      ~relative:(Hike_image.relative_values proj ~bias:(Hike_image.get_bias proj))
      ~externals:(Hike_image.external_references proj)
  in
  (* The DCE's escape roots: the storages carrying identity members.
     They ride the facts to the sweep's own pass, after [hike-types]. *)
  let escape_roots =
    Core.Map.map ctx.Hike_sections.sub_trees ~f:(fun tree ->
        Hike_sections.escape_roots_of_tree
          ~addr_bits:(Hike_stack_model.word_bits word) tree)
  in
  Hike_kb.install (Hike_kb.with_attribution facts ~spec ~escape_roots);
  Project.with_program proj program

(* The sweep runs after [hike-types]: SSA has materialized the joins, so
   the dead values only the versioned defs and phis distinguish are
   removable.  The escape roots ride the facts from the attribution. *)
let pass_dce proj =
  let facts = Hike_kb.facts () in
  let target = facts.target in
  Project.map_program proj ~f:(fun prog ->
      Term.map sub_t prog ~f:(fun sub ->
          let roots =
            Core.Map.find facts.escape_roots (Term.tid sub)
            |> Option.value ~default:Var.Set.empty
          in
          Hike_dce.dce ~roots ~target sub))

let pass_convlir ~output proj = convert_binary output proj

let pass_split_blocks proj =
  Project.map_program proj ~f:Hike_split_blocks.normalize

let pass_ssa proj =
  let target = Project.target proj in
  Project.map_program proj ~f:(Hike_ssa.ssa_program ~target)

let () =
  Extension.declare ~provides:["pass"; "hike"] (fun ctx ->
      let output_file = Extension.Configuration.get ctx output in
      Project.register_pass ~name:"filter" ~runonce:true pass_filter;
      let filter = last_pass () in
      let jump = chain ~name:"jump" ~deps:[ filter ] pass_jump in
      let split_mem = chain ~name:"split-mem" ~deps:[ jump ] pass_split_mem in
      let coerce = chain ~name:"coerce" ~deps:[ split_mem ] pass_coerce in
      let fp = chain ~name:"fp" ~deps:[ coerce ] pass_fp in
      let vsa = chain ~name:"vsa" ~deps:[ fp ] pass_vsa in
      let strip_canaries =
        chain ~name:"strip-canaries" ~deps:[ vsa ] pass_strip_canaries
      in
      let sections = chain ~name:"sections" ~deps:[ strip_canaries ] pass_attrib in
      let split_blocks =
        chain ~name:"split-blocks" ~deps:[ sections ] pass_split_blocks
      in
      let sign = chain ~name:"sign" ~deps:[ split_blocks ] Hike_types.sign_run in
      let ssa = chain ~name:"ssa" ~deps:[ sign ] pass_ssa in
      let types = chain ~name:"types" ~deps:[ ssa ] Hike_types.run in
      let dce = chain ~name:"dce" ~deps:[ types ] pass_dce in
      let convlir = chain' ~name:"convlir" ~deps:[ dce ] (pass_convlir ~output:output_file) in
      ignore convlir;
      Ok ())
