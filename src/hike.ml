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
  (* The re-lift's callee fragments: the seam's walk follows direct call
     edges, so a callee the program never lifted lands inside the lifted
     block list.  The entry sub's own blocks are the root's closure over
     the block graph's edges (goto, interrupt, call return); every other
     closure is the body of a direct callee, hoisted into its own sub so
     the flattened call names a defined function. *)
  let partition_lifted (blks : blk term list) :
      blk term list * (Tid.t * blk term list) list =
    let by_tid =
      Core.Map.of_alist_exn (module Tid)
        (Base.List.map blks ~f:(fun b -> (Term.tid b, b)))
    in
    let succ_tids b =
      Term.enum jmp_t b
      |> Seq.filter_map ~f:(fun j ->
          match Jmp.kind j with
          | Goto (Direct t) | Int (_, t) -> Some t
          | Call c -> (
            match Call.return c with
            | Some (Direct t) -> Some t
            | _ -> None)
          | _ -> None)
      |> Seq.filter ~f:(Core.Map.mem by_tid)
      |> Seq.to_list
    in
    let rec closure seen work =
      match work with
      | [] -> seen
      | t :: rest ->
        if Core.Set.mem seen t then closure seen rest
        else
          let seen = Core.Set.add seen t in
          match Core.Map.find by_tid t with
          | None -> closure seen rest
          | Some b -> closure seen (succ_tids b @ rest)
    in
    let blocks_of seen =
      Base.List.filter blks ~f:(fun b -> Core.Set.mem seen (Term.tid b))
    in
    let root = Base.List.hd_exn blks in
    let entry_seen = closure (Core.Set.empty (module Tid)) [ Term.tid root ] in
    let call_targets =
      Base.List.concat_map blks ~f:(fun b ->
          Term.enum jmp_t b
          |> Seq.filter_map ~f:(fun j ->
              match Jmp.kind j with
              | Call c -> (
                match Call.target c with Direct t -> Some t | _ -> None)
              | _ -> None)
          |> Seq.to_list)
      |> Base.List.dedup_and_sort ~compare:Tid.compare
    in
    let rec take remaining pending frags =
      match pending with
      | [] -> (remaining, List.rev frags)
      | t :: rest ->
        if
          (not (Core.Map.mem by_tid t)) || not (Core.Set.mem remaining t)
        then take remaining rest frags
        else
          let seen = closure (Core.Set.empty (module Tid)) [ t ] in
          take (Core.Set.diff remaining seen) rest
            ((t, blocks_of seen) :: frags)
    in
    let remaining, frags =
      take (Core.Set.diff
              (Core.Set.of_list (module Tid)
                 (Base.List.map blks ~f:Term.tid))
              entry_seen)
        call_targets []
    in
    (* Blocks no closure claimed stay with the entry sub: the lift lifted
       them, so the term keeps them. *)
    (blocks_of entry_seen @ blocks_of remaining, frags)
  in

  let main_tid, subs_acc, block_addrs, hoisted_subs =
    match main_addr with
    | None -> (None, subs_acc, block_addrs, [])
    | Some addr -> (
      match lookup addr with
      | Some t -> (Some t, subs_acc, block_addrs, [])
      | None -> (
        match lift_at (Addr.of_int64 addr) ~block_addrs with
        | None | Some [] -> (None, subs_acc, block_addrs, [])
        | Some blks ->
          let entry_blocks, frags = partition_lifted blks in
          let build_sub ~tid blocks =
            let sb = Sub.Builder.create ~tid ~name:(Tid.name tid) () in
            Base.List.iter blocks ~f:(fun b ->
                let b =
                  Term.concat_map def_t b ~f:Hike_split_mem.split_def
                in
                Sub.Builder.add_blk sb (Hike_coerce.coerce_block b));
            Sub.Builder.result sb
          in
          (* Each fragment earns its own tid; the flattened call retargets
             to it. *)
          let frag_tids =
            Base.List.map frags ~f:(fun (_, blocks) ->
                let entry = Base.List.hd_exn blocks in
                match Term.get_attr entry address with
                | Some a ->
                  Tid.for_name
                    (Printf.sprintf "sub_%Lx" (Word.to_int64_exn a))
                | None -> Tid.for_name "sub")
          in
          let retarget =
            match Base.List.map2 frags frag_tids ~f:(fun (entry_tid, _) ftid -> (entry_tid, ftid)) with
            | Ok rows -> Core.Map.of_alist_exn (module Tid) rows
            | Unequal_lengths ->
              failwith "hike-vsa: the re-lift partition lost a fragment tid"
          in
          let retarget_call t =
            Base.Option.value (Core.Map.find retarget t) ~default:t
          in
          let rewrite b =
            Term.map jmp_t b
              ~f:(Hike_cfg_complete.remap_jmp ~call:retarget_call
                    ~blk:(fun t -> t))
          in
          (* The re-lifted terms take the pre-solve normalization the
             program's own subs went through above this pass: the FP temp
             width qualification (the unsized intrinsic temp spellings). *)
          let fp_normalize (s : sub term) : sub term =
            Term.enum sub_t (Hike_fp.run_program (Program.create ~subs:[ s ] ()))
            |> Seq.hd_exn
          in
          let frag_subs =
            match
              Base.List.map2 frags frag_tids ~f:(fun (_, blocks) ftid ->
                  fp_normalize
                    (build_sub ~tid:ftid (Base.List.map blocks ~f:rewrite)))
            with
            | Ok subs -> subs
            | Unequal_lengths ->
              failwith "hike-vsa: the re-lift partition lost a fragment"
          in
          let main_tid = Tid.for_name "main" in
          let main_sub =
            fp_normalize
              (build_sub ~tid:main_tid
                 (Base.List.map entry_blocks ~f:rewrite))
          in
          (* The re-lifted terms' address stamps and entry rows enter the
             run's maps before the solve: a dispatch, the prune, or a
             resolution anywhere in the run names in-module targets
             through them. *)
          let block_addrs =
            Base.List.fold (frag_subs @ [ main_sub ]) ~init:block_addrs
              ~f:(fun m s ->
                Term.enum blk_t s
                |> Seq.fold ~init:m ~f:(fun m b ->
                    match Term.get_attr b address with
                    | Some a -> Core.Map.set m ~key:a ~data:(Term.tid b)
                    | None -> m))
          in
          let sub_addrs =
            (Addr.of_int64 addr, main_tid)
            :: Base.List.filter_map frag_subs ~f:(fun s ->
                match Term.first blk_t s with
                | Some b ->
                  Base.Option.map (Term.get_attr b address)
                    ~f:(fun a -> (a, Term.tid s))
                | None -> None)
            |> Core.Map.of_alist_exn (module Addr)
            |> Core.Map.fold ~init:sub_addrs ~f:(fun ~key ~data m ->
                   Core.Map.set m ~key ~data)
          in
          (* The hoisted subs ride their own summaries: main's call names
             a sub of the extended program. *)
          let written =
            Hike_vsa.kill_summaries ~abi:(Hike_abi.of_target target)
              (Program.create
                 ~subs:(Base.List.append
                          (Term.enum sub_t (Project.program proj)
                          |> Seq.to_list)
                          (frag_subs @ [ main_sub ]))
                 ())
          in
          let solved_frags = ref [] in
          let subs_acc, block_addrs =
            Base.List.fold frag_subs ~init:(subs_acc, block_addrs)
              ~f:(fun (acc, ba) s ->
                let envs, stamped, ba' =
                  Hike_vsa.fixpoint target ~lookup ~sub_addrs ~images
                    ~written ~lift_at ~block_addrs:ba s
                in
                solved_frags := stamped :: !solved_frags;
                ( Core.Map.set acc ~key:(Term.tid s) ~data:(envs, stamped),
                  Core.Map.fold ba' ~init:ba ~f:(fun ~key ~data m ->
                      Core.Map.set m ~key ~data) ))
          in
          let envs, stamped, block_addrs' =
            Hike_vsa.fixpoint target ~lookup ~sub_addrs ~images ~written
              ~lift_at ~block_addrs main_sub
          in
          ( Some main_tid,
            Core.Map.set subs_acc ~key:main_tid ~data:(envs, stamped),
            Core.Map.fold block_addrs' ~init:block_addrs
              ~f:(fun ~key ~data m -> Core.Map.set m ~key ~data),
            List.rev !solved_frags )))
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
  (* The rewritten subs are the program from here on, plus the re-lift's
     subs: a main the lift never discovered and the callees it hoisted. *)
  let program =
    let rewritten =
      Term.map sub_t (Project.program proj) ~f:(fun sub ->
          Option.value
            (Base.Option.map (Core.Map.find subs_acc (Term.tid sub)) ~f:snd)
            ~default:sub)
    in
    let rewritten =
      Base.List.fold hoisted_subs ~init:rewritten ~f:(fun prog s ->
          Term.append sub_t prog s)
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
      (* A target var whose reaching def reads the return-address cell is
         the return epilogue, never a dispatch. *)
      let is_return ~blk e =
        match e with
        | Bil.Var v -> (
          match
            Term.enum def_t blk
            |> Seq.find ~f:(fun d -> Var.equal (Def.lhs d) v)
          with
          | None -> false
          | Some d -> (
            match Hike_stack_model.addr_of_rhs (Def.rhs d) with
            | Some (addr, _) -> (
              match facts.Hike_kb.denote ~blk ~def:d addr with
              | Ok ws ->
                Hike_stack_model.is_return_address ws
                || Cbat_vsa.WordSet.is_bottom ws
              | Error _ -> false)
            | None -> false))
        | _ -> false
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
      (* The pair rule: an indirect target is either a foreign boundary
         (a read through an external-symbol slot — the transfer leaves
         the program, no edge), a return epilogue (no edge), or a
         bounded set whose every word names an in-module sub (the
         edges).  Anything else leaves the program's call graph
         unprovable: the prune refuses and the module keeps every sub,
         with the diagnostic naming the sub and block. *)
      let edges_of_sub sub : Tid.t list option =
        let reach = reachable_tids sub in
        let refuse blk =
          Hike_diag.warn
            "prune: sub %s: block %s: indirect target is neither resolvable \
             nor a foreign boundary - keeping every sub"
            (Sub.name sub) (Tid.name (Term.tid blk))
        in
        let indirect ~blk e =
          if is_foreign_boundary ~blk e then Some []
          else if is_return ~blk e then Some []
          else
            match target_words ~blk e with
            | None ->
              refuse blk;
              None
            | Some ws -> (
                let resolved = Base.List.map ws ~f:resolve_word in
                if Base.List.exists resolved ~f:(fun t -> Base.Option.is_none t)
                then (
                  refuse blk;
                  None)
                else Some (Base.List.filter_map resolved ~f:(fun t -> t)))
        in
        let edges_of_blk blk acc =
          Term.enum jmp_t blk
          |> Seq.fold ~init:(Some acc) ~f:(fun acc j ->
              match acc with
              | None -> None
              | Some acc -> (
                  match Jmp.kind j with
                  | Call c -> (
                    match Call.target c with
                    | Direct t -> Some (t :: acc)
                    | Indirect e -> indirect ~blk e)
                  | Goto g -> (
                    match g with
                    | Direct _ -> Some acc
                    | Indirect e -> indirect ~blk e)
                  | Ret _ | Int _ -> Some acc))
        in
        let rec edges_of_tids = function
          | [] -> Some []
          | blk :: rest -> (
              match edges_of_blk blk [] with
              | None -> None
              | Some more -> (
                match edges_of_tids rest with
                | None -> None
                | Some more' -> Some (List.rev_append more more')))
        in
        Term.enum blk_t sub
        |> Seq.filter ~f:(fun blk -> Core.Set.mem reach (Term.tid blk))
        |> Seq.to_list
        |> edges_of_tids
      in
      let rec closure seen work =
        match work with
        | [] -> Some seen
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
                if Term.has_attr s Sub.entry_point then Some []
                else edges_of_sub s
              in
              match more with
              | None -> None
              | Some more -> closure seen (more @ rest)
      in
      match closure (Core.Set.empty (module Tid)) [ root ] with
      | None -> program
      | Some closure ->
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
