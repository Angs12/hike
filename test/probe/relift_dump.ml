(* The re-lift seam dump: mirrors pass_vsa's main discovery + re-lift on a
   binary (typically stripped) and bisects the solve parameters for the
   flattened-callee fragments.  Probe-only forensics. *)
open Bap.Std
open Probe_common

let () =
  init ();
  let bin = Sys.argv.(1) in
  let proj = load_project bin in
  let target = Project.target proj in
  let program = production_input proj in
  let lookup =
    Hike.Resolve.symtab_lookup ~symtab:(Some (Project.symbols proj))
      ~table:(Hike.Resolve.name_table_of program)
      ~addr_bits:(Hike.Abi.addr_size_bits target)
  in
  let lift_at (a : Addr.t) ~(block_addrs : Tid.t Addr.Map.t) :
      blk term list option =
    match Seq.to_list (Memmap.lookup (Project.memory proj) a) with
    | [] -> None
    | (seg, _) :: _ -> (
        let lift_from ~rooter view =
          match
            Disasm_expert.Recursive.run ~rooter (Project.arch proj) view
          with
          | Error _ -> None
          | Ok rec_t ->
            let cfg = Disasm_expert.Recursive.cfg rec_t in
            Graphs.Cfg.nodes cfg
            |> Seq.iter ~f:(fun b ->
                Printf.printf "CFG node @%Lx\n%!"
                  (Word.to_int64_exn (Block.addr b)));
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
                let others =
                  Base.List.filter others ~f:(fun n ->
                      not (Core.Map.mem block_addrs (Block.addr n)))
                in
                Base.List.concat_map (root :: others) ~f:(Blk.lift cfg))
        in
        let whole = Memory.view_exn seg in
        match
          lift_from ~rooter:(Bap.Std.Rooter.create (Seq.return a)) whole
        with
        | Some _ as lifted -> lifted
        | None ->
          lift_from ~rooter:(Bap.Std.Rooter.create Seq.empty)
            (Memory.view_exn ~from:a seg))
  in
  let block_addrs =
    Term.enum sub_t program
    |> Seq.concat_map ~f:(Term.enum blk_t)
    |> Seq.filter_map ~f:(fun b ->
           Base.Option.map (Term.get_attr b address)
             ~f:(fun a -> (a, Term.tid b)))
    |> Seq.to_list
    |> Core.Map.of_alist_exn (module Addr)
  in
  let images =
    Hike.Image.get_section_images proj
    |> Base.List.map ~f:(fun (img_bytes, img_lo, img_hi) ->
           { Cbat_vsa.img_lo; img_hi; img_bytes;
             img_slots = Core.Int64.Set.empty })
  in
  let written =
    Hike.Vsa.kill_summaries ~abi:(Hike.Abi.of_target target) program
  in
  let entry =
    Term.enum sub_t program |> Seq.find ~f:(fun s -> Term.has_attr s Sub.entry_point)
  in
  match entry with
  | None -> print_endline "no entry sub"
  | Some entry -> (
    (* The original fold: every program sub solved in order, block_addrs
       growing exactly as pass_vsa's does. *)
    let subs_acc, block_addrs =
      Term.enum sub_t program
      |> Seq.fold ~init:(Tid.Map.empty, block_addrs)
           ~f:(fun (acc, block_addrs) sub ->
          let envs, sub', block_addrs', _facts =
            Hike.Vsa.fixpoint target ~lookup
              ~sub_addrs:(Core.Map.empty (module Addr)) ~images ~written
              ~foreign_slots:Core.Int64.Set.empty
              ~block_addrs sub
          in
          (Core.Map.set acc ~key:(Term.tid sub) ~data:(envs, sub'),
           Core.Map.fold block_addrs' ~init:block_addrs
             ~f:(fun ~key ~data m -> Core.Map.set m ~key ~data)))
    in
    ignore subs_acc;
    let envs, _, _, _ =
      Hike.Vsa.fixpoint target ~lookup
        ~sub_addrs:(Core.Map.empty (module Addr)) ~images:[] ~written
        ~foreign_slots:Core.Int64.Set.empty
        ~block_addrs entry
    in
    let arg0 = Hike.Abi.argc_argv_regs (Hike.Abi.of_target target) |> fst in
    let main_addr =
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
                              ~f:(fun w ->
                                Result.to_option (Cbat_word.to_int64 w))
                          | _ -> None)))
      |> Seq.hd
    in
    match main_addr with
    | None -> print_endline "no main addr"
    | Some main_addr ->
      Printf.printf "main_addr = %Lx\n" main_addr;
      match lift_at (Addr.of_int64 main_addr) ~block_addrs with
      | None | Some [] -> print_endline "lift_at failed"
      | Some blks ->
        Printf.printf "lifted blocks: %d\n" (Base.List.length blks);
        ignore (Hike.Vsa.set_addr_bits (Hike.Abi.addr_size_bits target));
        let abi = Hike.Abi.of_target target in
        let normalize blks =
          let sb = Bap.Std.Sub.Builder.create ~name:"probe_main" () in
          Base.List.iter blks ~f:(fun b ->
              let b = Term.concat_map def_t b ~f:Hike.Split_mem.split_def in
              Bap.Std.Sub.Builder.add_blk sb (Hike.Coerce.coerce_block b));
          Bap.Std.Sub.Builder.result sb
        in
        let whole = normalize blks in
        ignore whole;
        (* The fragment: everything but the root's closure, keyed by its
           call target (the second block in lift order for these shapes). *)
        ignore whole;
        let dump what s =
          Printf.printf "=== %s\n" what;
          Term.enum blk_t s
          |> Seq.iter ~f:(fun b ->
              let addr =
                match Term.get_attr b address with
                | Some a -> Printf.sprintf " @%Lx" (Word.to_int64_exn a)
                | None -> ""
              in
              Printf.printf "block %s%s\n" (Tid.name (Term.tid b)) addr;
              Term.enum jmp_t b
              |> Seq.iter ~f:(fun j ->
                  let kn =
                    match Jmp.kind j with
                    | Goto (Direct t) -> "goto " ^ Tid.name t
                    | Goto (Indirect e) ->
                      "goto ind"
                      ^ (match e with
                         | Bil.Var v -> " var " ^ Var.name v
                         | _ -> "")
                    | Call c ->
                      "call "
                      ^ (match Call.target c with
                         | Direct t -> Tid.name t
                         | Indirect _ -> "ind")
                      ^ (match Call.return c with
                         | Some (Direct t) -> " ret " ^ Tid.name t
                         | _ -> " noret")
                    | Ret (Direct t) -> "RET " ^ Tid.name t
                    | Ret (Indirect _) -> "RET ind"
                    | Int (_, t) -> "int " ^ Tid.name t
                  in
                  Printf.printf "  %s\n" kn))
        in
        (* One solve with explicit parameters. *)
        let run ~images ~written ~sub_addrs ~block_addrs what s =
          let sol =
            Cbat_vsa.with_images images (fun () ->
                Cbat_vsa.static_graph_vsa ~abi ~written
                  ~resolved:Tid.Map.empty ~sub_lookup:lookup
                  s
                  (Cbat_vsa.init_sol ~abi s))
          in
          let s1, _, ba', _facts, events =
            Hike.Cfg_complete.resolve_phase ~abi ~sol ~images
              ~block_addrs ~sub_addrs ~foreign_slots:Core.Int64.Set.empty
              s Tid.Map.empty
          in
          ignore ba';
          let s2 =
            Hike.Cfg_complete.materialize ~abi ~sol ~images
              ~block_addrs ~foreign_slots:Core.Int64.Set.empty s1
          in
          dump (Printf.sprintf "%s: resolve(events=%b) materialize" what events)
            s2
        in
        let empty : Tid.t Addr.Map.t = Core.Map.empty (module Addr) in
        ignore (run ~images:[] ~written ~sub_addrs:empty ~block_addrs
                  "whole empty-maps" whole);
        (* The EXACT new-producer flow: partition, retarget, hoist, solve
           with the extended maps, then the later passes. *)
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
        let entry_seen =
          closure (Core.Set.empty (module Tid)) [ Term.tid root ]
        in
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
          | [] -> List.rev frags
          | t :: rest ->
            if (not (Core.Map.mem by_tid t)) || not (Core.Set.mem remaining t)
            then take remaining rest frags
            else
              let seen = closure (Core.Set.empty (module Tid)) [ t ] in
              take (Core.Set.diff remaining seen) rest
                ((t, blocks_of seen) :: frags)
        in
        let frags =
          take
            (Core.Set.diff
               (Core.Set.of_list (module Tid) (Base.List.map blks ~f:Term.tid))
               entry_seen)
            call_targets []
        in
        Printf.printf "frags: %d\n" (Base.List.length frags);
        Base.List.iter frags ~f:(fun (entry_tid, blocks) ->
            Printf.printf "frag entry=%s blocks=%d:\n" (Tid.name entry_tid)
              (Base.List.length blocks);
            Base.List.iter blocks ~f:(fun b ->
                let addr =
                  match Term.get_attr b address with
                  | Some a -> Printf.sprintf "@%Lx" (Word.to_int64_exn a)
                  | None -> "@none"
                in
                Printf.printf "  %s %s\n" addr (Tid.name (Term.tid b))));
        let build_sub ~tid blocks =
          let sb = Bap.Std.Sub.Builder.create ~tid ~name:(Tid.name tid) () in
          Base.List.iter blocks ~f:(fun b ->
              let b = Term.concat_map def_t b ~f:Hike.Split_mem.split_def in
              Sub.Builder.add_blk sb (Hike.Coerce.coerce_block b));
          Sub.Builder.result sb
        in
        (* The production re-lift normalizes the FP temp widths. *)
        let fp_normalize (s : sub term) : sub term =
          Term.enum sub_t (Hike.Fp.run_program (Program.create ~subs:[ s ] ()))
          |> Seq.hd_exn
        in
        let frag_tids =
          Base.List.map frags ~f:(fun (_, blocks) ->
              let entry = Base.List.hd_exn blocks in
              match Term.get_attr entry address with
              | Some a ->
                Tid.for_name (Printf.sprintf "sub_%Lx" (Word.to_int64_exn a))
              | None -> Tid.for_name "sub")
        in
        let retarget =
          match
            Base.List.map2 frags frag_tids ~f:(fun (entry_tid, _) ftid ->
                (entry_tid, ftid))
          with
          | Ok rows -> Core.Map.of_alist_exn (module Tid) rows
          | Unequal_lengths -> failwith "frags"
        in
        let rewrite b =
          Term.map jmp_t b
            ~f:(Hike.Cfg_complete.remap_jmp
                  ~call:(fun t ->
                    Base.Option.value (Core.Map.find retarget t) ~default:t)
                  ~blk:(fun t -> t))
        in
        let frag_subs =
          match
            Base.List.map2 frags frag_tids ~f:(fun (_, blocks) ftid ->
                fp_normalize
                  (build_sub ~tid:ftid (Base.List.map blocks ~f:rewrite)))
          with
          | Ok subs -> subs
          | Unequal_lengths -> failwith "frags2"
        in
        let main_tid = Tid.for_name "main" in
        let main_sub =
          fp_normalize
            (build_sub ~tid:main_tid
               (Base.List.map (blocks_of entry_seen) ~f:rewrite))
        in
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
          (Addr.of_int64 main_addr, main_tid)
          :: Base.List.filter_map frag_subs ~f:(fun s ->
              match Term.first blk_t s with
              | Some b ->
                Base.Option.map (Term.get_attr b address)
                  ~f:(fun a -> (a, Term.tid s))
              | None -> None)
          |> Core.Map.of_alist_exn (module Addr)
          |> Core.Map.fold ~init:empty ~f:(fun ~key ~data m ->
                 Core.Map.set m ~key ~data)
        in
        let written =
          Hike.Vsa.kill_summaries ~abi
            (Bap.Std.Program.create
               ~subs:(Base.List.append
                        (Term.enum sub_t program |> Seq.to_list)
                        (frag_subs @ [ main_sub ]))
               ())
        in
        let solve s ~block_addrs =
          let envs, stamped, ba', _facts =
            Hike.Vsa.fixpoint target ~lookup ~sub_addrs ~images ~written
              ~foreign_slots:Core.Int64.Set.empty
              ~block_addrs s
          in
          (envs, stamped, ba')
        in
        let solved_frags, block_addrs, frag_envs =
          Base.List.fold frag_subs ~init:([], block_addrs, [])
            ~f:(fun (acc, ba, envs) s ->
              let e, stamped, ba' = solve s ~block_addrs:ba in
              (stamped :: acc, ba', e :: envs))
        in
        let solved_frags = List.rev solved_frags in
        let frag_envs = List.rev frag_envs in
        let main_env, main_solved, block_addrs = solve main_sub ~block_addrs in
        (* MAIN's roots: the start-successor set. *)
        let roots sub =
          let cfg = Bap.Std.Sub.to_graph sub in
          Graphs.Tid.Node.succs Graphs.Tid.start cfg
          |> Seq.filter ~f:(fun t ->
                 not (Tid.equal t Graphs.Tid.exit))
          |> Seq.to_list
          |> Base.List.map ~f:Tid.name
        in
        Printf.printf "MAIN roots: %s\n" (String.concat "," (roots main_solved));
        Base.List.iter solved_frags ~f:(fun s ->
            Printf.printf "FRAG %s roots: %s\n" (Sub.name s)
              (String.concat "," (roots s)));
        dump "REAL main after-solve" main_solved;
        Base.List.iter solved_frags ~f:(dump "REAL frag after-solve");
        (* The downstream chain, dumping jmp shapes between passes. *)
        let prog =
          Bap.Std.Program.create
            ~subs:(Base.List.append
                     (Term.enum sub_t program |> Seq.to_list)
                     (solved_frags @ [ main_solved ]))
            ()
        in
        let all_envs =
          Base.List.fold (frag_envs @ [ main_env ]) ~init:Tid.Map.empty
            ~f:(fun m envs ->
              Core.Map.fold envs ~init:m ~f:(fun ~key ~data m' ->
                  Core.Map.set m' ~key ~data))
        in
        Hike.Kb.install
          (Hike.Kb.build ~block_envs:all_envs ~block_addrs ~target ~lookup);
        let facts = Hike.Kb.facts () in
        let names =
          Term.enum sub_t prog
          |> Seq.fold ~init:Tid.Map.empty ~f:(fun m s ->
                 Core.Map.set m ~key:(Term.tid s) ~data:(Sub.name s))
        in
        let prog =
          Term.map sub_t prog ~f:(Hike.Strip_canaries.strip_sub ~facts ~names)
        in
        Base.List.iter solved_frags ~f:(fun s ->
            let s' =
              Term.enum sub_t prog
              |> Seq.find_exn ~f:(fun x ->
                     Tid.equal (Term.tid x) (Term.tid s))
            in
            dump (Printf.sprintf "after-strip %s" (Sub.name s)) s');
        let word = facts.Hike.Kb.abi.Hike.Abi.word in
        let meta = Hike.Sections.sec_meta ~word proj in
        let spans = Hike.Sections.attrib_spans ~meta in
        let prog =
          Term.map sub_t prog ~f:(fun s ->
              let dts = Hike.Sections.dynamic_alloc_tids_of ~facts s in
              Hike.Def_slots.stamp_dyn_allocs ~dynamic_alloc_tids:dts s)
        in
        let ctx =
          Hike.Sections.attribute ~facts ~word
            ~entry:Hike.Stack_model.segment_base ~spans prog
        in
        let prog =
          Term.map sub_t prog ~f:(Hike.Sections.stamp_tags ctx)
          |> Hike.Promote.rewrite_program ~word
               ~entry:Hike.Stack_model.segment_base ~facts ~spans ~ctx
        in
        Base.List.iter solved_frags ~f:(fun s ->
            let s' =
              Term.enum sub_t prog
              |> Seq.find_exn ~f:(fun x ->
                     Tid.equal (Term.tid x) (Term.tid s))
            in
            dump (Printf.sprintf "after-sections %s" (Sub.name s)) s');
        (* The real chain from the attribution on: the spec + escape roots
           install, split-blocks, sign, ssa, types, dce, then emission. *)
        let word = facts.Hike.Kb.abi.Hike.Abi.word in
        let spec =
          Hike.Sections.section_spec_of ~word
            ~comps:(Hike.Sections.global_comps_of ~word ~spans ctx)
            ~whole:(Hike.Sections.whole_comps_of ctx)
            ~meta
            ~relative:(Hike.Image.relative_values proj
                         ~bias:(Hike.Image.get_bias proj))
            ~externals:(Hike.Image.external_references proj)
        in
        let arities =
          Core.Map.map ctx.Hike.Sections.sub_trees
            ~f:(Hike.Promote.slot_arity ~word
                  ~entry:Hike.Stack_model.segment_base)
        in
        let window_readers =
          Term.enum sub_t prog
          |> Seq.fold ~init:Tid.Set.empty ~f:(fun acc sub ->
              let reads_window =
                Hike.Stack_model.is_variadic sub
                || Base.Option.value_map
                     (Core.Map.find ctx.Hike.Sections.sub_trees
                        (Term.tid sub))
                     ~default:false
                     ~f:(fun tree ->
                       Hike.Sections.Tree.to_sequence tree
                       |> Seq.exists ~f:(fun (_, rs) ->
                              Base.List.exists rs.Hike.Sections.members
                                ~f:(fun m ->
                                    m.Hike.Sections.m_identity
                                    && Hike.Sections.equal_sec
                                         m.Hike.Sections.m_sec
                                         Hike.Stack_model.Args)))
              in
              if reads_window then Core.Set.add acc (Term.tid sub) else acc)
        in
        let escape_roots =
          Term.enum sub_t prog
          |> Seq.fold ~init:Tid.Map.empty ~f:(fun m sub ->
              let tree =
                Core.Map.find ctx.Hike.Sections.sub_trees (Term.tid sub)
                |> Base.Option.value ~default:Hike.Sections.Tree.empty
              in
              Core.Map.set m ~key:(Term.tid sub)
                ~data:
                  (Hike.Sections.escape_roots_of_sub
                     ~addr_bits:(Hike.Stack_model.word_bits word)
                     ~abi:facts.Hike.Kb.abi ~arities ~window_readers ~tree
                     sub))
        in
        Hike.Kb.install (Hike.Kb.with_attribution facts ~spec ~escape_roots);
        let census what =
          let n =
            Term.enum sub_t prog
            |> Seq.find_exn ~f:(fun x -> Tid.equal (Term.tid x) main_tid)
            |> Term.enum blk_t |> Seq.to_list |> Base.List.length
          in
          Printf.printf "MAIN-BLOCKS %s: %d\n" what n
        in
        census "post-solve";
        let proj = Project.with_program proj prog in
        let proj =
          Project.with_program proj (Hike.Split_blocks.normalize (Project.program proj))
        in
        let proj = Hike.Types.sign_run proj in
        let proj =
          Project.with_program proj
            (Hike.Ssa.ssa_program ~target (Project.program proj))
        in
        let proj = Hike.Types.run proj in
        let prog = Project.program proj in
        let facts = Hike.Kb.facts () in
        census "post-types";
        let prog =
          Term.map sub_t prog ~f:(fun s ->
              let roots =
                Core.Map.find facts.Hike.Kb.escape_roots (Term.tid s)
                |> Option.value ~default:Var.Set.empty
              in
              Hike.Dce.dce ~roots ~target s)
        in
        census "post-dce";
        (* The emitter input: per-def rhs + stamps for every re-lifted
           sub, so a raw-routed def is visible beside its tags. *)
        let dump_defs what s =
          Printf.printf "EMIT-IN %s\n" what;
          Term.enum blk_t s
          |> Seq.iter ~f:(fun b ->
              Printf.printf "  blk %s\n" (Tid.name (Term.tid b));
              Term.enum jmp_t b
              |> Seq.iter ~f:(fun j ->
                  let js =
                    match Jmp.kind j with
                    | Goto (Direct t) -> "goto " ^ Tid.name t
                    | Goto (Indirect _) -> "gotoind"
                    | Call c ->
                      "call "
                      ^ (match Call.target c with
                         | Direct t -> Tid.name t
                         | Indirect _ -> "ind")
                      ^ ";ret="
                      ^ (match Call.return c with
                         | Some (Direct t) -> Tid.name t
                         | _ -> "none")
                    | Ret _ -> "ret"
                    | Int (_, t) -> "int " ^ Tid.name t
                  in
                  Printf.printf "    JMP %s\n" js);
              Term.enum phi_t b
              |> Seq.iter ~f:(fun ph ->
                  let incom =
                    Phi.values ph |> Seq.to_list
                    |> Base.List.map ~f:(fun (t, e) ->
                           Tid.name t ^ ":" ^ (Format.asprintf "%a" Exp.pp e))
                    |> String.concat " "
                  in
                  Printf.printf "    PHI %s := [%s]\n"
                    (Var.name (Phi.lhs ph)) incom);
              Term.enum def_t b
              |> Seq.iter ~f:(fun d ->
                  let a =
                    if Hike.Def_slots.def_is_window_value d then " W" else ""
                  in
                  let b =
                    match Hike.Def_slots.sec_tag d with
                    | Some t ->
                      " S" ^ (Base.Sexp.to_string (Hike.Stack_model.Tag.sexp_of_t t))
                    | None -> ""
                  in
                  let c =
                    match Hike.Def_slots.def_ptr_storage d with
                    | Some _ -> " P"
                    | None -> ""
                  in
                  let k = if Hike.Def_slots.def_ptr_kind d then " K" else "" in
                  let v = if Hike.Def_slots.def_is_dyn_alloc d then " V" else "" in
                  Printf.printf "    %s := %s%s\n"
                    (Var.name (Def.lhs d))
                    (Format.asprintf "%a" Exp.pp (Def.rhs d))
                    (String.concat "" [ a; b; c; k; v ])))
        in
        Base.List.iter solved_frags ~f:(fun s ->
            dump_defs (Printf.sprintf "frag %s" (Sub.name s))
              (Term.enum sub_t prog
              |> Seq.find_exn ~f:(fun x -> Tid.equal (Term.tid x) (Term.tid s))));
        dump_defs "main"
          (Term.enum sub_t prog
          |> Seq.find_exn ~f:(fun x -> Tid.equal (Term.tid x) main_tid));
        (* Emission: the exact entry the pass runs.  The prune keeps the
           re-lifted subs and the entry (emitted as a declaration), so the
           probe's module carries the same body set for these shapes. *)
        let keep =
          Core.Set.of_list (module Tid)
            (Base.List.map solved_frags ~f:Term.tid
            @ [ main_tid; Term.tid entry ])
        in
        let prog =
          Term.filter sub_t prog ~f:(fun s -> Core.Set.mem keep (Term.tid s))
        in
        let llvm_ctx = Llvm.create_context () in
        let llvm_module = Llvm.create_module llvm_ctx "ReliftProbe" in
        let out_file =
          if Array.length Sys.argv > 2 then Sys.argv.(2)
          else "/tmp/relift_probe.ll"
        in
        Hike.Bil2llvm.emit_program llvm_ctx llvm_module ~target
          ~addr_bits:(Hike.Abi.addr_size_bits target)
          ~symtab:(Some (Project.symbols proj))
          (Base.Option.value_exn facts.Hike.Kb.spec
             ~message:"probe: no spec installed")
          prog;
        Llvm.print_module out_file llvm_module;
        Printf.printf "EMITTED %s\n" out_file;
        flush stdout)
