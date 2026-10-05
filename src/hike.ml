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
module Attribution = Hike_attribution
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
  let prog = Project.program proj in
  Bil2llvm.emit_program llvm_ctx llvm_module
    ~target ~addr_bits
    ~symtab:(Some (Project.symbols proj))
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

(* The prune's closure debug; thunk-guarded like the completion's
   trace, so production never formats it. *)
let dbg_closure (msg : unit -> string) =
#ifdef VSA_DEBUG
  Printf.eprintf "hike-dbg-closure: %s\n%!" (msg ())
#else
  ignore msg
#endif

let pass_vsa proj =
  let target = Project.target proj in
  if Hike_abi.is_known_foreign target then
    Hike_diag.warn
      "target %s is not x86_64-gnu-elf; the x86-64 SysV convention record serves it"
      (KB.Name.to_string (Theory.Target.name target));
  (* The executable span: the completion's table walk reads a composed
     table's consecutive cells and keeps the entries that land in code. *)
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
          Int64.of_int (Hike_abi.word_bits (Hike_abi.of_target target) / 8)
        in
        [ lo; Int64.add lo w; Int64.add lo (Int64.mul 2L w) ]
      | None -> []
    in
    Hike_image.external_references proj
    |> Base.List.map ~f:fst
    |> Base.List.append reserved
    |> Core.Int64.Set.of_list
  in
  (* The ABI-reserved .got.plt head: the dynamic linker's own protocol
     slots (the link map and the resolver entry).  A sub whose exits
     transfer through one is the loader's machinery — the resolver
     head — whatever calls reach it. *)
  let reserved_slots =
    match range_of_section ".got.plt" with
    | Some (lo, _) ->
      let w =
        Int64.of_int (Hike_abi.word_bits (Hike_abi.of_target target) / 8)
      in
      Core.Int64.Set.of_list [ lo; Int64.add lo w; Int64.add lo (Int64.mul 2L w) ]
    | None -> Core.Int64.Set.empty
  in
  (* Image-backed loads are sound only where the runtime content is
     known: a relocation-free section is its file bytes, a section
     holding relocated words is its RELATIVE words' runtime values plus
     the bytes no relocation names, and a linker-owned slot's word is
     no value at all. *)
  let images =
    Hike_image.get_section_images proj
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
  (* The primary program's entry address: the fact the lifted program's
     entry sub is stamped from every round. *)
  let entry_addr =
    Term.enum sub_t (Project.program proj)
    |> Seq.filter_map ~f:(fun s ->
        if Term.has_attr s Sub.entry_point then
          Base.Option.bind (Term.first blk_t s) ~f:(fun b ->
              Term.get_attr b address)
        else None)
    |> Seq.hd
  in
  (* ---- the drive loop ---- *)
  (* One decode → solve → facts → decode fixpoint, BAP owning the
     structure: its scan decodes under the run's facts, its partition
     creates the subs, its symtab lift resolves the calls and builds
     the program.  The run's acts are the solve and the two fact kinds
     — an [is_subroutine] root per discovered entry, and the resolved
     destinations provided on the dispatch instructions
     ([collect_dests]'s own channel; [provide] unions, so a later
     round's larger set joins the earlier one).  Every round rebuilds
     the program from the decode, so a discovered sub is in the program
     the round after its discovery, and every sub solves under the same
     fold. *)
  let file = Hike_drive.file_of (Project.program proj) in
  (* The relocation lane's static facts: a relocated data word naming an
     unclaimed entry of the executable section is a root (the dead-text
     discovery).  The init/fini arrays are excluded: they belong to
     nothing the module runs. *)
  let init_fini_slots =
    Base.List.filter_map [ ".init_array"; ".fini_array" ] ~f:range_of_section
  in
  let rels =
    Hike_image.relative_values proj ~bias:(Hike_image.get_bias proj)
  in
  let is_code_addr v =
    match text_range with
    | Some (lo, hi) ->
      Int64.compare v lo >= 0 && Int64.compare v hi <= 0
    | None -> false
  in
  let in_init_fini slot =
    Base.List.exists init_fini_slots ~f:(fun (lo, hi) ->
        Int64.compare slot lo >= 0 && Int64.compare slot hi <= 0)
  in
  (* The decode channel: a resolved destination becomes a fact on the
     dispatch INSTRUCTION's own label. *)
  let provide_dests site w =
    let run : unit Toplevel.var = Toplevel.var "hike-drive-dests" in
    Toplevel.put run
      (let open KB.Syntax in
       let addr a = Word.to_bitvec (Addr.of_int64 a) in
       Theory.Label.for_addr ~package:file (addr site) >>= fun label ->
       Theory.Label.for_addr ~package:file (addr w) >>= fun dest ->
       KB.collect Theory.Semantics.slot label >>= fun sema ->
       let cur =
         match KB.Value.get Insn.Slot.dests sema with
         | Some s -> s
         | None -> Core.Set.empty (module Theory.Label)
       in
       KB.provide Theory.Semantics.slot label
         (KB.Value.put Insn.Slot.dests sema (Some (Core.Set.add cur dest))));
    Toplevel.get run
  in
  (* The run's roots: the relocation lane's code words seed them (main's
     denotation is a round's own discovery); the harvest grows them. *)
  let roots = ref [] in
  let add_root w =
    if is_code_addr w && not (Base.List.mem !roots w ~equal:Int64.equal)
    then roots := !roots @ [ w ]
  in
  Base.List.iter rels ~f:(fun (slot, value) ->
      if is_code_addr value && not (in_init_fini slot) then add_root value);
  let rounds_left = ref 64 in
  (* The bounded word set of a target denotation, as module addresses;
     a set too wide to enumerate names nothing. *)
  let bounded_words (ws : Cbat_vsa.WordSet.t) : int64 list option =
    if
      Cbat_vsa.WordSet.is_top ws
      || Cbat_vsa.WordSet.is_bottom ws
      || Cbat_vsa.WordSet.is_infinite ws
    then None
    else
      match Cbat_word.to_int64 (Cbat_vsa.WordSet.cardinality ws) with
      | Error _ -> None
      | Ok n when n <= 0L || n > 64L -> None
      | Ok _ ->
        Some
          (Base.List.filter_map (Cbat_vsa.WordSet.iter ws)
             ~f:(fun w -> Result.to_option (Cbat_word.to_int64 w)))
  in
  (* Every surviving indirect transfer's bounded words, denotated at
     the state its block reads; the dispatch sites' own word sets ride
     the completion's facts (collected during the solve).  The
     call-class words are sub entries, the goto-class words the
     dispatch's case bodies. *)
  let transfer_words (envs, sub') : (int64 * bool * int64 list) list =
    Base.List.concat_map (Term.enum blk_t sub' |> Seq.to_list)
      ~f:(fun blk ->
        match Core.Map.find envs (Term.tid blk) with
        | None -> []
        | Some (pre, post) -> (
          match Term.get_attr blk address with
          | None -> []
          | Some site ->
            let site = Word.to_int64_exn site in
            Base.List.filter_map (Term.enum jmp_t blk |> Seq.to_list)
              ~f:(fun j ->
                (* A real call (one WITH a return) names function
                   starts — the pushed return address is the ABI's
                   entry contract.  BAP renders an indirect TAIL JUMP
                   as a noreturn call; its destinations are jump
                   destinations, not entries (rooting them carves the
                   dispatching loop into per-case subs and hands the
                   loop head its own sub). *)
                let call, e =
                  match Jmp.kind j with
                  | Goto (Indirect e) -> (false, Some e)
                  | Call c -> (
                    match Call.target c with
                    | Indirect e ->
                      (Base.Option.is_some (Call.return c), Some e)
                    | _ -> (true, None))
                  | _ -> (false, None)
                in
                match e with
                | None | Some (Bil.Int _) -> None
                | Some e -> (
                  match Cbat_vsa.denote_exp_at ~pre ~post ~blk e with
                  | Error _ -> None
                  | Ok ws ->
                    Base.Option.map (bounded_words ws) ~f:(fun words ->
                        (site, call, words))))))
  in
  (* The completion's dispatch facts: the sites' word sets the solve's
     phases enumerated.  A goto fact decodes as the dispatching sub's
     own case body when it sits in no claimed span or in the
     dispatching sub's span; a foreign span names another sub's
     territory and rides nothing. *)
  (* Every resolved word rides the fact channel; the harvest routes it
     by class.  Nothing is dropped for sitting in another sub's
     territory — the owning sub is where the driver decodes it. *)
  (* The store lane: a solved root's store whose data denotates to a
     code word names a callee the pointer round trip loses at the
     load.  A store wider than the word packs one address per word
     cell (the vector table-init idiom); each cell names a callee on
     its own. *)
  let store_words (envs, stamped) : int64 list =
    let wb =
      Hike_stack_model.word_bits
        (Hike_abi.of_target target).Hike_abi.word
    in
    Base.List.concat_map (Term.enum blk_t stamped |> Seq.to_list)
      ~f:(fun blk ->
        match Core.Map.find envs (Term.tid blk) with
        | None -> []
        | Some (pre, post) ->
          Base.List.concat_map (Term.enum def_t blk |> Seq.to_list)
            ~f:(fun d ->
              match Hike_stack_model.store_data_of_rhs (Def.rhs d) with
              | None -> []
              | Some vexp ->
                let candidates =
                  match Hike_stack_model.addr_of_rhs (Def.rhs d) with
                  | Some (_, size) when Size.in_bits size > wb ->
                    Base.List.init (Size.in_bits size / wb) ~f:(fun k ->
                        let lo = k * wb in
                        Bil.extract ~hi:(lo + wb - 1) ~lo vexp)
                  | _ -> [ vexp ]
                in
                Base.List.filter_map candidates ~f:(fun vexp ->
                    match
                      Cbat_vsa.denote_exp_at ~pre ~post ~blk ~def:d vexp
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
                      | _ -> None))))
  in
  (* One round: BAP decodes and partitions, the run solves every sub of
     the decoded program under the same fold, and the harvest routes
     every resolved word by its class — a call-class word, or a goto
     word naming a partition entry (the cross-sub dispatch's handlers
     are other subs' entries), is a root; any other goto word is a case
     body the driver decodes inside its owning sub.  The loop settles
     when neither the decode nor the discoveries grow. *)
  let rec round prev =
    if !rounds_left <= 0 then begin
      Hike_diag.warn "vsa: the drive loop stopped at its round budget";
      (match prev with
       | Some (_, _, products) -> products
       | None -> failwith "hike-vsa: the drive loop's first round exceeded the budget")
    end else begin
      rounds_left := !rounds_left - 1;
      match Hike_drive.rescan proj ~file ~roots:!roots with
      | None -> failwith "hike-vsa: the drive loop's re-scan produced nothing"
      | Some out ->
        (* The lifted program is BAP's raw BIR: the normalizer chain runs
           over it once per round — one memory node per def, width-honest
           binops, the FP temp widths — so every later reader takes the
           terms as the passes left them. *)
        let lifted =
          Hike_drive.program_of_state out.grown out.subs
          |> Hike_split_mem.normalize |> Hike_coerce.coerce_program
          |> Hike_fp.run_program
        in
        (* The entry sub is the target's own fact (B1): the primary
           program's entry names the address; the lifted program's sub
           at that address carries the attr every later reader reads. *)
        let program =
          match entry_addr with
          | None -> lifted
          | Some ea ->
            Term.map sub_t lifted ~f:(fun s ->
                match Term.first blk_t s with
                | Some b -> (
                  match Term.get_attr b address with
                  | Some a when Addr.equal a ea ->
                    Term.set_attr s Sub.entry_point ()
                  | _ -> s)
                | None -> s)
        in
        (* The site → terminator-instruction map, off this round's
           decode: the solver's jmp rewrites drop the jmp's own
           [address] attr, so a dispatch's site is its BLOCK's address
           while the dests facts key on the instruction label. *)
        let terminator_of =
          let m =
            Core.Map.of_alist_exn (module Core.Int64)
              (Base.List.map (Hike_drive.terminators out.cfg)
                 ~f:(fun (b, i) ->
                   (Word.to_int64_exn b, Word.to_int64_exn i)))
          in
          fun a -> Base.Option.value (Core.Map.find m a) ~default:a
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
        let entry_addrs =
          Term.enum sub_t program
          |> Seq.fold ~init:Core.Int64.Map.empty ~f:(fun m s ->
                 match Term.first blk_t s with
                 | Some b -> (
                   match Term.get_attr b address with
                   | Some a ->
                     Core.Map.set m ~key:(Word.to_int64_exn a)
                       ~data:(Term.tid s)
                   | None -> m)
                 | None -> m)
        in
        let named =
          Hike_resolve.symtab_lookup
            ~symtab:(Some (Project.symbols proj))
            ~table:(Hike_resolve.name_table_of program)
            ~addr_bits:(Hike_abi.addr_size_bits target)
        in
        let lookup v =
          match named v with
          | Some t -> Some t
          | None -> Core.Map.find entry_addrs v
        in
        let sub_addrs =
          Core.Map.fold block_addrs ~init:Addr.Map.empty
            ~f:(fun ~key:addr ~data:_ m ->
              match lookup (Word.to_int64_exn addr) with
              | Some sub -> Core.Map.set m ~key:addr ~data:sub
              | None -> m)
        in
        let written =
          Hike_vsa.kill_summaries ~abi:(Hike_abi.of_target target) program
        in
        let subs_acc, dfacts, block_addrs =
          Term.enum sub_t program
          |> Seq.fold ~init:(Tid.Map.empty, [], block_addrs)
               ~f:(fun (acc, dfs, ba) sub ->
                 let envs, sub', ba', facts =
                   Hike_vsa.fixpoint target ~lookup ~sub_addrs ~images
                     ~written ~foreign_slots:linker_slots
                     ~code_range:text_range ~block_addrs:ba sub
                 in
                 (Core.Map.set acc ~key:(Term.tid sub) ~data:(envs, sub'),
                  Base.List.append dfs facts,
                  ba'))
        in
        (* main: the address the entry passes to the runtime — the
           entry's call block's postcondition denotates it as a
           singleton.  A named sub sits there (the symtab names it); a
           stripped binary has no sub at the address, and the fact
           routes it as a root for the next scan. *)
        let main_addr =
          match
            Term.enum sub_t program
            |> Seq.find ~f:(fun s -> Term.has_attr s Sub.entry_point)
          with
          | None -> None
          | Some entry -> (
            match Core.Map.find subs_acc (Term.tid entry) with
            | None -> None
            | Some (envs, sub') ->
              let arg0 = Abi.argc_argv_regs (Hike_abi.of_target target) |> fst in
              Term.enum blk_t sub'
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
                          Cbat_vsa.denote_exp_at ~pre:post ~post ~blk
                            (Bil.Var arg0)
                        with
                        | Error _ -> None
                        | Ok ws -> (
                          match
                            Cbat_word.to_int64
                              (Cbat_vsa.WordSet.cardinality ws)
                          with
                          | Ok 1L ->
                            Base.Option.bind (Cbat_vsa.WordSet.min_elem ws)
                              ~f:(fun w ->
                                Result.to_option (Cbat_word.to_int64 w))
                          | _ -> None)))
              |> Seq.hd)
        in
        let found_roots = ref [] in
        let found_dests = ref [] in
        (* The route follows the decode's own two channels: a real
           call's word, main, or a word already naming a sub is a
           FUNCTION START (the rooter); every other word is a JUMP
           DESTINATION (the brancher) — the driver decodes it as plain
           code and the partition assigns it to its owning sub.  An
           undecoded in-span case body is a destination, never an
           entry: rooting it carves its owner at the dispatch. *)
        (match main_addr with
         | Some w ->
           if not (Base.List.mem !found_roots w ~equal:Int64.equal) then
             found_roots := w :: !found_roots;
           add_root w
         | None -> ());
        let route site call w =
          if call || Core.Map.mem sub_addrs (Addr.of_int64 w) then begin
            if not (Base.List.mem !found_roots w ~equal:Int64.equal) then
              found_roots := w :: !found_roots;
            add_root w
          end else begin
            let site = terminator_of site in
            if
              not
                (Base.List.mem !found_dests (site, w)
                   ~equal:(fun (a, x) (b, y) ->
                     Int64.equal a b && Int64.equal x y))
            then found_dests := (site, w) :: !found_dests;
            provide_dests site w
          end
        in
        Core.Map.fold subs_acc ~init:() ~f:(fun ~key:_ ~data:solved () ->
            Base.List.iter (transfer_words solved)
              ~f:(fun (site, call, words) ->
                Base.List.iter words ~f:(route site call)));
        Base.List.iter dfacts ~f:(fun (a, call, ws) ->
            let site = Word.to_int64_exn a in
            Base.List.iter ws ~f:(fun w ->
                match Result.to_option (Cbat_word.to_int64 w) with
                | Some v -> route site call v
                | None -> ()));
        (* The store lane over every solved sub: a store whose data
           denotates to a code word names a callee the pointer round
           trip loses at the load — an entry only outside the
           partition's territory (a stored address inside a sub's
           territory is that sub's own code). *)
        let unclaimed w =
          not
            (Disasm.Subroutines.entries out.subs
             |> Core.Set.exists ~f:(fun e ->
                 Disasm.Subroutines.belongs out.subs ~entry:e
                   (Addr.of_int64 w)))
        in
        Core.Map.fold subs_acc ~init:() ~f:(fun ~key:_ ~data:solved () ->
            Base.List.iter (store_words solved) ~f:(fun w ->
                if unclaimed w then add_root w));
        let disc =
          (Base.List.sort !found_roots ~compare:Int64.compare,
           Base.List.sort !found_dests
             ~compare:(fun (a, x) (b, y) ->
               let c = Int64.compare a b in
               if c <> 0 then c else Int64.compare x y))
        in
        let products =
          (out, program, subs_acc, block_addrs, sub_addrs, entry_addrs,
           lookup, main_addr)
        in
        let settled =
          match prev with
          | Some (pstate, pdisc, _) ->
            Disasm.Driver.equal pstate out.grown
            && Base.List.equal Int64.equal (fst disc) (fst pdisc)
            && Base.List.equal
                 (fun (a, x) (b, y) -> Int64.equal a b && Int64.equal x y)
                 (snd disc) (snd pdisc)
          | None -> false
        in
        if settled then products
        else round (Some (out.grown, disc, products))
    end
  in
  let _out, program0, subs_acc, block_addrs, sub_addrs, entry_addrs, lookup,
    main_addr =
    round None
  in
  let main_tid =
    match main_addr with
    | None -> None
    | Some a ->
      Term.enum sub_t program0
      |> Seq.find_map ~f:(fun s ->
             match Term.get_attr s address with
             | Some x when Addr.equal x (Addr.of_int64 a) ->
               Some (Term.tid s)
             | _ -> None)
  in
  let all_envs =
    Core.Map.fold subs_acc ~init:Tid.Map.empty
      ~f:(fun ~key:_ ~data:(envs, _) m ->
        Core.Map.fold envs ~init:m
          ~f:(fun ~key ~data m' -> Core.Map.set m' ~key ~data))
  in
  Hike_kb.install
    { (Hike_kb.build ~block_envs:all_envs ~block_addrs ~target ~lookup) with
      Hike_kb.sub_addrs; images; foreign_slots = linker_slots };
  let facts = Hike_kb.facts () in
  (* The solved program: the loop's lift with every sub replaced by its
     solved rewrite.  Nothing is appended — the program already carries
     every sub the decode discovered. *)
  let program =
    Term.map sub_t program0 ~f:(fun sub ->
        Option.value
          (Base.Option.map (Core.Map.find subs_acc (Term.tid sub)) ~f:snd)
          ~default:sub)
  in
  (* The subs whose every exit leaves the module: a call to a block-less
     sub (a declaration — the loader owns it), an indirect through a
     linker-owned slot (the resolver owns the value), a return, an
     interrupt, or a call to another such sub.  A trampoline's body —
     the lazy-binding tail and the PLT's resolver path — never runs in
     the lifted module (the loader binds externals directly), so such a
     sub is itself a declaration: the prune cuts its edges and the
     emitter declares it. *)
  let leaving =
    let sub_list = Term.enum sub_t program |> Seq.to_list in
    let block_less s = Base.Option.is_none (Term.first blk_t s) in
    (* The loader binds DYNAMIC symbols only, and every dynamic
       external is a block-less sub of the program: a leaving
       candidate with a block-less twin of its own name is the
       loader's (its declare resolves); a candidate without one is
       module code that happens to tail out (a computed wrapper) —
       the module defines it. *)
    let dyn_name n =
      if Base.String.is_suffix ~suffix:":external" n then
        Base.String.sub ~pos:0 ~len:(Base.String.length n - 9) n
      else n
    in
    let dyn_names =
      Base.Set.of_list (module Base.String)
        (Base.List.filter_map sub_list ~f:(fun s ->
             if block_less s then Some (dyn_name (Sub.name s)) else None))
    in
    (* A candidate that no module code CALLS is dead when declared
       (the resolver protocol nothing enters by call); a called
       candidate needs the loader to bind its name (the dynamic twin)
       or the module defines its body. *)
    let called_tids =
      Base.Set.of_list (module Tid)
        (Base.List.concat_map sub_list ~f:(fun s ->
             Term.enum blk_t s |> Seq.concat_map ~f:(Term.enum jmp_t)
             |> Seq.filter_map ~f:(fun j ->
                    match Jmp.kind j with
                    | Call c -> (
                      match Call.target c with
                      | Direct t -> Some t
                      | _ -> None)
                    | _ -> None)
             |> Seq.to_list))
    in
    (* The sub leaves iff every exit in its body transfers to the
       loader's hands — a call to a block-less sub (a declaration — the
       loader binds it), a call to another leaving sub, an indirect
       through a linker-owned slot (the resolver owns the value), a
       trap — or is the loader protocol's own plumbing: a direct goto
       to a block of the SAME sub (the PLT's lazy tail and resolver
       head, which the partition absorbed into the stub — internal to
       the family, never a transfer into the module's computed code),
       with at least one loader-bound exit.  A sub whose body computes
       (a return, a call into the module) stays. *)
    let leaves seen s =
      let own_blocks =
        Core.Set.of_list (module Tid)
          (Term.enum blk_t s |> Seq.map ~f:Term.tid |> Seq.to_list)
      in
      let call_leaves s t =
        if Hike_return.is_target t || Tid.name t = "hike_return" then false
        else
          match
            Base.List.find sub_list ~f:(fun x -> Tid.equal (Term.tid x) t)
          with
          | Some callee ->
            block_less callee || Core.Set.mem seen (Term.tid callee)
          | None -> true
      in
      (* [Some true] = leaves; [Some false] = stays; [None] = internal
         plumbing (neither). *)
      let sub_of_block t =
        Base.List.find sub_list ~f:(fun x ->
            Term.enum blk_t x
            |> Seq.exists ~f:(fun b -> Tid.equal (Term.tid b) t))
      in
      let exit_kind s j =
        if Hike_return.is_jmp j then Some false
        else
          match Jmp.kind j with
          | Ret _ -> Some false
          | Int _ -> Some true
          | Goto (Direct t) ->
            if Core.Set.mem own_blocks t then None
            else
              (* A jump into another sub that itself only leaves (the
                 lazy tail into the resolver head) is the loader's
                 protocol, not a transfer into computed code. *)
              (match sub_of_block t with
               | Some x ->
                 Some
                   (block_less x || Core.Set.mem seen (Term.tid x))
               | None -> Some false)
          | Goto (Indirect e) -> (
            match Hike_transfer.slot_of_target ~sub:s e with
            | Some a -> Some (Core.Set.mem linker_slots a)
            | None -> Some false)
          | Call c -> (
            match Call.target c with
            | Indirect e -> (
              match Hike_transfer.slot_of_target ~sub:s e with
              | Some a -> Some (Core.Set.mem linker_slots a)
              | None -> Some false)
            | Direct t -> Some (call_leaves s t))
      in
      let reserved_transfer =
        Term.enum blk_t s |> Seq.concat_map ~f:(Term.enum jmp_t)
        |> Seq.exists ~f:(fun j ->
               let slot e =
                 Base.Option.bind (Hike_transfer.slot_of_target ~sub:s e)
                   ~f:(fun a -> Some (Core.Set.mem reserved_slots a))
               in
               match Jmp.kind j with
               | Goto (Indirect e) ->
                 Base.Option.value ~default:false (slot e)
               | Call c -> (
                 match Call.target c with
                 | Indirect e ->
                   Base.Option.value ~default:false (slot e)
                 | _ -> false)
               | _ -> false)
      in
      match
        Term.enum blk_t s |> Seq.concat_map ~f:(Term.enum jmp_t) |> Seq.to_list
      with
      | [] -> block_less s
      | js ->
        (block_less s
        || Core.Set.mem dyn_names (dyn_name (Sub.name s))
        || reserved_transfer
        || not (Core.Set.mem called_tids (Term.tid s)))
        && Base.List.for_all js ~f:(fun j -> exit_kind s j <> Some false)
        && Base.List.exists js ~f:(fun j -> exit_kind s j = Some true)
    in
    let rec fix seen =
      let more =
        Base.List.filter sub_list ~f:(fun s ->
            not (Core.Set.mem seen (Term.tid s)) && leaves seen s)
      in
      match more with
      | [] -> seen
      | _ ->
        fix
          (Base.List.fold more ~init:seen ~f:(fun acc s ->
               Core.Set.add acc (Term.tid s)))
    in
    fix (Core.Set.empty (module Tid))
  in
  dbg_closure (fun () ->
      let exit_kinds s =
        Term.enum blk_t s
        |> Seq.concat_map ~f:(Term.enum jmp_t)
        |> Seq.map ~f:(fun j ->
            match Jmp.kind j with
            | Ret _ -> "ret"
            | Int _ -> "int"
            | Goto (Direct t) -> "goto " ^ Tid.name t
            | Goto (Indirect _) -> "gotoind"
            | Call c -> (
              match Call.target c with
              | Direct t -> "call " ^ Tid.name t
              | Indirect _ -> "callind"))
        |> Seq.to_list
        |> String.concat ","
      in
      let one s = Sub.name s ^ "(" ^ exit_kinds s ^ ")" in
      let names =
        Term.enum sub_t program
        |> Seq.filter ~f:(fun s -> Core.Set.mem leaving (Term.tid s))
        |> Seq.map ~f:one
        |> Seq.to_list
        |> String.concat ","
      in
      "leaving=[" ^ names ^ "]");
  let program =
    Term.map sub_t program ~f:(fun s ->
        if Core.Set.mem leaving (Term.tid s)
        then Hike_stack_model.set_plt_trampoline s
        else s)
  in
  (* The recreated program is rooted at main: the prune walks its own
     edges. *)
  let discovered : Tid.t list = [] in
  (* The runtime's own stubs drop by reachability from the program's
     root (main), never by spelling.  The closure follows direct call
     targets and every target a bounded denotation names; an unbounded
     target or a relocated-slot read names no in-module sub and
     contributes no edge.  Without a root the prune does not run: the
     identity keeps every sub. *)
  let pruned_program =
    let roots =
      match main_tid with
      | Some t -> t :: discovered
      | None -> discovered
    in
    match roots with
    | [] -> program
    | root :: roots -> (
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
      let relocated = linker_slots in
      (* The set's own words of a bounded target denotation; [None] when
         the target is unbounded or the set is too wide to enumerate.
         The width compares as a WORD (unsigned): a cardinality past
         2^63 signed-extracts negative through int64 and a signed
         compare would read it small. *)
      let bounded_words (ws : Cbat_vsa.WordSet.t) : Cbat_word.t list option =
        if
          Cbat_vsa.WordSet.is_top ws
          || Cbat_vsa.WordSet.is_infinite ws
          || Cbat_vsa.WordSet.is_bottom ws
          || Cbat_word.gt_int (Cbat_vsa.WordSet.cardinality ws) 64
        then None
        else Some (Cbat_vsa.WordSet.iter ws)
      in
      let target_words ~blk e =
        match facts.Hike_kb.denote ~blk e with
        | Ok ws -> bounded_words ws
        | _ -> None
      in
      (* A target read through a relocated slot names no lifted sub: the
         slot rule resolves the target's load through the sub's own defs
         (the load may sit in any block). *)
      let is_foreign_boundary ~sub e =
        match Hike_transfer.slot_of_target ~sub e with
        | Some a -> Core.Set.mem relocated a
        | None -> false
      in
      let resolve_word w =
        match Cbat_word.to_int64 w with
        | Ok v -> Core.Map.find sub_addrs (Addr.of_int64 v)
        | Error _ -> None
      in
      (* A target var whose reaching def reads the return-address cell is
         the return epilogue, never a dispatch.  A BOTTOM address proves
         the shape only on a path the solve proved dead (a wholly-BOTTOM
         env); inside a live env it is an absent var — a never-defined
         register — and names no return. *)
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
                || (Cbat_vsa.WordSet.is_bottom ws
                    && Base.Option.value_map
                         (Cbat_vsa.env_tag d)
                         ~default:false
                         ~f:(fun env ->
                           Cbat_vsa.AI.equal env Cbat_vsa.AI.bottom))
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
                              (* A call's return continuation is an edge
                                 whatever the target's class: the call
                                 returns to it. *)
                              let seen =
                                match Call.target c with
                                | Indirect e ->
                                  (* A slot-read target leaves the program;
                                     the walk claims no deadness it cannot
                                     prove — only an unresolvable indirect
                                     keeps the blocks it cannot exclude. *)
                                  dbg_closure (fun () ->
                                      Printf.sprintf "call-ind %s blk %s exp %s foreign=%b"
                                        (Sub.name sub) (Tid.name (Term.tid blk))
                                        (Exp.to_string e)
                                        (is_foreign_boundary ~sub e));
                                  if is_foreign_boundary ~sub e then seen
                                  else (keeps_all := true; seen)
                                | _ -> seen
                              in
                              match Call.return c with
                              | Some (Direct l) -> go seen l
                              | _ -> seen)
                          | Ret _ -> seen
                          | Goto (Indirect e) ->
                            dbg_closure (fun () ->
                                Printf.sprintf "goto-ind %s blk %s exp %s foreign=%b"
                                  (Sub.name sub) (Tid.name (Term.tid blk))
                                  (Exp.to_string e)
                                  (is_foreign_boundary ~sub e));
                            if is_foreign_boundary ~sub e then seen
                            else (keeps_all := true; seen))
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
        (* A sub whose every exit leaves the module is a declaration:
           its edges leave with it. *)
        if Core.Set.mem leaving (Term.tid sub) then Some []
        else begin
        let reach = reachable_tids sub in
        let refuse blk =
          Hike_diag.warn
            "prune: sub %s: block %s: indirect target is neither resolvable \
             nor a foreign boundary - keeping every sub"
            (Sub.name sub) (Tid.name (Term.tid blk))
        in
        let indirect ~blk e =
          if is_foreign_boundary ~sub e then Some []
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
        end
      in
      (* An address taken as a VALUE (a callback handed to a foreign API —
         atexit, qsort) is an edge the native side walks: a def whose
         denotation names an in-module sub keeps that sub, and the
         closure recurses into its own calls. *)
      let addr_targets_of_sub sub =
        let reach = reachable_tids sub in
        Term.enum blk_t sub
        |> Seq.filter ~f:(fun blk -> Core.Set.mem reach (Term.tid blk))
        |> Seq.to_list
        |> Base.List.concat_map ~f:(fun blk ->
            Term.enum def_t blk
            |> Seq.to_list
            |> Base.List.filter_map ~f:(fun d ->
                match facts.Hike_kb.denote ~blk ~def:d (Def.rhs d) with
                | Ok ws -> (
                  match bounded_words ws with
                  | Some ws ->
                    Some
                      (Base.List.filter_map ws ~f:(fun w ->
                           match Cbat_word.to_int64 w with
                           | Ok v -> Core.Map.find sub_addrs (Addr.of_int64 v)
                           | Error _ -> None))
                  | None -> None)
                | _ -> None)
            |> Base.List.concat)
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
                else
                  match edges_of_sub s with
                  | None -> None
                  | Some es ->
                    dbg_closure (fun () ->
                        let blk_str b =
                          let a =
                            match Term.get_attr b address with
                            | Some a -> Addr.to_string a
                            | None -> "?"
                          in
                          let nj = Seq.length (Term.enum jmp_t b) in
                          Printf.sprintf "%s@%s:%dj" (Tid.name (Term.tid b)) a nj
                        in
                        Printf.sprintf "%s a=%s blocks=[%s] -> [%s]"
                          (Sub.name s)
                          (match Term.get_attr s address with
                           | Some a -> Addr.to_string a
                           | None -> "none")
                          (Term.enum blk_t s |> Seq.map ~f:blk_str
                           |> Seq.to_list |> String.concat " ")
                          (Base.List.map es ~f:Tid.name |> String.concat ","));
                    Some (es @ addr_targets_of_sub s)
              in
              match more with
              | None -> None
              | Some more -> closure seen (more @ rest)
      in
      match
        closure (Core.Set.empty (module Tid)) (root :: roots)
      with
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

(* ELF facts are read here; attribution owns the BIR and facts protocol. *)
let pass_attrib proj =
  let facts = Hike_kb.facts () in
  let word = facts.abi.Hike_abi.word in
  let meta = Hike_sections.sec_meta ~word proj in
  let spans = Hike_sections.attrib_spans ~meta in
  let result =
    Hike_attribution.run ~facts ~word
      ~entry:Hike_stack_model.segment_base ~spans ~meta
      ~relative:(Hike_image.relative_values proj ~bias:(Hike_image.get_bias proj))
      ~externals:(Hike_image.external_references proj) (Project.program proj)
  in
  Hike_kb.install result.facts;
  Project.with_program proj result.program

(* The sweep runs after [hike-types]: SSA has materialized the joins, so
   the dead values only the versioned defs and phis distinguish are
   removable.  The escape roots ride the facts from the attribution. *)
let pass_dce proj =
  let facts = Hike_kb.facts () in
  let target = facts.target in
  Project.map_program proj ~f:(fun prog ->
      Term.map sub_t prog ~f:(fun sub ->
          let roots =
            Core.Option.value
              (Core.Map.find facts.escape_roots (Term.tid sub))
              ~default:Var.Set.empty
          in
          Hike_dce.dce ~target ~escape_roots:roots sub))

let pass_convlir ~output proj = convert_binary output proj

let pass_split_blocks proj =
  Project.map_program proj ~f:Hike_split_blocks.normalize

let pass_ssa proj =
  let target = Project.target proj in
  Project.map_program proj ~f:(Hike_ssa.ssa_program ~target)

let () =
  Extension.declare ~provides:["pass"; "hike"] (fun ctx ->
      let output_file = Extension.Configuration.get ctx output in
      (* The filter runs AFTER the VSA: the complete program — the
         re-decode's own subs included — is what gets filtered, so the
         re-discovered stubs and externs drop by the same rules. *)
      Project.register_pass ~name:"jump" ~runonce:true
        (fun proj -> map_subs (Hike_jump.compile_sub (Project.target proj)) proj);
      let jump = last_pass () in
      let split_mem = chain ~name:"split-mem" ~deps:[ jump ] pass_split_mem in
      let coerce = chain ~name:"coerce" ~deps:[ split_mem ] pass_coerce in
      let fp = chain ~name:"fp" ~deps:[ coerce ] pass_fp in
      let vsa = chain ~name:"vsa" ~deps:[ fp ] pass_vsa in
      let filter = chain ~name:"filter" ~deps:[ vsa ] pass_filter in
      let strip_canaries =
        chain ~name:"strip-canaries" ~deps:[ filter ] pass_strip_canaries
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
