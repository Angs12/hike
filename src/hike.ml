open Bap.Std
open Bap_main
open Bap_core_theory
module Atomic = Hike_atomic
module Abi = Hike_abi

(* Public re-exports; consumers use [Hike.Abi], etc. *)
module Vsa = Hike_vsa
module Drive = Hike_drive
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

let pass_filter proj = Hike_filter.filter_subs proj

(* The prune's closure debug; thunk-guarded like the completion's
   trace, so production never formats it. *)
let dbg_closure (msg : unit -> string) =
#ifdef VSA_DEBUG
  Printf.eprintf "hike-dbg-closure: %s\n%!" (msg ())
#else
  ignore msg
#endif

let pass_discover proj = Project.with_program proj (Hike_drive.run proj)

let pass_vsa proj =
  let target = Project.target proj in
  if Hike_abi.is_known_foreign target then
    Hike_diag.warn
      "target %s is not x86_64-gnu-elf; the x86-64 SysV convention record serves it"
      (KB.Name.to_string (Theory.Target.name target));
  let context = Hike_program_vsa.prepare proj in
  let solution = Hike_program_vsa.run context proj (Project.program proj) in
  Hike_program_vsa.install context solution;
  let facts = Hike_kb.facts () in
  let program = solution.program in
  let sub_addrs = solution.sub_addrs in
  let linker_slots = context.linker_slots in
  let reserved_slots = context.reserved_slots in
  let main_tid =
    Term.enum sub_t program
    |> Seq.find_map ~f:(fun s ->
        Base.Option.some_if (Term.has_attr s Hike_stack_model.main_role) (Term.tid s))
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
    let sub_by_tid =
      Core.Map.of_alist_exn (module Tid)
        (Base.List.map sub_list ~f:(fun s -> (Term.tid s, s)))
    in
    let sub_by_block =
      Core.Map.of_alist_exn (module Tid)
        (Base.List.concat_map sub_list ~f:(fun s ->
             Term.enum blk_t s |> Seq.to_list
             |> Base.List.map ~f:(fun b -> (Term.tid b, s))))
    in
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
      let index = Hike_transfer.index_of_sub s in
      let own_blocks =
        Core.Set.of_list (module Tid)
          (Term.enum blk_t s |> Seq.map ~f:Term.tid |> Seq.to_list)
      in
      let call_leaves s t =
        if Hike_return.is_target t || Tid.name t = "hike_return" then false
        else
          match Core.Map.find sub_by_tid t with
          | Some callee ->
            block_less callee || Core.Set.mem seen (Term.tid callee)
          | None -> true
      in
      (* [Some true] = leaves; [Some false] = stays; [None] = internal
         plumbing (neither). *)
      let sub_of_block t = Core.Map.find sub_by_block t in
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
            match Hike_transfer.slot_of_target ~index e with
            | Some a -> Some (Core.Set.mem linker_slots a)
            | None -> Some false)
          | Call c -> (
            match Call.target c with
            | Indirect e -> (
              match Hike_transfer.slot_of_target ~index e with
              | Some a -> Some (Core.Set.mem linker_slots a)
              | None -> Some false)
            | Direct t -> Some (call_leaves s t))
      in
      let reserved_transfer =
        Term.enum blk_t s |> Seq.concat_map ~f:(Term.enum jmp_t)
        |> Seq.exists ~f:(fun j ->
               let slot e =
                 Base.Option.bind (Hike_transfer.slot_of_target ~index e)
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
        then None
        else Cbat_vsa.WordSet.enumerate ~cap:64 ws
      in
      let target_words ~blk e =
        match facts.Hike_kb.denote ~blk e with
        | Ok ws -> bounded_words ws
        | _ -> None
      in
      (* A target read through a relocated slot names no lifted sub: the
         slot rule resolves the target's load through the sub's own defs
         (the load may sit in any block). *)
      let is_foreign_boundary ~index e =
        match Hike_transfer.slot_of_target ~index e with
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
        let index = Hike_transfer.index_of_sub sub in
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
                                        (is_foreign_boundary ~index e));
                                  if is_foreign_boundary ~index e then seen
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
                                  (is_foreign_boundary ~index e));
                            if is_foreign_boundary ~index e then seen
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
        let index = Hike_transfer.index_of_sub sub in
        let reach = reachable_tids sub in
        let refuse blk =
          Hike_diag.warn
            "prune: sub %s: block %s: indirect target is neither resolvable \
             nor a foreign boundary - keeping every sub"
            (Sub.name sub) (Tid.name (Term.tid blk))
        in
        let indirect ~blk e =
          if is_foreign_boundary ~index e then Some []
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
        closure (Core.Set.empty (module Tid)) [root]
      with
      | None -> program
      | Some closure ->
        Term.filter sub_t program ~f:(fun s -> Core.Set.mem closure (Term.tid s)))
  in
  Project.with_program proj pruned_program

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
      let discover = chain ~name:"discover" ~deps:[] pass_discover in
      let vsa = chain ~name:"vsa" ~deps:[ discover ] pass_vsa in
      let filter = chain ~name:"filter" ~deps:[ vsa ] pass_filter in
      let sections = chain ~name:"sections" ~deps:[ filter ] pass_attrib in
      let split_blocks =
        chain ~name:"split-blocks" ~deps:[ sections ] pass_split_blocks
      in
      let sign = chain ~name:"sign" ~deps:[ split_blocks ] Hike_types.sign_run in
      let ssa = chain ~name:"ssa" ~deps:[ sign ] pass_ssa in
      let types = chain ~name:"types" ~deps:[ ssa ] Hike_types.run in
      let convlir = chain' ~name:"convlir" ~deps:[ types ] (pass_convlir ~output:output_file) in
      ignore convlir;
      Ok ())
