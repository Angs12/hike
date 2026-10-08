(* The program discovery fixpoint. Decode products and analysis stay internal. *)
open Bap.Std
open Bap_core_theory
module Abi = Hike_abi

type step = {
  decoded : Hike_decode.out;
  program : program term;
  main_addr : int64 option;
  noreturn : Tid.Set.t;
  roots : Core.Int64.Set.t;
  destinations : Core.Int64.Set.t Core.Int64.Map.t;
  (* The destinations provided when [program]'s jumps compiled. *)
  compiled : Core.Int64.Set.t Core.Int64.Map.t;
}

let run proj =
  let context = Hike_program_vsa.prepare proj in
  let target = context.target in
  let text_range = context.text_range in
  (* The primary program's entry address: the fact the lifted program's
     entry sub is stamped from every round. *)
  let range_of_section name =
    Hike_image.get_section_mem name proj |> Hike_image.get_section_data
    |> Base.Option.map ~f:(fun (_, lo, hi) ->
        (Word.to_int64_exn lo, Word.to_int64_exn hi))
  in
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
  let file = Hike_decode.file_of (Project.program proj) in
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
  let root_set = ref Core.Int64.Set.empty in
  let destinations = ref Core.Int64.Map.empty in
  let add_root w =
    if is_code_addr w && not (Core.Set.mem !root_set w) then begin
      root_set := Core.Set.add !root_set w;
      roots := w :: !roots
    end
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
      Base.Option.map (Cbat_vsa.WordSet.enumerate ~cap:64 ws) ~f:(fun words ->
          Base.List.filter_map words
            ~f:(fun w -> Result.to_option (Cbat_word.to_int64 w)))
  in
  (* Resolved targets retain their instruction sites so BAP can classify
     the transfers from the original instruction semantics. *)
  let transfer_words (envs, sub') : (int64 * int64 list) list =
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
                let e =
                  match Jmp.kind j with
                  | Goto (Indirect e) -> Some e
                  | Call c -> (
                    match Call.target c with
                    | Indirect e -> Some e
                    | Direct _ -> None)
                  | _ -> None
                in
                match e with
                | None | Some (Bil.Int _) -> None
                | Some e -> (
                  match Cbat_vsa.denote_exp_at ~pre ~post ~blk e with
                  | Error _ -> None
                  | Ok ws ->
                    Base.Option.map (bounded_words ws) ~f:(fun words ->
                        (site, words))))))
  in
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
  (* The value lane: a def whose value denotates to a bounded singleton
     naming an unclaimed code word roots it — a register-carried
     function pointer (the lea+call-argument idiom) loses no callee to
     the store lane's memory-only scan. *)
  let value_words (envs, stamped) : int64 list =
    Base.List.concat_map (Term.enum blk_t stamped |> Seq.to_list)
      ~f:(fun blk ->
        match Core.Map.find envs (Term.tid blk) with
        | None -> []
        | Some (pre, post) ->
          Base.List.filter_map (Term.enum def_t blk |> Seq.to_list)
            ~f:(fun d ->
              match Hike_stack_model.store_data_of_rhs (Def.rhs d) with
              | Some _ -> None
              | None -> (
                match
                  Cbat_vsa.denote_exp_at ~pre ~post ~blk ~def:d (Def.rhs d)
                with
                | Error _ -> None
                | Ok ws -> (
                  match
                    Cbat_word.to_int64 (Cbat_vsa.WordSet.cardinality ws)
                  with
                  | Ok 1L ->
                    Base.Option.bind (Cbat_vsa.WordSet.min_elem ws)
                      ~f:(fun w -> Result.to_option (Cbat_word.to_int64 w))
                  | _ -> None))))
  in
  (* Each round supplies destinations and data-discovered entry roots,
     then lets BAP decode and partition the resulting graph. *)
  (* The noreturn fact: computed on each round's SOLVED program (where
     the denotations and canonical returns are final) and threaded into
     the next round's solve, so the completion's edge set never keeps a
     return continuation for a never-returning callee. *)
  let noreturn = ref Tid.Set.empty in
  let rec round prev =
    if !rounds_left <= 0 then begin
      Hike_diag.warn "vsa: the drive loop stopped at its round budget";
      (match prev with
       | Some products -> products
       | None -> failwith "hike-vsa: the drive loop's first round exceeded the budget")
    end else begin
      rounds_left := !rounds_left - 1;
      let decoded = match prev with
        | None -> Some (Hike_decode.initial proj)
        | Some _ -> Hike_decode.rescan proj ~file ~roots:(Base.List.rev !roots) in
      match decoded with
      | None -> failwith "hike-vsa: the drive loop's re-scan produced nothing"
      | Some out ->
        (* The same decoded instructions, partition and noreturn inputs
           under this image context produce the same discoveries. *)
        match prev with
        | Some p when Disasm.Driver.equal p.decoded.grown out.grown
                      && Disasm.Subroutines.equal p.decoded.subs out.subs
                      && Core.Set.equal p.noreturn !noreturn
                      && Core.Map.equal Core.Set.equal p.compiled !destinations ->
          { p with decoded = out }
        | _ ->
        (* The lifted program is BAP's raw BIR: the normalizer chain runs
           over it once per round — one memory node per def, width-honest
           binops, the FP temp widths — so every later reader takes the
           terms as the passes left them. *)
        let lifted =
          match prev with
          | None -> Project.program proj
          | Some _ -> Hike_decode.program_of_state ~file out.grown out.subs
        in
        (* The entry sub is the target's own fact (B1): the primary
           program's entry names the address; the lifted program's sub
           at that address carries the attr every later reader reads.
           Every sub names the decode's package, as the primary
           program's do, so a reader of its instruction labels (the
           jump compiler's destinations) finds them. *)
        let raw =
          Term.map sub_t lifted ~f:(fun s ->
              let s = Term.set_attr s filename file in
              match entry_addr with
              | None -> s
              | Some ea -> (
                match Term.first blk_t s with
                | Some b -> (
                  match Term.get_attr b address with
                  | Some a when Addr.equal a ea ->
                    Term.set_attr s Sub.entry_point ()
                  | _ -> s)
                | None -> s))
        in
        (* The jump compiler reads the destinations provided so far;
           a round that resolves more recompiles under them. *)
        let compiled = !destinations in
        let program = Hike_program_vsa.normalize context raw in
        let used_noreturn = !noreturn in
        (* The site → terminator-instruction map, off this round's
           decode: the solver's jmp rewrites drop the jmp's own
           [address] attr, so a dispatch's site is its BLOCK's address
           while the dests facts key on the instruction label. *)
        let terminator_of =
          let m =
            Core.Map.of_alist_exn (module Core.Int64)
              (Base.List.map (Hike_decode.terminators out.cfg)
                 ~f:(fun (b, i) ->
                   (Word.to_int64_exn b, Word.to_int64_exn i)))
          in
          fun a -> Base.Option.value (Core.Map.find m a) ~default:a
        in
        let solution = Hike_program_vsa.solve context proj ~noreturn:!noreturn program in
        let subs_acc = solution.subs in
        (* The noreturn fact on the solved program (denotations and the
           canonical returns are final): the set feeds the NEXT round's
           solve, whose completion keeps no continuation for a
           never-returning callee. *)
        let solved_program = solution.program in
        let noreturn' = Hike_noreturn.classify ~target solved_program in
        let noreturn_changed = not (Core.Set.equal noreturn' !noreturn) in
        noreturn := noreturn';
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
        (* Resolved transfers feed BAP's destination channel. Instruction
           semantics determine calls; the partition owns function entries. *)
        Base.Option.iter main_addr ~f:add_root;
        let transfer_targets = ref
            (Core.Map.fold !destinations ~init:Core.Int64.Set.empty
               ~f:(fun ~key:_ ~data targets -> Core.Set.union targets data)) in
        let route site w =
          transfer_targets := Core.Set.add !transfer_targets w;
          let site = terminator_of site in
          let words = Base.Option.value (Core.Map.find !destinations site)
              ~default:Core.Int64.Set.empty in
          if not (Core.Set.mem words w) then begin
            destinations := Core.Map.set !destinations ~key:site
                ~data:(Core.Set.add words w);
            provide_dests site w
          end
        in
        Core.Map.fold subs_acc ~init:() ~f:(fun ~key:_ ~data:solved () ->
            Base.List.iter (transfer_words solved)
              ~f:(fun (site, words) ->
                Base.List.iter words ~f:(route site)));
        (* A transfer target is decoded through its instruction, not rooted
           again by the code-value scan. Other code values retain the data
           discovery lane for callbacks outside the decoded sub extents. *)
        let decoded_extents =
          Term.enum sub_t solved_program
          |> Seq.filter_map ~f:(fun s ->
                 let addrs =
                   Term.enum blk_t s
                   |> Seq.filter_map ~f:(fun b ->
                       Term.get_attr b address
                       |> Base.Option.bind ~f:(fun a ->
                           Result.to_option (Addr.to_int64 a)))
                   |> Seq.to_list
                 in
                 match addrs with
                 | [] -> None
                 | _ -> (
                   match
                     ( Base.List.min_elt addrs ~compare:Int64.compare,
                       Base.List.max_elt addrs ~compare:Int64.compare )
                   with
                   | Some lo, Some hi -> Some (lo, hi)
                   | _ -> None ))
          |> Seq.to_list
        in
        let unclaimed w =
          not
            (Base.List.exists decoded_extents ~f:(fun (lo, hi) ->
                 Int64.compare w lo >= 0 && Int64.compare w hi <= 0))
        in
        Core.Map.fold subs_acc ~init:() ~f:(fun ~key:_ ~data:solved () ->
            Base.List.iter (store_words solved) ~f:(fun w ->
                if unclaimed w && not (Core.Set.mem !transfer_targets w) then add_root w);
            Base.List.iter (value_words solved) ~f:(fun w ->
                if unclaimed w && not (Core.Set.mem !transfer_targets w) then add_root w));
        let result = { decoded = out; program = raw;
                       main_addr; noreturn = used_noreturn;
                       roots = !root_set; destinations = !destinations;
                       compiled } in
        let settled = not noreturn_changed && match prev with
          | Some p -> Disasm.Driver.equal p.decoded.grown out.grown
                      && Core.Set.equal p.roots !root_set
                      && Core.Map.equal Core.Set.equal p.destinations !destinations
          | None -> false in
        if settled then result else round (Some result)
    end
  in
  let result = round None in
  match result.main_addr with
  | None -> result.program
  | Some a ->
    Term.map sub_t result.program ~f:(fun s ->
        match Term.get_attr s address with
        | Some x when Addr.equal x (Addr.of_int64 a) ->
          Term.set_attr s Hike_stack_model.main_role ()
        | _ -> s)
