(* The CFG completion: a BIR-to-BIR rewrite driven by the VSA's own
   denotations.  A CONSUMER of the VSA — the solver passes the seam and
   the round's solution in, and its loop (Hike_vsa.fixpoint) drives the
   rounds: solve -> complete -> if the sub changed -> re-solve the NEW
   sub.  The rewritten BIR is the only product: return epilogues become
   real [Ret] jmps and resolvable dispatches become guarded-goto series
   in the existing blocks — no kinds map, no tags; later passes and the
   emitter read plain BAP shape.  Each rewrite converts an indirect
   transfer to direct structure, so the rounds terminate. *)

open Bap.Std
module Vsa = Cbat_vsa
module Model = Hike_stack_model

(* The seam the solver passes in: [e] denotes in [blk] (in the target
   def's before-env when [~def] is given). *)
type denote =
  blk:blk term -> ?def:def term -> exp -> (Vsa.WordSet.t, Type.error) Result.t

(* The round-solution seam: every block's precondition is the
   solution's own entry state for the block. *)
let denote_of_sol (sol : Vsa.vsa_sol) : denote =
  fun ~blk ?def e ->
    Vsa.denote_exp_at
      ~pre:(Graphlib.Std.Solution.get sol (Term.tid blk)) ~blk ?def e

(* One-line contract: the def's memory node is a load of at most one
   word; its address, if so. *)
let load_addr_of (word_bits : int) (d : def term) : exp option =
  match Model.addr_of_rhs (Def.rhs d) with
  | Some (addr, size) when Size.in_bits size <= word_bits ->
      if Option.is_none (Model.store_data_of_rhs (Def.rhs d)) then Some addr
      else None
  | _ -> None

(* One-line contract: the address denotates, in the def's own
   before-env, to the entry-RSP cell — THE return-address fact. *)
let reads_retaddr_cell ~(denote : denote) (blk : blk term) (d : def term)
    (addr : exp) : bool =
  match denote ~blk ~def:d addr with
  | Ok ws -> Model.is_return_address ws
  | Error _ -> false

(* The retaddr proof, re-derived through the denotation: the defs
   whose load address denotates — at the def's own before-env — to
   the stack-symbolic singleton at the entry-RSP cell (offset 0 on
   the segment line) read the return address. *)
let retaddr_defs ~(abi : Hike_abi.t) ~(sol : Vsa.vsa_sol)
    (sub : sub term) : Tid.Set.t =
  let denote = denote_of_sol sol in
  let note (acc : Tid.Set.t) blk d =
    match load_addr_of (8 * abi.Hike_abi.word) d with
    | Some addr when reads_retaddr_cell ~denote blk d addr ->
        Core.Set.add acc (Term.tid d)
    | _ -> acc
  in
  Term.enum blk_t sub
  |> Seq.fold ~init:Tid.Set.empty ~f:(fun acc blk ->
         Seq.fold (Term.enum def_t blk) ~init:acc ~f:(fun acc d ->
             note acc blk d))

(* The dispatch resolution's debug trace; compiled out of production. *)
let option_if_debug msg =
#ifdef VSA_DEBUG
  Printf.eprintf "hike-dbg-dispatch: %s\n%!" msg
#else
  ignore msg
#endif

(* The sub's addressed starts: every block's own address stamp,
   ascending — the block extents' bounds. *)
let addressed_starts (sub : sub term) : (Addr.t * tid) list =
  Term.enum blk_t sub
  |> Seq.filter_map ~f:(fun b ->
         Base.Option.map (Term.get_attr b address)
           ~f:(fun a -> (a, Term.tid b)))
  |> Seq.to_list
  |> Base.List.sort ~compare:(fun (a, _) (b, _) -> Word.compare a b)

(* The dispatch's case words: a bounded plain set no larger than the
   run's block count — the words a resolution may target or split at. *)
let bounded_words ~(denote : denote) ~(blk : blk term) ?def
    (texp : exp) : Cbat_word.t list option =
  let blocks = Hike_kb.block_addrs () in
  if Core.Map.is_empty blocks then None
  else
    Base.Option.bind (Result.to_option (denote ~blk ?def texp)) ~f:(fun ws ->
        if Vsa.WordSet.is_top ws || Vsa.WordSet.is_infinite ws
           || Vsa.WordSet.is_bottom ws
        then (
          option_if_debug
            (Printf.sprintf "bounded_words: the target denotation is %s"
               (if Vsa.WordSet.is_top ws then "TOP"
                else if Vsa.WordSet.is_infinite ws then "INFINITE"
                else "BOTTOM"));
          None)
        else
          let card =
            match Cbat_word.to_int64 (Vsa.WordSet.cardinality ws) with
            | Ok c -> c
            | Error _ -> Int64.max_int in
          let over =
            Int64.compare card (Int64.of_int (Core.Map.length blocks)) > 0 in
          if over then
            option_if_debug
              (Printf.sprintf
                 "bounded_words: card %Ld exceeds the map's %d blocks"
                 card (Core.Map.length blocks));
          if over then None else Some (Vsa.WordSet.iter ws))

(* One mid-block case entry: the containing block splits at the entry
   instruction — the prefix keeps the block's tid (its incoming edges)
   and falls through to the fresh entry block, which takes the
   address.  Sound only when the prefix is transparent: nothing it
   defines is read past it — else the split needs phi repair (loud). *)
let split_entry ~(starts : (Addr.t * tid) list) (a : Addr.t)
    (sub : sub term) : sub term * tid =
  let container =
    Base.List.fold starts ~init:None ~f:(fun best (sa, t) ->
        if Word.compare sa a < 0 then
          match best with
          | Some (sa', _) when Word.compare sa' sa >= 0 -> best
          | _ -> Some (sa, t)
        else best)
  in
  match container with
  | None ->
      failwith
        (Printf.sprintf
           "hike-cfg-complete: dispatch word %s names no block in the run's block-address map"
           (Word.to_string a))
  | Some (sa, ctid) ->
    let c =
      Term.enum blk_t sub
      |> Seq.find_exn ~f:(fun b -> Tid.equal (Term.tid b) ctid)
    in
    let defs = Seq.to_list (Term.enum def_t c) in
    let pivot =
      Base.List.find defs ~f:(fun d ->
          match Term.get_attr d address with
          | Some da -> Word.equal da a
          | None -> false)
    in
    match pivot with
    | None ->
        failwith
          (Printf.sprintf
             "hike-cfg-complete: dispatch word %s falls inside the block at %s (%s) with no entry instruction to split at"
             (Word.to_string a) (Word.to_string sa) (Tid.name ctid))
    | Some pivot ->
        let b1, b2 = Blk.split_before c pivot in
        let b2 = Term.set_attr b2 address a in
        let b2_free = Blk.free_vars b2 in
        let repair_needed =
          Term.enum def_t b1 |> Seq.exists ~f:(fun d ->
              Core.Set.mem b2_free (Def.lhs d))
          || (Term.enum phi_t b1 |> Seq.exists ~f:(fun p ->
                 Core.Set.mem b2_free (Phi.lhs p)))
        in
        (* The prefix's reachability decides its fate.  A prefix block
           nothing targets is dead code and drops (the case entry skips
           it natively); a prefix something jumps into stays a real
           block feeding the entry -- and then a prefix-defined value
           read past the split needs phi repair (loud). *)
        let entry = Term.first blk_t sub |> Base.Option.value_exn in
        let targets tid blk =
          Term.enum jmp_t blk
          |> Seq.exists ~f:(fun j ->
                 match Jmp.kind j with
                 | Goto (Direct t) -> Tid.equal t tid
                 | Call c -> (
                     match Call.return c with
                     | Some (Direct t) -> Tid.equal t tid
                     | _ -> false)
                 | _ -> false)
        in
        let reachable =
          Tid.equal ctid (Term.tid entry)
          || Seq.exists (Term.enum blk_t sub) ~f:(fun b ->
                 not (Tid.equal (Term.tid b) ctid)
                 && targets (Term.tid b1) b)
        in
        if reachable then (
          if not (Tid.equal (Term.tid b1) ctid) then
            failwith
              "hike-cfg-complete: the split's prefix lost the container's tid";
          if repair_needed then
            failwith
              (Printf.sprintf
                 "hike-cfg-complete: the split of the block at %s at %s needs phi repair"
                 (Word.to_string sa) (Word.to_string a));
          let sub' =
            Term.concat_map blk_t sub ~f:(fun b ->
                if Tid.equal (Term.tid b) ctid then [ b1; b2 ] else [ b ])
          in
          (sub', Term.tid b2))
        else
          let sub' =
            Term.concat_map blk_t sub ~f:(fun b ->
                if Tid.equal (Term.tid b) ctid then [ b2 ] else [ b ])
          in
          (sub', Term.tid b2)

(* The round's dispatch preparation: every resolvable dispatch's case
   words land on the run's map — exact starts are already there,
   mid-block entries through the block split.  A cross-sub word stays
   foreign (the extern machinery's class); a word in no block is a
   loud analysis loss.  One split per pass; each split adds a block,
   so the passes terminate. *)
(* The dispatch's case words, denotated at the state the jump reads.
   A bare-variable target is the sum its reaching definition computes,
   so the words are that sum's addends denotated at the definition's
   before-env -- the delta plus the base -- never the post-transfer
   state, which a noreturn call poisons. *)
let dispatch_words ~(denote : denote) ~(reaching : tid Var.Map.t)
    ~(blk : blk term) (texp : exp) : Cbat_word.t list option =
  match texp with
  | Bil.BinOp (Bil.PLUS, _, _) -> bounded_words ~denote ~blk texp
  | Bil.Var v ->
      Base.Option.bind (Core.Map.find reaching v) ~f:(fun dtid ->
          Base.Option.bind
            (Seq.find (Term.enum def_t blk) ~f:(fun d ->
                 Tid.equal (Term.tid d) dtid))
            ~f:(fun add_def ->
              bounded_words ~denote ~blk ~def:add_def (Def.rhs add_def)))
  | _ -> None

(* The dispatch's guard subject and base: the target's top-level
   summands -- one denotates to a singleton (the base the deltas
   telescope through), the other carries the table's delta and is the
   guard's subject.  A bare-variable target looks through its reaching
   definition (the sum's own addends, denotated at that def's
   before-env); the subject is then the sum minus the base, whose
   value is the delta in every address space. *)

let rec prepare_dispatches ~(denote : denote) ~(changed : bool ref)
    (sub : sub term) : sub term =
  let starts = addressed_starts sub in
  let dispatch_word blk =
    let reaching = Core.Map.map (Vsa.last_defs blk) ~f:Term.tid in
    Base.List.find_map (Term.enum jmp_t blk |> Seq.to_list) ~f:(fun j ->
        let target =
          match Jmp.kind j with
          | Call c -> (match Call.target c with Indirect e -> Some e | _ -> None)
          | Goto (Indirect e) -> Some e
          | _ -> None
        in
        Base.Option.bind
          ~f:(dispatch_words ~denote ~reaching ~blk) target
        |> Base.Option.bind ~f:(fun words ->
               Base.List.find_map words ~f:(fun w ->
                   let a = Cbat_word.to_word w in
                   match Hike_kb.block_addr a with
                   | Some _ -> None
                   | None -> Some a)))
  in
  match
    Term.enum blk_t sub
    |> Seq.filter_map ~f:(fun blk ->
           match dispatch_word blk with
           | None -> None
           | Some a ->
               let sub', t = split_entry ~starts a sub in
               Some (a, sub', t))
    |> Seq.to_list
    |> Base.List.hd
  with
  | None ->
      option_if_debug "prepare: no missing word, done";
      sub
  | Some (a, sub', t) ->
      option_if_debug
        (Printf.sprintf "prepare: split at %s -> tid %s"
           (Word.to_string a) (Tid.name t));
      Hike_kb.add_block_addr ~addr:a ~tid:t;
      changed := true;
      prepare_dispatches ~denote ~changed sub'

let delta_subject ~(denote : denote) ~(reaching : tid Var.Map.t)
    ~(blk : blk term) (texp : exp) : (exp * exp * Int64.t) option =
  let singleton_value ?def e =
    match Result.to_option (denote ~blk ?def e) with
    | Some ws ->
      (match Cbat_word.to_int64 (Vsa.WordSet.cardinality ws) with
       | Ok 1L ->
         Base.Option.bind (Vsa.WordSet.min_elem ws)
           ~f:(fun w -> Result.to_option (Cbat_word.to_int64 w))
       | _ -> None)
    | None -> None
  in
  let pick ?def x y =
    match singleton_value ?def x with
    | Some bval -> Some (y, x, bval)
    | None -> Base.Option.map (singleton_value ?def y) ~f:(fun bval -> (x, y, bval))
  in
  let reaching_sum v =
    Base.Option.bind (Core.Map.find reaching v) ~f:(fun dtid ->
        Base.Option.bind
          (Seq.find (Term.enum def_t blk) ~f:(fun d ->
               Tid.equal (Term.tid d) dtid))
          ~f:(fun add_def ->
            match Def.rhs add_def with
            | Bil.BinOp (Bil.PLUS, x, y) -> pick ~def:add_def x y
            | _ -> None))
  in
  match texp with
  | Bil.BinOp (Bil.PLUS, x, y) -> pick x y
  | Bil.Var v -> reaching_sum v
  | _ -> None

(* The dispatch's case pairs off the target's denotation: a bounded
   set no larger than the run's block count, every word naming an
   in-sub block on the run's map.  The pairs are BASE-RELATIVE -- the
   guard word is the case's delta [w - base], so the runtime
   comparison lives in the delta domain and never depends on where the
   module linked the table.  A cross-sub word leaves the whole
   dispatch foreign (the extern machinery's class); a resolvable word
   the map cannot name is a loud failure -- an analysis loss, never a
   silent foreign transfer. *)
let resolved_pairs_of ~(denote : denote) ~(reaching : tid Var.Map.t)
    ~(sub_tids : Tid.Set.t) ~(blk : blk term) (texp : exp) :
    (exp * (word * tid) list) option =
  let blocks = Hike_kb.block_addrs () in
  match dispatch_words ~denote ~reaching ~blk texp with
  | None -> None
  | Some ws ->
    if Base.List.length ws > Core.Map.length blocks then None
    else
        Base.Option.bind (delta_subject ~denote ~reaching ~blk texp)
          ~f:(fun (delta_exp, base_exp, bval) ->
          let subject =
            match texp with
            | Bil.BinOp (Bil.PLUS, _, _) -> delta_exp
            | _ -> Bil.BinOp (Bil.MINUS, texp, base_exp)
          in
          let case (w : Cbat_word.t) : (word * tid) option =
            let a = Cbat_word.to_word w in
            match Hike_kb.block_addr a with
            | Some t when Core.Set.mem sub_tids t ->
              Some (Addr.of_int64 (Int64.sub (Word.to_int64_exn a) bval), t)
            | Some _ -> None
            | None ->
                failwith
                  (Printf.sprintf
                     "hike-cfg-complete: dispatch word %s names no block in the run's block-address map"
                     (Word.to_string a))
          in
          let pairs = Base.List.map ws ~f:case in
          if Base.List.exists pairs ~f:Option.is_none then None
          else Some (subject, Base.List.filter_map pairs ~f:(fun p -> p)))

(* The eq chain of one target's words: [sel = w1 || sel = w2 || ...].
   The words share the selector's width, so the comparisons typecheck. *)
let guarded_cond (sel : exp) (ws : word list) : exp =
  let eq w = Bil.BinOp (Bil.EQ, sel, Bil.Int w) in
  match ws with
  | [] -> Bil.Int (Word.one 1)
  | w :: rest ->
      Base.List.fold rest ~init:(eq w)
        ~f:(fun acc w -> Bil.BinOp (Bil.OR, acc, eq w))

(* The literal-true condition ([Jmp.create]'s default guard) and the
   guard composition: the dispatch jmp's own guard narrows every case
   and the default alike. *)
let true_cond : exp = Bil.Int (Word.one 1)

let is_true_cond (e : exp) : bool =
  match e with Bil.Int w -> Word.equal w (Word.one 1) | _ -> false

let guard_of (j : jmp term) : exp option =
  match Jmp.cond j with c when is_true_cond c -> None | c -> Some c

let and_guard (guard : exp option) (cond : exp) : exp =
  Base.Option.fold guard ~init:cond ~f:(fun cond g -> Bil.BinOp (Bil.AND, g, cond))

(* The dispatch's successor series: one conditional goto per distinct
   case target (its words OR-merge into one guard), then the
   unconditional default.  The default target's own words need no
   guard — every other guard failing falls through to it — so its
   group is dropped and one edge per target survives for the phis.
   [pairs] is non-empty by [resolved_pairs_of]'s contract, so with no
   continuation the lowest case word's group is the default. *)
let dispatch_jmps (j : jmp term) (sel : exp)
    (pairs : (word * tid) list) (cont : tid option) :
    jmp term list =
  let by_target =
    Base.List.fold pairs ~init:[] ~f:(fun acc (w, t) ->
        match Base.List.Assoc.find acc t ~equal:Tid.equal with
        | Some ws -> Base.List.Assoc.add acc t (w :: ws) ~equal:Tid.equal
        | None -> (t, [ w ]) :: acc)
  in
  (* Groups in ascending first-word order; the head names the lowest
     case word (the no-continuation default, as the switch chose). *)
  let ascending = List.rev by_target in
  let groups, default_tid =
    match cont with
    | Some t ->
        (Base.List.filter ascending ~f:(fun (g, _) -> not (Tid.equal g t)),
         t)
    | None ->
        (Base.List.tl_exn ascending, fst (Base.List.hd_exn ascending))
  in
  let guard = guard_of j in
  let cases =
    Base.List.map groups ~f:(fun (t, ws) ->
        Jmp.create ~cond:(and_guard guard (guarded_cond sel ws))
          (Goto (Direct t)))
  in
  cases
  @ [ Jmp.create
        ~cond:(Base.Option.value guard ~default:true_cond)
        (Goto (Direct default_tid)) ]

(* The return epilogue's replacement: the BIR's canonical return
   shape.  This fork stores a [Ret] as a return-less call with the
   return-address label as its target ([Jmp.create (Ret _)] reads back
   as that call), and the emitter's shape dispatch renders exactly
   this class through the return lane.  The var-free target leaves no
   reader for the retaddr load, so the sweep kills it. *)
let ret_jmp ~(word_bits : int) : jmp term =
  Jmp.create
    (Call
       (Call.create
          ~target:(Indirect (Bil.Unknown ("hike-cfg-ret", Type.Imm word_bits)))
          ()))

(* One jmp's rewrite decision: the return epilogue (a noreturn call
   whose target var's reaching def is the retaddr read) lands in the
   canonical return shape; a dispatch whose case words all resolve
   becomes the guarded-goto series (a call dispatch's continuation is
   the default); everything else stays. *)
let rewritten_jmps ~(denote : denote) ~(retaddr : Tid.Set.t)
    ~(word_bits : int) ~(sub_tids : Tid.Set.t)
    ~(reaching : tid Var.Map.t) ~(blk : blk term) (j : jmp term) :
    jmp term list option =
  let retaddr_read v =
    Base.Option.value_map (Core.Map.find reaching v) ~default:false
      ~f:(fun dtid -> Core.Set.mem retaddr dtid)
  in
  match Jmp.kind j with
  | Call c -> (
      match (Call.return c, Call.target c) with
      | None, Indirect (Bil.Var v) when retaddr_read v ->
          Some [ ret_jmp ~word_bits ]
      | _, Indirect texp ->
          let cont =
            match Call.return c with
            | Some (Direct t) -> Some t
            | Some (Indirect _) | None -> None
          in
          Base.Option.bind
            (resolved_pairs_of ~denote ~reaching ~sub_tids ~blk texp)
            ~f:(fun (delta_exp, pairs) ->
                Some (dispatch_jmps j delta_exp pairs cont))
      | _ -> None)
  | Goto (Indirect texp) ->
      Base.Option.bind (resolved_pairs_of ~denote ~reaching ~sub_tids ~blk texp)
        ~f:(fun (delta_exp, pairs) ->
            Some (dispatch_jmps j delta_exp pairs None))
  | _ -> None

(* Rebuilds [blk] with exactly [js'] as its jmps (the builder copies
   the defs and phis; the attrs follow). *)
let with_jmps (blk : blk term) (js' : jmp term list) : blk term =
  let b = Blk.Builder.init ~copy_phis:true ~copy_defs:true blk in
  Base.List.iter js' ~f:(Blk.Builder.add_jmp b);
  Term.with_attrs (Blk.Builder.result b) (Term.attrs blk)

(* The completion round: every block's jmps pass through the rewrite
   decision; a sub with no decision comes back unchanged. *)
(* Unreachable-block elimination: a block no reachable transfer names
   is dead (a resolved dispatch's replaced container).  Skipped while a
   foreign indirect transfer survives -- its targets cannot be counted,
   so a pred-less block might still be entered. *)
let prune_unreachable (sub : sub term) : sub term * bool =
  let entry = Base.Option.value_exn (Term.first blk_t sub) in
  let blocks = Seq.to_list (Term.enum blk_t sub) in
  let rec go seen blk =
    if Core.Set.mem seen (Term.tid blk) then seen
    else
      let seen = Core.Set.add seen (Term.tid blk) in
      Term.enum jmp_t blk
      |> Seq.fold ~init:seen ~f:(fun seen j ->
             let targets =
               match Jmp.kind j with
               | Goto (Direct t) -> [ t ]
               | Call c -> (
                   match Call.return c with
                   | Some (Direct t) -> [ t ]
                   | _ -> [])
               | _ -> []
             in
             Base.List.fold targets ~init:seen ~f:(fun seen t ->
                 match
                   Base.List.find blocks ~f:(fun b ->
                       Tid.equal (Term.tid b) t)
                 with
                 | Some b -> go seen b
                 | None -> seen))
  in
  let reachable = go Tid.Set.empty entry in
  let pruned = Core.Set.length reachable < List.length blocks in
  let sub' = Term.filter_map blk_t sub ~f:(fun b ->
      if Core.Set.mem reachable (Term.tid b) then Some b else None)
  in
  (sub', pruned)

let rewrite_sub ~(denote : denote) ~(retaddr : Tid.Set.t)
    ~(word_bits : int)
    (sub : sub term) : sub term * bool =
  let changed = ref false in
  let sub = prepare_dispatches ~denote ~changed sub in
  let sub_tids =
    Core.Set.of_list (module Tid)
      (Base.List.map (Seq.to_list (Term.enum blk_t sub)) ~f:Term.tid)
  in
  let reblock (blk : blk term) : blk term =
    let js = Seq.to_list (Term.enum jmp_t blk) in
    let reaching = Core.Map.map (Vsa.last_defs blk) ~f:Term.tid in
    let decided =
      Base.List.filter_map js ~f:(fun j ->
          rewritten_jmps ~denote ~retaddr ~word_bits ~sub_tids ~reaching ~blk
            j
          |> Base.Option.map ~f:(fun js' -> (Term.tid j, js')))
    in
    match decided with
    | [] -> blk
    | _ ->
        changed := true;
        let rewr = Core.Map.of_alist_exn (module Tid) decided in
        let spliced =
          Base.List.concat_map js ~f:(fun j ->
              match Core.Map.find rewr (Term.tid j) with
              | Some js' -> js'
              | None -> [ j ])
        in
        with_jmps blk spliced
  in
  let sub' = Term.map blk_t sub ~f:reblock in
  let has_foreign =
    Term.enum blk_t sub' |> Seq.exists ~f:(fun b ->
        Term.enum jmp_t b |> Seq.exists ~f:(fun j ->
            match Jmp.kind j with
            | Goto (Indirect _) -> true
            | Call c -> (
                match Call.target c with Indirect _ -> true | _ -> false)
            | _ -> false))
  in
  if has_foreign then (sub', !changed)
  else
    let sub'', pruned = prune_unreachable sub' in
    (sub'', !changed || pruned)

(* One completion round on the round's own solution: the retaddr proof
   re-derives through the solution, the dispatch classification
   denotates through the seam with the images armed (the jump-table
   case words live in .rodata), and the rewrites land in the terms.
   The product is the REWRITTEN SUB and whether anything changed. *)
let complete ~(denote : denote)
    ~(abi : Hike_abi.t) ~(sol : Vsa.vsa_sol)
    ~(images : Vsa.section_image list)
    (sub : sub term) : sub term * bool =
  let retaddr = retaddr_defs ~abi ~sol sub in
  Vsa.set_section_images images;
  let word_bits = 8 * abi.Hike_abi.word in
  let result =
    (try rewrite_sub ~denote ~retaddr ~word_bits sub
     with exn -> Vsa.set_section_images []; raise exn)
  in
  Vsa.set_section_images [];
  result
