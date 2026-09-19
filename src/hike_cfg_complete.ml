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
let bounded_words ~(denote : denote) ~(blk : blk term) (texp : exp) :
    Cbat_word.t list option =
  let blocks = Hike_kb.block_addrs () in
  if Core.Map.is_empty blocks then None
  else
    Base.Option.bind (Result.to_option (denote ~blk texp)) ~f:(fun ws ->
        if Vsa.WordSet.is_top ws || Vsa.WordSet.is_infinite ws
           || Vsa.WordSet.is_bottom ws
        then None
        else
          let card =
            match Cbat_word.to_int64 (Vsa.WordSet.cardinality ws) with
            | Ok c -> c
            | Error _ -> Int64.max_int in
          if
            Int64.compare card (Int64.of_int (Core.Map.length blocks)) > 0
          then None
          else Some (Vsa.WordSet.iter ws))

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
        if repair_needed then
          failwith
            (Printf.sprintf
               "hike-cfg-complete: the split of the block at %s at %s needs phi repair"
               (Word.to_string sa) (Word.to_string a));
        let sub' =
          Term.concat_map blk_t sub ~f:(fun b ->
              if Tid.equal (Term.tid b) ctid then [ b1; b2 ] else [ b ])
        in
        (sub', Term.tid b2)

(* The round's dispatch preparation: every resolvable dispatch's case
   words land on the run's map — exact starts are already there,
   mid-block entries through the block split.  A cross-sub word stays
   foreign (the extern machinery's class); a word in no block is a
   loud analysis loss.  One split per pass; each split adds a block,
   so the passes terminate. *)
let rec prepare_dispatches ~(denote : denote) ~(changed : bool ref)
    (sub : sub term) : sub term =
  let starts = addressed_starts sub in
  let dispatch_word blk =
    Base.List.find_map (Term.enum jmp_t blk |> Seq.to_list) ~f:(fun j ->
        let target =
          match Jmp.kind j with
          | Call c -> (match Call.target c with Indirect e -> Some e | _ -> None)
          | Goto (Indirect e) -> Some e
          | _ -> None
        in
        Base.Option.bind ~f:(bounded_words ~denote ~blk) target
        |> Base.Option.bind ~f:(fun words ->
               Base.List.find_map words ~f:(fun w ->
                   match Hike_kb.block_addr (Cbat_word.to_word w) with
                   | Some _ -> None
                   | None -> Some (Cbat_word.to_word w))))
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
  | None -> sub
  | Some (a, sub', t) ->
      Hike_kb.add_block_addr ~addr:a ~tid:t;
      changed := true;
      prepare_dispatches ~denote ~changed sub'

(* The dispatch's case pairs off the target's denotation: a bounded
   set no larger than the run's block count, every word naming an
   in-sub block on the run's map.  A cross-sub word leaves the whole
   dispatch foreign (the extern machinery's class); a resolvable word
   the map cannot name is a loud failure — an analysis loss, never a
   silent foreign transfer. *)
let resolved_pairs_of ~(denote : denote) ~(sub_tids : Tid.Set.t)
    ~(blk : blk term) (texp : exp) : (Cbat_word.t * tid) list option =
  let blocks = Hike_kb.block_addrs () in
  if Core.Map.is_empty blocks then None
  else
    Base.Option.bind (Result.to_option (denote ~blk texp)) ~f:(fun ws ->
        if Vsa.WordSet.is_top ws || Vsa.WordSet.is_infinite ws
           || Vsa.WordSet.is_bottom ws
        then None
        else
          let card =
            match Cbat_word.to_int64 (Vsa.WordSet.cardinality ws) with
            | Ok c -> c
            | Error _ -> Int64.max_int in
          if
            Int64.compare card (Int64.of_int (Core.Map.length blocks)) > 0
          then None
          else
            let pair (w : Cbat_word.t) : (Cbat_word.t * tid) option =
              match Hike_kb.block_addr (Cbat_word.to_word w) with
              | Some t when Core.Set.mem sub_tids t -> Some (w, t)
              | Some _ -> None
              | None ->
                  failwith
                    (Printf.sprintf
                       "hike-cfg-complete: dispatch word %s names no block in the run's block-address map"
                       (Word.to_string (Cbat_word.to_word w)))
            in
            let pairs = Vsa.WordSet.iter ws |> Base.List.map ~f:pair in
            if Base.List.exists pairs ~f:Option.is_none then None
            else Some (Base.List.filter_map pairs ~f:(fun p -> p)))


(* The eq chain of one target's words: [sel = w1 || sel = w2 || ...].
   The words share the selector's width, so the comparisons typecheck. *)
let guarded_cond (sel : exp) (ws : Cbat_word.t list) : exp =
  let eq w = Bil.BinOp (Bil.EQ, sel, Bil.Int (Cbat_word.to_word w)) in
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
  match guard with None -> cond | Some g -> Bil.BinOp (Bil.AND, g, cond)

(* The dispatch's successor series: one conditional goto per distinct
   case target (its words OR-merge into one guard), then the
   unconditional default.  The default target's own words need no
   guard — every other guard failing falls through to it — so its
   group is dropped and one edge per target survives for the phis.
   [pairs] is non-empty by [resolved_pairs_of]'s contract, so with no
   continuation the lowest case word's group is the default. *)
let dispatch_jmps (j : jmp term) (sel : exp)
    (pairs : (Cbat_word.t * tid) list) (cont : tid option) :
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
    match Core.Map.find reaching v with
    | Some dtid -> Core.Set.mem retaddr dtid
    | None -> false
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
            (resolved_pairs_of ~denote ~sub_tids ~blk texp)
            ~f:(fun pairs -> Some (dispatch_jmps j texp pairs cont))
      | _ -> None)
  | Goto (Indirect texp) ->
      Base.Option.bind (resolved_pairs_of ~denote ~sub_tids ~blk texp)
        ~f:(fun pairs -> Some (dispatch_jmps j texp pairs None))
  | _ -> None

(* Rebuilds [blk] with exactly [js'] as its jmps (the builder copies
   the defs and phis; the attrs follow). *)
let with_jmps (blk : blk term) (js' : jmp term list) : blk term =
  let b = Blk.Builder.init ~copy_phis:true ~copy_defs:true blk in
  Base.List.iter js' ~f:(Blk.Builder.add_jmp b);
  Term.with_attrs (Blk.Builder.result b) (Term.attrs blk)

(* The completion round: every block's jmps pass through the rewrite
   decision; a sub with no decision comes back unchanged. *)
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
  (sub', !changed)

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
