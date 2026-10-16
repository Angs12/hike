(* The CFG completion, fused into the solver's own loop: per phase,
   bounding dispatches grow the extra edges and split their mid-block
   case entries; at drain the materialization lands once. *)

open Bap.Std
module Vsa = Cbat_vsa
module Model = Hike_stack_model

(* The solve's own denotation: [e] denotes in [blk] (in the target
   def's before-env when [~def] is given), replayed from the phase's
   solution state by the solve's own replay. *)
type denote = Hike_kb.denote

(* The phase solution's denotation. *)
let denote_of_sol (sol : Vsa.vsa_sol) : denote =
  fun ~blk ?def e ->
    Vsa.solve_denote
      ~pre:(Graphlib.Std.Solution.get sol (Term.tid blk)) ~blk ?def e

(* A load of at most one word; its address, if so. *)
let load_addr_of (word_bits : int) (d : def term) : exp option =
  match Model.addr_of_rhs (Def.rhs d) with
  | Some (addr, size) when Size.in_bits size <= word_bits ->
      if Option.is_none (Model.store_data_of_rhs (Def.rhs d)) then Some addr
      else None
  | _ -> None

(* The defs whose load address denotates, in the def's own before-env,
   to the stack-symbolic entry-RSP cell.  A BOTTOM address inside a
   live env is an absent var (a never-defined register), not a dead
   path — it proves no return shape; only a wholly-BOTTOM env (a path
   the solve proved dead) keeps the return shape with a bottom address.
   One replay per block: the fold carries each def's before-env, so
   the per-def address denotations ride the block's single pass. *)
let retaddr_defs ~(abi : Hike_abi.t) ~(sol : Vsa.vsa_sol)
    (sub : sub term) : Tid.Set.t =
  let word_bits = Hike_abi.word_bits abi in
  Term.enum blk_t sub
  |> Seq.fold ~init:Tid.Set.empty ~f:(fun acc blk ->
         fst
           (Vsa.fold_block_states ~sol blk ~init:acc
              ~f:(fun before _after d acc ->
                  match load_addr_of word_bits d with
                  | Some addr -> (
                      match Vsa.denote_imm_exp addr before with
                      | Ok ws when Model.is_return_address ws ->
                        Core.Set.add acc (Term.tid d)
                      | Ok ws
                        when Vsa.WordSet.is_bottom ws
                             && Vsa.AI.equal before Vsa.AI.bottom ->
                        Core.Set.add acc (Term.tid d)
                      | _ -> acc)
                  | None -> acc)))

(* A target variable whose reaching def reads the return-address cell:
   a return, never a dispatch candidate. *)
let retaddr_read ~(last_defs : def term Var.Map.t) ~(retaddr : Tid.Set.t)
    (v : var) : bool =
  Base.Option.value_map (Core.Map.find last_defs v |> Option.map Term.tid)
    ~default:false
    ~f:(fun dtid -> Core.Set.mem retaddr dtid)

(* The jmp's indirect target when it is neither a retaddr read nor a
   read through a linker-owned slot: the ret epilogue's target is the
   stack-symbolic cell, and a slot-read target is a foreign boundary —
   the dynamic linker fills the value, so the file bytes are not a
   dispatch's case words.  Neither is ever a dispatch. *)
let dispatch_target ~(last_defs : def term Var.Map.t) ~(retaddr : Tid.Set.t)
    ~(index : Hike_transfer.index) ~(foreign_slots : Core.Int64.Set.t)
    (j : jmp term) : exp option =
  let target =
    match Jmp.kind j with
    | Call c -> (match Call.target c with Indirect e -> Some e | _ -> None)
    | Goto (Indirect e) -> Some e
    | _ -> None
  in
  match target with
  | Some (Bil.Var v) when retaddr_read ~last_defs ~retaddr v -> None
  | Some t when
      Base.Option.value_map (Hike_transfer.slot_of_target ~index t)
        ~default:false ~f:(fun a -> Core.Set.mem foreign_slots a) -> None
  | t -> t

(* The sub's block tids. *)
let sub_tids (sub : sub term) : Tid.Set.t =
  Core.Set.of_list (module Tid)
    (Base.List.map (Seq.to_list (Term.enum blk_t sub)) ~f:Term.tid)

let bounded_words ~(denote : denote) ~(block_addrs : Tid.t Addr.Map.t)
    ~(blk : blk term) ?def
    (texp : exp) : Cbat_word.t list option =
  if Core.Map.is_empty block_addrs then None
  else
    Base.Option.bind (Base.Result.ok (denote ~blk ?def texp)) ~f:(fun ws ->
        if Vsa.WordSet.is_top ws || Vsa.WordSet.is_infinite ws
           || Vsa.WordSet.is_bottom ws
        then (
          Hike_diag.debug ~tag:"hike-dbg-dispatch" (fun () ->
              Printf.sprintf "bounded_words: the target denotation is %s"
                (if Vsa.WordSet.is_top ws then "TOP"
                 else if Vsa.WordSet.is_infinite ws then "INFINITE"
                 else "BOTTOM"));
          None)
        else
          (match
             Vsa.WordSet.enumerate ~cap:(Core.Map.length block_addrs) ws
           with
           | Some ws -> Some ws
           | None ->
             Hike_diag.debug ~tag:"hike-dbg-dispatch" (fun () ->
                 Printf.sprintf
                   "bounded_words: card exceeds the map's %d blocks"
                   (Core.Map.length block_addrs));
             None))

(* A module-relative dispatch's base: the module-address var summand of
   the target's value read at some position, with its link-time values.
   The guards subtract the summand itself, so the relocation of whatever
   global holds the base cancels; each case then compares table data
   against [word - base].  [site] is the position to bind the summand at
   when its var is rewritten before the transfer. *)
type base = {
  summand : exp;
  values : int64 list;
  site : Hike_backsubst.form option;
}

type dispatch = {
  words : Cbat_word.t list;
  base : base option;
}

(* The base guard enumerates (base, word) pairs: a few bases at most. *)
let base_cap = 16

let is_module_address (ws : Vsa.WordSet.t) : bool =
  match Vsa.WordSet.origin ws with
  | Some (Vsa.WordSet.Origin.Rip _) -> true
  | _ -> false

let rec summands (e : exp) : exp list =
  match e with
  | Bil.BinOp (Bil.PLUS, a, b) -> summands a @ summands b
  | e -> [ e ]

(* The target's value at each position the backward substitution
   reaches: a form whose summands hold one module-address var beside
   others names the base, read there.  The nearest form whose summand
   still holds at the transfer wins, else the nearest form, bound at its
   position.  [Some None]: no form
   has a module-address summand.  [None]: one does, but no form gives
   an enumerable var base, so no case series is sound. *)
let module_base ~(denote : denote) ~(graph : Hike_backsubst.graph) ~(blk : blk term)
    (texp : exp) : base option option =
  let classify (f : Hike_backsubst.form) =
    let parts = summands f.exp in
    let based =
      Base.List.filter_map parts ~f:(fun e ->
          match denote ~blk:f.blk ?def:f.at e with
          | Ok ws when is_module_address ws -> Some (e, ws)
          | _ -> None)
    in
    match based with
    | [] -> `No_base
    | [ _ ] when Base.List.length parts < 2 -> `No_base
    | [ ((Bil.Var _ as e), ws) ] -> (
      match Vsa.WordSet.enumerate ~cap:base_cap ws with
      | Some ws -> (
        match Base.Option.all (Base.List.map ws ~f:Cbat_word.to_int64_opt) with
        | Some values ->
          `Base { summand = e; values;
                  site = Base.Option.some_if (not (Hike_backsubst.holds f e)) f }
        | None -> `Bad)
      | None -> `Bad)
    | _ -> `Bad
  in
  let classes = Base.List.map (Hike_backsubst.forms graph blk texp) ~f:classify in
  let bases = Base.List.filter_map classes ~f:(function `Base b -> Some b | _ -> None) in
  match Base.List.find bases ~f:(fun b -> Option.is_none b.site), bases with
  | Some b, _ | None, b :: _ -> Some (Some b)
  | None, [] ->
    if Base.List.exists classes ~f:(function `Bad -> true | _ -> false) then None
    else Some None

(* A dispatch site's destination words: the target's bounded
   denotation, read before its last def. *)
let case_words ~(denote : denote) ~(block_addrs : Tid.t Addr.Map.t)
    ~(last_defs : def term Var.Map.t) ~(blk : blk term) (texp : exp) :
    Cbat_word.t list option =
  Hike_diag.debug ~tag:"hike-dbg-dispatch" (fun () ->
      Printf.sprintf "dw: blk %s texp=%s last=%b"
        (Tid.name (Term.tid blk))
        (match texp with
         | Bil.Var v -> "var " ^ Var.name v
         | Bil.BinOp (Bil.PLUS, _, _) -> "plus"
         | _ -> "other")
        (match texp with
         | Bil.Var v -> Core.Map.mem last_defs v
         | _ -> true));
  let rhs, at =
    match texp with
    | Bil.Var v -> (
      match Core.Map.find last_defs v with
      | Some d -> (Def.rhs d, Some d)
      | None -> (texp, None))
    | _ -> (texp, None)
  in
  bounded_words ~denote ~block_addrs ~blk ?def:at rhs

(* [graph] must carry every dispatch's case edges: the base walk crosses
   only a block's sole predecessor. *)
let dispatch_words ~(denote : denote) ~(graph : Hike_backsubst.graph)
    ~(block_addrs : Tid.t Addr.Map.t)
    ~(last_defs : def term Var.Map.t) ~(blk : blk term) (texp : exp) :
    dispatch option =
  match module_base ~denote ~graph ~blk texp with
  | None -> None
  | Some base ->
    Base.Option.map (case_words ~denote ~block_addrs ~last_defs ~blk texp)
      ~f:(fun words -> { words; base })

(* A dispatch arm: a direct goto, guarded by its indirect transfer's
   target equalling one destination word, placed before that transfer in
   its block.  The tag is the word: the guard compares model addresses
   until [Split_blocks.materialize] rewrites it relocation-safe. *)
let arm_tag : int64 Value.Tag.t =
  Value.Tag.register ~package:"hike" ~name:"hike-dispatch-arm"
    ~uuid:"2a9e6c1d-4b7f-4e03-8d52-91c6f0a3b7e8"
    (module Core.Int64)

let arm_word (j : jmp term) : int64 option = Term.get_attr j arm_tag

(* The case blocks of a complete dispatch: every word names an in-sub
   block, or the series would drop live cases. *)
let resolved_cases ~(denote : denote) ~(last_defs : def term Var.Map.t)
    ~(sub_tids : Tid.Set.t) ~(block_addrs : Tid.t Addr.Map.t)
    ~(blk : blk term) (texp : exp) : tid list option =
  (* An armed word's edge is its arm, entered under its guard. *)
  let armed =
    Term.enum jmp_t blk |> Seq.filter_map ~f:arm_word |> Seq.to_list
    |> Core.Int64.Set.of_list
  in
  Base.Option.bind (case_words ~denote ~block_addrs ~last_defs ~blk texp)
    ~f:(fun words ->
      let words =
        Base.List.filter words ~f:(fun w ->
            not (Base.Option.value_map (Cbat_word.to_int64_opt w) ~default:false
                   ~f:(Core.Set.mem armed)))
      in
      let cases =
        Base.List.filter_map words ~f:(fun w ->
            match Core.Map.find block_addrs (Cbat_word.to_word w) with
            | Some t when Core.Set.mem sub_tids t -> Some t
            | _ -> None)
      in
      if Base.List.length cases = Base.List.length words
         && not (Base.List.is_empty cases)
      then Some cases
      else None)

let true_cond : exp = Bil.Int (Word.one 1)

let guard_of (j : jmp term) : exp option =
  match Jmp.cond j with c when Model.is_true_cond c -> None | c -> Some c

let and_guard (guard : exp option) (cond : exp) : exp =
  Base.Option.fold guard ~init:cond ~f:(fun cond g -> Bil.BinOp (Bil.AND, g, cond))

(* The target of a transfer an arm can stand in for: an indirect goto,
   or the noreturn call that renders an indirect tail jump. *)
let jump_target (j : jmp term) : exp option =
  match Jmp.kind j with
  | Goto (Indirect e) -> Some e
  | Call c when Option.is_none (Call.return c) -> (
    match Call.target c with Indirect e -> Some e | Direct _ -> None)
  | _ -> None

(* Each indirect transfer gains one arm per destination word ([dests])
   naming the start of one of [sub]'s blocks; the transfer stays after
   them as the fallback for every word no arm tests.  The BIR then
   carries every resolved edge, and each case block is entered under
   its own guard.  An armed jump is a goto: its noreturn-call rendering
   would leave the block's goto series, and a word naming a sub is the
   tail call [Split_blocks.materialize] makes of it. *)
let arm_dispatches ~(dests : jmp term -> int64 list) (sub : sub term) : sub term =
  let starts =
    Term.enum blk_t sub
    |> Seq.filter_map ~f:(fun b ->
        Base.Option.map (Term.get_attr b address) ~f:(fun a ->
            (Word.to_int64_exn a, Term.tid b)))
    |> Seq.to_list
    |> Core.Int64.Map.of_alist_reduce ~f:(fun a _ -> a)
  in
  Term.map blk_t sub ~f:(fun blk ->
      Term.concat_map jmp_t blk ~f:(fun j ->
          match jump_target j with
          | Some e -> (
            match Type.infer e with
            | Ok (Type.Imm bits) ->
            let arms =
              Base.List.filter_map (dests j) ~f:(fun w ->
                  Base.Option.map (Core.Map.find starts w) ~f:(fun t ->
                      let test =
                        Bil.BinOp (Bil.EQ, e, Bil.Int (Word.of_int64 ~width:bits w)) in
                      Jmp.create ~cond:(and_guard (guard_of j) test) (Goto (Direct t))
                      |> fun a -> Term.set_attr a arm_tag w))
              in
              if Base.List.is_empty arms then [ j ]
              else arms @ [ Jmp.with_kind j (Goto (Indirect e)) ]
            | _ -> [ j ])
          | None -> [ j ]))

(* The return epilogue's replacement: the canonical direct return edge. *)
let ret_jmp : jmp term = Hike_return.create ()

(* The canonical return keeps the original edge's condition; an
   unconditional return stays unconditional. *)
let canonical_ret (j : jmp term) : jmp term =
  if Model.is_true_cond (Jmp.cond j) then ret_jmp
  else Jmp.with_cond ret_jmp (Jmp.cond j)

let ret_rewrite ~(last_defs : def term Var.Map.t) ~(retaddr : Tid.Set.t)
    (j : jmp term) : jmp term list option =
  match Jmp.kind j with
  | Call c -> (
      match (Call.return c, Call.target c) with
      | None, Indirect (Bil.Var v) when retaddr_read ~last_defs ~retaddr v ->
          Some [ canonical_ret j ]
      | _ -> None)
  | Goto (Indirect (Bil.Var v)) when retaddr_read ~last_defs ~retaddr v ->
      Some [ canonical_ret j ]
  | _ -> None

(* Rebuilds [blk] replacing each jmp its classifier rewrites; a
   classifier [None] keeps the jmp. *)
let splice_jmps (blk : blk term)
    ~(classify : jmp term -> jmp term list option) : blk term =
  let js = Seq.to_list (Term.enum jmp_t blk) in
  let decided =
    Base.List.filter_map js ~f:(fun j ->
        Base.Option.map (classify j) ~f:(fun js' -> (Term.tid j, js')))
  in
  match decided with
  | [] -> blk
  | _ ->
      let rewr = Core.Map.of_alist_exn (module Tid) decided in
      Term.concat_map jmp_t blk ~f:(fun j ->
          match Core.Map.find rewr (Term.tid j) with
          | Some js' -> js'
          | None -> [ j ])

(* The drain's one BIR change: the retaddr read becomes the canonical
   return edge.  The bounded dispatches materialize later, in
   [Split_blocks.materialize], where the whole-program address maps are
   final. *)
let rewrite_jmps_once ~(retaddr : Tid.Set.t) (sub : sub term) : sub term =
  Term.map blk_t sub ~f:(fun blk ->
      let last_defs = Vsa.last_defs blk in
      splice_jmps blk
        ~classify:(ret_rewrite ~last_defs ~retaddr))

(* Each block's follower in [sub]'s term order: the false edge of a
   conditional goto whose block has no explicit one. *)
let fallthroughs (sub : sub term) : Tid.t Tid.Map.t =
  let tids = Term.enum blk_t sub |> Seq.map ~f:Term.tid |> Seq.to_list in
  match tids with
  | [] -> Tid.Map.empty
  | _ :: followers ->
    Base.List.zip_exn (Base.List.drop_last_exn tids) followers
    |> Core.Map.of_alist_reduce (module Tid) ~f:(fun a _ -> a)

(* The unreachable-block rule, one walk over the rewritten edge set: a
   block is kept iff the walk reaches it — from the sub's entry over the
   explicit edges, or through a surviving indirect transfer of a REACHED
   block.  Such a transfer is classified where it stands: a target read
   through a linker-owned slot ([foreign_slots]) leaves the program; a
   retaddr read is the return epilogue; a bounded target names its
   in-sub blocks; an unresolvable target keeps every block (the walk
   claims no deadness it cannot prove).  A block the walk does not
   reach cannot execute — no other sub transfers into it (a jump into
   another sub's interior is the tail-call rule, its entry only) — so
   dropping it is dead-code removal, never a missing definition. *)
let prune_unreachable ~(denote : denote) ~(retaddr : Tid.Set.t)
    ~(block_addrs : Tid.t Addr.Map.t)
    ~(foreign_slots : Core.Int64.Set.t) (sub : sub term) : sub term =
  (* The walk starts at the sub's own entry — the block at the address
     the partition named — falling back to the graph's in-degree-0 root
     (a single-root sub).  A partition may hand a sub blocks the entry
     never reaches (a decoded region's orphans); the address attr is
     what names the real one. *)
  let entry =
    let at_addr =
      match Term.get_attr sub address with
      | Some a ->
        Term.enum blk_t sub
        |> Seq.find ~f:(fun b ->
               match Term.get_attr b address with
               | Some x -> Addr.equal x a
               | None -> false)
      | None -> None
    in
    match at_addr with Some b -> Some b | None -> Vsa.entry_block_of sub
  in
  match entry with
  | None -> sub
  | Some entry ->
    let index = Hike_transfer.index_of_sub sub in
    let blocks = Seq.to_list (Term.enum blk_t sub) in
    let by_tid =
      Core.Map.of_alist_exn (module Tid)
        (Base.List.map blocks ~f:(fun b -> (Term.tid b, b)))
    in
    let find_block t = Core.Map.find by_tid t in
    let all = Core.Set.of_list (module Tid) (Base.List.map blocks ~f:Term.tid) in
    let fall_tbl = fallthroughs sub in
    let indirect_targets ~blk texp : Tid.Set.t option =
      let last_defs = Vsa.last_defs blk in
      match texp with
      | Bil.Var v when retaddr_read ~last_defs ~retaddr v -> Some Tid.Set.empty
      | _ -> (
        match
          Base.Option.bind (Hike_transfer.slot_of_target ~index texp)
            ~f:(fun a -> Base.Option.some_if (Core.Set.mem foreign_slots a) a)
        with
        | Some _ -> Some Tid.Set.empty
        | None ->
          match case_words ~denote ~block_addrs ~last_defs ~blk texp with
          | None -> Some all
          | Some ws ->
            Some
              (Base.List.fold ws ~init:Tid.Set.empty ~f:(fun acc w ->
                   let a = Cbat_word.to_word w in
                   match Core.Map.find block_addrs a with
                   | Some t -> Core.Set.add acc t
                   | _ -> acc)))
    in
    let rec go seen blk =
      if Core.Set.mem seen (Term.tid blk) then seen
      else
        let seen = Core.Set.add seen (Term.tid blk) in
        let js = Seq.to_list (Term.enum jmp_t blk) in
        let follow_direct seen ts =
          Base.List.fold ts ~init:seen ~f:(fun seen t ->
              match find_block t with
              | Some b -> go seen b
              | None -> seen)
        in
        let indirect seen ~blk texp =
          match indirect_targets ~blk texp with
          | None -> Core.Set.union seen all
          | Some extra -> follow_direct seen (Core.Set.to_list extra)
        in
        let seen =
          Base.List.fold js ~init:seen ~f:(fun seen j ->
              match Jmp.kind j with
              | Goto (Direct t) -> follow_direct seen [ t ]
              | Int (_, t) -> follow_direct seen [ t ]
              | Call c -> (
                  (* A call's return continuation is an edge whatever the
                     target's class: the call returns to it. *)
                  let seen =
                    match Call.target c with
                    | Indirect texp -> indirect seen ~blk texp
                    | _ -> seen
                  in
                  match Call.return c with
                  | Some (Direct t) -> follow_direct seen [ t ]
                  | _ -> seen)
              | Goto (Indirect texp) -> indirect seen ~blk texp
              | Ret _ -> seen)
        in
        (* The false edge of a conditional's term-order fallthrough is
           an edge (ADR 0024); the completion materializes it after this
           walk, so the walk reads it from the term order itself. *)
        if
          Base.List.is_empty js
          || not (Model.is_true_cond (Jmp.cond (Base.List.last_exn js)))
        then
          match Core.Map.find fall_tbl (Term.tid blk) with
          | Some t -> (
              match find_block t with
              | Some b -> go seen b
              | None -> seen)
          | _ -> seen
        else seen
    in
    let reachable = go Tid.Set.empty entry in
    Term.filter_map blk_t sub ~f:(fun b ->
        Base.Option.some_if (Core.Set.mem reachable (Term.tid b)) b)

(* The completion owns the edge set, so it names it here: the BIR's jumps
   ARE the block's successors.  A conditional goto's implicit false edge
   becomes an explicit Goto, and a block whose every edge leads to ONE
   destination is that single unconditional edge — the guards select
   nothing.  A guarded series keeps its edges: the split makes each piece
   a block of its own, so their destinations never collide. *)
let materialize_fallthroughs (sub : sub term) : sub term =
  let followers = fallthroughs sub in
  let direct (j : jmp term) : Tid.t option =
    match Jmp.kind j with Goto (Direct t) -> Some t | _ -> None
  in
  let normalize (blk : blk term) : blk term =
    let blk =
      match Base.List.last (Term.enum jmp_t blk |> Seq.to_list) with
      | Some j
        when Option.is_some (direct j)
             && not (Model.is_true_cond (Jmp.cond j)) -> (
          match Core.Map.find followers (Term.tid blk) with
          | Some succ -> Term.append jmp_t blk (Jmp.create (Goto (Direct succ)))
          | None -> blk)
      | _ -> blk
    in
    match Term.enum jmp_t blk |> Seq.to_list with
    | [] | [ _ ] -> blk
    | first :: _ as jmps -> (
        let targets = Base.List.map jmps ~f:direct in
        match direct first with
        | Some t
          when Base.List.for_all targets ~f:(fun x ->
                   Option.equal Tid.equal x (Some t)) ->
            Term.filter jmp_t blk ~f:(fun x ->
                Tid.equal (Term.tid x) (Term.tid first))
            |> Term.map jmp_t ~f:(fun x ->
                   Jmp.create ~tid:(Term.tid x) ~cond:true_cond (Jmp.kind x))
        | _ -> blk)
  in
  Term.map blk_t sub ~f:normalize

(* One resolution event pass on the phase's own solution: the resolved
   dispatches contribute their target sets to the extra edges.  The
   words are the target denotations; the drive discovers the case
   bodies from the raw transfers' own denotations, so the completion
   carries no fact channel. *)
let resolve_phase ~(abi : Hike_abi.t) ~(sol : Vsa.vsa_sol)
    ~(block_addrs : Tid.t Addr.Map.t)
    ~(foreign_slots : Core.Int64.Set.t)
    (sub : sub term) (resolved : Tid.Set.t Tid.Map.t) :
    Tid.Set.t Tid.Map.t * bool =
  let denote = denote_of_sol sol in
  let retaddr = retaddr_defs ~abi ~sol sub in
  let sub_tids = sub_tids sub in
  let index = Hike_transfer.index_of_sub sub in
  let resolved', grew =
    Term.enum blk_t sub
    |> Seq.fold ~init:(resolved, false) ~f:(fun acc blk ->
        let last_defs = Vsa.last_defs blk in
        Term.enum jmp_t blk
        |> Seq.fold ~init:acc ~f:(fun ((m, grew) as acc) j ->
            match dispatch_target ~last_defs ~retaddr ~index ~foreign_slots j with
            | None -> acc
            | Some texp -> (
                match
                  resolved_cases ~denote ~last_defs ~sub_tids
                    ~block_addrs ~blk texp
                with
                | None -> acc
                | Some cases ->
                    let ts = Core.Set.of_list (module Tid) cases in
                    match Core.Map.find m (Term.tid j) with
                    | Some old when Core.Set.equal old ts -> acc
                    | Some old ->
                        ( Core.Map.set m ~key:(Term.tid j)
                            ~data:(Core.Set.union old ts),
                          true )
                    | None ->
                        (Core.Map.set m ~key:(Term.tid j) ~data:ts, true))))
  in
  (resolved', grew)

(* The exit materialization at drain: the return canonicalization lands
   once, then the unreachable-block rule runs on the edge set.  The
   bounded dispatches materialize later, in
   [Split_blocks.materialize].  The denotations read the images through
   the caller's bracket. *)
let materialize ~(abi : Hike_abi.t) ~(sol : Vsa.vsa_sol)
    ~(block_addrs : Tid.t Addr.Map.t)
    ~(foreign_slots : Core.Int64.Set.t)
    (sub : sub term) : sub term =
  let retaddr = retaddr_defs ~abi ~sol sub in
  let sub = rewrite_jmps_once ~retaddr sub in
  prune_unreachable ~denote:(denote_of_sol sol) ~retaddr ~block_addrs
    ~foreign_slots sub
  |> materialize_fallthroughs
