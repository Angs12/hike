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

(* The dispatch words the resolution's phases enumerated, with each
   site's address and call class: the drive loop's fact source.  The
   facts ride the solve's return, never a global. *)
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

(* The dispatch resolution's debug trace; the message is a thunk so
   production never formats it. *)
let debug_trace (msg : unit -> string) =
#ifdef VSA_DEBUG
  Printf.eprintf "hike-dbg-dispatch: %s\n%!" (msg ())
#else
  ignore msg
#endif

(* The jmp's indirect target when it is neither a retaddr read nor a
   read through a linker-owned slot: the ret epilogue's target is the
   stack-symbolic cell, and a slot-read target is a foreign boundary —
   the dynamic linker fills the value, so the file bytes are not a
   dispatch's case words.  Neither is ever a dispatch. *)
let dispatch_target ~(last_defs : def term Var.Map.t) ~(retaddr : Tid.Set.t)
    ~(sub : sub term) ~(foreign_slots : Core.Int64.Set.t)
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
      Base.Option.value_map (Hike_transfer.slot_of_target ~sub t)
        ~default:false ~f:(fun a -> Core.Set.mem foreign_slots a) -> None
  | t -> t

(* The sub's block tids. *)
let sub_tids (sub : sub term) : Tid.Set.t =
  Core.Set.of_list (module Tid)
    (Base.List.map (Seq.to_list (Term.enum blk_t sub)) ~f:Term.tid)

let addressed_starts ~(block_addrs : Tid.t Addr.Map.t) (sub : sub term) :
    (Addr.t * tid) list =
  let tids = sub_tids sub in
  block_addrs
  |> Core.Map.to_alist
  |> Base.List.filter ~f:(fun (_, t) -> Core.Set.mem tids t)

(* The dispatch's case words: a bounded plain set no larger than the
   run's block count — the words a resolution may target or split at. *)
let bounded_words ~(denote : denote) ~(block_addrs : Tid.t Addr.Map.t)
    ~(blk : blk term) ?def
    (texp : exp) : Cbat_word.t list option =
  if Core.Map.is_empty block_addrs then None
  else
    Base.Option.bind (Base.Result.ok (denote ~blk ?def texp)) ~f:(fun ws ->
        if Vsa.WordSet.is_top ws || Vsa.WordSet.is_infinite ws
           || Vsa.WordSet.is_bottom ws
        then (
          debug_trace (fun () ->
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
             debug_trace (fun () ->
                 Printf.sprintf
                   "bounded_words: card exceeds the map's %d blocks"
                   (Core.Map.length block_addrs));
             None))

(* Rewrite a lifted term's direct targets: a call's target names a
   subroutine, a goto's a block, so the two resolve through different
   maps.  Indirect targets stay the resolution's own. *)
let remap_label f = function
  | Direct t -> Direct (f t)
  | Indirect e -> Indirect e

let remap_jmp ~(call : Tid.t -> Tid.t) ~(blk : Tid.t -> Tid.t) (j : jmp term) :
    jmp term =
  if Hike_return.is_jmp j then j
  else
    let kind =
      match Jmp.kind j with
      | Goto l -> Goto (remap_label blk l)
      | Ret l -> Ret (remap_label blk l)
      | Int (n, t) -> Int (n, blk t)
      | Call c ->
        Call
          (Call.create ~target:(remap_label call (Call.target c))
             ?return:(Base.Option.map (Call.return c) ~f:(remap_label blk))
             ())
    in
    Jmp.create ~tid:(Term.tid j) ~cond:(Jmp.cond j) kind

(* The dispatch's case words, denotated at the state the jump reads;
   a bare-variable target's words come from its reaching definition's
   before-env, never the noreturn-poisoned post-transfer state. *)

(* A composed expression's form: [Whole e] is an operand made entirely
   of base subtrees — no loaded cell — and [e] is the operand as it
   participates in the subtraction (a cast is transparent, a bare var
   keeps its name); [Cells bases] is the base operands that isolate
   exactly one loaded cell. *)
type composed = Whole of exp | Cells of exp list

(* The composed address's base operands: the very operand subtrees that
   contributed the table's start address.  The guard subtracts them from
   the target so the subject is the loaded cell value — the table's own
   data coordinate, which cancels any runtime base (PIE).  A var read
   inside a def's rhs resolves to the def of that var strictly before
   the reading def, in the sub's term order; a [v := v + e] def composes
   over the def it extends.  Two cell sets or a missing side refuse the
   composition. *)
let base_operands ~(last_defs : def term Var.Map.t) ~(sub : sub term)
    ~(at : def term option) (texp : exp) : exp list option =
  (* A var read inside a def's rhs resolves to the def of that var
     strictly before the reading def, in the SUB's term order: the
     table's base register is commonly defined blocks away from the
     dispatch block. *)
  let definitions = lazy (
    Term.enum blk_t sub |> Seq.concat_map ~f:(Term.enum def_t)
    |> Seq.fold ~init:(Tid.Map.empty, Var.Map.empty, Var.Map.empty)
         ~f:(fun (before, first, last) d ->
           let v = Def.lhs d in
           (Core.Map.set before ~key:(Term.tid d) ~data:last,
            (if Core.Map.mem first v then first
             else Core.Map.set first ~key:v ~data:d),
            Core.Map.set last ~key:v ~data:d)))
  in
  let find_def at v =
    match at with
    | Some d ->
      (* [before] is the definition prefix before [d] in the sub's term
         order, so the answer is strictly earlier than the reading
         def.  A def outside the sub has no position there; the
         composition refuses rather than resolving forward. *)
      let before, _, _ = Lazy.force definitions in
      Base.Option.bind (Core.Map.find before (Term.tid d)) ~f:(fun defs ->
          Core.Map.find defs v)
    | None -> (
      match Core.Map.find last_defs v with
      | Some _ as found -> found
      | None ->
        let _, first, _ = Lazy.force definitions in
        Core.Map.find first v)
  in
  (* One composition rule over the supported grammar: a cast is
     transparent; a plus over a whole-base side and a cell side is the
     cell's base list; a bare var follows its definition.  Termination:
     a var step resolves to a def strictly EARLIER than the reading def
     in the sub's term order ([find_def]'s prefix), and every other
     step descends into a strictly smaller expression — a well-founded
     descent, so no depth budget is needed.  The rule returns the
     operand's form: [Whole] keeps the operand as it participates (a
     cast is transparent, a bare var keeps its name), [Cells] the base
     operands isolating its one loaded cell. *)
  let rec compose ~at (e : exp) : composed option =
    match e with
    | Bil.Int _ -> Some (Whole e)
    | Bil.Load _ -> Some (Cells [])
    | Bil.Cast (_, _, e2) -> compose ~at e2
    | Bil.BinOp (Bil.PLUS, a, b) -> (
      match (compose ~at a, compose ~at b) with
      | Some (Whole _), Some (Whole _) -> Some (Whole e)
      | Some (Whole pa), Some (Cells bs) -> Some (Cells (pa :: bs))
      | Some (Cells bs), Some (Whole pb) -> Some (Cells (pb :: bs))
      | _ -> None)
    | Bil.Var v when Hike_synth.is_base_var Hike_synth.empty v ->
      (* Every synthetic base family — the resolved rip address, the
         argument lanes, the allocas, the storage pointers — is a base
         operand, never a cell. *)
      Some (Whole e)
    | Bil.Var v -> (
      match find_def at v with
      | Some d -> (
        match compose ~at:(Some d) (Def.rhs d) with
        | Some (Whole _) -> Some (Whole e)
        | Some (Cells _ as cells) -> Some cells
        | None -> None)
      | None -> None)
    | _ -> None
  in
  match compose ~at texp with
  | Some (Cells bases) -> Some bases
  | Some (Whole _) | None -> None

(* The dispatch's table words: the composed base operands give the
   guard's delta coordinate; the denotation is the one destination-set
   fact and enumerates the cells — the phase loop widens the index
   across the resolved edges, so no image walk is needed. *)
let table_words ~(denote : denote) ~(block_addrs : Tid.t Addr.Map.t)
    ~(last_defs : def term Var.Map.t) ~(sub : sub term) ~(blk : blk term)
    ~(at : def term option) (texp : exp) :
    (Int64.t * exp list * Cbat_word.t list) option =
  match base_operands ~last_defs ~sub ~at texp with
  | Some bases when not (Base.List.is_empty bases) -> (
    let base_exp =
      Base.List.reduce_exn bases ~f:(fun a b -> Bil.BinOp (Bil.PLUS, a, b))
    in
    match
      ( bounded_words ~denote ~block_addrs ~blk ?def:at texp,
        bounded_words ~denote ~block_addrs ~blk base_exp )
    with
    | Some ws, Some [ b ] ->
      Base.Option.map (Base.Result.ok (Cbat_word.to_int64 b))
        ~f:(fun base -> (base, bases, ws))
    | _ -> None)
  | _ -> None

let dispatch_words ~(denote : denote) ~(block_addrs : Tid.t Addr.Map.t)
    ~(last_defs : def term Var.Map.t)
    ~(sub : sub term)
    ~(blk : blk term) (texp : exp) :
    (Int64.t option * exp list option * Cbat_word.t list) option =
  debug_trace (fun () ->
      Printf.sprintf "dw: blk %s texp=%s last=%b"
        (Tid.name (Term.tid blk))
        (match texp with
         | Bil.Var v -> "var " ^ Var.name v
         | Bil.BinOp (Bil.PLUS, _, _) -> "plus"
         | _ -> "other")
        (match texp with
         | Bil.Var v -> Core.Map.mem last_defs v
         | _ -> true));
  let table e at =
    Base.Option.map
      (table_words ~denote ~block_addrs ~last_defs ~sub ~blk ~at e)
      ~f:(fun (base, bases, ws) -> (Some base, Some bases, ws))
  in
  let plain e ?def () =
    Base.Option.map (bounded_words ~denote ~block_addrs ~blk ?def e)
      ~f:(fun ws -> (None, None, ws))
  in
  match texp with
  | Bil.BinOp (Bil.PLUS, _, _) -> (
    (* The composed table's guard coordinate (the base subtraction) with
       the denotation's bounded set as the destination words; the plain
       arm serves the shapes no base composes. *)
    match table texp None with
    | Some _ as r -> r
    | None -> plain texp ())
  | Bil.Var v ->
    (match Core.Map.find last_defs v with
     | Some add_def ->
       let rhs = Def.rhs add_def in
       (match table rhs (Some add_def) with
        | Some _ as r -> r
        | None -> plain rhs ~def:add_def ())
     | None -> plain texp ())
  | _ -> plain texp ()

let resolved_pairs_of ~(denote : denote) ~(last_defs : def term Var.Map.t)
    ~(sub_tids : Tid.Set.t) ~(block_addrs : Tid.t Addr.Map.t)
    ~(sub : sub term)
    ~(blk : blk term) (texp : exp) :
    (exp * (word * tid) list * Int64.t) option =
  match
    dispatch_words ~denote ~block_addrs ~last_defs ~sub ~blk texp
  with
  | None -> None
  | Some (base, bases, ws) ->
    (* The guard's subject subtracts every base operand as the very
       exp that contributed it, so the subtraction cancels exactly in
       any coordinate system (a section-backed base may render as a
       real pointer under PIE; a raw module constant beside it would
       disagree) — the guards then compare the loaded entry's signed
       delta, which is table data.  A plain bounded set has no base:
       its guards compare the target itself (internally consistent).
       The set is complete by construction — the walk covers every
       consecutive code entry from the base, and a bounded
       denotation is an over-approximation. *)
    let b = Base.Option.value base ~default:0L in
    let case (w : Cbat_word.t) : (word * tid) option =
      let a = Cbat_word.to_word w in
      match Core.Map.find block_addrs a with
      | Some t when Core.Set.mem sub_tids t ->
        Some (Addr.of_int64 (Int64.sub (Word.to_int64_exn a) b), t)
      | _ -> None
    in
    let pairs = Base.List.filter_map ws ~f:case in
    if
      Base.List.length pairs = Base.List.length ws
      && not (Base.List.is_empty pairs)
    then
      let subject =
        Base.List.fold_left (Base.Option.value ~default:[] bases)
          ~init:texp
          ~f:(fun acc b -> Bil.BinOp (Bil.MINUS, acc, b))
      in
      Some (subject, pairs, b)
    else None

(* The eq chain of one target's words: [sel = w1 || sel = w2 || ...].
   The words share the selector's width, so the comparisons typecheck. *)
(* [ws] is non-empty — a case group is built from at least one word. *)
let guarded_cond (sel : exp) (ws : word list) : exp =
  let eq w = Bil.BinOp (Bil.EQ, sel, Bil.Int w) in
  (match ws with
   | w :: rest ->
       Base.List.fold rest ~init:(eq w)
         ~f:(fun acc w -> Bil.BinOp (Bil.OR, acc, eq w))
   | [] -> failwith "hike-cfg-complete: empty case group")
  |> Hike_coerce.coerce_exp

(* The dispatch jmp's own guard narrows every case and the default
   alike. *)
let true_cond : exp = Bil.Int (Word.one 1)

let guard_of (j : jmp term) : exp option =
  match Jmp.cond j with c when Model.is_true_cond c -> None | c -> Some c

let and_guard (guard : exp option) (cond : exp) : exp =
  Base.Option.fold guard ~init:cond ~f:(fun cond g -> Bil.BinOp (Bil.AND, g, cond))

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
    let blocks = Seq.to_list (Term.enum blk_t sub) in
    let by_tid =
      Core.Map.of_alist_exn (module Tid)
        (Base.List.map blocks ~f:(fun b -> (Term.tid b, b)))
    in
    let find_block t = Core.Map.find by_tid t in
    let all = Core.Set.of_list (module Tid) (Base.List.map blocks ~f:Term.tid) in
    let rec nexts = function
      | [] -> []
      | b :: tl -> (
          let nx = match tl with b2 :: _ -> Some (Term.tid b2) | [] -> None in
          (Term.tid b, nx) :: nexts tl)
    in
    let fall_tbl = Core.Map.of_alist_exn (module Tid) (nexts blocks) in
    let indirect_targets ~blk texp : Tid.Set.t option =
      let last_defs = Vsa.last_defs blk in
      match texp with
      | Bil.Var v when retaddr_read ~last_defs ~retaddr v -> Some Tid.Set.empty
      | _ -> (
        match
          Base.Option.bind (Hike_transfer.slot_of_target ~sub texp)
            ~f:(fun a -> Base.Option.some_if (Core.Set.mem foreign_slots a) a)
        with
        | Some _ -> Some Tid.Set.empty
        | None ->
          match dispatch_words ~denote ~block_addrs ~last_defs ~sub ~blk texp with
          | None -> Some all
          | Some (_, _, ws) ->
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
        let follow_extra seen extra =
          Core.Set.fold extra ~init:seen ~f:(fun seen t ->
              match find_block t with
              | Some b -> go seen b
              | None -> seen)
        in
        let follow_direct seen ts =
          Base.List.fold ts ~init:seen ~f:(fun seen t ->
              match find_block t with
              | Some b -> go seen b
              | None -> seen)
        in
        let indirect seen ~blk texp =
          match indirect_targets ~blk texp with
          | None -> Core.Set.union seen all
          | Some extra -> follow_extra seen extra
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
          | Some (Some t) -> (
              match find_block t with
              | Some b -> go seen b
              | None -> seen)
          | _ -> seen
        else seen
    in
    let reachable = go Tid.Set.empty entry in
    Term.filter_map blk_t sub ~f:(fun b ->
        Base.Option.some_if (Core.Set.mem reachable (Term.tid b)) b)

(* The shape-only return canonicalization, for a sub whose fixpoint did
   not converge: a target var whose reaching def loads the entry SP
   cell.  This is the sanctioned pre-solution projection — the
   denotation path supersedes it wherever a solution exists. *)
(* The block that follows [blk] in [sub]'s term order: the false edge of a
   conditional goto whose block has no explicit one. *)
let fallthrough (sub : sub term) (blk : blk term) : Tid.t option =
  let tid = Term.tid blk in
  let rec go seen = function
    | [] -> None
    | b :: rest ->
        if seen then Some (Term.tid b)
        else go (Tid.equal (Term.tid b) tid) rest
  in
  go false (Term.enum blk_t sub |> Seq.to_list)

(* The completion owns the edge set, so it names it here: the BIR's jumps
   ARE the block's successors.  A conditional goto's implicit false edge
   becomes an explicit Goto, and a block whose every edge leads to ONE
   destination is that single unconditional edge — the guards select
   nothing.  A guarded series keeps its edges: the split makes each piece
   a block of its own, so their destinations never collide. *)
(* The noreturn fact's consumption: a call whose resolved target is a
   classified never-returning sub carries no return continuation, so the
   decode's fallthrough after it is not an edge.  Runs before the
   fallthrough materialization and the solve's phases. *)
let clear_noreturn_returns ~(noreturn : Tid.Set.t) (sub : sub term) : sub term =
  if Core.Set.is_empty noreturn then sub
  else
    Term.map blk_t sub ~f:(fun blk ->
        Term.map jmp_t blk ~f:(fun j ->
            match Jmp.kind j with
            | Call c -> (
                match Call.target c with
                | Direct t
                  when Core.Set.mem noreturn t
                       && Base.Option.is_some (Call.return c) ->
                  Jmp.with_kind j (Call (Call.with_noreturn c))
                | _ -> j)
            | _ -> j))

let materialize_fallthroughs (sub : sub term) : sub term =
  let direct (j : jmp term) : Tid.t option =
    match Jmp.kind j with Goto (Direct t) -> Some t | _ -> None
  in
  let normalize (blk : blk term) : blk term =
    let blk =
      match Base.List.last (Term.enum jmp_t blk |> Seq.to_list) with
      | Some j
        when Option.is_some (direct j)
             && not (Model.is_true_cond (Jmp.cond j)) -> (
          match fallthrough sub blk with
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

let canonicalize_shape_returns ~(abi : Hike_abi.t) (sub : sub term) : sub term =
  let word_bits = Hike_abi.word_bits abi in
  let retaddr =
    Term.enum blk_t sub
    |> Seq.concat_map ~f:(Term.enum def_t)
    |> Seq.filter_map ~f:(fun d ->
           match load_addr_of word_bits d with
           | Some addr when Model.is_return_address_shape ~abi addr ->
               Some (Term.tid d)
           | _ -> None)
    |> Seq.to_list |> Tid.Set.of_list
  in
  if Core.Set.is_empty retaddr then materialize_fallthroughs sub
  else
    Term.map blk_t sub ~f:(fun blk ->
        let last_defs = Vsa.last_defs blk in
        splice_jmps blk
          ~classify:(ret_rewrite ~retaddr ~last_defs))
    |> materialize_fallthroughs

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
  let grew = ref false in
  let resolved' =
    Term.enum blk_t sub
    |> Seq.fold ~init:resolved ~f:(fun acc blk ->
        let last_defs = Vsa.last_defs blk in
        Term.enum jmp_t blk
        |> Seq.fold ~init:acc ~f:(fun acc j ->
            match dispatch_target ~last_defs ~retaddr ~sub ~foreign_slots j with
            | None -> acc
            | Some texp -> (
                match
                  resolved_pairs_of ~denote ~last_defs ~sub_tids
                    ~block_addrs ~sub ~blk texp
                with
                | None -> acc
                | Some (_, pairs, _) ->
                    let ts =
                      Core.Set.of_list (module Tid)
                        (Base.List.map pairs ~f:snd) in
                    match Core.Map.find acc (Term.tid j) with
                    | Some old when Core.Set.equal old ts -> acc
                    | Some old ->
                        grew := true;
                        Core.Map.set acc ~key:(Term.tid j)
                          ~data:(Core.Set.union old ts)
                    | None ->
                        grew := true;
                        Core.Map.set acc ~key:(Term.tid j) ~data:ts)))
  in
  (resolved', !grew)

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
