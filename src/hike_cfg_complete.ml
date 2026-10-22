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
let denote_of_sol ~(synth : Hike_synth.table) (sol : Vsa.vsa_sol) : denote =
  fun ~blk ?def e ->
    Vsa.solve_denote ~synth
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
let retaddr_defs ~(abi : Hike_abi.t) ~(synth : Hike_synth.table)
    ~(sol : Vsa.vsa_sol)
    (sub : sub term) : Tid.Set.t =
  let word_bits = Hike_abi.word_bits abi in
  Term.enum blk_t sub
  |> Seq.fold ~init:Tid.Set.empty ~f:(fun acc blk ->
         fst
           (Vsa.fold_block_states ~synth ~sol blk ~init:acc
              ~f:(fun before _after d acc ->
                  match load_addr_of word_bits d with
                  | Some addr -> (
                      match Vsa.denote_imm_exp ~synth addr before with
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
let dispatch_target ~synth ~(last_defs : def term Var.Map.t) ~(retaddr : Tid.Set.t)
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
      Base.Option.value_map (Hike_transfer.slot_of_target ~synth ~index t)
        ~default:false ~f:(fun a -> Core.Set.mem foreign_slots a) -> None
  | t -> t

(* [cap] defaults to the block budget: a complete pre-freeze dispatch
   names at most one block per word.  The site materializer passes a
   wider bound because the case blocks do not exist yet. *)
let bounded_words ?cap ~(denote : denote)
    ~(block_addrs : Tid.t Addr.Map.t) ~(blk : blk term) ?def
    (texp : exp) : Cbat_word.t list option =
  if Core.Map.is_empty block_addrs then None
  else
    let cap =
      Base.Option.value cap ~default:(Core.Map.length block_addrs) in
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
          (match Vsa.WordSet.enumerate ~cap ws with
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
let case_words ?cap ~(denote : denote) ~(block_addrs : Tid.t Addr.Map.t)
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
  bounded_words ?cap ~denote ~block_addrs ~blk ?def:at rhs

(* [graph] must carry every dispatch's case edges: the base walk crosses
   only a block's sole predecessor. *)
let dispatch_words ?cap ~(denote : denote) ~(graph : Hike_backsubst.graph)
    ~(block_addrs : Tid.t Addr.Map.t)
    ~(last_defs : def term Var.Map.t) ~(blk : blk term) (texp : exp) :
    dispatch option =
  match module_base ~denote ~graph ~blk texp with
  | None -> None
  | Some base ->
    Base.Option.map
      (case_words ?cap ~denote ~block_addrs ~last_defs ~blk texp)
      ~f:(fun words -> { words; base })

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

(* The return epilogue's replacement: the canonical direct return edge. *)
let ret_jmp : jmp term = Hike_return.create ()

(* The canonical return keeps the original edge's condition; an
   unconditional return stays unconditional. *)
let canonical_ret (j : jmp term) : jmp term =
  (* Preserve the transfer's own effects: the canonical return reads the
     SSA versions the original transfer wrote, not the entry lanes. *)
  Jmp.with_kind j (Jmp.kind ret_jmp)

let ret_rewrite ~(last_defs : def term Var.Map.t) ~(retaddr : Tid.Set.t)
    (j : jmp term) : jmp term =
  match jump_target j with
  | Some (Bil.Var v) when retaddr_read ~last_defs ~retaddr v -> canonical_ret j
  | _ -> j

(* The drain's one BIR change: the retaddr read becomes the canonical
   return edge.  Dispatch arms were already installed during the
   solve. *)
let rewrite_jmps_once ~(retaddr : Tid.Set.t) (sub : sub term) : sub term =
  Term.map blk_t sub ~f:(fun blk ->
      let last_defs = Vsa.last_defs blk in
      Term.map jmp_t blk ~f:(ret_rewrite ~last_defs ~retaddr))

(* Each block's follower in [sub]'s term order: the false edge of a
   conditional goto whose block has no explicit one. *)
let fallthroughs (sub : sub term) : Tid.t Tid.Map.t =
  let tids = Term.enum blk_t sub |> Seq.map ~f:Term.tid |> Seq.to_list in
  match tids with
  | [] -> Tid.Map.empty
  | _ :: followers ->
    Base.List.zip_exn (Base.List.drop_last_exn tids) followers
    |> Core.Map.of_alist_reduce (module Tid) ~f:(fun a _ -> a)

let term_follower (sub : sub term) (tid : Tid.t) : Tid.t option =
  Core.Map.find (fallthroughs sub) tid

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
let prune_unreachable ~synth ~(denote : denote) ~(retaddr : Tid.Set.t)
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
    match at_addr with
    | Some b -> Some b
    | None -> Vsa.entry_block_of sub
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
          Base.Option.bind (Hike_transfer.slot_of_target ~synth ~index texp)
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

(* The exit materialization at drain: the return canonicalization lands
   once, then the unreachable-block rule runs on the edge set.  The
   denotations read the images through the caller's bracket.  The
   caller supplies the same [retaddr_defs] set as the drained
   resolution phase. *)
let materialize ~(sol : Vsa.vsa_sol)
    ~(synth : Hike_synth.table)
    ~(block_addrs : Tid.t Addr.Map.t)
    ~(foreign_slots : Core.Int64.Set.t)
    ~(retaddr : Tid.Set.t)
    (sub : sub term) : sub term =
  let sub = rewrite_jmps_once ~retaddr sub in
  prune_unreachable ~synth ~denote:(denote_of_sol ~synth sol) ~retaddr ~block_addrs
    ~foreign_slots sub

(* ---- staged site builder ---- *)

(* A site materialization's intra-sub case target: the validated target
   address, its final tid, and the target's lifted fragment.  The builder
   is the growth runner's Prepare/Create/Wire/Finalize/DCE over exactly
   the new blocks and the exact block edges; the source block is already
   rewritten in [working] before the run. *)

type case = int64 * Tid.t * sub term

(* Exact block edge: source block, destination block. *)
type edge = Tid.t * Tid.t

type delta = {
  delta_sub : sub term;
  delta_synth : Hike_synth.table;
  new_blocks : Tid.Set.t;
  new_edges : edge list;
  woken : Tid.Set.t;
}

let fail_build fmt =
  Printf.ksprintf (fun s -> failwith ("hike-dispatch: " ^ s)) fmt

let block_addr (b : blk term) : int64 option =
  Base.Option.map (Term.get_attr b address) ~f:Word.to_int64_exn

let same_tid a b = Tid.equal a b

(* A block with the builder's tid, every other component preserved. *)
let retag ~tid (b : blk term) : blk term =
  let b' =
    Blk.create ~tid
      ~phis:(Term.enum phi_t b |> Seq.to_list)
      ~defs:(Term.enum def_t b |> Seq.to_list)
      ~jmps:(Term.enum jmp_t b |> Seq.to_list) ()
  in
  Term.with_attrs b' (Term.attrs b)

let map_jmp_refs (rename : Tid.t -> Tid.t) (j : jmp term) : jmp term =
  let relabel = Label.change ~direct:(fun t -> rename t) in
  Jmp.with_kind j
    (match Jmp.kind j with
     | Goto l -> Goto (relabel l)
     | Ret l -> Ret (relabel l)
     | Int (n, r) -> Int (n, rename r)
     | Call c -> (
       match Call.return c with
       | Some r -> Call (Call.with_return c (relabel r))
       | None -> Call c))

let map_block_refs rename (b : blk term) : blk term =
  Term.map jmp_t b ~f:(map_jmp_refs rename)

let map_phi_refs rename (b : blk term) : blk term =
  Term.map phi_t b ~f:(fun p ->
      Phi.of_list (Phi.lhs p)
        (Phi.values p
        |> Seq.map ~f:(fun (src, e) -> (rename src, e))
        |> Seq.to_list))

let map_refs rename b = map_block_refs rename (map_phi_refs rename b)

let isolate_block (blk : blk term) : blk term * blk term list =
  let moved = ref [] in
  let is_goto j = match Jmp.kind j with Goto _ -> true | _ -> false in
  let jmps = Term.enum jmp_t blk |> Seq.to_list in
  if Base.List.length jmps < 2 || Base.List.for_all jmps ~f:is_goto then
    (blk, [])
  else
    let blk =
      Term.concat_map jmp_t blk ~f:(fun j ->
          if is_goto j then [ j ]
          else begin
            let own =
              Blk.create ~jmps:[ Jmp.with_cond j (Bil.Int (Word.one 1)) ] ()
            in
            moved := own :: !moved;
            [ Jmp.create_goto ~cond:(Jmp.cond j) (Direct (Term.tid own)) ]
          end)
    in
    (blk, Base.List.rev !moved)

let isolate_transfers (sub : sub term) : sub term =
  let moved = ref [] in
  let sub =
    Term.map blk_t sub ~f:(fun blk ->
        let blk, own = isolate_block blk in
        moved := Base.List.rev_append own !moved;
        blk)
  in
  Base.List.fold (Base.List.rev !moved) ~init:sub ~f:(Term.append blk_t)

let all_block_tids (sub : sub term) : Tid.Set.t =
  Core.Set.of_list (module Tid)
    (Base.List.map (Term.enum blk_t sub |> Seq.to_list) ~f:Term.tid)

(* One builder run's state: [old] is the pre-rewrite sub (the SSA baseline),
   [working] is the assembled rewrite the stages transform. *)
type context = {
  target : Bap_core_theory.Theory.Target.t;
  abi : Hike_abi.t;
  callee_tid : Tid.t -> Tid.t;
  rip_address : int64 -> bool;
  claim : sub term -> sub term;
  synth : Hike_synth.table ref;
  mutable block_addrs : Tid.t Addr.Map.t;
  old : sub term;
  mutable working : sub term;
  fragments : sub term Core.Int64.Map.t;
  target_tids : Tid.t Core.Int64.Map.t;
  mutable created : Tid.Set.t;
  mutable created_blocks : blk term list;
  mutable edges : edge list;
  mutable result : sub term option;
  mutable woken : Tid.Set.t;
}

type stage = Create | Wire | Finalize

type item = Block of Tid.t | Edge of edge | Batch

type pass = {
  name : string;
  stage : stage;
  run : context -> sub term -> item -> sub term;
}

(* ---- Prepare ---- *)

let prepare_new_block ctx (addr : int64) : unit =
  if Core.Map.mem ctx.block_addrs (Addr.of_int64 addr) then ()
  else begin
    let fragment = Core.Map.find_exn ctx.fragments addr in
    let fragment = ctx.claim fragment in
    let fragment = isolate_transfers fragment in
    let old_tids = all_block_tids ctx.old in
    let used = Core.Set.union old_tids ctx.created in
    let raw = Term.enum blk_t fragment |> Seq.to_list in
    let target_block =
      Base.List.find raw ~f:(fun b ->
          match block_addr b with Some a -> Int64.equal a addr | None -> false)
    in
    if Base.Option.is_none target_block then
      fail_build "resolved target %Lx did not decode to a block" addr;
    (* The final tid per raw fragment block: an existing block keeps its
       tid, a resolved target keeps the allocated tid, and a genuinely
       new direct successor keeps the decoder's tid unless it collides. *)
    let final_of = Core.Hashtbl.create (module Tid) in
    Base.List.iter raw ~f:(fun b ->
        match block_addr b with
        | None -> ()
        | Some a ->
          let tid =
            match Core.Map.find ctx.block_addrs (Addr.of_int64 a) with
            | Some existing -> existing
            | None -> (
              match Core.Map.find ctx.target_tids a with
              | Some allocated -> allocated
              | None ->
                let raw_tid = Term.tid b in
                if Core.Set.mem used raw_tid then Tid.create () else raw_tid)
          in
          Core.Hashtbl.set final_of ~key:(Term.tid b) ~data:tid;
          ());
    let rename tid =
      Base.Option.value (Core.Hashtbl.find final_of tid) ~default:tid
    in
    let inserted = ref [] in
    Base.List.iter raw ~f:(fun b ->
        let tid = rename (Term.tid b) in
        let exists =
          Core.Set.mem ctx.created tid
          || Core.Set.mem (all_block_tids ctx.old) tid
          || (match block_addr b with
              | Some a -> Core.Map.mem ctx.block_addrs (Addr.of_int64 a)
              | None -> false)
        in
        if exists then ()
        else begin
          let b = map_refs rename b in
          let b = retag ~tid b in
          let b = map_block_refs rename b in
          inserted := !inserted @ [ b ];
          ctx.created <- Core.Set.add ctx.created tid;
          (match block_addr b with
           | Some a ->
             ctx.block_addrs <-
               Core.Map.set ctx.block_addrs ~key:(Addr.of_int64 a) ~data:tid
           | None -> ())
        end);
    ctx.working <-
      Base.List.fold !inserted ~init:ctx.working ~f:(fun s b ->
          Term.append blk_t s b);
    ctx.created_blocks <- ctx.created_blocks @ !inserted
  end

let prepare ctx (cases : case list) : unit =
  let addrs =
    Base.List.filter_map cases ~f:(fun (addr, _, _) ->
        Base.Option.some_if
          (not (Core.Map.mem ctx.block_addrs (Addr.of_int64 addr)))
          addr)
    |> Base.List.dedup_and_sort ~compare:Int64.compare
  in
  Base.List.iter addrs ~f:(prepare_new_block ctx)

(* ---- Create ---- *)

let addr_bits ctx = Hike_abi.word_bits ctx.abi

let link_block ctx (b : blk term) : blk term =
  let own tid =
    Core.Set.mem (all_block_tids ctx.old) tid
    || Core.Set.mem ctx.created tid
  in
  Term.map jmp_t b ~f:(fun j ->
      match Jmp.kind j with
      | Goto (Direct l) when own l -> j
      | Goto (Direct l) ->
        Jmp.with_kind j
          (Call (Call.create ~target:(Direct (ctx.callee_tid l)) ()))
      | Call c -> (
        match Call.target c with
        | Direct l ->
          Jmp.with_kind j
            (Call (Call.with_target c (Direct (ctx.callee_tid l))))
        | Indirect _ -> j)
      | Ret _ | Goto (Indirect _) | Int _ -> j)

(* A ret instruction's indirect transfer is the canonical return.  The
   instruction itself is the proof; no state is needed. *)
let canonical_return (b : blk term) : blk term =
  let is_ret j =
    match Term.get_attr j Disasm.insn with
    | Some insn -> (
      (* BAP's x86-64 decoder names the near return RET64. *)
      match String.lowercase_ascii (Insn.name insn) with
      | "ret" | "retq" | "ret64" -> true
      | _ -> false)
    | None -> false
  in
  Term.map jmp_t b ~f:(fun j ->
      if not (is_ret j) then j
      else
        match Jmp.kind j with
        | Ret (Indirect _) | Goto (Indirect _) ->
          let r = Hike_return.create_ret ~jmp_tid:(Term.tid j) () in
          Jmp.with_cond r (Jmp.cond j)
        | Call c
          when Base.Option.is_none (Call.return c)
               && (match Call.target c with Indirect _ -> true | Direct _ -> false) ->
          let r = Hike_return.create_ret ~jmp_tid:(Term.tid j) () in
          Jmp.with_cond r (Jmp.cond j)
        | _ -> j)

let create_block ctx (b : blk term) : blk term =
  let cell = ctx.synth in
  let b = Hike_atomic.normalize_block ~addr_bits:(addr_bits ctx) b in
  (* Jump compilation stays block-local: a new block cannot rewrite a
     frozen predecessor's defs. *)
  let mini =
    Sub.create ~tid:(Term.tid ctx.old) ~name:(Sub.name ctx.old) ~blks:[ b ] ()
  in
  let synth, mini = Hike_jump.compile_sub ~synth:!cell ctx.target mini in
  cell := synth;
  let b =
    Term.enum blk_t mini
    |> Seq.find_exn ~f:(fun x -> same_tid (Term.tid x) (Term.tid b))
  in
  let b = Hike_split_mem.split_block ~synth:cell b in
  let b = Hike_coerce.coerce_block b in
  let b =
    Hike_fp.run_block ~word_bits:(Hike_abi.word_bits ctx.abi) ~synth:cell b
  in
  let b =
    Hike_rip.prepare_block ~synth:cell ~addr_bits:(addr_bits ctx)
      ~is_address:ctx.rip_address b
  in
  let b = link_block ctx b in
  let outgoing =
    ctx.abi.Hike_abi.sp
    :: (Model.sig_rets ctx.old
        |> Base.List.concat_map ~f:(fun arg ->
            Exp.free_vars (Arg.rhs arg) |> Core.Set.to_list))
  in
  let b =
    Model.prepare_block_effects ~synth:!cell ~abi:ctx.abi
      ~callee:(fun _ -> None) ~outgoing b
  in
  canonical_return b

let update_created ctx (b : blk term) : unit =
  ctx.created_blocks <-
    Base.List.map ctx.created_blocks ~f:(fun old ->
        if same_tid (Term.tid old) (Term.tid b) then b else old)

let create_pass : pass =
  { name = "create"; stage = Create;
    run = (fun ctx sub -> function
      | Block tid -> (
        match Base.List.find ctx.created_blocks ~f:(fun b ->
            same_tid (Term.tid b) tid) with
        | None -> fail_build "Create item %s has no created block" (Tid.name tid)
        | Some b ->
          let b = create_block ctx b in
          update_created ctx b;
          Term.update blk_t sub b)
      | Edge _ | Batch -> sub) }

(* A conditional goto's false edge is explicit, and a series whose every
   edge leads to one destination collapses.  No block is added. *)
let finish_created_jmps ctx : unit =
  if Base.List.is_empty ctx.created_blocks then ()
  else begin
    let mini =
      Sub.create ~tid:(Term.tid ctx.old) ~name:(Sub.name ctx.old)
        ~blks:ctx.created_blocks ()
    in
    let mini = materialize_fallthroughs mini in
    let by_tid =
      Term.enum blk_t mini
      |> Seq.fold ~init:Tid.Map.empty ~f:(fun m b ->
          Core.Map.set m ~key:(Term.tid b) ~data:b)
    in
    ctx.created_blocks <-
      Base.List.map ctx.created_blocks ~f:(fun b ->
          match Core.Map.find by_tid (Term.tid b) with
          | Some b -> b
          | None ->
            fail_build "fallthrough pass dropped created block %s"
              (Tid.name (Term.tid b)));
    (* The explicit edges and the compaction can change a block's jmp
       lanes. *)
    let outgoing =
      ctx.abi.Hike_abi.sp
      :: (Model.sig_rets ctx.old
          |> Base.List.concat_map ~f:(fun arg ->
              Exp.free_vars (Arg.rhs arg) |> Core.Set.to_list))
    in
    ctx.created_blocks <-
      Base.List.map ctx.created_blocks ~f:(fun b ->
          Model.prepare_block_effects ~synth:!(ctx.synth) ~abi:ctx.abi
            ~callee:(fun _ -> None) ~outgoing b)
  end

(* ---- Wire ---- *)

let wire_pass : pass =
  { name = "wire"; stage = Wire;
    run = (fun ctx sub -> function
      | Edge e -> ctx.edges <- e :: ctx.edges; sub
      | Block _ | Batch -> sub) }

(* ---- Finalize ---- *)

(* The complete rewrite is finalized as one SSA update against the
   pre-rewrite sub: the source's new defs/jmps, the new case blocks and the
   old targets' new phi operands all leave Finalize SSA-complete.  DCE
   stays confined to the created blocks. *)
let finalize ctx : sub term =
  let sub, woken =
    Hike_ssa.update_sub_woken ~synth:!(ctx.synth) ~target:ctx.target
      ~old:ctx.old ctx.working
  in
  let sub =
    Hike_dce.dce_blocks ~synth:!(ctx.synth) ~target:ctx.target
      ~blocks:ctx.created sub
  in
  ctx.created_blocks <-
    Base.List.map ctx.created_blocks ~f:(fun b ->
        match Term.find blk_t sub (Term.tid b) with
        | Some b -> b
        | None ->
          fail_build "DCE dropped created block %s" (Tid.name (Term.tid b)));
  ctx.woken <- woken;
  ctx.result <- Some sub;
  sub

let finalize_pass : pass =
  { name = "finalize"; stage = Finalize;
    run = (fun ctx _sub -> function
      | Batch -> finalize ctx
      | Block _ | Edge _ -> fail_build "finalize pass received a non-batch item") }

let default_passes = [ create_pass; wire_pass; finalize_pass ]

(* ---- contract checks (debug builds only) ---- *)

#ifdef VSA_DEBUG
let check_contract ~old ~result ~created =
  let result_tids = all_block_tids result in
  Core.Set.iter (all_block_tids old) ~f:(fun tid ->
      if not (Core.Set.mem result_tids tid) then
        fail_build "existing block %s was removed" (Tid.name tid));
  Core.Set.iter created ~f:(fun tid ->
      if not (Core.Set.mem result_tids tid) then
        fail_build "created block %s was removed" (Tid.name tid))
#else
let check_contract ~old:_ ~result:_ ~created:_ = ()
#endif

let direct_edges_of_block (b : blk term) : edge list =
  let src = Term.tid b in
  Term.enum jmp_t b
  |> Seq.filter_map ~f:(fun j ->
      match Jmp.kind j with
      | Goto (Direct t) | Ret (Direct t) | Int (_, t) -> Some (src, t)
      | Call c -> (
        match Call.return c with
        | Some (Direct t) -> Some (src, t)
        | Some (Indirect _) | None -> None)
      | Goto (Indirect _) | Ret (Indirect _) -> None)
  |> Seq.to_list

let dedup_edges (edges : edge list) : edge list =
  Base.List.fold edges ~init:[] ~f:(fun acc ((s, d) as e) ->
      if Base.List.exists acc ~f:(fun (s', d') ->
             Tid.equal s s' && Tid.equal d d')
      then acc
      else e :: acc)
  |> Base.List.rev

let wire_edges passes ctx sub edges =
  Base.List.fold edges ~init:sub ~f:(fun sub e ->
      Base.List.fold passes ~init:sub ~f:(fun sub pass ->
          if pass.stage = Wire then pass.run ctx sub (Edge e) else sub))

let case_dedup (cases : case list) : case list =
  Core.List.fold cases ~init:[] ~f:(fun acc ((addr, dst, _) as c) ->
      if
        Core.List.exists acc ~f:(fun (a, d, _) ->
            Int64.equal a addr && Tid.equal d dst)
      then acc
      else acc @ [ c ])

(* Post-solve: a retained jump fallback is retired only when the no-match
   condition over its arms proves its target bottom.  The arms themselves
   were materialized in the solve; this pass adds no targets. *)
let retire_jump_fallbacks ~(sol : Vsa.vsa_sol) ~(synth : Hike_synth.table)
    (sub : sub term) : sub term =
  let landmarks = Cbat_landmarks.create () in
  let traps = ref [] in
  let is_indirect_tail j =
    match Jmp.kind j with
    | Goto (Indirect _) -> true
    | Call c ->
      Option.is_none (Call.return c)
      && (match Call.target c with Indirect _ -> true | _ -> false)
    | _ -> false
  in
  let sub =
    Term.map blk_t sub ~f:(fun blk ->
        let jmps = Term.enum jmp_t blk |> Seq.to_list in
        let rec split acc = function
          | [] -> None
          | j :: js ->
            if is_indirect_tail j then Some (Base.List.rev acc, j, js)
            else split (j :: acc) js
        in
        match split [] jmps with
        | Some ([], _, _) | None -> blk
        | Some (arms, fallback, _) ->
          let cond =
            Base.List.fold arms ~init:(Jmp.cond fallback)
              ~f:(fun c j -> Bil.BinOp (Bil.AND, c, Bil.UnOp (Bil.NOT, Jmp.cond j)))
          in
          let _, post =
            Vsa.fold_block_states ~synth ~sol blk ~init:()
              ~f:(fun _ _ _ () -> ())
          in
          let env =
            Vsa.constrain_edge ~synth ~env:post ~landmarks cond
          in
          let bottom =
            match Vsa.Dispatch.indirect_target fallback with
            | None -> false
            | Some target -> (
              match Vsa.denote_imm_exp ~synth target env with
              | Ok ws -> Vsa.WordSet.is_bottom ws
              | Error _ -> false)
          in
          if not bottom then blk
          else begin
            let tid = Tid.create () in
            let trap =
              Term.set_attr
                (Blk.create ~tid ~jmps:[ Jmp.create_int 0 tid ] ())
                Model.ssa_tag ()
            in
            traps := trap :: !traps;
            Term.map jmp_t blk ~f:(fun j ->
                if Tid.equal (Term.tid j) (Term.tid fallback) then
                  Jmp.create_goto (Direct tid)
                else j)
          end)
  in
  Base.List.fold !traps ~init:sub ~f:(Term.append blk_t)

(* The builder's entry: Prepare inserts the missing case blocks, Create
   transforms them, Wire records the exact source and created-block edges,
   and Finalize runs the complete-rewrite SSA update then DCEs the created
   blocks. *)
let materialize_site ~target ~abi ~callee_tid
    ~rip_address ~claim ~synth ~block_addrs ~old ~working
    ~(cases : case list) ~(edges : edge list) : delta =
  let cases = case_dedup cases in
  let fragments =
    Base.List.fold cases ~init:Core.Int64.Map.empty ~f:(fun m (addr, _, f) ->
        if Core.Map.mem m addr then m
        else Core.Map.set m ~key:addr ~data:f)
  in
  let target_tids =
    Base.List.fold cases ~init:Core.Int64.Map.empty ~f:(fun m (addr, dst, _) ->
        match Core.Map.find m addr with
        | Some tid when Tid.equal tid dst -> m
        | Some tid ->
          fail_build "target %Lx has two tids (%s, %s)" addr
            (Tid.name tid) (Tid.name dst)
        | None -> Core.Map.set m ~key:addr ~data:dst)
  in
  let ctx =
    { target; abi; callee_tid; rip_address; claim;
      synth = ref synth; block_addrs; old; working; fragments; target_tids;
      created = Tid.Set.empty; created_blocks = []; edges = [];
      result = None; woken = Tid.Set.empty }
  in
  prepare ctx cases;
  let sub = wire_edges default_passes ctx ctx.working edges in
  let sub =
    Core.Set.fold ctx.created ~init:sub ~f:(fun sub tid ->
        Base.List.fold default_passes ~init:sub ~f:(fun sub pass ->
            if pass.stage = Create then pass.run ctx sub (Block tid) else sub))
  in
  let sub =
    Base.List.fold ctx.created_blocks ~init:sub ~f:(Term.update blk_t)
  in
  ctx.working <- sub;
  finish_created_jmps ctx;
  let sub =
    Base.List.fold ctx.created_blocks ~init:sub ~f:(Term.update blk_t)
  in
  ctx.working <- sub;
  let created_edges =
    Base.List.concat_map ctx.created_blocks ~f:direct_edges_of_block
  in
  let sub = wire_edges default_passes ctx sub created_edges in
  ctx.working <- sub;
  let sub =
    Base.List.fold default_passes ~init:sub ~f:(fun sub pass ->
        if pass.stage = Finalize then pass.run ctx sub Batch else sub)
  in
  ctx.working <- sub;
  let result =
    match ctx.result with
    | Some result -> result
    | None -> fail_build "Finalize did not produce a sub"
  in
  check_contract ~old ~result ~created:ctx.created;
  { delta_sub = result;
    delta_synth = !(ctx.synth);
    new_blocks = ctx.created;
    new_edges = dedup_edges ctx.edges;
    woken = ctx.woken }
