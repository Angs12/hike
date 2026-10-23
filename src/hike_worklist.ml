(* The callee-first discovery worklist (ADR 0027).  A function is
   explored from BAP's decode, its callees are solved before it, and its
   body is lifted, linked and solved; its summary is published once and
   never revised.  A recursive cycle is solved jointly from the
   optimistic side until no member's summary changes.  Indirect targets
   are materialized in the solve's own fan-out: there is no pause/resume
   and no post-drain growth. *)

open Bap.Std
open Bap_core_theory
module Kb = Bap_core_theory.KB
module D = Hike_decode
module S = Hike_summary
module Vsa = Cbat_vsa

(* A lifted function: [solved] is the normalized body the solve
   rewrote, with its environments and block addresses. *)
type func = {
  solved : sub term;
  envs : (Vsa.AI.t * Vsa.AI.t) Tid.Map.t;
  block_addrs : Tid.t Addr.Map.t;
  summary : S.t;
}

(* A solved entry: a lifted function, a stub that stands for an external
   symbol, or an address where nothing decodes. *)
type final = Function of func | Alias of Tid.t | Missing

(* [Open] entries are on the pause stack. *)
type status = Fresh | Open of int | Final of final

type entry = {
  addr : int64;
  tid : Tid.t;
  name : string;
  mutable status : status;
  (* The lowest stack index this entry's solve read (Tarjan's lowlink). *)
  mutable low : int;
}

(* A solve in progress: the lowest stack index it read. *)
type frame = { mutable reach : int }

(* The discovery frontier: one place records what every address is for
   the decode.  The symtab's entries are decode entries from the start; a
   discovered root becomes one when it is solved; the code words a body
   materialises and the resolved jumps are candidate roots the closure
   drains.  A jump destination is never a root of its own. *)
type origin = Symtab | Discovered

type frontier = {
  (* Every address's first decode role. *)
  seen : (int64, origin) Core.Hashtbl.t;
  (* The symtab's entries, in their own order. *)
  symtab : int64 list;
  (* Decode-root batches traverse addresses; solves keep discovery order. *)
  symtab_addresses : Core.Int64.Set.t;
  (* Decode entries: the symtab's entries, then the discovered roots. *)
  mutable roots : int64 list;
  (* Batches appended since [roots] was last materialized, newest first. *)
  mutable roots_pending : int64 list list;
  (* Code words a solve materialised, newest first. *)
  mutable found : int64 list;
  mutable found_addresses : Core.Int64.Set.t;
  (* Resolved jump destinations: never roots of their own. *)
  mutable jumps : Core.Int64.Set.t;
}

(* The first occurrence of each address, in order. *)
let first_occurrences (addrs : int64 list) : int64 list =
  let seen = Core.Hash_set.create (module Core.Int64) in
  Base.List.filter addrs ~f:(fun a -> Core.Hash_set.strict_add seen a |> Result.is_ok)

let frontier_create ~(subroutines : int64 list) : frontier =
  let symtab = first_occurrences subroutines in
  let seen = Core.Hashtbl.create (module Core.Int64) in
  let symtab_addresses =
    Base.List.fold symtab ~init:Core.Int64.Set.empty ~f:(fun addresses a ->
        Core.Hashtbl.set seen ~key:a ~data:Symtab;
        Core.Set.add addresses a)
  in
  { seen; symtab; symtab_addresses; roots = symtab; roots_pending = [];
    found = [];
    found_addresses = Core.Int64.Set.empty; jumps = Core.Int64.Set.empty }

(* Appends the addresses not yet decode entries; the first role wins, so
   a symtab entry never re-enters as a discovered root. *)
let frontier_add_roots f (addrs : int64 list) : unit =
  let fresh =
    Base.List.filter addrs ~f:(fun a -> not (Core.Hashtbl.mem f.seen a))
  in
  if not (Base.List.is_empty fresh) then begin
    Base.List.iter fresh ~f:(fun a ->
        Core.Hashtbl.set f.seen ~key:a ~data:Discovered);
    f.roots_pending <- fresh :: f.roots_pending
  end

(* The decode entries in append order; pending batches join the prefix
   once per scan. *)
let frontier_roots f : int64 list =
  (match f.roots_pending with
   | [] -> ()
   | pending ->
     f.roots <- f.roots @ Base.List.concat (Base.List.rev pending);
     f.roots_pending <- []);
  f.roots

(* Prepends the code words a solve just materialised (newest first). *)
let frontier_add_found f (ws : int64 list) : unit =
  f.found <- Base.List.rev_append ws f.found;
  f.found_addresses <-
    Base.List.fold ws ~init:f.found_addresses ~f:Core.Set.add

let frontier_set_found f (ws : int64 list) : unit =
  f.found <- ws;
  f.found_addresses <-
    Base.List.fold ws ~init:Core.Int64.Set.empty ~f:Core.Set.add

let frontier_add_jump f (w : int64) : unit =
  f.jumps <- Core.Set.add f.jumps w

(* Drains the candidate roots in discovery and address order, with
   resolved jumps and repeats removed from both views. *)
let frontier_take_found f : int64 list * int64 list =
  let words =
    Base.List.rev f.found
    |> Base.List.filter ~f:(fun w -> not (Core.Set.mem f.jumps w))
    |> first_occurrences
  in
  let addresses = Core.Set.to_list (Core.Set.diff f.found_addresses f.jumps) in
  f.found <- [];
  f.found_addresses <- Core.Int64.Set.empty;
  (words, addresses)

type t = {
  proj : Project.t;
  file : string;
  context : Hike_program_vsa.context;
  abi : Hike_abi.t;
  slot_names : string Core.Int64.Map.t;
  mutable state : Disasm.Driver.state;
  (* The synthetic vars the solves' normalization minted. *)
  mutable synth : Hike_synth.table;
  (* Target words already armed at each retained fallback jmp. *)
  dispatch_seen : (Tid.t, Cbat_word.t list) Core.Hashtbl.t;
  (* The symtab entries, discovered roots, materialised code words and
     resolved jump destinations, with each address's decode role. *)
  frontier : frontier;
  entries : (int64, entry) Core.Hashtbl.t;
  by_tid : (Tid.t, entry) Core.Hashtbl.t;
  (* External and intrinsic targets: name and summary. *)
  symbols : (Tid.t, string * S.t) Core.Hashtbl.t;
  (* Published names supply deterministic declaration order. *)
  mutable symbol_names : Tid.t Core.String.Map.t;
  (* Each lifted term tid's owner. *)
  owner : (Tid.t, int64) Core.Hashtbl.t;
  (* Whether a reached call is unresolved: every code word a body
     materialises is then a root. *)
  mutable refused : bool;
  (* Published entries, newest first. *)
  mutable order : int64 list;
  mutable next_index : int;
  mutable stack : entry list;
  tentative : (int64, S.t) Core.Hashtbl.t;
  (* Tentative summaries read, newest first. *)
  mutable reads : (entry * S.t) list;
  results : (int64, final) Core.Hashtbl.t;
}

let eval = Hike_kb.eval

let label_for_name t name =
  eval (Kb.Symbol.in_package t.file (fun () -> Theory.Label.for_name name))

let is_entry t (a : int64) : bool =
  Core.Hashtbl.mem t.entries a
  || Disasm.Driver.is_subroutine t.state (Addr.of_int64 a)

(* The one enumeration cap for dispatch targets: jumps here and calls in
   the same worklist path share it.  A larger set is TOP. *)
let dispatch_cap = 1024

(* The entry role in a decode state the caller has not installed yet; the
   discovery tables and the decode must agree during validation. *)
let is_entry_in t (state : Disasm.Driver.state) (a : int64) : bool =
  Core.Hashtbl.mem t.entries a
  || Disasm.Driver.is_subroutine state (Addr.of_int64 a)

(* The frontier's decode entries are the symtab's entries and every
   discovered root; the scan's promise must carry all of them. *)
let rescan t =
  t.state <- D.scan t.proj ~file:t.file ~roots:(frontier_roots t.frontier)

(* The frontier roots a full scan would record that [state] does not
   yet: in a code region, neither a subroutine nor rejected as data. *)
let pending_roots t state =
  Base.List.filter (frontier_roots t.frontier) ~f:(fun a ->
      let w = Addr.of_int64 a in
      D.in_code t.proj a
      && (not (Disasm.Driver.is_subroutine state w))
      && not (Disasm.Driver.is_data state w))

(* [state] with every pending frontier root decoded as a subroutine. *)
let with_pending_roots t state =
  match pending_roots t state with
  | [] -> state
  | starts ->
      D.resume ~subroutines:true t.proj ~file:t.file
        ~roots:(frontier_roots t.frontier) state ~starts

(* A resumed state stands only if no frontier root is left pending: each
   is now a subroutine or was rejected as data. *)
let settled t state = Base.List.is_empty (pending_roots t state)

(* New roots change the decode only where they and their reach lie:
   resume from every pending root as a subroutine.  A root outside the
   code regions has no effect on a scan; the resumed state stands only if
   every other root is a subroutine or was rejected as data, else the
   whole binary is scanned again. *)
let rescan_roots t =
  let resumed = with_pending_roots t t.state in
  let kept = settled t resumed in
#ifdef VSA_DEBUG
  let full = D.scan t.proj ~file:t.file ~roots:(frontier_roots t.frontier) in
  Printf.eprintf "hike-dbg-rescan: roots=%d resume=%s equal=%b subs=%b\n%!"
    (List.length (pending_roots t t.state)) (if kept then "kept" else "fallback")
    (Disasm.Driver.equal resumed full)
    (Core.Set.equal (Disasm.Driver.subroutines resumed)
       (Disasm.Driver.subroutines full));
  t.state <- (if kept then resumed else full)
#else
  if kept then t.state <- resumed else rescan t
#endif

(* ---- targets ---- *)

let entry_of t (a : int64) : entry =
  match Core.Hashtbl.find t.entries a with
  | Some e -> e
  | None ->
    let label =
      eval (Theory.Label.for_addr ~package:t.file
              (Word.to_bitvec (Addr.of_int64 a)))
    in
    let name =
      match eval (Kb.collect Theory.Label.name label) with
      | Some n -> n
      | None -> Printf.sprintf "sub_%Lx" a
    in
    let tid = label_for_name t name in
    let tid = if Core.Hashtbl.mem t.by_tid tid then eval Theory.Label.fresh else tid in
    let e = { addr = a; tid; name; status = Fresh; low = max_int } in
    Core.Hashtbl.set t.entries ~key:a ~data:e;
    Core.Hashtbl.set t.by_tid ~key:tid ~data:e;
    e

(* The loader-level name of an external label: its symbol without the
   kind suffix.  An intrinsic keeps its full name. *)
let symbol t (label_name : string) : Tid.t =
  let name =
    if Hike_abi.is_intrinsic_name label_name then label_name
    else
      match Base.String.index label_name ':' with
      | Some i -> Base.String.prefix label_name i
      | None -> label_name
  in
  let tid = label_for_name t name in
  if not (Core.Hashtbl.mem t.symbols tid) then begin
    let summary =
      if Hike_abi.is_intrinsic_name name then
        { S.unknown with
          written = Base.Option.some_if (Hike_abi.is_atomic_intrinsic_name name)
              Core.Int.Set.empty }
      else
        { S.unknown with
          returns =
            not (Base.Option.exists
                   (Hike_signatures.find t.context.signatures name)
                   ~f:(fun r -> r.Hike_signatures.noreturn)) }
    in
    Core.Hashtbl.set t.symbols ~key:tid ~data:(name, summary);
    t.symbol_names <- Core.Map.set t.symbol_names ~key:name ~data:tid
  end;
  tid

(* The target expression of an indirect transfer. *)
let indirect_target (j : jmp term) : exp option =
  match Jmp.kind j with
  | Goto (Indirect e) -> Some e
  | Call c -> (match Call.target c with Indirect e -> Some e | Direct _ -> None)
  | _ -> None

let symbol_summary t tid = snd (Core.Hashtbl.find_exn t.symbols tid)

(* A body-less import's callee: the user's record for its library and
   symbol version, when there is one, bounds the call's reads and writes. *)
let symbol_callee t name (s : S.t) : Vsa.Call_effects.callee =
  match Hike_signatures.find t.context.signatures name with
  | Some record -> Declared (s.written, record)
  | None -> Summary s.written

let final_summary t = function
  | Function f -> f.summary
  | Alias x -> symbol_summary t x
  | Missing -> S.unknown

let read_open t frame e index =
  frame.reach <- min frame.reach index;
  let s = Core.Hashtbl.find_exn t.tentative e.addr in
  t.reads <- (e, s) :: t.reads;
  s

(* ---- the pause stack ---- *)

(* An entry's summary for the solve in [frame]: final, or tentative
   while the entry is on the stack (the read joins [frame] to its
   cycle). *)
(* A block's (pre, post) when the solve reached it. *)
let reached_env envs (blk : blk term) : (Vsa.AI.t * Vsa.AI.t) option =
  match Core.Map.find envs (Term.tid blk) with
  | Some (pre, post) when not (Vsa.AI.equal pre Vsa.AI.bottom) -> Some (pre, post)
  | _ -> None

let rec summary t frame (e : entry) : S.t =
  match e.status with
  | Fresh ->
    visit t e;
    frame.reach <- min frame.reach e.low;
    summary t frame e
  | Open index -> read_open t frame e index
  | Final f -> final_summary t f

(* Tarjan's walk with iteration at the cycle head: a member's solve
   leaves it on the stack; the head re-solves the cycle until every
   tentative summary it read is current, then publishes every member. *)
and visit t (e : entry) : unit =
  let index = t.next_index in
  t.next_index <- index + 1;
  e.status <- Open index;
  t.stack <- e :: t.stack;
  if not (Core.Hashtbl.mem t.tentative e.addr) then
    Core.Hashtbl.set t.tentative ~key:e.addr ~data:S.optimistic;
  let rec iterate () =
    let frame = { reach = index } in
    let mark = t.reads in
    let result = build t frame e in
    Core.Hashtbl.set t.results ~key:e.addr ~data:result;
    Core.Hashtbl.update t.tentative e.addr ~f:(function
        | Some s -> S.join s (final_summary t result)
        | None -> final_summary t result);
    e.low <- frame.reach;
    if frame.reach >= index then
      if current t ~mark then close_cycle t e ~publish:true
      else begin
        close_cycle t e ~publish:false;
        iterate ()
      end
  in
  iterate ()

(* Whether every tentative summary read since [mark] is still the
   member's current one. *)
and current t ~mark : bool =
  let rec settled = function
    | l when l == mark -> true
    | [] -> true
    | (e, s) :: rest ->
      (match e.status with
       | Open _ -> S.equal s (Core.Hashtbl.find_exn t.tentative e.addr)
       | Fresh | Final _ -> true)
      && settled rest
  in
  settled t.reads

(* Pops the members above [head]: published with their last results, or
   reset for the head's next iteration (their tentative summaries
   stay). *)
and close_cycle t (head : entry) ~publish : unit =
  let rec pop () =
    match t.stack with
    | m :: rest when publish || m != head ->
      t.stack <- rest;
      if publish then begin
        m.status <- Final (Core.Hashtbl.find_exn t.results m.addr);
        Core.Hashtbl.remove t.tentative m.addr;
        t.order <- m.addr :: t.order
      end
      else m.status <- Fresh;
      Core.Hashtbl.remove t.results m.addr;
      if m != head then pop ()
    | _ -> ()
  in
  pop ()

(* ---- one function ---- *)

and build t frame (e : entry) : final =
  let entry = Addr.of_int64 e.addr in
  let cfg =
    D.function_cfg ~file:t.file t.state ~entry ~is_entry:(fun a ->
        is_entry t (Word.to_int64_exn a))
  in
  match D.block_at cfg entry with
  | None -> Missing
  | Some blk -> (
    match stub_symbol blk with
    | Some name -> Alias (symbol t name)
    | None -> body t frame e cfg blk)

(* A stub: an entry block whose one instruction transfers to exactly
   one external symbol (the loader binds it; decision 10). *)
and stub_symbol (blk : Block.t) : string option =
  match D.dests blk with
  | [ label ] when D.transfers_only blk -> (
    match D.dest label with
    | Symbol n when not (Hike_abi.is_intrinsic_name n) -> Some n
    | _ -> None)
  | _ -> None

(* The body's local closure: lift, solve, and the growth loop. *)
and body t frame e cfg blk : final =
  let raw =
    D.trim cfg ~entry:blk ~keep_fall:(returns t frame)
    |> D.lift ~file:t.file ~tid:e.tid ~name:e.name blk
    |> link t frame |> claim t e
  in
  let f = solve_body t frame e raw in
  frontier_add_found t.frontier (code_words t f);
  if t.refused then
    frontier_add_found t.frontier (materialised_words t f);
  Function f

(* A reached call keeps its fallthrough when one of its destinations may
   return; an unknown destination may.  [D.trim] asks in execution
   order, so each callee is solved before its fallthrough is followed. *)
and returns t frame (blk : Block.t) : bool =
  match D.dests blk with
  | [] -> true
  | labels ->
    Base.List.exists labels ~f:(fun l -> (target_summary t frame l).S.returns)

and target_summary t frame (label : Tid.t) : S.t =
  match D.dest label with
  | Code a -> summary t frame (entry_of t a)
  | Symbol n -> symbol_summary t (symbol t n)
  | Unknown -> S.unknown

(* The tid a transfer to [label] names: a solved entry's (an alias's
   symbol for a stub), or the external symbol's. *)
and callee_tid t frame (label : Tid.t) : Tid.t =
  match D.dest label with
  | Code a -> (
    let e = entry_of t a in
    ignore (summary t frame e);
    match e.status with Final (Alias x) -> x | _ -> e.tid)
  | Symbol n -> symbol t n
  | Unknown -> label

(* Program-level linking: a jump that leaves the body is a tail call,
   and every call target (a recursive call's included) names its
   callee. *)
and link t frame (sub : sub term) : sub term =
  let own =
    Term.enum blk_t sub |> Seq.map ~f:Term.tid |> Seq.to_list
    |> Core.Set.of_list (module Tid)
  in
  let tail target = Call (Call.create ~target ()) in
  Term.map blk_t sub ~f:(fun blk ->
      Term.map jmp_t blk ~f:(fun j ->
          match Jmp.kind j with
          | Goto (Direct l) when Core.Set.mem own l -> j
          | Goto (Direct l) -> Jmp.with_kind j (tail (Direct (callee_tid t frame l)))
          | Goto (Indirect e) -> Jmp.with_kind j (tail (Indirect e))
          | Call c -> (
            match Call.target c with
            | Direct l -> Jmp.with_kind j (Call (Call.with_target c (Direct (callee_tid t frame l))))
            | Indirect _ -> j)
          | Ret _ | Int _ -> j))

(* Every term is owned by one function.  The lift reuses an
   instruction's term tids wherever it is lifted, so a block holding a
   term another function's body owns is copied with fresh tids (the
   overlap of decision 7). *)
and claim t (e : entry) (sub : sub term) : sub term =
  let terms b =
    Term.tid b
    :: (Seq.to_list (Seq.map (Term.enum phi_t b) ~f:Term.tid)
        @ Seq.to_list (Seq.map (Term.enum def_t b) ~f:Term.tid)
        @ Seq.to_list (Seq.map (Term.enum jmp_t b) ~f:Term.tid))
  in
  let foreign b =
    Base.List.exists (terms b) ~f:(fun tid ->
        match Core.Hashtbl.find t.owner tid with
        | Some a -> not (Int64.equal a e.addr)
        | None -> false)
  in
  let fresh x = Term.with_attrs (Term.clone x) (Term.attrs x) in
  let copy b =
    fresh b |> Term.map phi_t ~f:fresh |> Term.map def_t ~f:fresh |> Term.map jmp_t ~f:fresh
  in
  let copies =
    Term.enum blk_t sub |> Seq.filter ~f:foreign
    |> Seq.map ~f:(fun b -> (Term.tid b, copy b))
    |> Seq.to_list |> Core.Map.of_alist_exn (module Tid)
  in
  let rename tid =
    Base.Option.value_map (Core.Map.find copies tid) ~default:tid ~f:Term.tid
  in
  let label = Label.change ~direct:rename in
  let relink j =
    Jmp.with_kind j
      (match Jmp.kind j with
       | Goto l -> Goto (label l)
       | Ret l -> Ret (label l)
       | Int (n, r) -> Int (n, rename r)
       | Call c -> (
         match Call.return c with
         | Some r -> Call (Call.with_return c (label r))
         | None -> Call c))
  in
  let sub =
    Term.map blk_t sub ~f:(fun b ->
        let b = Base.Option.value (Core.Map.find copies (Term.tid b)) ~default:b in
        Term.map jmp_t b ~f:relink)
  in
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun b ->
      Base.List.iter (terms b) ~f:(fun tid ->
          Core.Hashtbl.set t.owner ~key:tid ~data:e.addr));
  sub

(* ---- the solve/grow loop ---- *)

and block_addrs_of (sub : sub term) : Tid.t Addr.Map.t =
  Term.enum blk_t sub
  |> Seq.fold ~init:Addr.Map.empty ~f:(fun m b ->
      match Term.get_attr b address with
      | None -> m
      | Some a ->
        (match Core.Map.find m a with
         | Some tid when Tid.equal tid (Term.tid b) -> m
         | Some tid ->
           failwith
             (Printf.sprintf
                "hike-grow: two blocks at address %s (%s, %s)"
                (Addr.to_string a) (Tid.name tid) (Tid.name (Term.tid b)))
         | None -> Core.Map.set m ~key:a ~data:(Term.tid b)))

and lookup_addr t (a : int64) : Tid.t option =
  if is_entry t a then Some (entry_of t a).tid else None

(* An indirect call target in a code region is a function entry even when
   no symbol or earlier transfer named it.  The VSA calls [callee] on this
   entry and recursively solves it at the call site. *)
and lookup_call_target t (a : int64) : Tid.t option =
  if is_entry t a || D.in_code t.proj a then Some (entry_of t a).tid
  else None

(* Decode the resolved addresses so the target's body is reachable.
   [lift_target] owns the block assertion: the driver cannot record a
   non-entry case target as a block without also making it a subroutine. *)
and preview_decoded t (addrs : int64 list) : Disasm.Driver.state option =
  if Base.List.is_empty addrs then Some t.state
  else begin
    let starts = Base.List.dedup_and_sort addrs ~compare:Int64.compare in
    let resumed =
      D.resume t.proj ~file:t.file ~roots:(frontier_roots t.frontier)
        t.state ~starts
      |> with_pending_roots t
    in
    Base.Option.some_if (settled t resumed) resumed
  end

(* The resolved target's own decoded body, rooted at the target.  The
   worklist-only decode state stays here; the runner sees a closure. *)
and lift_target_in t frame (state : Disasm.Driver.state) (e : entry)
    (addr : int64) : sub term option =
  let entry = Addr.of_int64 addr in
  let cfg =
    D.function_cfg ~file:t.file state ~entry ~is_entry:(fun a ->
        is_entry_in t state (Word.to_int64_exn a))
  in
  match D.block_at cfg entry with
  | None -> None
  | Some blk ->
    let cfg = D.trim cfg ~entry:blk ~keep_fall:(returns t frame) in
    (try Some (D.lift ~file:t.file ~tid:e.tid ~name:e.name blk cfg)
     with _ -> None)

(* The exact direct block edges of one block's transfers: a goto/return
   names its successor, a call's return is the continuation, and a trap
   names its own target. *)
and direct_block_edges (b : blk term) : (Tid.t * Tid.t) list =
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

(* The site materializer for an indirect jump or call: enumerate the
   target set from the source post-state, validate every word and every
   target without mutating anything, then commit discovery/lifting and
   return the sub view VSA installs.  A rejected set returns [None] and
   leaves the decode, sub, frontier and entries untouched. *)
and materialize_dispatch t frame (e : entry) : Hike_vsa.materialize_transfer =
 fun ~state ~source ~blk ~jmp ~env ->
  let target_kind =
    match Jmp.kind jmp with
    | Goto (Indirect _) -> Some `Jump
    | Call c -> (
      match Call.target c with
      | Indirect _ when Option.is_some (Call.return c) -> Some `Call
      | Indirect _ -> Some `Jump
      | Direct _ -> None)
    | _ -> None
  in
  match target_kind with
  | None -> None
  | Some kind -> begin
    let sub = Vsa.state_sub state in
    let module_addr a =
      Bil.Var
        (Hike_synth.record
           (Vsa.state_ctx state).Cbat_vsa.Runctx.rc_synth
           (Hike_synth.mint_module_addr ~addr_bits:(Hike_abi.word_bits t.abi) a))
    in
    let sol = Vsa.state_sol state in
    let synth = Vsa.state_synth state in
    let block_addrs = block_addrs_of sub in
    let rip_address a =
      is_entry t a
      || Base.List.exists t.context.data_spans ~f:(fun span ->
             Int64.unsigned_compare span.Hike_sections.ds_lo a <= 0
             && Int64.unsigned_compare a span.Hike_sections.ds_hi <= 0)
    in
    let last_defs = Vsa.last_defs blk in
    let index = Hike_transfer.index_of_sub sub in
    let retaddr =
      Hike_cfg_complete.retaddr_defs ~abi:t.abi ~synth ~sol sub
    in
    let texp =
      Hike_cfg_complete.dispatch_target ~synth ~last_defs ~retaddr ~index
        ~foreign_slots:t.context.linker_slots jmp
    in
    match texp with
    | None -> None
    | Some texp -> (
      (* The graph's edge condition already carries the preceding arms'
         guards.  Its simple [target <> word] conjuncts are exactly the
         targets those arms cover; a true/absent condition covers none. *)
      let cond =
        match Core.Map.find (Vsa.Runctx.jmp_conds_of sub) source with
        | Some by_jmp -> Core.Map.find by_jmp (Term.tid jmp)
        | None -> None
      in
      Hike_diag.debug ~tag:"hike-dbg-cond" (fun () ->
          Printf.sprintf "blk %s cond=%s arms=[%s]"
            (Tid.name source)
            (match cond with None -> "none" | Some c -> Exp.to_string c)
            (String.concat ","
               (Term.enum jmp_t blk
                |> Seq.filter_map ~f:(fun j ->
                       match Jmp.kind j with
                       | Call c -> (
                           match Call.target c with
                           | Indirect _ -> Some "indirect"
                           | Direct t ->
                             Some
                               (Printf.sprintf "%s if %s" (Tid.name t)
                                  (Exp.to_string (Jmp.cond j))))
                       | _ -> None)
                |> Seq.to_list)));
      let pre = Graphlib.Std.Solution.get sol source in
      let denote ~blk ?def exp =
        Vsa.solve_denote ~synth ~pre ~blk ?def exp
      in
      let _, post =
        Vsa.fold_block_states ~synth ~sol blk ~init:()
          ~f:(fun _ _ _ () -> ())
      in
      let post_raw = post in
      let post =
        match cond with
        | Some c when not (Hike_stack_model.is_true_cond c) ->
          Vsa.constrain_edge ~synth ~env:post
            ~landmarks:(Vsa.state_ctx state).Cbat_vsa.Runctx.rc_landmarks c
        | _ -> post
      in
      Hike_diag.debug ~tag:"hike-dbg-rawref" (fun () ->
          let show = function
            | Ok ws ->
              let s = Format.asprintf "%a" Vsa.WordSet.pp ws in
              if String.length s > 300 then Base.String.prefix s 300 else s
            | Error _ -> "error"
          in
          let target =
            match texp with
            | Bil.Var v -> (
                match Core.Map.find last_defs v with
                | None -> "no-def"
                | Some d -> Exp.to_string (Def.rhs d))
            | _ -> "non-var"
          in
          let rax_defs =
            match texp with
            | Bil.Var v ->
              let defs =
                Term.enum def_t blk
                |> Seq.filter ~f:(fun d ->
                       String.equal (Var.name (Var.base (Def.lhs d))) "RAX")
                |> Seq.map ~f:(fun d ->
                       Printf.sprintf "%s:=%s" (Var.name (Def.lhs d))
                         (Exp.to_string (Def.rhs d)))
                |> Seq.to_list
              in
              let phis =
                Term.enum phi_t blk
                |> Seq.filter ~f:(fun p ->
                       String.equal (Var.name (Var.base (Phi.lhs p))) "RAX")
                |> Seq.map ~f:(fun p ->
                       Printf.sprintf "%s<-{%s}" (Var.name (Phi.lhs p))
                         (Phi.values p
                          |> Seq.map ~f:(fun (src, e) ->
                                 Printf.sprintf "%s:%s"
                                   (Tid.name src) (Exp.to_string e))
                          |> Seq.to_list |> String.concat ";"))
                |> Seq.to_list
              in
              String.concat ";" (defs @ phis)
            | _ -> ""
          in
          let inputs =
            match texp with
            | Bil.Var v -> (
                match Core.Map.find last_defs v with
                | None -> ""
                | Some d ->
                  Exp.free_vars (Def.rhs d)
                  |> Core.Set.to_list
                  |> Base.List.map ~f:(fun v ->
                         Printf.sprintf "%s=%s" (Var.name v)
                           (match
                              Vsa.denote_imm_exp ~synth (Bil.Var v) post_raw
                            with
                            | Ok ws -> (
                                match Vsa.WordSet.enumerate ~cap:8 ws with
                                | Some ws ->
                                  String.concat "|"
                                    (Base.List.map ws ~f:Cbat_word.to_string)
                                | None -> "big")
                            | Error _ -> "err"))
                  |> String.concat "," )
            | _ -> ""
          in
          let preds =
            let g = Sub.to_graph (Vsa.state_sub state) in
            Graphs.Tid.Node.preds (Term.tid blk) g
            |> Seq.filter_map ~f:(fun tid ->
                   match Term.find blk_t (Vsa.state_sub state) tid with
                   | None -> None
                   | Some p ->
                     let defs =
                       Term.enum def_t p
                       |> Seq.filter ~f:(fun d ->
                              String.equal (Var.name (Var.base (Def.lhs d)))
                                "RAX")
                       |> Seq.map ~f:(fun d ->
                              Printf.sprintf "%s:=%s"
                                (Var.name (Def.lhs d))
                                (Exp.to_string (Def.rhs d)))
                       |> Seq.to_list
                     in
                     let phis =
                       Term.enum phi_t p
                       |> Seq.filter ~f:(fun phi ->
                              String.equal (Var.name (Var.base (Phi.lhs phi)))
                                "RAX")
                       |> Seq.map ~f:(fun phi ->
                              Printf.sprintf "%s<-%s"
                                (Var.name (Phi.lhs phi))
                                (Phi.values phi
                                 |> Seq.map ~f:(fun (s, e) ->
                                        Printf.sprintf "%s:%s" (Tid.name s)
                                          (Exp.to_string e))
                                 |> Seq.to_list |> String.concat ";"))
                       |> Seq.to_list
                     in
                     Some
                       (Printf.sprintf "%s{%s}" (Tid.name tid)
                          (String.concat ";" (defs @ phis))))
            |> Seq.to_list |> String.concat ","
          in
          Printf.sprintf
            "raw=[%s] refined=[%s] target=%s rax_defs=[%s] preds=[%s] inputs=[%s]"
            (show (Vsa.denote_imm_exp ~synth texp post_raw))
            (show (Vsa.denote_imm_exp ~synth texp post))
            target rax_defs preds inputs);
      let words =
        match Vsa.denote_exp_at ~synth ~post ~pre ~blk texp with
        | Ok ws when Vsa.WordSet.is_bottom ws -> Some []
        | Ok ws
          when not (Vsa.WordSet.is_top ws)
               && not (Vsa.WordSet.is_infinite ws) ->
          Vsa.WordSet.enumerate ~cap:dispatch_cap ws
        | Ok _ -> None
        | Error _ -> None
      in
      Hike_diag.debug ~tag:"hike-dbg-refined" (fun () ->
          Printf.sprintf "blk %s texp=%s words=[%s]" (Tid.name source)
            (Exp.to_string texp)
            (match words with
             | None -> "none"
             | Some ws ->
               String.concat ","
                 (Base.List.map ws ~f:Cbat_word.to_string)));
      match words with
      | None -> None
      | Some [] ->
        (* Every target this fallback could name is already covered by
           the arms.  Keep the block compilable and emit the no-match as
           a trap instead of an indirect transfer. *)
        let source_blk = Term.find_exn blk_t sub source in
        let trap_tid = Tid.create () in
        let trap =
          Blk.create ~tid:trap_tid
            ~jmps:[ Jmp.create_int 0 trap_tid ] ()
        in
        let fallback = Jmp.with_kind jmp (Goto (Direct trap_tid)) in
        let rewritten =
          Term.concat_map jmp_t source_blk ~f:(fun j ->
              if Tid.equal (Term.tid j) (Term.tid jmp) then [ fallback ]
              else [ j ])
        in
        let working =
          Term.append blk_t (Term.update blk_t sub rewritten) trap
        in
        let synth =
          Hike_synth.union (Vsa.state_synth state) t.synth
        in
        let delta =
          Hike_cfg_complete.materialize_site
            ~target:t.context.target ~abi:t.abi
            ~callee_tid:(fun tid -> callee_tid t frame tid)
            ~rip_address ~claim:(claim t e) ~synth ~block_addrs
            ~old:sub ~working ~cases:[]
            ~edges:(direct_block_edges rewritten)
        in
        let built_synth = delta.Hike_cfg_complete.delta_synth in
        if not (Base.phys_equal built_synth (Vsa.state_synth state)) then
          (Vsa.state_ctx state).Cbat_vsa.Runctx.rc_synth := built_synth;
        Some
          { Vsa.Dispatch.base = None; targets = [];
            sub = delta.Hike_cfg_complete.delta_sub; module_addr }
      | Some words -> (
        match
          Base.Option.all
            (Base.List.map words ~f:Cbat_word.to_int64_opt)
        with
        | None -> None
        | Some addrs ->
          if not (Base.List.for_all addrs ~f:(D.in_code t.proj)) then None
          else begin
            let starts =
              Base.List.dedup_and_sort addrs ~compare:Int64.compare
            in
            match preview_decoded t starts with
            | None -> None
            | Some decoded ->
              let is_entry_at a = is_entry_in t decoded a in
              let lifted =
                Base.List.map addrs ~f:(fun a ->
                    (a, lift_target_in t frame decoded e a))
              in
              if Base.List.exists lifted ~f:(fun (_, f) -> Option.is_none f)
              then None
              else begin
                (* One construction path for both wrappers: the wrapper
                   decides discovery and the arm kind; the rewrite and
                   finalization are shared. *)
                let commit ~(dkind : Vsa.Dispatch.arm_kind) ~targets ~base
                    ~pre_sub ~cases ~is_intra ~synth =
                  let source_blk = Term.find_exn blk_t pre_sub source in
                  let false_target =
                    if Hike_stack_model.is_true_cond (Jmp.cond jmp) then None
                    else Hike_cfg_complete.term_follower sub source
                  in
                  let rewritten, trap =
                    Vsa.Dispatch.rewrite_source
                      { Vsa.Dispatch.base; targets; sub = pre_sub; module_addr }
                      ~kind:dkind ~blk:source_blk ~jmp ~is_intra ~false_target
                  in
                  (* The rewrite minted the case words' address synths. *)
                  let synth = Hike_synth.union synth (Vsa.state_synth state) in
                  let working = Term.update blk_t pre_sub rewritten in
                  let working =
                    match trap with
                    | Some b -> Term.append blk_t working b
                    | None -> working
                  in
                  let delta =
                    Hike_cfg_complete.materialize_site
                      ~target:t.context.target ~abi:t.abi
                      ~callee_tid:(fun tid -> callee_tid t frame tid)
                      ~rip_address ~claim:(claim t e) ~synth ~block_addrs
                      ~old:sub ~working ~cases
                      ~edges:(direct_block_edges rewritten)
                  in
                  Hike_diag.debug ~tag:"hike-dbg-install" (fun () ->
                      let count sub =
                        let b = Term.find_exn blk_t sub source in
                        Term.enum jmp_t b |> Seq.length
                      in
                      Printf.sprintf
                        "source=%s rewritten_jmps=%d delta_jmps=%d"
                        (Tid.name source)
                        (Term.enum jmp_t rewritten |> Seq.length)
                        (count delta.Hike_cfg_complete.delta_sub));
                  let built_synth = delta.Hike_cfg_complete.delta_synth in
                  if not (Base.phys_equal built_synth (Vsa.state_synth state)) then
                    (Vsa.state_ctx state).Cbat_vsa.Runctx.rc_synth :=
                      built_synth;
                  Some
                    { Vsa.Dispatch.base; targets;
                      sub = delta.Hike_cfg_complete.delta_sub; module_addr }
                in
                match kind with
                | `Call ->
                  (* ---- validation passed; commit ---- *)
                  t.state <- decoded;
                  frontier_add_roots t.frontier addrs;
                  let synth = Vsa.state_synth state in
                  let targets =
                    Base.List.map2_exn words addrs ~f:(fun w a ->
                        let en = entry_of t a in
                        ignore (summary t frame en);
                        let tid =
                          match en.status with
                          | Final (Alias x) -> x
                          | Fresh | Open _ | Final _ -> en.tid
                        in
                        (w, tid))
                  in
                  let synth =
                    if Base.phys_equal t.synth synth then synth
                    else begin
                      let merged = Hike_synth.union synth t.synth in
                      (Vsa.state_ctx state).Cbat_vsa.Runctx.rc_synth := merged;
                      merged
                    end
                  in
                  commit ~dkind:Vsa.Dispatch.Call ~targets ~base:None
                    ~pre_sub:sub ~cases:[] ~is_intra:(fun _ -> false) ~synth
                | `Jump ->
                (* ---- validation passed; commit ---- *)
                t.state <- decoded;
                let site =
                  match Term.get_attr jmp address with
                  | Some a -> Some (Word.to_int64_exn a)
                  | None ->
                    Base.Option.map (Term.get_attr blk address)
                      ~f:Word.to_int64_exn
                in
                Base.Option.iter site ~f:(fun site ->
                    Base.List.iter addrs ~f:(fun a ->
                        D.provide_dest ~file:t.file ~site a));
                let entry_addrs =
                  Base.List.filter addrs ~f:is_entry_at
                in
                let case_addrs =
                  Base.List.filter addrs ~f:(fun a ->
                      not (is_entry_at a))
                in
                Base.List.iter case_addrs ~f:(frontier_add_jump t.frontier);
                Base.List.iter entry_addrs ~f:(fun a ->
                    frontier_add_roots t.frontier [ a ]);
                let fragments =
                  Base.List.fold lifted ~init:Core.Int64.Map.empty
                    ~f:(fun m (a, f) ->
                      match f with
                      | Some frag -> Core.Map.set m ~key:a ~data:frag
                      | None -> m)
                in
                let allocated = ref Core.Int64.Map.empty in
                let block_tid a =
                  match Core.Map.find block_addrs (Addr.of_int64 a) with
                  | Some tid -> tid
                  | None -> (
                    match Core.Map.find !allocated a with
                    | Some tid -> tid
                    | None ->
                      let tid = Tid.create () in
                      allocated :=
                        Core.Map.set !allocated ~key:a ~data:tid;
                      tid)
                in
                let cases =
                  Base.List.map case_addrs ~f:(fun a ->
                      (a, block_tid a, Core.Map.find_exn fragments a))
                in
                (* A function-entry target is discovered/solved once; an
                   already-Final entry is only read.  An alias arm names
                   its external symbol, like every linked call. *)
                let entry_tids =
                  Base.List.fold entry_addrs ~init:Core.Int64.Map.empty
                    ~f:(fun m a ->
                      let en = entry_of t a in
                      ignore (summary t frame en);
                      let tid =
                        match en.status with
                        | Final (Alias x) -> x
                        | _ -> en.tid
                      in
                      Core.Map.set m ~key:a ~data:tid)
                in
                let target_tid a =
                  if is_entry_at a then
                    Core.Map.find_exn entry_tids a
                  else
                    match Core.Map.find block_addrs (Addr.of_int64 a) with
                    | Some tid -> tid
                    | None -> Core.Map.find_exn !allocated a
                in
                let targets =
                  Base.List.map2_exn words addrs ~f:(fun w a ->
                      (w, target_tid a))
                in
                let synth = Vsa.state_synth state in
                (* A table base is bound at its site in the pre-rewrite
                   source; another block is frozen, so such a base falls
                   back to equality guards.  The binding is part of the
                   rewrite the builder finalizes. *)
                let base, pre_sub, synth =
                  match
                    Hike_cfg_complete.dispatch_words ~cap:dispatch_cap ~denote
                      ~block_addrs ~last_defs ~blk texp
                  with
                  | None | Some { Hike_cfg_complete.base = None; _ } ->
                    (None, sub, synth)
                  | Some { base = Some b; _ } -> (
                    match b.Hike_cfg_complete.site with
                    | None ->
                      ( Some
                          { Vsa.Dispatch.summand = b.summand;
                            values = b.values },
                        sub, synth )
                    | Some f
                      when Tid.equal (Term.tid f.blk) source -> (
                      match Type.infer b.summand with
                      | Ok (Type.Imm bits) ->
                        let src_blk = Term.find_exn blk_t sub source in
                        let at_present =
                          match f.at with
                          | None -> true
                          | Some d ->
                            Option.is_some
                              (Term.find def_t src_blk (Term.tid d))
                        in
                        if not at_present then (None, sub, synth)
                        else begin
                          let cell = ref synth in
                          let v =
                            Hike_synth.record cell
                              (Hike_synth.mint_fresh ~bits
                                 Hike_synth.Binding)
                          in
                          let d = Def.create v b.summand in
                          let src_blk =
                            match f.at with
                            | Some at ->
                              Term.prepend def_t
                                ~before:(Term.tid at) src_blk d
                            | None -> Term.append def_t src_blk d
                          in
                          ( Some
                              { Vsa.Dispatch.summand = Bil.Var v;
                                values = b.values },
                            Term.update blk_t sub src_blk, !cell )
                        end
                      | Ok _ | Error _ -> (None, sub, synth))
                    | Some _ -> (None, sub, synth))
                in
                let case_tids =
                  Core.Set.of_list (module Tid)
                    (Base.List.map cases ~f:(fun (_, tid, _) -> tid))
                in
                commit ~dkind:Vsa.Dispatch.Jump ~targets ~base ~pre_sub
                  ~cases
                  ~is_intra:(fun tid -> Core.Set.mem case_tids tid) ~synth
              end
          end))
    end

(* One solve, resuming through blocked callees until the caller's
   summaries are final.  A persisted state continues the same solve. *)
and solve_to_fix ?state t frame e ~sub ~resolved ~synth ~seed ~wake :
    Hike_vsa.solution =
  let ctx = t.context in
  let lookup a = lookup_call_target t a in
  let known tid =
    match Core.Hashtbl.find t.symbols tid, Core.Hashtbl.find t.by_tid tid with
    | Some (name, s), _ -> `Symbol (name, s)
    | None, Some e -> `Entry e
    | None, None -> `Unknown
  in
  let callee tid : Vsa.Call_effects.callee =
    match known tid with
    | `Symbol (name, s) -> symbol_callee t name s
    | `Unknown -> Summary None
    | `Entry e -> (
      match e.status with
      | Fresh -> Summary (summary t frame e).written
      | Open index -> Summary (read_open t frame e index).written
      | Final f -> Summary (final_summary t f).written)
  in
  let images = ctx.images and foreign_slots = ctx.linker_slots in
  let (Hike_vsa.Solved s) =
    Hike_vsa.solve ?state ~materialize_transfer:(materialize_dispatch t frame e)
      ctx.target ~lookup ~images ~callee ~foreign_slots ~sub ~resolved ~synth
      ~seed ~wake
  in
  s

(* The initial body's construction: normalize, SSA, DCE, explicit
   fallthroughs from the pre-install term order, one solve with site
   materialization, then the canonical return/prune pass.  That pass is
   term-only, so the solution stands and nothing is re-solved. *)
and solve_initial t frame (e : entry) (raw : sub term) :
    sub term * (Vsa.AI.t * Vsa.AI.t) Tid.Map.t * Hike_vsa.solution *
    Tid.t Addr.Map.t * Hike_synth.table =
  let ctx = t.context in
  let abi = t.abi in
  let sub, synth =
    Hike_program_vsa.prepare_function ctx ~synth:t.synth
      ~is_entry:(is_entry t) raw
  in
  let sub, synth =
    let cell = ref synth in
    let sub = Hike_vsa.normalize_round ~synth:cell sub in
    (sub, !cell)
  in
  (* The fallthrough pass reads the pre-install term order: an installed
     source's guard chain is not an ordinary conditional jmp. *)
  let sub = Hike_cfg_complete.materialize_fallthroughs sub in
  let s =
    solve_to_fix t frame e ~sub ~resolved:Tid.Map.empty ~synth ~seed:None
      ~wake:Tid.Set.empty
  in
  (* A site materialization installs arms and new blocks in the same
     solve; the completion pass reads that view, not the pre-solve one. *)
  let solved = s.Hike_vsa.sub in
  let sol = s.Hike_vsa.sol and synth = s.Hike_vsa.synth in
  let solved = Hike_cfg_complete.retire_jump_fallbacks ~sol ~synth solved in
  let block_addrs = block_addrs_of solved in
  let retaddr = Hike_cfg_complete.retaddr_defs ~abi ~synth ~sol solved in
  let materialized =
    Hike_cfg_complete.materialize ~sol ~synth ~retaddr
      ~block_addrs ~foreign_slots:ctx.linker_slots solved
  in
  let materialized, synth =
    let cell = ref synth in
    let m = Hike_vsa.normalize_round ~synth:cell materialized in
    (m, !cell)
  in
  (* The completion pass rewrites terminal jmps and removes unreachable
     blocks; defs, phis and their SSA names are untouched, so the warm
     solution still keys the surviving blocks.  No re-solve. *)
  let sub' = materialized in
  let sol = s.Hike_vsa.sol in
  let sub', synth =
    let cell = ref synth in
    let sub' = Hike_vsa.normalize_round ~synth:cell sub' in
    (sub', !cell)
  in
  let envs, stamped =
    Hike_vsa.stamp ~images:ctx.images ~synth ~sol sub'
  in
  (* The initial SSA/materialization normalized the terms; refresh one
     facts pass before the freeze, keeping the same run context. *)
  let state =
    Vsa.state_with_sub s.Hike_vsa.state stamped
    |> fun st -> Vsa.state_with_synth st synth
  in
  (stamped, envs,
   { Hike_vsa.sol; synth; state; sub = stamped },
   block_addrs_of stamped, synth)

(* The post-initial solve: the same persisted state, one solve entry.
   Site materialization is the only growth trigger; the worklist owns it
   through [materialize_dispatch]. *)
and solve_body t frame (e : entry) (raw : sub term) : func =
  let sub, envs, initial, _block_addrs, _synth =
    solve_initial t frame e raw
  in
  let abi = t.abi in
  let lookup a = lookup_call_target t a in
  let known tid =
    match Core.Hashtbl.find t.symbols tid, Core.Hashtbl.find t.by_tid tid with
    | Some (name, s), _ -> `Symbol (name, s)
    | None, Some en -> `Entry en
    | None, None -> `Unknown
  in
  let callee tid : Vsa.Call_effects.callee =
    match known tid with
    | `Symbol (name, s) -> symbol_callee t name s
    | `Unknown -> Summary None
    | `Entry en -> (
      match en.status with
      | Fresh -> Summary (summary t frame en).written
      | Open index -> Summary (read_open t frame en index).written
      | Final f -> Summary (final_summary t f).written)
  in
  let images = t.context.images in
  let foreign_slots = t.context.linker_slots in
  let (Hike_vsa.Solved solved) =
    Hike_vsa.solve ~state:initial.Hike_vsa.state
      ~materialize_transfer:(materialize_dispatch t frame e)
      t.context.target ~lookup ~images ~callee ~foreign_slots ~sub
      ~resolved:Tid.Map.empty ~synth:initial.Hike_vsa.synth
      ~seed:(Some initial.Hike_vsa.sol) ~wake:Tid.Set.empty
  in
  let envs, stamped =
    Hike_vsa.stamp ~images:t.context.images ~synth:solved.Hike_vsa.synth
      ~sol:solved.Hike_vsa.sol solved.Hike_vsa.sub
  in
  let summary =
    S.of_solved ~abi ~synth:solved.Hike_vsa.synth
      ~callee:(fun tid ->
          match Core.Hashtbl.find t.symbols tid,
                Core.Hashtbl.find t.by_tid tid with
          | Some (_, s), _ -> Some s
          | _, Some en -> Some (summary t frame en)
          | _ -> None)
      ~slot:(fun a ->
          Base.Option.map (Core.Map.find t.slot_names a) ~f:(fun n ->
              symbol_summary t (symbol t n)))
      ~lookup:(lookup_addr t) ~foreign_slots:t.context.linker_slots
      ~block_addrs:(block_addrs_of stamped) ~envs stamped
  in
  t.synth <- Hike_synth.union t.synth solved.Hike_vsa.synth;
  let seen = Tid.Table.create () in
  Term.enum blk_t stamped
  |> Seq.iter ~f:(fun b ->
      let tid = Term.tid b in
      let n = Option.value (Core.Hashtbl.find seen tid) ~default:0 in
      Core.Hashtbl.set seen ~key:tid ~data:(n + 1));
  let dups =
    Core.Hashtbl.fold seen ~init:[] ~f:(fun ~key ~data acc ->
        if data > 1 then Tid.name key :: acc else acc)
  in
  if not (Base.List.is_empty dups) then
    failwith
      (Printf.sprintf "hike-dispatch: duplicate block tids in %s: %s"
         (Sub.name stamped) (String.concat "," dups));
  ({ solved = stamped; envs; block_addrs = block_addrs_of stamped;
     summary })

(* ---- facts from a solved body ---- *)

(* The words of a bounded denotation; [None] when it is too wide. *)
and bounded_words (ws : Vsa.WordSet.t) : int64 list option =
  if Vsa.WordSet.is_top ws || Vsa.WordSet.is_bottom ws || Vsa.WordSet.is_infinite ws
  then None
  else
    Base.Option.map (Vsa.WordSet.enumerate ~cap:64 ws) ~f:(fun words ->
        Base.List.filter_map words ~f:Cbat_word.to_int64_opt)

(* The words of a bounded value with the text origin. *)
and text_words (ws : Vsa.WordSet.t) : int64 list =
  match Vsa.WordSet.origin ws with
  | Some (Vsa.WordSet.Origin.Rip Hike_section.Text) ->
    Base.Option.value (bounded_words ws) ~default:[]
  | _ -> []

(* The code words that leave the body: every word of a bounded
   value with the text origin in an integer argument register at a
   call, or in an integer return register at a return.  A code value the
   body only calls is a resolved destination; one it only uses as an
   address names no function; one stored and reloaded keeps its origin
   through memory. *)
and code_words t (f : func) : int64 list =
  let wb = Hike_abi.word_bits t.abi in
  let ints regs =
    Base.List.filter regs ~f:(fun v -> Type.equal (Var.typ v) (Type.Imm wb)) in
  let args = ints t.abi.Hike_abi.int_param_regs in
  let rets = ints t.abi.Hike_abi.return_regs in
  let text ~blk post v =
    match Vsa.denote_exp_at ~synth:t.synth ~pre:post ~post ~blk
            (Bil.Var (Hike_stack_model.version_at_end blk v)) with
    | Ok ws -> text_words ws
    | Error _ -> []
  in
  Term.enum blk_t f.solved |> Seq.to_list
  |> Base.List.concat_map ~f:(fun blk ->
      match reached_env f.envs blk with
      | Some (pre, post) ->
        let jmps = Term.enum jmp_t blk |> Seq.to_list in
        let calls =
          Base.List.exists jmps ~f:(fun j ->
              match Jmp.kind j with
              | Call _ -> not (Hike_return.is_jmp j)
              | _ -> false)
        in
        let returns = Base.List.exists jmps ~f:Hike_return.is_jmp in
        (if calls then Base.List.concat_map args ~f:(text ~blk post) else [])
        @ (if returns then Base.List.concat_map rets ~f:(text ~blk post) else [])
      | _ -> [])

(* The code words a body materialises, for a call no denotation
   resolves: every word with the text origin of a bounded value a def
   computes or a store writes (a wide store word by word, each keeping
   its lane's origin).  A call instruction's own defs push its return
   address, which names no function. *)
and materialised_words t (f : func) : int64 list =
  let wb = Hike_abi.word_bits t.abi in
  let text ~pre ~post ~blk ~def e =
    match Vsa.denote_exp_at ~synth:t.synth ~pre ~post ~blk ~def e with
    | Ok ws -> text_words ws
    | Error _ -> []
  in
  Term.enum blk_t f.solved |> Seq.to_list
  |> Base.List.concat_map ~f:(fun blk ->
      match reached_env f.envs blk with
      | Some (pre, post) ->
        Term.enum def_t blk |> Seq.to_list
        |> Base.List.filter ~f:(fun d ->
            match Term.get_attr d Disasm.insn with
            | Some insn -> not (Insn.is Insn.call insn)
            | None -> true)
        |> Base.List.concat_map ~f:(fun d ->
            let values =
              match Hike_stack_model.store_data_of_rhs (Def.rhs d) with
              | None -> [ Def.rhs d ]
              | Some data -> (
                match Hike_stack_model.addr_of_rhs (Def.rhs d) with
                | Some (_, size) when Size.in_bits size > wb ->
                  Base.List.init (Size.in_bits size / wb) ~f:(fun k ->
                      Bil.extract ~hi:(((k + 1) * wb) - 1) ~lo:(k * wb) data)
                | _ -> [ data ])
            in
            Base.List.concat_map values ~f:(text ~pre ~post ~blk ~def:d))
      | _ -> [])

(* ---- the program ---- *)

let create ~signatures proj ~file ~state ~subroutines : t =
  let context = Hike_program_vsa.prepare ~signatures proj in
  {
    proj;
    file;
    context;
    abi = Hike_abi.of_target context.target;
    slot_names =
      Core.Map.of_alist_reduce (module Core.Int64) ~f:(fun a _ -> a)
        (Hike_image.external_references proj);
    state;
    synth = Hike_synth.empty;
    dispatch_seen = Core.Hashtbl.create (module Tid);
    frontier = frontier_create ~subroutines;
    entries = Core.Hashtbl.create (module Core.Int64);
    by_tid = Core.Hashtbl.create (module Tid);
    symbols = Core.Hashtbl.create (module Tid);
    symbol_names = Core.String.Map.empty;
    owner = Core.Hashtbl.create (module Tid);
    refused = false;
    order = [];
    next_index = 0;
    stack = [];
    tentative = Core.Hashtbl.create (module Core.Int64);
    reads = [];
    results = Core.Hashtbl.create (module Core.Int64);
  }

(* Data-found and refusal roots lie in the executable's text: the PLT and
   the runtime's init and fini code are the loader's. *)
let in_text t (w : int64) : bool =
  match t.context.text_range with
  | Some (lo, hi) -> Int64.compare w lo >= 0 && Int64.compare w hi <= 0
  | None -> false

(* The producer's unique address traversal orders the decode batch;
   [addrs] retains discovery order for the callee-first solves. *)
let solve_roots t ~(addresses : int64 list) (addrs : int64 list) : unit =
  let fresh =
    Base.List.filter addresses ~f:(fun a -> not (is_entry t a))
  in
  if not (Base.List.is_empty fresh) then begin
    frontier_add_roots t.frontier fresh;
    t.state <- D.grow t.proj ~file:t.file ~roots:(frontier_roots t.frontier)
        ~destinations:[] t.state
  end;
  Base.List.iter addrs ~f:(fun a -> ignore (summary t { reach = max_int } (entry_of t a)))

let functions t : (int64 * func) list =
  Base.List.rev t.order
  |> Base.List.filter_map ~f:(fun a ->
      match (Core.Hashtbl.find_exn t.entries a).status with
      | Final (Function f) -> Some (a, f)
      | _ -> None)

(* The code words name functions, as BAP's subroutine facts do: a word
   inside another function's decoded bytes is still an entry, and a
   resolved jump destination is not one.  They are solved as roots until
   none is left. *)
let rec close t : unit =
  let words, addresses = frontier_take_found t.frontier in
  if not (Base.List.is_empty words) then begin
    solve_roots t ~addresses words;
    close t
  end

(* Main: the first integer argument at every call of the entry's solved
   body; one agreed address is main. *)
let main_of t (f : func) : int64 option =
  let arg0 = fst (Hike_abi.argc_argv_regs t.abi) in
  let named =
    Term.enum blk_t f.solved |> Seq.to_list
    |> Base.List.filter_map ~f:(fun blk ->
        let calls =
          Term.enum jmp_t blk
          |> Seq.exists ~f:(fun j -> match Jmp.kind j with Call _ -> true | _ -> false)
        in
        match Core.Map.find f.envs (Term.tid blk) with
        | Some (_, post) when calls -> (
          match Vsa.denote_exp_at ~synth:t.synth ~pre:post ~post ~blk
                  (Bil.Var (Hike_stack_model.version_at_end blk arg0)) with
          | Ok ws -> (match bounded_words ws with Some [ w ] -> Some w | _ -> None)
          | Error _ -> None)
        | _ -> None)
    |> Base.List.fold ~init:`Empty ~f:(fun agreed a ->
        match agreed with
        | `Empty -> `One a
        | `One b when Int64.equal a b -> agreed
        | `One _ | `Conflict -> `Conflict)
  in
  match named with
  | `One main -> Some main
  | `Empty -> None
  | `Conflict ->
    Hike_diag.warn "discover: the entry's calls name different main addresses; no main";
    None

(* Whether a reached indirect call of [f] may target a function no
   denotation names: anything but a linker slot, a return, or bounded
   words that each name a block of [f] or an entry. *)
let unresolved_call t (f : func) : bool =
  let index = Hike_transfer.index_of_sub f.solved in
  Term.enum blk_t f.solved
  |> Seq.exists ~f:(fun blk ->
      match reached_env f.envs blk with
      | Some (pre, post) ->
        Term.enum jmp_t blk
        |> Seq.exists ~f:(fun j ->
            match indirect_target j with
            | Some e when not (Hike_return.is_jmp j) -> (
              match Hike_transfer.slot_of_target ~synth:t.synth ~index e with
              | Some a when Core.Set.mem t.context.linker_slots a -> false
              | _ -> (
                match Vsa.denote_exp_at ~synth:t.synth ~pre ~post ~blk e with
                | Ok ws -> (
                  match bounded_words ws with
                  | Some words ->
                    not (Base.List.for_all words ~f:(fun w ->
                        Core.Map.mem f.block_addrs (Addr.of_int64 w) || is_entry t w))
                  | None -> true)
                | Error _ -> true))
            | _ -> false)
      | _ -> false)

type result = { program : program term; facts : Hike_kb.facts }

(* The analysis facts of the published solves: every block's
   environments, the block and entry addresses, and the entry lookup. *)
let facts t : Hike_kb.facts =
  let funcs = functions t in
  let union maps =
    Base.List.fold maps ~init:Addr.Map.empty ~f:(fun acc m ->
        Core.Map.merge_skewed acc m ~combine:(fun ~key:_ a _ -> a))
  in
  let tid_of (e : entry) =
    match e.status with Final (Alias x) -> x | _ -> e.tid
  in
  let lookup a = Base.Option.map (Core.Hashtbl.find t.entries a) ~f:tid_of in
  let sub_addrs =
    Core.Hashtbl.data t.entries
    |> Base.List.map ~f:(fun e -> (Addr.of_int64 e.addr, tid_of e))
    |> Core.Map.of_alist_reduce (module Addr) ~f:(fun a _ -> a)
  in
  let built =
    Hike_kb.build ~target:t.context.target ~lookup
      ~block_envs:(Base.List.fold funcs ~init:Tid.Map.empty ~f:(fun acc (_, f) ->
          Core.Map.merge_skewed acc f.envs ~combine:(fun ~key:_ a _ -> a)))
      ~block_addrs:(union (Base.List.map funcs ~f:(fun (_, f) -> f.block_addrs)))
  in
  let synth = Hike_synth.union built.synth t.synth in
  Hike_kb.with_synth { built with
    Hike_kb.sub_addrs;
    images = t.context.images;
    foreign_slots = t.context.linker_slots;
    signatures = t.context.signatures }
    synth

(* The worklist's program: main's closure (or, on refusal, that of
   every subroutine entry and every materialised code word) as solved
   bodies with one jump per block, plus a block-less declaration per
   external target (the emitter maps intrinsic targets itself); and the
   solves' analysis facts. *)
let run ~signatures (proj : Project.t) ~file ~state ~subroutines : result =
  let t = create ~signatures proj ~file ~state ~subroutines in
  let entry = Hike_image.entry_point proj in
  Base.Option.iter entry ~f:(fun a -> solve_roots t ~addresses:[ a ] [ a ]);
  let main =
    match Base.Option.map entry ~f:(fun a -> (Core.Hashtbl.find_exn t.entries a).status) with
    | Some (Final (Function f)) -> main_of t f
    | _ -> None
  in
  let relocated =
    let init_fini =
      Base.List.filter_map [ ".init_array"; ".fini_array" ] ~f:(fun name ->
          Hike_image.get_section_mem name proj |> Hike_image.get_section_data
          |> Base.Option.map ~f:(fun (_, lo, hi) ->
              (Word.to_int64_exn lo, Word.to_int64_exn hi)))
    in
    Hike_image.relative_values proj ~bias:(Hike_image.get_bias proj)
    |> Base.List.filter ~f:(fun (slot, _) ->
        not (Base.List.exists init_fini ~f:(fun (lo, hi) ->
            Int64.compare slot lo >= 0 && Int64.compare slot hi <= 0)))
    |> Base.List.map ~f:snd
  in
  frontier_add_found t.frontier relocated;
  Base.Option.iter main ~f:(fun a -> solve_roots t ~addresses:[ a ] [ a ]);
  close t;
  if Base.Option.is_none main
  || Base.List.exists (functions t) ~f:(fun (_, f) -> unresolved_call t f)
  then begin
    if Base.Option.is_none main then
      Hike_diag.warn "discover: no main; every BAP subroutine in the text is a root";
    t.refused <- true;
    frontier_set_found t.frontier
      (Base.List.concat_map (functions t) ~f:(fun (_, f) -> materialised_words t f));
    solve_roots t
      ~addresses:(Core.Set.to_list
          (Core.Set.filter t.frontier.symtab_addresses ~f:(in_text t)))
      (Base.List.filter t.frontier.symtab ~f:(in_text t));
    close t
  end;
  let lifted =
    Base.List.map (functions t) ~f:(fun (a, f) ->
        let sub = Term.set_attr f.solved filename t.file in
        let sub =
          if Base.Option.is_some main && Base.Option.equal Int64.equal entry (Some a)
          then Term.set_attr sub Sub.entry_point () else sub
        in
        if Base.Option.equal Int64.equal main (Some a)
        then Term.set_attr sub Hike_stack_model.main_role () else sub)
  in
  let externals =
    Core.Map.to_alist t.symbol_names
    |> Base.List.filter_map ~f:(fun (name, tid) ->
        Base.Option.some_if (not (Hike_abi.is_intrinsic_name name))
          (Term.set_attr (Sub.create ~tid ~name ()) Term.synthetic ()))
  in
  { program =
      Base.List.fold (lifted @ externals) ~init:(Program.create ())
        ~f:(fun p s -> Term.append sub_t p s);
    facts = facts t }
