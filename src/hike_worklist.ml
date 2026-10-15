(* The callee-first discovery worklist (ADR 0027).  A function is
   explored from BAP's decode, its callees are solved before it, and its
   body is lifted, linked and solved; its summary is published once and
   never revised.  A recursive cycle is solved jointly from the
   optimistic side until no member's summary changes.  A solve that
   reaches an unsolved callee pauses and resumes once the callee is
   final. *)

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
  (* Code words a solve materialised, newest first. *)
  mutable found : int64 list;
  mutable found_addresses : Core.Int64.Set.t;
  (* Resolved jump destinations: never roots of their own. *)
  mutable jumps : Core.Int64.Set.t;
}

let frontier_create ~(subroutines : int64 list) : frontier =
  let symtab = Base.List.stable_dedup subroutines ~compare:Int64.compare in
  let seen = Core.Hashtbl.create (module Core.Int64) in
  let symtab_addresses =
    Base.List.fold symtab ~init:Core.Int64.Set.empty ~f:(fun addresses a ->
        Core.Hashtbl.set seen ~key:a ~data:Symtab;
        Core.Set.add addresses a)
  in
  { seen; symtab; symtab_addresses; roots = symtab; found = [];
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
    f.roots <- f.roots @ fresh
  end

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
    |> Base.List.stable_dedup ~compare:Int64.compare
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
  (* The symtab entries, discovered roots, materialised code words and
     resolved jump destinations, with each address's decode role. *)
  frontier : frontier;
  (* The provided destinations, by dispatch instruction. *)
  mutable dests : Core.Int64.Set.t Core.Int64.Map.t;
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

let eval (x : 'a Kb.t) : 'a =
  let v = Toplevel.var "hike-worklist" in
  Toplevel.put v x;
  Toplevel.get v

let label_for_name t name =
  eval (Kb.Symbol.in_package t.file (fun () -> Theory.Label.for_name name))

let is_entry t (a : int64) : bool =
  Core.Hashtbl.mem t.entries a
  || Disasm.Driver.is_subroutine t.state (Addr.of_int64 a)

(* The frontier's decode entries are the symtab's entries and every
   discovered root; the scan's promise must carry all of them. *)
let rescan t =
  t.state <- D.scan t.proj ~file:t.file ~roots:t.frontier.roots

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
            not (Base.List.mem t.abi.Hike_abi.noreturn_symbols name
                   ~equal:String.equal) }
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
  let rec since = function
    | l when l == mark -> []
    | [] -> []
    | r :: rest -> r :: since rest
  in
  Base.List.for_all (since t.reads) ~f:(fun (e, s) ->
      match e.status with
      | Open _ -> S.equal s (Core.Hashtbl.find_exn t.tentative e.addr)
      | Fresh | Final _ -> true)

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

(* The body's local closure: lift, solve, and while the solve resolves
   new dispatch destinations, decode them and lift again. *)
and body t frame e cfg blk : final =
  let keep_fall = walk t frame cfg blk in
  let raw =
    D.trim cfg ~entry:blk ~keep_fall
    |> D.lift ~file:t.file ~tid:e.tid ~name:e.name blk
    |> link t frame |> claim t e |> arm t
  in
  let f = solve t frame raw in
  if learn_dests t cfg f then build t frame e
  else begin
    frontier_add_found t.frontier (code_words t f);
    if t.refused then
      frontier_add_found t.frontier (materialised_words t f);
    Function f
  end

(* The callee-first walk: each reached call's destinations are solved
   before its fallthrough is followed, and the fallthrough is kept only
   when one of them may return. *)
and walk t frame cfg (entry : Block.t) : Block.t -> bool =
  let returns blk =
    match D.dests blk with
    | [] -> true
    | labels ->
      Base.List.map labels ~f:(target_summary t frame)
      |> Base.List.exists ~f:(fun (s : S.t) -> s.returns)
  in
  let rec go (seen, kept) b =
    if Core.Set.mem seen b then (seen, kept)
    else
      let fall = (not (D.is_call b)) || returns b in
      let kept = if fall then Core.Set.add kept b else kept in
      Graphs.Cfg.Node.outputs b cfg
      |> Seq.fold ~init:(Core.Set.add seen b, kept) ~f:(fun acc edge ->
          match Graphs.Cfg.Edge.label edge with
          | `Fall when not fall -> acc
          | _ -> go acc (Graphs.Cfg.Edge.dst edge))
  in
  let _, kept = go (Block.Set.empty, Block.Set.empty) entry in
  Core.Set.mem kept

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

(* Each dispatch gains one arm per destination the solves resolved. *)
and arm t (sub : sub term) : sub term =
  let dests j =
    match Term.get_attr j address with
    | None -> []
    | Some a ->
      Base.Option.value_map (Core.Map.find t.dests (Word.to_int64_exn a))
        ~default:[] ~f:Core.Set.to_list
  in
  Hike_cfg_complete.arm_dispatches ~dests sub

(* The solve, paused at each unsolved callee until it is solved. *)
and solve t frame (raw : sub term) : func =
  let ctx = t.context in
  let sub = Hike_program_vsa.prepare_function ctx ~is_entry:(is_entry t) raw in
  let block_addrs =
    Term.enum blk_t sub
    |> Seq.filter_map ~f:(fun b ->
        Base.Option.map (Term.get_attr b address) ~f:(fun a -> (a, Term.tid b)))
    |> Seq.to_list |> Core.Map.of_alist_reduce (module Addr) ~f:(fun a _ -> a)
  in
  let lookup a = if is_entry t a then Some (entry_of t a).tid else None in
  let callee tid : Vsa.Call_effects.callee =
    match Core.Hashtbl.find t.symbols tid, Core.Hashtbl.find t.by_tid tid with
    | Some (_, s), _ -> Summary s.written
    | None, None -> Summary None
    | None, Some e -> (
      match e.status with
      | Fresh -> Blocked
      | Open index -> Summary (read_open t frame e index).written
      | Final f -> Summary (final_summary t f).written)
  in
  let images = ctx.images and foreign_slots = ctx.linker_slots in
  let rec run = function
    | Hike_vsa.Done (envs, solved, block_addrs) -> (envs, solved, block_addrs)
    | Paused p ->
      Core.Set.iter p.p_blocked ~f:(fun tid ->
          ignore (summary t frame (Core.Hashtbl.find_exn t.by_tid tid)));
      run (Hike_vsa.resume ctx.target ~lookup ~images ~callee ~foreign_slots p)
  in
  let envs, solved, block_addrs =
    run (Hike_vsa.start ctx.target ~lookup ~images ~callee ~block_addrs ~foreign_slots sub)
  in
  let summary =
    S.of_solved ~abi:t.abi
      ~callee:(fun tid ->
          match Core.Hashtbl.find t.symbols tid, Core.Hashtbl.find t.by_tid tid with
          | Some (_, s), _ -> Some s
          | None, Some e -> Some (summary t frame e)
          | None, None -> None)
      ~slot:(fun a ->
          Base.Option.map (Core.Map.find t.slot_names a) ~f:(fun n ->
              symbol_summary t (symbol t n)))
      ~lookup ~foreign_slots ~block_addrs ~envs solved
  in
  { solved; envs; block_addrs; summary }

(* ---- facts from a solved body ---- *)

(* The words of a bounded denotation; [None] when it is too wide. *)
and bounded_words (ws : Vsa.WordSet.t) : int64 list option =
  if Vsa.WordSet.is_top ws || Vsa.WordSet.is_bottom ws || Vsa.WordSet.is_infinite ws
  then None
  else
    Base.Option.map (Vsa.WordSet.enumerate ~cap:64 ws) ~f:(fun words ->
        Base.List.filter_map words ~f:(fun w -> Result.to_option (Cbat_word.to_int64 w)))

(* The resolved destinations of the body's indirect transfers become
   decode facts on their instructions.  Whether any is new: the body
   is then decoded and lifted again.  A jump's destination stays inside
   a function, as in BAP's decode, so it is never a root. *)
and learn_dests t cfg (f : func) : bool =
  let instruction =
    Core.Map.of_alist_reduce (module Core.Int64) ~f:(fun a _ -> a)
      (Base.List.map (D.terminators cfg) ~f:(fun (b, i) ->
           (Word.to_int64_exn b, Word.to_int64_exn i)))
  in
  let calls =
    Graphs.Cfg.nodes cfg |> Seq.filter ~f:D.is_call
    |> Seq.map ~f:(fun b -> Word.to_int64_exn (Block.addr b))
    |> Seq.to_list |> Core.Int64.Set.of_list
  in
  let learned =
    Term.enum blk_t f.solved |> Seq.to_list
    |> Base.List.concat_map ~f:(fun blk ->
        match Core.Map.find f.envs (Term.tid blk), Term.get_attr blk address with
        | Some (pre, post), Some site -> (
          match Core.Map.find instruction (Word.to_int64_exn site) with
          | None -> []
          | Some insn ->
            let jump =
              not (Core.Set.mem calls (Word.to_int64_exn site)) in
            Term.enum jmp_t blk |> Seq.to_list
            |> Base.List.filter_map ~f:indirect_target
            |> Base.List.concat_map ~f:(fun e ->
                match Vsa.denote_exp_at ~pre ~post ~blk e with
                | Ok ws ->
                  Base.List.map (Base.Option.value (bounded_words ws) ~default:[])
                    ~f:(fun w ->
                        if jump then frontier_add_jump t.frontier w;
                        (insn, w))
                | Error _ -> []))
        | _ -> [])
    |> Base.List.filter ~f:(fun (site, w) ->
        match Core.Map.find t.dests site with
        | Some ws -> not (Core.Set.mem ws w)
        | None -> true)
  in
  Base.List.iter learned ~f:(fun (site, w) ->
      t.dests <- Core.Map.update t.dests site ~f:(function
          | Some ws -> Core.Set.add ws w
          | None -> Core.Int64.Set.singleton w);
      D.provide_dest ~file:t.file ~site w);
  if Base.List.is_empty learned then false
  else begin
    rescan t;
    true
  end

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
    match Vsa.denote_exp_at ~pre:post ~post ~blk (Bil.Var v) with
    | Ok ws -> text_words ws
    | Error _ -> []
  in
  Term.enum blk_t f.solved |> Seq.to_list
  |> Base.List.concat_map ~f:(fun blk ->
      match Core.Map.find f.envs (Term.tid blk) with
      | Some (pre, post) when not (Vsa.AI.equal pre Vsa.AI.bottom) ->
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
    match Vsa.denote_exp_at ~pre ~post ~blk ~def e with
    | Ok ws -> text_words ws
    | Error _ -> []
  in
  Term.enum blk_t f.solved |> Seq.to_list
  |> Base.List.concat_map ~f:(fun blk ->
      match Core.Map.find f.envs (Term.tid blk) with
      | Some (pre, post) when not (Vsa.AI.equal pre Vsa.AI.bottom) ->
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

let create proj ~file ~state ~subroutines : t =
  let context = Hike_program_vsa.prepare proj in
  {
    proj;
    file;
    context;
    abi = Hike_abi.of_target context.target;
    slot_names =
      Core.Map.of_alist_reduce (module Core.Int64) ~f:(fun a _ -> a)
        (Hike_image.external_references proj);
    state;
    frontier = frontier_create ~subroutines;
    dests = Core.Int64.Map.empty;
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
    rescan t
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
          match Vsa.denote_exp_at ~pre:post ~post ~blk (Bil.Var arg0) with
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
      match Core.Map.find f.envs (Term.tid blk) with
      | Some (pre, post) when not (Vsa.AI.equal pre Vsa.AI.bottom) ->
        Term.enum jmp_t blk
        |> Seq.exists ~f:(fun j ->
            match indirect_target j with
            | Some e when not (Hike_return.is_jmp j) -> (
              match Hike_transfer.slot_of_target ~index e with
              | Some a when Core.Set.mem t.context.linker_slots a -> false
              | _ -> (
                match Vsa.denote_exp_at ~pre ~post ~blk e with
                | Ok ws -> (
                  match bounded_words ws with
                  | Some words ->
                    not (Base.List.for_all words ~f:(fun w ->
                        Core.Map.mem f.block_addrs (Addr.of_int64 w) || is_entry t w))
                  | None -> true)
                | Error _ -> true))
            | _ -> false)
      | _ -> false)

(* One jump per block for the downstream passes: each non-goto jump
   moves to a block of its own, entered under the jump's condition. *)
let simplify_jmps (sub : sub term) : sub term =
  Term.concat_map blk_t sub ~f:(fun blk ->
      match Term.enum jmp_t blk |> Seq.to_list with
      | [ _ ] -> [ blk ]
      | jmps ->
        let builder = Blk.Builder.init ~copy_phis:true ~copy_defs:true blk in
        let moved =
          Base.List.filter_map jmps ~f:(fun j ->
              match Jmp.kind j with
              | Goto _ ->
                Blk.Builder.add_jmp builder j;
                None
              | _ ->
                let own = Blk.create ~jmps:[ Jmp.with_cond j Bil.(int (Word.one 1)) ] () in
                Blk.Builder.add_jmp builder
                  (Jmp.create_goto ~cond:(Jmp.cond j) (Direct (Term.tid own)));
                Some own)
        in
        moved @ [ Term.with_attrs (Blk.Builder.result builder) (Term.attrs blk) ])

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
  { (Hike_kb.build ~target:t.context.target ~lookup
       ~block_envs:(Base.List.fold funcs ~init:Tid.Map.empty ~f:(fun acc (_, f) ->
           Core.Map.merge_skewed acc f.envs ~combine:(fun ~key:_ a _ -> a)))
       ~block_addrs:(union (Base.List.map funcs ~f:(fun (_, f) -> f.block_addrs))))
    with
    Hike_kb.sub_addrs;
    images = t.context.images;
    foreign_slots = t.context.linker_slots }

(* The worklist's program: main's closure (or, on refusal, that of
   every subroutine entry and every materialised code word) as solved
   bodies with one jump per block, plus a block-less declaration per
   external target (the emitter maps intrinsic targets itself); and the
   solves' analysis facts. *)
let run (proj : Project.t) ~file ~state ~subroutines : result =
  let t = create proj ~file ~state ~subroutines in
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
        let sub = Term.set_attr (simplify_jmps f.solved) filename t.file in
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
