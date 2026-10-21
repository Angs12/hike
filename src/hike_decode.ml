(* The BAP decoder adapter.  One decode context — the program's own
   package, unit, and theory instance — re-drives BAP's scan with the
   worklist's discoveries: an [is_subroutine] answer per discovered
   entry, and the resolved dispatch destinations provided on the
   instruction labels' [Insn.Slot.dests] facts so the driver keeps
   decoding at them.  Each scan starts fresh; a function's body is
   explored from it. *)

open Bap.Std
open Bap_core_theory
module Kb = Bap_core_theory.KB
module Driver = Disasm.Driver

(* A plain recursive fold over the knowledge monad. *)
let rec kb_fold (f : 'a -> 'x -> 'a Kb.t) (acc : 'a) (xs : 'x list) :
    'a Kb.t =
  let open Kb.Syntax in
  match xs with
  | [] -> !!acc
  | x :: xs -> f acc x >>= fun acc -> kb_fold f acc xs

let file_of (proj : Project.t) : string =
  match Project.get proj filename with
  | Some file -> file
  | None -> failwith "hike-decode: the project names no source file"

let code_mems (proj : Project.t) : mem list =
  Memmap.to_sequence (Project.memory proj)
  |> Seq.filter ~f:(fun (_, v) -> Option.is_some (Value.get Image.code_region v))
  |> Seq.map ~f:fst
  |> Seq.to_list

(* A cfg over the grown state: every explored block's insns merged
   with their semantics (the [with_basic] merge — [of_basic] alone would
   drop the lifter's call shape), the edges labeled fall/cond/jump.
   [entry] and [follow] are the driver's own exploration bounds. *)
let explore_cfg ?entry ?follow (state : Driver.state) : Graphs.Cfg.t Kb.t =
  let open Kb.Syntax in
  let follows_after m1 m2 =
    Addr.equal (Addr.succ (Memory.max_addr m1)) (Memory.min_addr m2)
  in
  let has_conditional_jump blk =
    let insn = Block.terminator blk in
    Insn.is Insn.jump insn && Insn.is Insn.conditional insn
  in
  Driver.explore ?entry ?follow state
    ~init:Graphs.Cfg.empty
    ~block:(fun mem insns ->
      Driver.execution_order insns
      >>= fun labels ->
      Kb.List.filter_map labels ~f:(fun label ->
              Kb.collect Disasm_expert.Basic.Insn.slot label
              >>= fun basic ->
              Kb.collect Theory.Semantics.slot label >>= fun s ->
              Kb.collect Memory.slot label
              >>| function
              | None -> None
              | Some mem ->
                let insn =
                  match basic with Some b -> Insn.with_basic s b | None -> s
                in
                Some (mem, insn))
      >>| fun kept ->
      if Base.List.is_empty kept && not (Base.List.is_empty labels) then
        Hike_diag.warn
          "decode: block at %s lost every semantic instruction"
          (Addr.to_string (Memory.min_addr mem));
      Block.create mem kept)
    ~node:(fun node cfg -> Kb.return (Graphs.Cfg.Node.insert node cfg))
    ~edge:(fun src dst g ->
      let k =
        if follows_after (Block.memory src) (Block.memory dst) then `Fall
        else if has_conditional_jump src then `Cond
        else `Jump
      in
      Kb.return (Graphs.Cfg.Edge.insert (Graphs.Cfg.Edge.create src dst k) g))

(* One function's candidate graph: every block the decode reaches from
   [entry] without entering another entry ([is_entry]), every edge kept,
   call fallthroughs included.  A transfer into another entry is a call
   or a tail call, so its target stays out of the graph. *)
let function_cfg ~(file : string) (state : Driver.state) ~(entry : Addr.t)
    ~(is_entry : Addr.t -> bool) : Graphs.Cfg.t =
  let follow a = Kb.return (Addr.equal a entry || not (is_entry a)) in
  Hike_kb.eval
    (Kb.Symbol.in_package file @@ fun () -> explore_cfg ~entry ~follow state)

(* What a destination label names: a code address, or a symbol with no
   address in the module (an external or an intrinsic). *)
type dest = Code of int64 | Symbol of string | Unknown

let dest (label : Tid.t) : dest =
  let addr = Toplevel.eval Theory.Label.addr (Kb.return label) in
  let name = Toplevel.eval Theory.Label.name (Kb.return label) in
  match addr, name with
  | Some a, _ -> Code (Bitvec.to_int64 a)
  | None, Some n -> Symbol n
  | None, None -> Unknown

(* The destinations the decode recorded on a block's last instruction. *)
let dests (blk : Block.t) : Tid.t list =
  match Kb.Value.get Insn.Slot.dests (Block.terminator blk) with
  | Some s -> Core.Set.to_list s
  | None -> []

let is_call (blk : Block.t) : bool = Insn.is Insn.call (Block.terminator blk)

(* Whether the block's last instruction is its only one with
   semantics. *)
let transfers_only (blk : Block.t) : bool =
  match Base.List.rev (Block.insns blk) with
  | _ :: rest -> Base.List.for_all rest ~f:(fun (_, i) -> Base.List.is_empty (Insn.bil i))
  | [] -> false

let block_at (cfg : Graphs.Cfg.t) (addr : Addr.t) : Block.t option =
  Graphs.Cfg.nodes cfg |> Seq.find ~f:(fun b -> Addr.equal (Block.addr b) addr)

(* The body: a call block's fallthrough stays only when [keep_fall]
   accepts it (the callee may return), then only what [entry] reaches
   stays. *)
let trim (cfg : Graphs.Cfg.t) ~(entry : Block.t) ~(keep_fall : Block.t -> bool) :
    Graphs.Cfg.t =
  let cut =
    Graphs.Cfg.edges cfg
    |> Seq.fold ~init:cfg ~f:(fun g e ->
        let src = Graphs.Cfg.Edge.src e in
        match Graphs.Cfg.Edge.label e with
        | `Fall when is_call src && not (keep_fall src) -> Graphs.Cfg.Edge.remove e g
        | _ -> g)
  in
  let reached =
    Graphlib.Std.Graphlib.fold_reachable (module Graphs.Cfg) ~init:Block.Set.empty
      ~f:Core.Set.add cut entry
  in
  Graphs.Cfg.nodes cut
  |> Seq.fold ~init:cut ~f:(fun g b ->
      if Core.Set.mem reached b then g else Graphs.Cfg.Node.remove b g)

(* The body lifted by BAP's own sub lifter: blocks named by their
   address labels, a call's return the cfg's fallthrough edge. *)
let lift ~(file : string) ~(tid : Tid.t) ~(name : string) (entry : Block.t)
    (cfg : Graphs.Cfg.t) : sub term =
  let lifted =
    Hike_kb.eval
      (Kb.Symbol.in_package file @@ fun () -> Sub.KB.lift entry cfg) in
  Sub.create ~tid ~name ~blks:(Term.enum blk_t lifted |> Seq.to_list) ()
  |> fun s -> Term.set_attr s address (Block.addr entry)

(* The decode channel: a resolved destination becomes a fact on the
   dispatch INSTRUCTION's own label ([provide] unions, so a later
   destination joins the earlier ones). *)
let provide_dest ~(file : string) ~(site : int64) (dest : int64) : unit =
  Hike_kb.eval
    (let open Kb.Syntax in
     let addr a = Word.to_bitvec (Addr.of_int64 a) in
     Theory.Label.for_addr ~package:file (addr site) >>= fun label ->
     Theory.Label.for_addr ~package:file (addr dest) >>= fun dest ->
     Kb.collect Theory.Semantics.slot label >>= fun sema ->
     let cur =
       match Kb.Value.get Insn.Slot.dests sema with
       | Some s -> s
       | None -> Core.Set.empty (module Theory.Label)
     in
     Kb.provide Theory.Semantics.slot label
       (Kb.Value.put Insn.Slot.dests sema (Some (Core.Set.add cur dest))))

let in_code (proj : Project.t) (a : int64) : bool =
  let a = Addr.of_int64 a in
  Base.List.exists (code_mems proj) ~f:(fun m -> Memory.contains m a)

(* The decode context: every root in [roots] answers [is_subroutine]
   through the entry promise, and every provided destination fact is
   read.  The driver classifies each code address through a scoped
   label, so the address-keyed promise — not a stored fact — marks a
   root; [roots] must carry every entry on each decode. *)
let decoding (proj : Project.t) ~(file : string) ~(roots : int64 list)
    (body : Driver.state Kb.t) : Driver.state =
#ifdef VSA_DEBUG
  Printf.eprintf "hike-dbg-roots: [%s]\n%!"
    (Base.List.map roots ~f:(Printf.sprintf "%Lx") |> String.concat ",");
#endif
  let width = Theory.Target.code_addr_size (Project.target proj) in
  let roots_set =
    Core.Set.of_list (module Addr) (Base.List.map roots ~f:Addr.of_int64)
  in
  let entry_promise label =
    let open Kb.Syntax in
    Kb.collect Theory.Label.addr label >>= function
    | Some a ->
        !!(Base.Option.some_if (Core.Set.mem roots_set (Word.create a width)) true)
    | None -> !!(None)
  in
  (* The resolved destinations ride the dispatch instruction's own
     [Insn.Slot.dests]: the run provides them as facts before each scan
     (monotone — [provide] unions), so the driver keeps decoding at the
     addresses the VSA resolved.  No brancher re-declaration: a promise's
     answer is cached at its first query, while a provided fact grows. *)
  Hike_kb.eval
    (let open Kb.Syntax in
     Theory.instance () >>= fun theory ->
     Theory.with_current theory @@ fun () ->
     Theory.Unit.for_file file >>= fun unit ->
     Kb.Symbol.in_package file @@ fun () ->
     Kb.promising Theory.Label.unit ~promise:(fun _ -> !!(Some unit)) @@ fun () ->
     Kb.promising Theory.Label.is_subroutine ~promise:entry_promise @@ fun () ->
     body)

(* A fresh decode of every code region. *)
let scan (proj : Project.t) ~(file : string) ~(roots : int64 list) : Driver.state =
  decoding proj ~file ~roots
    (kb_fold (fun s mem -> Driver.scan mem s) Driver.init
       (code_mems proj |> List.rev))

(* The decode resumed from [starts] over the regions holding them: the
   driver's own pending-work step, so only the code reachable from the
   starts is decoded again.  A start becomes a subroutine only when
   [subroutines] says it is a root. *)
let resume ?(subroutines = false) (proj : Project.t) ~(file : string)
    ~(roots : int64 list) (state : Driver.state) ~(starts : int64 list) :
    Driver.state =
  let starts = Base.List.map starts ~f:Addr.of_int64 in
  decoding proj ~file ~roots
    (kb_fold (fun s mem ->
         match Base.List.filter starts ~f:(Memory.contains mem) with
         | [] -> Kb.return s
         | here ->
             Driver.resume ~record:subroutines
               (Core.Set.of_list (module Addr) here) mem s)
        state (code_mems proj))

(* Grow from learned dispatches and pending roots. Accept the resumed
   state only after every fact is represented; otherwise scan afresh. *)
let grow (proj : Project.t) ~(file : string) ~(roots : int64 list)
    ~(destinations : (int64 * int64) list) (state : Driver.state) : Driver.state =
  Base.List.iter destinations ~f:(fun (site, dest) -> provide_dest ~file ~site dest);
  let pending state =
    Base.List.filter roots ~f:(fun a ->
        let w = Addr.of_int64 a in
        in_code proj a && not (Driver.is_subroutine state w)
        && not (Driver.is_data state w))
  in
  let starts = Base.List.map destinations ~f:fst
      |> Base.List.dedup_and_sort ~compare:Core.Int64.compare in
  let resumed = match starts with
    | [] -> state
    | _ -> resume proj ~file ~roots state ~starts in
  let resumed = match pending resumed with
    | [] -> resumed
    | starts -> resume ~subroutines:true proj ~file ~roots resumed ~starts in
  let decoded (site, target) =
    let target = Addr.of_int64 target in
    (match Driver.jump resumed (Addr.of_int64 site) with
     | Some jump -> Core.Set.mem (Driver.destinations jump) target
     | None -> false)
    && (Driver.is_block resumed target || Driver.is_data resumed target)
  in
  let kept = Base.List.is_empty (pending resumed)
      && Base.List.for_all destinations ~f:decoded in
#ifdef VSA_DEBUG
  let full = scan proj ~file ~roots in
  Printf.eprintf "hike-dbg-rescan: starts=%d roots=%d resume=%s equal=%b subs=%b\n%!"
    (List.length starts) (List.length (pending state))
    (if kept then "kept" else "fallback")
    (Driver.equal resumed full)
    (Core.Set.equal (Driver.subroutines resumed) (Driver.subroutines full));
  if kept then resumed else full
#else
  if kept then resumed else scan proj ~file ~roots
#endif

(* Each decoded block's start address and its terminator instruction's
   address.  The solver's jmp rewrites rebuild jmps with [Jmp.create
   ~tid], dropping the [address] attr, so a dispatch's site is the
   block's own (stable) address and its instruction address is read off
   the decode (the driver's dests facts key on the instruction label). *)
let terminators (cfg : Graphs.Cfg.t) : (Addr.t * Addr.t) list =
  Graphs.Cfg.nodes cfg
  |> Seq.filter_map ~f:(fun b ->
         match Base.List.last (Block.insns b) with
         | Some (mem, _) -> Some (Block.addr b, Memory.min_addr mem)
         | None -> None)
  |> Seq.to_list

(* BAP's partition of a decode into subroutines and the symbol table it
   names them by, computed as the project's own disassembly computes
   them. *)
let symtab ~(file : string) (state : Driver.state) : Symtab.t =
  Hike_kb.eval
    (let open Kb.Syntax in
     Kb.Symbol.in_package file @@ fun () ->
     Theory.instance () >>= fun theory ->
     Theory.with_current theory @@ fun () ->
     Theory.Unit.for_file file >>= fun unit ->
     Kb.promising Theory.Label.unit ~promise:(fun _ -> !!(Some unit)) (fun () ->
         Disasm.Subroutines.update Disasm.Subroutines.empty state)
     >>= fun subs -> Symtab.create state subs)
