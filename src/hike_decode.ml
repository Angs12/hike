(* The BAP decoder adapter.  One decode context — the program's own
   package, unit, and theory instance — re-drives BAP's scan with the
   worklist's discoveries: an [is_subroutine] fact per discovered entry,
   and the resolved dispatch destinations provided on the instruction
   labels' [Insn.Slot.dests] facts so the driver keeps decoding at them.
   Each scan starts fresh; a function's body is explored from it. *)

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

let file_of (prog : program term) : string =
  match
    Term.enum sub_t prog
    |> Seq.filter_map ~f:(fun s -> Term.get_attr s filename)
    |> Seq.hd
  with
  | Some file -> file
  | None -> failwith "hike-drive: the program names no source file"

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
      >>= Kb.List.filter_map ~f:(fun label ->
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
      >>| Block.create mem)
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
  let run : Graphs.Cfg.t Toplevel.var = Toplevel.var "hike-decode-function" in
  Toplevel.put run
    (Kb.Symbol.in_package file @@ fun () -> explore_cfg ~entry ~follow state);
  Toplevel.get run

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
  let run : sub term Toplevel.var = Toplevel.var "hike-decode-lift" in
  Toplevel.put run (Kb.Symbol.in_package file @@ fun () -> Sub.KB.lift entry cfg);
  let lifted = Toplevel.get run in
  Sub.create ~tid ~name ~blks:(Term.enum blk_t lifted |> Seq.to_list) ()
  |> fun s -> Term.set_attr s address (Block.addr entry)

(* The decode channel: a resolved destination becomes a fact on the
   dispatch INSTRUCTION's own label ([provide] unions, so a later
   destination joins the earlier ones). *)
let provide_dest ~(file : string) ~(site : int64) (dest : int64) : unit =
  let run : unit Toplevel.var = Toplevel.var "hike-decode-dests" in
  Toplevel.put run
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
       (Kb.Value.put Insn.Slot.dests sema (Some (Core.Set.add cur dest))));
  Toplevel.get run

(* The loader's decode. *)
let initial (proj : Project.t) : Driver.state =
  Project.State.disassembly (Project.state proj)

(* A fresh decode of every code region with [roots] as subroutine
   facts and every provided destination fact. *)
let scan (proj : Project.t) ~(file : string) ~(roots : int64 list) : Driver.state =
#ifdef VSA_DEBUG
  Printf.eprintf "hike-dbg-roots: [%s]\n%!"
    (Base.List.map roots ~f:(Printf.sprintf "%Lx") |> String.concat ",");
#else
  ignore roots;
#endif
  let width = Theory.Target.code_addr_size (Project.target proj) in
  (* The program's own entries ride every scan: they are the decode the
     primary lift already named, and their facts keep the partition
     from assigning their blocks to a discovered root. *)
  let program_roots =
    Term.enum sub_t (Project.program proj)
    |> Seq.filter_map ~f:(fun s ->
           match Term.first blk_t s with
           | Some b -> Base.Option.map (Term.get_attr b address)
                         ~f:(fun a -> Word.to_int64_exn a)
           | None -> None)
    |> Seq.to_list
  in
  let roots =
    Base.List.append program_roots
      (Base.List.filter roots
         ~f:(fun w -> not (Base.List.mem program_roots w ~equal:Int64.equal)))
  in
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
  let out : Driver.state Toplevel.var = Toplevel.var "hike-decode-scan" in
  Toplevel.put out
    (let open Kb.Syntax in
     Theory.instance () >>= fun theory ->
     Theory.with_current theory @@ fun () ->
     Theory.Unit.for_file file >>= fun unit ->
     Kb.Symbol.in_package file @@ fun () ->
     kb_fold
       (fun () a ->
         Theory.Label.for_addr (Word.to_bitvec (Addr.of_int64 a))
         >>= fun l ->
         Kb.provide Theory.Label.is_subroutine l (Some true))
       () roots
     >>= fun () ->
     Kb.promising Theory.Label.unit ~promise:(fun _ -> !!(Some unit)) @@ fun () ->
     Kb.promising Theory.Label.is_subroutine ~promise:entry_promise @@ fun () ->
     let mems = code_mems proj |> List.rev in
     kb_fold (fun s mem -> Driver.scan mem s) Driver.init mems);
  Toplevel.get out

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
