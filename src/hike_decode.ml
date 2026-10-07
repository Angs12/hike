(* The drive loop's re-decode.  One decode context — the program's own
   package, unit, and theory instance — re-drives BAP's scan with the
   run's discoveries: an [is_subroutine] fact per discovered entry
   (durable for the partition, promised for the scan's root
   classification), and the resolved dispatch destinations provided on
   the instruction labels' [Insn.Slot.dests] facts so the driver keeps
   decoding at them.  The scan starts fresh every round; the grown state
   is the round's complete decode. *)

open Bap.Std
open Bap_core_theory
module Kb = Bap_core_theory.KB
module Driver = Disasm.Driver
module Subs = Disasm.Subroutines

type out = {
  grown : Driver.state;
  cfg : Graphs.Cfg.t;
  subs : Subs.t;
}

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

(* The cfg of a grown state: every block's insns merged with their
   semantics (the [with_basic] merge — [of_basic] alone would drop the
   lifter's call shape), the edges labeled fall/cond/jump. *)
let cfg_of_state (state : Driver.state) : Graphs.Cfg.t Kb.t =
  let open Kb.Syntax in
  let follows_after m1 m2 =
    Addr.equal (Addr.succ (Memory.max_addr m1)) (Memory.min_addr m2)
  in
  let has_conditional_jump blk =
    let insn = Block.terminator blk in
    Insn.is Insn.jump insn && Insn.is Insn.conditional insn
  in
  Driver.explore state
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

let initial proj =
  let state = Project.state proj in
  let grown = Project.State.disassembly state in
  let cfg = Toplevel.var "hike-drive-initial-cfg" in
  Toplevel.put cfg
    (Kb.Symbol.in_package (file_of (Project.program proj)) @@ fun () ->
     cfg_of_state grown);
  { grown; cfg = Toplevel.get cfg; subs = Project.State.subroutines state }

let rescan (proj : Project.t) ~(file : string) ~(roots : int64 list) :
    out option =
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
  let out : out option Toplevel.var = Toplevel.var "hike-drive-rescan" in
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
     kb_fold (fun s mem -> Driver.scan mem s) Driver.init mems
     >>= fun grown ->
     cfg_of_state grown >>= fun cfg ->
     Subs.update Subs.empty grown >>| fun subs ->
     Some { grown; cfg; subs });
  Toplevel.get out

(* The program of a grown decode: BAP's own lift of the partition — the
   same three calls the loader makes ([Symtab.create] over the state and
   the partition, [Program.lift]) — so every sub the decode and the
   partition name is in the program, discovered callees included. *)
let program_of_state ~(file : string) (state : Driver.state) (subs : Subs.t) : program term =
  let run : program term Toplevel.var = Toplevel.var "hike-drive-program" in
  Toplevel.put run
    (Kb.Symbol.in_package file @@ fun () ->
     let open Kb.Syntax in
     Symtab.create state subs >>= fun symtab -> Program.KB.lift symtab);
  Toplevel.get run

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
