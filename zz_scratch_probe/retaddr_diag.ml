(* The ret-not-dispatch diagnosis: for one sub, print every RET
   epilogue's ADDRESS denotation (the retaddr predicate) and its VALUE
   denotation (what the resolution's dispatch walk reads), with the
   memory state it comes from, phase by phase.
   Usage: retaddr_diag.exe <binary> [subname] (default fts_maxarglen). *)

open Bap.Std
open Probe_common

module Vsa = Cbat_vsa
module Model = Hike.Stack_model

let mem_idx = { Cbat_vsa.Mem.addr_width = 64; Cbat_vsa.Mem.addressable_width = 8 }

let print_ws (label : string) (ws : Ws.t) : unit =
  Printf.printf "    %s: %s" label (ws_to_string ws);
  (match Ws.enumerate ~cap:8 ws with
   | Some ws ->
     Printf.printf "  enumerate=[%s]"
       (Base.String.concat ~sep:"; "
          (Base.List.map ws ~f:(fun w -> Word.to_string (Cbat_word.to_word w))))
   | None -> Printf.printf "  enumerate=>(cap)");
  print_newline ()

let def_of_tid blk dtid =
  Seq.find (Term.enum def_t blk) ~f:(fun d -> Tid.equal (Term.tid d) dtid)

(* The ADDRESS predicate: every load whose address denotation is the
   entry-RSP cell, printed with its before-env address denotation. *)
let retaddr_defs_of (sol : Vsa.vsa_sol) (sub : sub term) : Tid.Set.t =
  Printf.printf "-- retaddr defs (the ADDRESS predicate) --\n";
  let retaddr =
    Term.enum blk_t sub
    |> Seq.fold ~init:Tid.Set.empty ~f:(fun acc blk ->
           fst
             (Vsa.fold_block_states ~sol blk ~init:acc
                ~f:(fun before _after d acc ->
                    match Model.addr_of_rhs (Def.rhs d) with
                    | None -> acc
                    | Some (addr, _) -> (
                        match Vsa.denote_imm_exp addr before with
                        | Ok ws when Model.is_return_address ws ->
                          Printf.printf "  def %s (%s := %s): retaddr, addr=%s\n"
                            (Tid.name (Term.tid d))
                            (Var.name (Def.lhs d))
                            (Format.asprintf "%a" Exp.pp (Def.rhs d))
                            (ws_to_string ws);
                          Core.Set.add acc (Term.tid d)
                        | _ -> acc))))
  in
  Printf.printf "  total: %d\n" (Core.Set.length retaddr);
  retaddr

(* The dispatch value of a load-shaped reaching def: its rhs replayed
   from the block's solution entry in the def's own before-env, plus the
   memory cell the load's address reads. *)
let report_def_value (sol : Vsa.vsa_sol) (blk : blk term) (d : def term)
    ~(retaddr : bool) : unit =
  let pre = Graphlib.Std.Solution.get sol (Term.tid blk) in
  Printf.printf "    reaching def %s: retaddr=%b\n" (Tid.name (Term.tid d))
    retaddr;
  (match Vsa.solve_denote ~pre ~blk ~def:d (Def.rhs d) with
   | Ok ws -> print_ws "VALUE denotation (dispatch input)" ws
   | Error _ -> Printf.printf "    VALUE denotation: type error\n");
  match Def.rhs d with
  | Bil.Load (Bil.Var m, _, endian, size) ->
    let mem = Vsa.AI.find_memory mem_idx pre m in
    Printf.printf "    mem var %s: top=%b bottom=%b\n" (Var.name m)
      (Vsa.Mem.equal mem (Vsa.Mem.top mem_idx))
      (Vsa.Mem.equal mem (Vsa.Mem.bottom mem_idx));
    (match Model.addr_of_rhs (Def.rhs d) with
     | None -> ()
     | Some (addr, _) -> (
         match Vsa.solve_denote ~pre ~blk ~def:d addr with
         | Error _ -> Printf.printf "    cell key: addr type error\n"
         | Ok aws -> (
             match Vsa.Mem.Key.of_wordset aws with
             | None ->
               Printf.printf "    cell key: unkeyable (%s)\n" (ws_to_string aws)
             | Some k ->
               let cell = Vsa.Mem.find (Size.in_bits size, endian) mem k in
               Printf.printf "    cell find: top=%b bottom=%b data=%s\n"
                 (Vsa.Mem.Val.is_top cell)
                 (Vsa.Mem.Val.is_bottom cell)
                 (ws_to_string (Vsa.Mem.Val.data cell));
               let data = Vsa.Mem.Val.data cell in
               if Ws.is_top data then
                 Printf.printf
                   "    -> the MEMORY MAP's unallocated-cell default\n"
               else if Ws.is_bottom data then
                 Printf.printf "    -> the MEMORY MAP's bottom (unreachable)\n"
               else Printf.printf "    -> an ALLOCATED cell's stored value\n")))
  | _ -> ()

let report_jmp (sol : Vsa.vsa_sol) ~(retaddr : Tid.Set.t) (blk : blk term)
    (j : jmp term) : unit =
  let target =
    match Jmp.kind j with
    | Call c -> (match Call.target c with Indirect e -> Some e | _ -> None)
    | Goto (Indirect e) -> Some e
    | _ -> None
  in
  match target with
  | None -> ()
  | Some texp -> (
      Printf.printf "  jmp %s in blk %s: target %s\n" (Tid.name (Term.tid j))
        (Tid.name (Term.tid blk))
        (Format.asprintf "%a" Exp.pp texp);
      match texp with
      | Bil.Var v -> (
          match
            Core.Map.find (Vsa.last_defs blk) v |> Base.Option.map ~f:Term.tid
          with
          | None -> Printf.printf "    no reaching def\n"
          | Some dtid -> (
              match def_of_tid blk dtid with
              | None -> Printf.printf "    reaching def %s: not in this block\n"
                          (Tid.name dtid)
              | Some d -> report_def_value sol blk d
                            ~retaddr:(Core.Set.mem retaddr (Term.tid d))))
      | _ -> ())

let report_dispatch_values (sol : Vsa.vsa_sol) ~(retaddr : Tid.Set.t)
    (sub : sub term) : unit =
  Printf.printf "-- indirect targets and the values the resolution reads --\n";
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun blk ->
         Term.enum jmp_t blk |> Seq.iter ~f:(report_jmp sol ~retaddr blk))

(* Where the cell at the RET address is allocated: the whole-sub scan
   reports each block whose entry-map has the cell and each def that
   creates it (absent before, present after), with the stored data's
   denotation. *)
let report_cell_writers (sol : Vsa.vsa_sol) (sub : sub term) ~(mv : var)
    ~(key : Vsa.Mem.Key.t) ~(lo_word : Cbat_word.t) : unit =
  Printf.printf "-- the retaddr cell's writers --\n";
  let mem_of env = Vsa.AI.find_memory mem_idx env mv in
  let cell env = Vsa.Mem.find (64, LittleEndian) (mem_of env) key in
  let allocated env =
    Vsa.Mem.has_cell_in (mem_of env) ~lo:lo_word ~hi:lo_word
  in
  let any = ref false in
  let created = ref false in
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun blk ->
         let pre = Graphlib.Std.Solution.get sol (Term.tid blk) in
         if allocated pre then begin
           any := true;
           Printf.printf "  blk %s: cell at block entry, data=%s\n"
             (Tid.name (Term.tid blk))
             (ws_to_string (Vsa.Mem.Val.data (cell pre)))
         end;
         ignore
           (Vsa.fold_block_states ~sol blk ~init:() ~f:(fun before after d () ->
                let was = allocated before and now = allocated after in
                if now && not was then begin
                  created := true;
                  any := true;
                  print_endline
                    (Printf.sprintf "  def %s (%s := %s): creates the cell, data=%s"
                       (Tid.name (Term.tid d))
                       (Var.name (Def.lhs d))
                       (Format.asprintf "%a" Exp.pp (Def.rhs d))
                       (ws_to_string (Vsa.Mem.Val.data (cell after))));
                  (match Model.store_data_of_rhs (Def.rhs d) with
                   | Some (data, _) -> (
                       match Vsa.denote_imm_exp data before with
                       | Ok ws ->
                         print_ws "stored data denotation" ws
                       | Error _ ->
                         Printf.printf "    stored data: type error\n")
                   | None -> ());
                  (match Model.addr_of_rhs (Def.rhs d) with
                   | Some (addr, _) -> (
                       match Vsa.denote_imm_exp addr before with
                       | Ok ws -> print_ws "store address denotation" ws
                       | Error _ ->
                         Printf.printf "    store address: type error\n")
                   | None -> ())
                end)));
  if not !created then
    Printf.printf
      "  no def creates the cell: it comes from an edge transfer (the backward walk's trace-exact cell meet, Mem.meet_range), never a store\n";
  if not !any then
    Printf.printf "  no block entry and no def carries the cell at this phase\n"

(* The mem var and the first address word of the RET loads. *)
let retaddr_mem_var (sub : sub term) (retaddr : Tid.Set.t) : var option =
  Term.enum blk_t sub
  |> Seq.find_map ~f:(fun blk ->
         Seq.find_map (Term.enum def_t blk) ~f:(fun d ->
             if Core.Set.mem retaddr (Term.tid d) then
               match Def.rhs d with
               | Bil.Load (Bil.Var m, _, _, _) -> Some m
               | _ -> None
             else None))

let retaddr_cell_word (sol : Vsa.vsa_sol) (sub : sub term)
    (retaddr : Tid.Set.t) : Cbat_word.t option =
  Term.enum blk_t sub
  |> Seq.find_map ~f:(fun blk ->
         let pre = Graphlib.Std.Solution.get sol (Term.tid blk) in
         Seq.find_map (Term.enum def_t blk) ~f:(fun d ->
             if Core.Set.mem retaddr (Term.tid d) then
               match Model.addr_of_rhs (Def.rhs d) with
               | Some (addr, _) -> (
                   match Vsa.solve_denote ~pre ~blk ~def:d addr with
                   | Ok ws -> Ws.min_elem ws
                   | Error _ -> None)
               | None -> None
             else None))

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  init ();
  match args with
  | [] -> usage Sys.argv.(0) "<binary> [subname]"
  | path :: rest ->
    let proj = load_project path in
    let prog = Project.program proj in
    let target = Project.target proj in
    let name = match rest with n :: _ -> n | [] -> "fts_maxarglen" in
    let sub =
      match find_sub prog name with
      | Some s -> s
      | None ->
        usage Sys.argv.(0)
          (Printf.sprintf "<binary> [subname] — %s not found" name)
    in
    let abi = Hike.Abi.of_target target in
    Printf.printf "=== retaddr_diag %s :: %s ===\n" (Filename.basename path)
      (Sub.name sub);
    let written = Hike.Vsa.kill_summaries ~abi prog in
    let rec phases k (sub : sub term) (resolved : Tid.Set.t Tid.Map.t)
        (fresh : Tid.Set.t) (block_addrs : Tid.t Addr.Map.t)
        (init : Vsa.vsa_sol option) =
      let seed =
        match init with Some s -> s | None -> Vsa.init_sol ~abi sub
      in
      let sol =
        Vsa.static_graph_vsa ~abi ~written ~resolved
          (Program.create ~subs:[ sub ] ())
          sub seed
      in
      Printf.printf "\n== PHASE %d ==\n" k;
      let retaddr = retaddr_defs_of sol sub in
      report_dispatch_values sol ~retaddr sub;
      (match
         ( retaddr_mem_var sub retaddr,
           Vsa.Mem.Key.of_wordset (Ws.stack_word_i64 0L),
           retaddr_cell_word sol sub retaddr )
       with
       | Some mv, Some key, Some w -> report_cell_writers sol sub ~mv ~key ~lo_word:w
       | _ -> Printf.printf "-- retaddr cell: no keyable entry-RSP cell --\n");
      let sub', resolved', fresh', block_addrs', events =
        Hike.Cfg_complete.resolve_phase ~abi ~sol ~images:[] ~block_addrs sub
          resolved
      in
      Printf.printf "  resolution: events=%b fresh=%d\n" events
        (Core.Set.length fresh');
      if events && k < 8 then
        phases (k + 1) sub' resolved' (Core.Set.union fresh fresh') block_addrs'
          (Some sol)
    in
    phases 0 sub Tid.Map.empty Tid.Set.empty
      (Core.Map.empty (module Addr)) None
