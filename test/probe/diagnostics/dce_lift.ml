(* Probe driver for the narrow DCE.  The census runs the production
   pass over the pre-solve SSA of each sub and checks the removed terms
   against the words `materialised_words` would discover.  The lift mode
   runs the production pipeline (the pass is wired before the solve). *)

open Bap.Std
open Bap_core_theory
open Probe_common

module Model = Hike.Stack_model
module Abi = Hike.Abi
module Vsa = Cbat_vsa

let usage () =
  Printf.eprintf
    "usage: %s <binary> census | %s <binary> lift <out.ll>\n%!"
    Sys.argv.(0) Sys.argv.(0);
  exit 2

let defs_of sub =
  Term.enum blk_t sub |> Seq.concat_map ~f:(Term.enum def_t) |> Seq.to_list
let phis_of sub =
  Term.enum blk_t sub |> Seq.concat_map ~f:(Term.enum phi_t) |> Seq.to_list

let def_lhs d =
  match Core.Set.to_list (Model.writes (`Def d)) with
  | [ v ] -> v
  | _ -> failwith "dce probe: def has no single written var"

let diff by_tid before after =
  let kept =
    Base.List.map after ~f:by_tid |> Tid.Set.of_list
  in
  Base.List.filter before ~f:(fun t ->
      not (Core.Set.mem kept (by_tid t)))

let solve_ssa ~synth ~callee target sub =
  match
    Hike.Vsa.solve target ~lookup:(fun _ -> None) ~images:[] ~callee
      ~synth ~sub
      ~foreign_slots:Core.Int64.Set.empty ~resolved:Tid.Map.empty
      ~seed:None ~wake:Tid.Set.empty
  with
  | Hike.Vsa.Solved s ->
    let envs, solved =
      Hike.Vsa.stamp ~images:[] ~synth:s.Hike.Vsa.synth ~sol:s.Hike.Vsa.sol
        s.Hike.Vsa.sub
    in
    (envs, solved, s.Hike.Vsa.synth)

let flag_cone ~abi removed_defs =
  let by_lhs : (var, def term) Core.Hashtbl.t = Core.Hashtbl.create (module Var) in
  Base.List.iter removed_defs ~f:(fun d ->
      Core.Hashtbl.set by_lhs ~key:(def_lhs d) ~data:d);
  let flags =
    Base.List.filter removed_defs ~f:(fun d -> Abi.is_flag_reg abi (def_lhs d))
  in
  let seen = Core.Hash_set.create (module Var) in
  let work = Queue.create () in
  Base.List.iter flags ~f:(fun d ->
      let v = def_lhs d in
      if Core.Hash_set.strict_add seen v |> Result.is_ok then Queue.add v work);
  while not (Queue.is_empty work) do
    let v = Queue.pop work in
    match Core.Hashtbl.find by_lhs v with
    | None -> ()
    | Some d ->
      Core.Set.iter (Model.reads (`Def d)) ~f:(fun r ->
          if Core.Hashtbl.mem by_lhs r
             && (Core.Hash_set.strict_add seen r |> Result.is_ok)
          then Queue.add r work)
  done;
  (Base.List.length flags, Core.Hash_set.length seen)

let census path =
  let proj = load_project path in
  let target = Project.target proj in
  let abi = Abi.of_target target in
  let word_bits = Hike_abi.word_bits abi in
  let synth, prog = production_input proj in
  let callee = callee_of ~synth prog in
  let defs = ref 0 and phis = ref 0 in
  let removed_defs = ref [] and removed_phis = ref [] in
  let flag_defs = ref 0 and cone_defs = ref 0 in
  let scanned = ref Tid.Set.empty in
  let word_defs = ref [] in
  let words_b = ref [] and words_d = ref [] in
  Term.enum sub_t prog
  |> Seq.iter ~f:(fun raw ->
         let ssa = Hike.Ssa.ssa_sub ~synth ~target raw in
         let dce = Hike.Dce.dce_sub ~synth ~target ssa in
         let before_defs = defs_of ssa and before_phis = phis_of ssa in
         defs := !defs + Base.List.length before_defs;
         phis := !phis + Base.List.length before_phis;
         let gone_defs = diff Term.tid before_defs (defs_of dce) in
         let gone_phis = diff Term.tid before_phis (phis_of dce) in
         removed_defs := gone_defs @ !removed_defs;
         removed_phis := gone_phis @ !removed_phis;
         let flags, cone = flag_cone ~abi gone_defs in
         flag_defs := !flag_defs + flags;
         cone_defs := !cone_defs + cone;
         let envs_b, solved_b, synth_b = solve_ssa ~synth ~callee target ssa in
         let envs_d, solved_d, synth_d = solve_ssa ~synth ~callee target dce in
         let mw_b = materialised ~word_bits ~synth:synth_b ~envs:envs_b solved_b in
         let mw_d = materialised ~word_bits ~synth:synth_d ~envs:envs_d solved_d in
         Base.List.iter mw_b ~f:(fun (tid, ws) ->
             scanned := Core.Set.add !scanned tid;
             if not (Base.List.is_empty ws) then
               word_defs := tid :: !word_defs);
         words_b := Base.List.concat_map mw_b ~f:snd @ !words_b;
         words_d := Base.List.concat_map mw_d ~f:snd @ !words_d);
  let removed = Base.List.length !removed_defs in
  let scanned_hits =
    Base.List.count !removed_defs ~f:(fun d ->
        Core.Set.mem !scanned (Term.tid d))
  in
  let gone = Tid.Set.of_list (Base.List.map !removed_defs ~f:Term.tid) in
  let word_defs =
    Base.List.count
      (Base.List.dedup_and_sort !word_defs ~compare:Tid.compare)
      ~f:(fun tid -> Core.Set.mem gone tid)
  in
  let words_b =
    Base.List.dedup_and_sort !words_b ~compare:Int64.compare
  in
  let words_d =
    Base.List.dedup_and_sort !words_d ~compare:Int64.compare
  in
  let other_defs = removed - !cone_defs in
  Printf.printf
    "CENSUS\t%s\tdefs=%d\tphis=%d\tremoved_def=%d\tremoved_phi=%d\tflag=%d\tcone=%d\tother=%d\n%!"
    (Filename.basename path) !defs !phis removed
    (Base.List.length !removed_phis) !flag_defs !cone_defs other_defs;
  Printf.printf
    "DISCOVERY\t%s\tremoved=%d\tscanned_hits=%d\tword_defs=%d\twords_base=%d\twords_dce=%d\thash_base=%d\thash_dce=%d\n%!"
    (Filename.basename path) removed scanned_hits word_defs
    (Base.List.length words_b) (Base.List.length words_d)
    (Stdlib.Hashtbl.hash words_b) (Stdlib.Hashtbl.hash words_d);
  if word_defs > 0 || not (Base.List.equal Int64.equal words_b words_d) then exit 2

let lift path out =
  let proj =
    match Hike.Drive.load path with
    | Ok proj -> proj
    | Error e -> failwith (Core.Error.to_string_hum e)
  in
  let t0 = Unix.gettimeofday () in
  let lifted = Hike.lift proj in
  let t1 = Unix.gettimeofday () in
  Hike.emit out lifted;
  let t2 = Unix.gettimeofday () in
  let program = Project.program lifted in
  let subs = Seq.length (Term.enum sub_t program) in
  let defs =
    Term.enum sub_t program |> Seq.concat_map ~f:(Term.enum blk_t)
    |> Seq.concat_map ~f:(Term.enum def_t) |> Seq.length
  in
  let phis =
    Term.enum sub_t program |> Seq.concat_map ~f:(Term.enum blk_t)
    |> Seq.concat_map ~f:(Term.enum phi_t) |> Seq.length
  in
  Printf.printf "LIFT\t%s\tlift=%.3f\temit=%.3f\tsubs=%d\tdefs=%d\tphis=%d\n%!"
    (Filename.basename path) (t1 -. t0) (t2 -. t1) subs defs phis

let () =
  init ();
  match Array.to_list Sys.argv |> List.tl with
  | [ path; "census" ] -> census path; exit 0
  | [ path; "lift"; out ] -> lift path out; exit 0
  | _ -> usage ()
