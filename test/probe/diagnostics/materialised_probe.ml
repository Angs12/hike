(* Probe-only discovery-word census over a solved program: the same
   materialised-word rule as Hike_worklist, without touching production. *)

open Bap.Std
open Bap_core_theory
open Probe_common

module Model = Hike.Stack_model
module Vsa = Cbat_vsa

let () =
  init ();
  match Array.to_list Sys.argv |> List.tl with
  | [ path ] ->
    let proj =
      match Hike.Drive.load path with
      | Ok proj -> proj
      | Error e -> failwith (Core.Error.to_string_hum e)
    in
    let target = Project.target proj in
    let { Hike.Drive.program; facts; _ } = Hike.Drive.run proj in
    let word_bits = Hike_abi.word_bits (Hike.Abi.of_target target) in
    let scanned = ref 0 and words = ref [] in
    let word_defs = ref [] in
    Term.enum sub_t program
    |> Seq.iter ~f:(fun sub ->
           let mw =
             materialised ~word_bits ~synth:facts.Hike.Kb.synth
               ~envs:facts.Hike.Kb.envs sub
           in
           scanned := !scanned + Base.List.length mw;
           Base.List.iter mw ~f:(fun (tid, ws) ->
               if not (Base.List.is_empty ws) then
                 word_defs := tid :: !word_defs;
               words := ws @ !words));
    let words = Base.List.dedup_and_sort !words ~compare:Int64.compare in
    Printf.printf
      "MATERIALISED\t%s\tsubs=%d\tscanned=%d\tword_defs=%d\twords=%d\thash=%d\n%!"
      (Filename.basename path) (Seq.length (Term.enum sub_t program)) !scanned
      (Base.List.length !word_defs) (Base.List.length words)
      (Stdlib.Hashtbl.hash words);
    let tids =
      Base.List.dedup_and_sort !word_defs ~compare:Tid.compare
      |> Base.List.map ~f:Tid.to_string
    in
    Printf.printf "WORDDEFS\t%s\t%s\n%!" (Filename.basename path)
      (String.concat "," tids)
  | _ ->
    Printf.eprintf "usage: %s <binary>\n%!" Sys.argv.(0);
    exit 2
