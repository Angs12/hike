(* Probe-only discovery-word census over a solved program: the same
   materialised-word rule as Hike_worklist, without touching production. *)

open Bap.Std
open Bap_core_theory
open Probe_common

module Model = Hike.Stack_model
module Vsa = Cbat_vsa

let bounded_words (ws : Vsa.WordSet.t) : int64 list option =
  if Vsa.WordSet.is_top ws || Vsa.WordSet.is_bottom ws
     || Vsa.WordSet.is_infinite ws
  then None
  else
    Base.Option.map (Vsa.WordSet.enumerate ~cap:64 ws) ~f:(fun words ->
        Base.List.filter_map words ~f:Cbat_word.to_int64_opt)

let text_words (ws : Vsa.WordSet.t) : int64 list =
  match Vsa.WordSet.origin ws with
  | Some (Vsa.WordSet.Origin.Rip Model.Text) ->
    Base.Option.value (bounded_words ws) ~default:[]
  | _ -> []

let materialised ~word_bits ~synth ~envs sub : (Tid.t * int64 list) list =
  let wb = word_bits in
  let text ~pre ~post ~blk ~def e =
    match Vsa.denote_exp_at ~synth ~pre ~post ~blk ~def e with
    | Ok ws -> text_words ws
    | Error _ -> []
  in
  Term.enum blk_t sub |> Seq.to_list
  |> Base.List.concat_map ~f:(fun blk ->
         match Core.Map.find envs (Term.tid blk) with
         | None -> []
         | Some (pre, post) ->
           Term.enum def_t blk |> Seq.to_list
           |> Base.List.filter ~f:(fun d ->
                  match Term.get_attr d Disasm.insn with
                  | Some insn -> not (Insn.is Insn.call insn)
                  | None -> true)
           |> Base.List.concat_map ~f:(fun d ->
                  let values =
                    match Model.store_data_of_rhs (Def.rhs d) with
                    | None -> [ Def.rhs d ]
                    | Some data -> (
                      match Model.addr_of_rhs (Def.rhs d) with
                      | Some (_, size) when Size.in_bits size > wb ->
                        Base.List.init (Size.in_bits size / wb) ~f:(fun k ->
                            Bil.extract ~hi:(((k + 1) * wb) - 1) ~lo:(k * wb)
                              data)
                      | _ -> [ data ])
                  in
                  let words =
                    Base.List.concat_map values ~f:(text ~pre ~post ~blk ~def:d)
                  in
                  [ (Term.tid d, words) ]))

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
