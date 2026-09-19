(* Precision-attribution census: per sub of a binary, the window-class
   traffic hull, its class (EXACT / MID / FULLSPAN / WRAP32 / NOLANE),
   and — for every unservable hull — the contributing defs (the Caller
   tags and SP extents that carry it).  Mirrors the production pass:
   jump compile + split-mem normalize, then the composed producer per sub with
   Usage: pa_census.exe <binary> [sub]
   (stdout TSV; the [sub] filter prints one sub's row + culprits). *)

open Bap.Std
open Probe_common

module Model = Hike__Hike_stack_model

(* The model segment span (8 MiB) and the window capacity, mirrored
   from the composite domain for classification. *)
let seg_span = Int64.shift_left 1L 23
let window_bytes = 65536L

let classify_hull (w : int64) : string =
  if Int64.compare w window_bytes <= 0 then "EXACT"
  else if Int64.compare w (Int64.shift_left 1L 31) >= 0 then "WRAP32"
  else if Int64.compare w seg_span >= 0 then "FULLSPAN"
  else "MID"

(* The window hull from the Caller tags (the promoted slots excluded).
   A wrapped pair (lo > hi) floors the hull at one word. *)
let window_hull (offsets : Model.vsa_kind Tid.Map.t)
    (slots : int Tid.Map.t) : int64 option =
  let word = 8L in
  let acc = ref None in
  let see l h =
    if Int64.compare l h > 0 then
      acc := Some (Base.Option.value !acc ~default:word)
    else
      let w = Int64.sub h Model.segment_base in
      if Int64.compare w word >= 0 then
        acc := Some (Int64.max w (Base.Option.value !acc ~default:word))
  in
  Core.Map.iteri offsets ~f:(fun ~key:dtid ~data:k ->
      if Core.Map.mem slots dtid then ()
      else
        match k with
        | Model.Caller (lo, hi) -> see lo hi
        | _ -> ());
  !acc

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  init ();
  match args with
  | [] -> usage Sys.argv.(0) "<binary> [sub-filter]"
  | path :: rest ->
    let filter = match rest with f :: _ -> f | [] -> "" in
    let proj = load_project path in
    let target = Project.target proj in
    let sp = sp_of proj in
    let bin = Filename.basename path in
    let prog =
      Hike.Split_mem.normalize
        (Term.map sub_t (Project.program proj) ~f:(Hike.Jump.compile_sub target)) in
      let counts =
      List.map (fun c -> (c, ref 0))
        [ "EXACT"; "MID"; "FULLSPAN"; "WRAP32"; "NONE"; "ERROR" ] in
    let bump c =
      match List.find_opt (fun (k, _) -> String.equal k c) counts with
      | Some (_, r) -> incr r
      | None -> () in
    let t0 = Unix.gettimeofday () in
    let nsubs = ref 0 in
    Term.enum sub_t prog
    |> Seq.iter ~f:(fun sub ->
        let name = Sub.name sub in
        if filter <> "" && not (String.equal name filter) then ()
        else begin
          incr nsubs;
          (* tid -> (var, block, rhs) for culprit naming. *)
          let defs =
            Term.enum blk_t sub
            |> Seq.concat_map ~f:(fun b ->
                Term.enum def_t b
                |> Seq.map ~f:(fun d ->
                    (Term.tid d, (Var.name (Def.lhs d), Tid.name (Term.tid b),
                                  Format.asprintf "%a" Exp.pp (Def.rhs d)))))
            |> Seq.to_list
          in
          let squash s =
            String.concat " "
              (String.split_on_char '\n'
                 (String.concat " " (String.split_on_char '\n' s |> List.filter (fun l -> not (String.equal (String.trim l) "")))))
            |> fun s -> String.sub s 0 (Int.min 110 (String.length s))
          in
          let name_of t =
            match
              Base.List.find_map defs ~f:(fun (t', (v, blk, rhs)) ->
                  if Tid.equal t t' then
                    Some (Printf.sprintf "%s@%s := %s" v blk (squash rhs))
                  else None)
            with
            | Some s -> s
            | None -> Tid.name t
          in
          match
            (try
               Some
                 (let fixed =
                    Hike.Vsa.fixpoint target sp ~prog:(Project.program proj)
                      ~images:[] ~block_addrs:[] sub
                  in
                  match fixed with
                  | None -> (Tid.Map.empty, Tid.Map.empty)
                  | Some _ ->
                    let sol =
                      Cbat_vsa.static_graph_vsa ~abi:Hike_abi.x86_64_sysv
                        ~resolved:Tid.Map.empty []
                        (Program.create ~subs:[ sub ] ()) sub
                        (Cbat_vsa.init_sol ~abi:Hike_abi.x86_64_sysv sub)
                    in
                    (seam_kinds_of sol sub, Tid.Map.empty))
             with e -> Printf.printf "ERRSUB\t%s\t%s\t%s\n" bin name (describe_exn e); None)
          with
          | None -> bump "ERROR"
          | Some (offsets, _) ->
            let hull = window_hull offsets Tid.Map.empty in
            let wrapped_arm =
              (* the no-extent markers: Mixed tags / wrapped pairs *)
              Core.Map.to_alist offsets
              |> Base.List.exists ~f:(fun (_dtid, k) ->
                  match k with
                  | Model.Mixed _ -> true
                  | Model.Caller (lo, hi) -> Int64.compare lo hi > 0
                  | _ -> false)
            in
            (match hull with
             | None -> bump "NONE"
             | Some w ->
                 let cls = classify_hull w in
                 bump cls;
                 if wrapped_arm && String.equal cls "EXACT" then
                   (* an EXACT hull plus a wrap marker: the marker, not
                      the hull, is the residual imprecision *)
                   Printf.printf "SUB\t%s\t%s\t%s-wrappedarm\t%Ld\n" bin name cls w
                 else
                   Printf.printf "SUB\t%s\t%s\t%s\t%Ld\n" bin name cls w;
                 (* Culprits: every contributor past the capacity. *)
                 Core.Map.iteri offsets
                   ~f:(fun ~key:dtid ~data:k ->
                     match k with
                       | Model.Caller (lo, hi) when Int64.compare lo hi <= 0 ->
                           let ext = Int64.sub hi Model.segment_base in
                           if Int64.compare ext window_bytes > 0 then
                             Printf.printf
                               "CULPRIT\t%s\t%s\tCaller\t%s\t%.16Lx\t%.16Lx\t%Ld\n"
                               bin name (name_of dtid) lo hi ext
                       | Model.Caller (lo, hi) ->
                           Printf.printf
                             "CULPRIT\t%s\t%s\tCallerWrapped\t%s\t%.16Lx\t%.16Lx\n"
                             bin name (name_of dtid) lo hi
                       | Model.Mixed (lo, hi) ->
                           Printf.printf
                             "CULPRIT\t%s\t%s\tMixed\t%s\t%.16Lx\t%.16Lx\n"
                             bin name (name_of dtid) lo hi
                       | _ -> ()))
        end);
    let wall = Unix.gettimeofday () -. t0 in
    Printf.printf "BIN\t%s\tsubs=%d\twall=%.1f" bin !nsubs wall;
    Base.List.iter counts ~f:(fun (k, r) ->
        Printf.printf "\t%s=%d" k !r);
    Printf.printf "\n";
    flush stdout
