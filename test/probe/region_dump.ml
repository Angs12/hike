(* The region inspector: the attribution's per-sub bindings, one line
   per (range, storage, member count).  vsa-debug only.
   Usage: region_dump.exe <binary> [<sub-name>] *)
open Bap.Std
open Probe_common

module Vsa = Cbat_vsa
module Hv = Hike.Vsa

let dump_sub ~(word : int) (proj : Project.t) (sub : sub term) : unit =
  let envs, sub', _ =
    Hv.fixpoint (Project.target proj)
      ~lookup:(fun _ -> None) ~images:[]
      ~written:(Hv.kill_summaries ~abi:Hike.Abi.x86_64_sysv
                  (Program.create ~subs:[ sub ] ()))
      ~lift_at:(fun _ ~block_addrs:_ -> None)
      ~block_addrs:(Core.Map.empty (module Addr)) sub
  in
  let () =
    Hike.Kb.install
      (Hike.Kb.build ~block_envs:envs
         ~block_addrs:(Core.Map.empty (module Addr))
         ~target:(Project.target proj)
         ~lookup:(fun _ -> None))
  in
  let facts = Hike.Kb.facts () in
  let sub = Hike.Def_slots.(fun s -> s) sub' in
  let dyn_tids =
    Hike.Sections.dynamic_alloc_tids_of ~facts sub in
  let sub = Hike.Def_slots.stamp_dyn_allocs ~dynamic_alloc_tids:dyn_tids sub in
  let meta = Hike.Sections.sec_meta ~word proj in
  let spans = Hike.Sections.attrib_spans ~meta in
  let ctx =
    Hike.Sections.attribute ~facts ~word
      ~entry:Hike.Stack_model.segment_base ~spans
      (Program.create ~subs:[ sub ] ())
  in
  Printf.printf "sub %s: regions\n%!" (Sub.name sub);
  match Core.Map.find ctx.Hike.Sections.sub_trees (Term.tid sub) with
  | None -> Printf.printf "  (no tree)\n%!"
  | Some tree ->
    Hike.Sections.Tree.to_sequence tree
    |> Seq.iter ~f:(fun (k, rs) ->
        let storage =
          match rs.Hike.Sections.storage with
          | Hike.Sections.Stack_region n -> Printf.sprintf "region%d" n
          | Hike.Sections.Stack_residue -> "residue"
          | Hike.Sections.Arg_slot i -> Printf.sprintf "slot%d" i
          | Hike.Sections.Data_region n -> Printf.sprintf "data%d" n
        in
        let identity =
          Base.List.count rs.Hike.Sections.members
            ~f:(fun mm -> mm.Hike.Sections.m_identity) in
        Printf.printf "  [%s %Ld .. %s %Ld] %s members=%d identity=%d\n%!"
          (Hike.Stack_model.sec_name k.Hike.Sections.lo.p_sec)
          k.Hike.Sections.lo.p_pos
          (Hike.Stack_model.sec_name k.Hike.Sections.hi.p_sec)
          k.Hike.Sections.hi.p_pos
          storage
          (Base.List.length rs.Hike.Sections.members)
          identity;
        Base.List.iter rs.Hike.Sections.members
          ~f:(fun mm ->
            if mm.Hike.Sections.m_identity then
              match mm.Hike.Sections.m_def with
              | None ->
                Printf.printf "    identity (escape) [%Ld..%Ld]\n%!"
                  mm.Hike.Sections.m_lo mm.Hike.Sections.m_hi
              | Some dtid ->
                let rhs =
                  Term.enum blk_t sub
                  |> Seq.concat_map ~f:(Term.enum def_t)
                  |> Seq.find_map ~f:(fun d ->
                         if Tid.equal (Term.tid d) dtid then Some (Def.rhs d)
                         else None)
                in
                let rhs_str =
                  match rhs with
                  | None -> "(def not in sub)"
                  | Some e ->
                    let bs = Buffer.create 300 in
                    let fmt = Format.formatter_of_buffer bs in
                    Format.pp_set_margin fmt 1_000_000;
                    Format.fprintf fmt "%a" Exp.pp e;
                    Format.pp_print_flush fmt ();
                    Buffer.contents bs
                in
                let blk_of_def_rhs re =
                  Term.enum blk_t sub
                  |> Seq.find_map ~f:(fun b ->
                         Term.enum def_t b
                         |> Seq.find_map ~f:(fun d ->
                                if Tid.equal (Term.tid d) dtid then Some (b, d)
                                else None))
                in
                let addr_str =
                  match rhs with
                  | Some e -> (
                      match Hike.Stack_model.addr_of_rhs e with
                      | Some (a, _) -> (
                        let blk_of_def =
                          Term.enum blk_t sub
                          |> Seq.find ~f:(fun b ->
                                 Term.enum def_t b
                                 |> Seq.exists ~f:(fun d ->
                                        Tid.equal (Term.tid d) dtid))
                        in
                        let ws =
                          match blk_of_def with
                          | Some b -> (
                              match
                                facts.Hike.Kb.denote ~blk:b
                                  ~def:(Base.Option.value_exn
                                          (Term.find def_t b dtid))
                                  a
                              with
                              | Ok w -> w
                              | Error _ -> Ws.top 64)
                          | None -> Ws.top 64
                        in
                        let kind =
                          match Ws.stack_offsets ws with
                          | Some offs -> (
                              match
                                (Ws.Clp.min_elem offs, Ws.Clp.max_elem offs)
                              with
                              | Some a2, Some b2 ->
                                Printf.sprintf "stackoff[%s..%s]"
                                  (Cbat_word.to_string a2)
                                  (Cbat_word.to_string b2)
                              | _ -> "stackoff-no-extrema")
                          | None ->
                            Printf.sprintf "plain top=%b min=%s"
                              (Ws.is_top ws)
                              (match Ws.min_elem ws with
                               | Some v -> Cbat_word.to_string v
                               | None -> "none")
                        in
                        "addr=" ^ kind)
                      | None -> "addr=none")
                  | None -> ""
                in
                let rax_str =
                  match blk_of_def_rhs rhs with
                  | Some (b, d) -> (
                      match
                        facts.Hike.Kb.denote ~blk:b ~def:d
                          (Bil.Var
                             (Var.create ~is_virtual:false ~fresh:false "RAX"
                                (Type.Imm 64)))
                      with
                      | Error _ -> "rax=err"
                      | Ok w -> (
                          match Ws.stack_offsets w with
                          | Some offs -> (
                              match
                                (Ws.Clp.min_elem offs, Ws.Clp.max_elem offs)
                              with
                              | Some a2, Some b2 ->
                                Printf.sprintf "rax=stackoff[%s..%s]"
                                  (Cbat_word.to_string a2)
                                  (Cbat_word.to_string b2)
                              | _ -> "rax=stackoff-no-extrema")
                          | None ->
                            Printf.sprintf "rax=plain top=%b"
                              (Ws.is_top w)))
                  | None -> ""
                in
                Printf.printf "    identity def %s [%Ld..%Ld] %s %s rhs=%s\n%!"
                  (Tid.name dtid) mm.Hike.Sections.m_lo mm.Hike.Sections.m_hi
                  addr_str rax_str rhs_str))

let () =
  init ();
  match List.tl (Array.to_list Sys.argv) with
  | bin :: rest ->
    let proj = load_project bin in
    let word = (Hike.Abi.of_target (Project.target proj)).Hike_abi.word in
    let name = match rest with n :: _ -> n | [] -> "main" in
    (match find_sub (Project.program proj) name with
     | None -> Printf.eprintf "no sub %s\n%!" name
     | Some sub -> dump_sub ~word proj sub)
  | _ -> usage Sys.argv.(0) "<binary> [<sub-name>]"
