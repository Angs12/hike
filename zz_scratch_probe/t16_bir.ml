(* Replicates the pass chain (filter -> jump -> vsa ->
   stack-to-locals -> dce) on one sub and dumps the post-pipeline BIR.
   Usage: t16_bir.exe <binary> [subname] *)

open Bap.Std
open Probe_common

module Vsa = Hike.Vsa
module Cvsa = Cbat_vsa
module Model = Hike.Stack_model

let dump_sub (s : sub term) : unit =
  Printf.printf "== sub %s\n" (Sub.name s);
  Seq.iter (Term.enum arg_t s) ~f:(fun a ->
      Printf.printf "  arg %s\n" (Var.name (Arg.lhs a)));
  Seq.iter (Term.enum blk_t s) ~f:(fun blk ->
      Printf.printf " -- blk %s\n" (Tid.name (Term.tid blk));
      Seq.iter (Term.enum def_t blk) ~f:(fun d ->
          Printf.printf "    %s := %s\n"
            (Var.name (Def.lhs d))
            (Format.asprintf "%a" Exp.pp (Def.rhs d)));
      Seq.iter (Term.enum jmp_t blk) ~f:(fun j ->
          let kind = match Jmp.kind j with
            | Goto (Direct t) -> Printf.sprintf "goto %s" (Tid.name t)
            | Goto (Indirect e) -> Printf.sprintf "goto %s" (Format.asprintf "%a" Exp.pp e)
            | Ret (Direct t) -> Printf.sprintf "ret %s" (Tid.name t)
            | Ret (Indirect e) -> Printf.sprintf "ret %s" (Format.asprintf "%a" Exp.pp e)
            | Call c ->
              let t = match Call.target c with
                | Direct t -> Printf.sprintf "direct %s" (Tid.name t)
                | Indirect e -> Printf.sprintf "indirect %s" (Format.asprintf "%a" Exp.pp e) in
              Printf.sprintf "call %s" t
            | Int _ -> "int" in
          let cond = Format.asprintf "%a" Exp.pp (Jmp.cond j) in
          Printf.printf "    jmp %s  if %s\n" kind cond))

let () =
  let args = match Array.to_list Sys.argv with _ :: rest -> rest | [] -> [] in
  let path = match args with p :: _ -> p | [] -> exit 0 in
  let name = match args with _ :: n :: _ -> n | _ -> "main" in
  init ();
  let proj = load_project path in
  let prog = Project.program proj in
  let target = Project.target proj in
  let sp = sp_of proj in
  let sub = match find_sub prog name with
    | Some s -> s | None -> Printf.eprintf "no sub %s\n" name; exit 1 in
  (match args with
   | _ :: _ :: "sol" :: _ ->
     (* Solution diff: raw vs compiled fixpoint. *)
     let compiled = Hike.Jump.compile_sub target sub in
     let dump_sol (tag : string) (sub : sub term) =
       let prog' = Program.create ~subs:[ sub ] () in
       let sol = Cvsa.static_graph_vsa ~abi:Hike_abi.x86_64_sysv [] prog' sub (Cvsa.init_sol ~abi:Hike_abi.x86_64_sysv sub) in
       Printf.printf "=== sol %s ===\n%!" tag;
       Seq.iter (Term.enum blk_t sub) ~f:(fun blk ->
           let st = Graphlib.Std.Solution.get sol (Term.tid blk) in
           let regs =
             Seq.filter (Term.enum def_t blk) ~f:(fun d ->
                 let n = Var.name (Def.lhs d) in
                 n = "RDX" || n = "RAX" || n = "RSP")
             |> Seq.map ~f:(fun d -> Var.name (Def.lhs d))
             |> Seq.to_list in
           let vals =
             Base.List.filter_map regs ~f:(fun rn ->
                 match
                   Seq.find (Term.enum def_t blk) ~f:(fun d ->
                       String.equal (Var.name (Def.lhs d)) rn)
                 with
                 | Some d ->
                   (match
                      Cvsa.Test_seam.denote_imm_exp (Bil.Var (Def.lhs d)) st
                    with
                    | Ok ws ->
                      Some (Printf.sprintf "%s=%s" rn
                              (if Cvsa.WordSet.is_top ws then "TOP"
                               else if Cvsa.WordSet.is_bottom ws then "BOT"
                               else
                                 (match
                                    Cvsa.WordSet.min_elem ws,
                                    Cvsa.WordSet.max_elem ws
                                  with
                                  | Some a, Some b ->
                                    Printf.sprintf "[%Ld..%Ld]"
                                      (Cbat_word.to_int64_exn a)
                                      (Cbat_word.to_int64_exn b)
                                  | _ -> "?")))
                    | Error _ -> None)
                 | None -> None)
           in
           Printf.printf "  %s %s\n%!" (Tid.name (Term.tid blk))
             (Stdlib.String.concat " " vals))
     in
     dump_sol "raw" sub;
     dump_sol "compiled" compiled;
     exit 0
   | _ -> ());
  (* filter: keep the sub as-is (the named-exclusion lane is per-sub) *)
  let sub = Hike.Jump.compile_sub target sub in
  Printf.printf "===== AFTER JUMP =====\n";
  dump_sub sub;
  ignore (Vsa.fixpoint target sp ~prog:(Project.program proj) ~images:[] ~block_addrs:[] sub);
  let sol =
    Cbat_vsa.static_graph_vsa ~abi:Hike_abi.x86_64_sysv ~resolved:Tid.Map.empty []
      (Program.create ~subs:[ sub ] ()) sub
      (Cbat_vsa.init_sol ~abi:Hike_abi.x86_64_sysv sub)
  in
  let kind_str (kind : Model.vsa_kind) = match kind with
    | Model.Range (a,b) -> Printf.sprintf "Range(%Ld,%Ld)" a b
    | Model.Infinite (a,b) -> Printf.sprintf "Infinite(%Ld,%Ld)" a b
    | Model.Caller (a,b) -> Printf.sprintf "Caller(%Ld,%Ld)" a b
    | Model.Mixed (a,b) -> Printf.sprintf "Mixed(%Ld,%Ld)" a b
    | Model.Dead -> "Dead" in
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun blk ->
      Seq.iter (Term.enum def_t blk) ~f:(fun d ->
          let opt (r : ('a, 'b) Result.t) : 'a option =
            match r with Ok w -> Some w | Error _ -> None in
          let kind =
            let open Base.Option in
            Base.Option.bind
              (Cbat_vsa.Cbat_extraction.stack_address_of_rhs (Def.rhs d))
              ~f:(fun addr ->
                opt
                  (Cbat_vsa.denote_exp_at
                     ~pre:(Graphlib.Std.Solution.get sol (Term.tid blk))
                     ~blk ~def:d addr))
            >>= fun ws ->
            if Ws.is_bottom ws || Ws.in_stack_segment ws then
              Some
                (Cbat_vsa.Cbat_extraction.caller_split
                   (Cbat_vsa.Cbat_extraction.classify ws))
            else if Ws.is_top ws then Some Model.unbounded_span
            else None
          in
          match kind with
          | Some kind -> Printf.printf "TAG %s %s\n%!" (Tid.name (Term.tid d)) (kind_str kind)
          | None -> ()));
  let sub =
    Model.stamp_dyn_allocs
      ~dynamic_alloc_tids:(Hike.Sections.dynamic_alloc_tids_of ~sp ~denote:Hike.Vsa.denote_exp_at sub) sub in
  let abi = Hike_abi.of_target target in
  (* The T2 chain: the attribution owns the promotion, the rewrite, and
     the layout. *)
  Hike.Kb.install_run ~block_envs:Tid.Map.empty;
  let prog = Program.create ~subs:[ sub ] () in
  let ctx =
    Hike.Sections.attribute ~word:8 ~entry:Model.segment_base ~abi ~spans:[]
      ~denote:Hike.Vsa.denote_exp_at prog
  in
  let prog = Term.map sub_t prog ~f:(Hike.Sections.stamp_tags ctx) in
  let prog =
    Hike.Sections.rewrite_program ~word:8 ~entry:Model.segment_base ~abi ~sp
      ~symtab:None ~spans:[] ~denote:Hike.Vsa.denote_exp_at ~ctx
      prog
  in
  let sub = Term.first sub_t prog |> Base.Option.value_exn in
  Printf.printf "===== AFTER ATTRIBUTION =====\n";
  dump_sub sub;
  let sub = Hike.Dce.dce ~target sub in
  Printf.printf "===== AFTER DCE =====\n";
  dump_sub sub
