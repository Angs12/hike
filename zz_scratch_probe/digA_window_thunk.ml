(* digA: the outgoing-window store path for one sub — the post-rewrite
   (pre-DCE) defs of the call block, stage_a's site bindings, and the
   same defs after Hike_dce.dce.  Proves where the outgoing stores go. *)
open Bap.Std
open Bap_core_theory

module A = Hike.Sections
module S = Hike.Stack_model
module Hv = Hike.Vsa

let dump_defs ~label (sub : sub term) =
  Printf.printf "=== %s ===\n" label;
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun blk ->
      let has_call =
        Term.enum jmp_t blk
        |> Seq.exists ~f:(fun j -> match Jmp.kind j with Call _ -> true | _ -> false)
      in
      if has_call then begin
        Printf.printf "BLOCK %s:\n" (Tid.name (Term.tid blk));
        Term.enum def_t blk
        |> Seq.iter ~f:(fun d ->
            Printf.printf "  DEF %s lhs=%s: %s\n" (Tid.name (Term.tid d))
              (Var.name (Def.lhs d))
              (Format.asprintf "%a" Exp.pp (Def.rhs d)))
      end)

let () =
  Bap_main.init ~argv:[| Sys.executable_name |] () |> ignore;
  let path = Sys.argv.(1) in
  let want = Sys.argv.(2) in
  let proj = Probe_common.load_project path in
  let target = Project.target proj in
  let abi = Hike_abi.of_target target in
  let sp = Probe_common.sp_of proj in
  let symtab = Some (Project.symbols proj) in
  let prog =
    Hike.Split_mem.normalize
      (Term.map sub_t (Project.program proj) ~f:(Hike.Jump.compile_sub target))
  in
  let sub =
    Term.enum sub_t prog
    |> Seq.find_exn ~f:(fun s -> String.equal (Sub.name s) want)
  in
  let envs, _sub' = Hv.fixpoint target sp ~prog ~images:[] ~block_addrs:[] sub
    |> Base.Option.value ~default:(Tid.Map.empty, sub) in
  let all_envs =
    Core.Map.fold envs ~init:Tid.Map.empty
      ~f:(fun ~key ~data m -> Core.Map.set m ~key ~data)
  in
  Hike.Kb.install_run ~block_envs:all_envs;
  let ctx =
    A.attribute ~word:8 ~entry:S.segment_base ~abi ~spans:[]
      ~denote:Hv.denote_exp_at (Program.create ~subs:[ sub ] ())
  in
  (* stage_a: the call-site correspondence for this sub. *)
  let sites = A.stage_a ~word:8 ~abi ~sp ~denote:Hv.denote_exp_at sub in
  Core.Map.iteri sites ~f:(fun ~key:btid ~data:bs ->
      Printf.printf "SITE %s: %d binding(s)\n" (Tid.name btid) (Base.List.length bs);
      Base.List.iter bs ~f:(fun b ->
          Printf.printf "  slot %d full=%b def=%s\n" b.A.sb_slot b.A.sb_full
            (Tid.name (Term.tid b.A.sb_def))));
  let prog2 =
    Term.map sub_t (Program.create ~subs:[ sub ] ())
      ~f:(A.stamp_tags ctx)
    |> A.rewrite_program ~word:8 ~entry:S.segment_base ~abi ~sp
         ~symtab:None ~spans:[] ~denote:Hv.denote_exp_at ~ctx
  in
  let sub2 =
    Term.enum sub_t prog2 |> Seq.find_exn ~f:(fun s -> String.equal (Sub.name s) want)
  in
  dump_defs ~label:"POST-REWRITE (pre-DCE)" sub2;
  let sub3 = Hike.Dce.dce ~target sub2 in
  dump_defs ~label:"POST-DCE" sub3
