(* The strip-canaries lane's emit driver: the production pipeline in
   process — filter, jump, split-mem, vsa, [strip-canaries],
   lift-sections + dce, the LLVM emission — with the strip switchable,
   so the corpus A/B (strip vs no-strip) diffs byte-identical modules.
   Usage: canary_emit.exe <out.ll> strip|nostrip <binary> *)

open Bap.Std
open Bap_core_theory
open Probe_common

module Abi = Hike_abi
module Sections = Hike__Hike_sections
module Benv = Hike__Bil2llvm_env
open Benv
module Model = Hike.Stack_model

let map_subs f proj = Project.map_program proj ~f:(fun prog -> Term.map sub_t prog ~f)

let run ~strip (path : string) (out : string) : unit =
  let proj = load_project path in
  let target = Project.target proj in
  Hike__Hike_vsa.set_addr_bits (Abi.addr_size_bits target);
  let proj = Hike__Hike_filter.filter_subs proj in
  let proj = map_subs (Hike.Jump.compile_sub target) proj in
  let proj = Project.map_program proj ~f:Hike.Split_mem.normalize in
  (* The vsa pass: the record built complete at one site. *)
  let abi = Abi.of_target target in
  let prog = Project.program proj in
  let images =
    Sections.get_section_mem
      ("." ^ Benv.section_type_to_string Benv.RODATA)
      proj
    |> Sections.get_section_data
    |> Base.Option.map ~f:(fun (arr, min_addr, max_addr) ->
        [ { Hike.Vsa.img_lo = Word.to_int64_exn min_addr;
            img_hi = Word.to_int64_exn max_addr;
            img_bytes = arr } ])
    |> Base.Option.value ~default:[]
  in
  let symtab = Some (Project.symbols proj) in
  let acc =
    Term.enum sub_t prog
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun acc sub ->
        let envs, sub' =
          Hike.Vsa.fixpoint target (Abi.sp target) ~prog
            ~images ~block_addrs:[] sub
          |> Base.Option.value ~default:(Tid.Map.empty, sub)
        in
        Core.Map.set acc ~key:(Term.tid sub) ~data:(envs, sub'))
  in
  let all_envs =
    Core.Map.fold acc ~init:Tid.Map.empty
      ~f:(fun ~key:_ ~data:(envs, _) m ->
        Core.Map.fold envs ~init:m
          ~f:(fun ~key ~data m' -> Core.Map.set m' ~key ~data))
  in
  Hike.Kb.install_run ~block_envs:all_envs;
  let dyn_allocs =
    Term.enum sub_t prog
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m sub ->
           Core.Map.set m ~key:(Term.tid sub)
             ~data:(Hike.Sections.dynamic_alloc_tids_of ~sp:(Abi.sp target)
                ~denote:Hike.Vsa.denote_exp_at sub))
  in
  let prog =
    Term.map sub_t prog ~f:(fun sub ->
        let sub =
          match Core.Map.find acc (Term.tid sub) with
          | Some (_, sub') -> sub'
          | None -> sub
        in
        Model.stamp_dyn_allocs
          ~dynamic_alloc_tids:
            (Option.value (Core.Map.find dyn_allocs (Term.tid sub))
               ~default:Tid.Set.empty)
          sub)
  in
  (* The canary strip: on/off is the A/B switch. *)
  let prog =
    if strip then
      let names =
        Term.enum sub_t prog
        |> Seq.fold ~init:Tid.Map.empty ~f:(fun mm s ->
            Core.Map.set mm ~key:(Term.tid s) ~data:(Sub.name s))
      in
      Term.map sub_t prog ~f:(Hike.Strip_canaries.strip_sub ~abi ~names)
    else prog
  in
  (* The attribution: the trees and slim tags, then the rewrite. *)
  let ptrsize = Theory.Target.bits target in
  let word = ptrsize / 8 in
  let entry = Model.segment_base in
  let sp = Abi.sp target in
  let spans = Hike.attrib_spans ~word proj in
  let ctx =
    Hike.Sections.attribute ~word ~entry ~abi ~spans
      ~denote:Hike.Vsa.denote_exp_at prog
  in
  let prog = Term.map sub_t prog ~f:(Hike.Sections.stamp_tags ctx) in
  let prog =
    Hike.Sections.rewrite_program ~word ~entry ~abi ~sp ~symtab ~spans
      ~denote:Hike.Vsa.denote_exp_at ~ctx prog
  in
  (* The DCE over the rewrite's vars. *)
  let prog = Term.map sub_t prog ~f:(Hike.Dce.dce ~target) in
  (* The emission (the convlir pass's body): the spec from the one
     builder, the copy-reloc slot list beside it. *)
  let llvm_ctx = Llvm.create_context () in
  let llvm_module = Llvm.create_module llvm_ctx "Convlir" in
  Hike.Bil2llvm.emit_program llvm_ctx llvm_module
    ~target ~ptrsize
    ~symtab:(Some (Project.symbols proj))
    ~copy_relocs:(Hike.copy_reloc_slot_addrs proj)
    (Hike.section_spec_of ~word
       ~comps:(Hike.Sections.global_comps_of ~word ~spans ctx)
       ~whole:(Hike.Sections.whole_comps_of ~word ~spans ctx) proj)
    prog;
  Llvm.print_module out llvm_module;
  Llvm.dispose_module llvm_module;
  Llvm.dispose_context llvm_ctx

let () =
  match Base.List.drop (Array.to_list Sys.argv) 1 with
  | [ out; mode; path ] ->
    init ();
    run ~strip:(String.equal mode "strip") path out
  | _ -> usage Sys.argv.(0) "<out.ll> strip|nostrip <binary>"
