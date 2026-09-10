(* Filter pass: drops non-emittable subs, then splits multi-jmp blocks. *)

open Bap.Std
open Bap.Std.Bil.Types


module StrSet = Set.Make (String)

let is_goto jmp = match Jmp.kind jmp with Goto _ -> true | _ -> false

(* Intrinsics are owned by the emitter; the filter shares the facts. *)
let is_intrinsic = Bil2llvm.is_intrinsic
let is_emittable_intrinsic = Bil2llvm.is_emittable_intrinsic
let is_llvm_x86_intrinsic = Bil2llvm.is_llvm_x86_intrinsic

let simplify_jmps sub =
  let new_sub =
    Sub.Builder.create ~tid:(Term.tid sub) ~name:(Sub.name sub) ()
  in
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun blk ->
      let jmps = Term.enum jmp_t blk in
      if Seq.length jmps = 1 then Sub.Builder.add_blk new_sub blk
      else
        let blk_builder =
          Blk.Builder.init ~copy_phis:true ~copy_defs:true blk
        in
        Seq.iter jmps ~f:(fun jmp ->
            if is_goto jmp then Blk.Builder.add_jmp blk_builder jmp
            else
              let cond = Jmp.cond jmp in
              let new_jmp = Jmp.with_cond jmp (Int (Word.one 1)) in
              let new_blk = Blk.create ~jmps:[ new_jmp ] () in
              Sub.Builder.add_blk new_sub new_blk;
              let goto = Jmp.create_goto ~cond (Direct (Term.tid new_blk)) in
              Blk.Builder.add_jmp blk_builder goto);
        let new_blk = Blk.Builder.result blk_builder in
        (* Copies block attrs. *)
        let new_blk = Term.with_attrs new_blk (Term.attrs blk) in
        Sub.Builder.add_blk new_sub new_blk);
  let res = Sub.Builder.result new_sub in
  (* Copies sub attrs. *)
  Term.with_attrs res (Term.attrs sub)

(* CRT and unwinding stubs carry no convertible code. *)
let excluded_subs =
  [
    "_init";
    "_fini";
    "__cxa_finalize";
    "_start";
    "__libc_start_main";
    "register_tm_clones";
    "deregister_tm_clones";
    "__do_global_dtors_aux";
    "frame_dummy";
  ]

(* FP instructions modeled as soft-float calls. *)
let calls_intrinsic prog =
  let callgraph = Program.to_graph prog in
  let visit_edge _ edge filter_set =
    let caller = Graphs.Callgraph.Edge.src edge in
    let callee = Graphs.Callgraph.Edge.dst edge in
    let term = Term.find sub_t prog callee in
    if
      Base.Option.value_map term ~default:false ~f:(fun term ->
          is_intrinsic term
          && not (is_emittable_intrinsic term)
          && not (is_llvm_x86_intrinsic term))
    then Core.Set.add filter_set caller
    else filter_set
  in
  Graphlib.Std.Graphlib.depth_first_search
    (module Graphs.Callgraph)
    callgraph ~init:Tid.Set.empty ~enter_edge:visit_edge

let should_filter filter_set syms sub =
  (* Emittable intrinsics stay; their calls inline. *)
  if is_emittable_intrinsic sub then false
  else
    Base.List.mem ~equal:String.equal excluded_subs (Sub.name sub)
    || Term.has_attr sub Sub.stub
    || Term.has_attr sub Sub.extern
    || Term.has_attr sub Sub.entry_point
    || is_intrinsic sub
    || Core.Set.mem filter_set (Term.tid sub)
    || (not @@ StrSet.mem (Sub.name sub) syms)

let filter_subs proj =
  let syms =
    Symtab.to_sequence (Project.symbols proj)
    |> Seq.fold ~init:StrSet.empty ~f:(fun set (name, _, _) ->
        StrSet.add name set)
  in
  Project.map_program proj ~f:(fun prog ->
      let filter_set = calls_intrinsic prog in
      Term.filter_map sub_t prog ~f:(fun sub ->
          if should_filter filter_set syms sub then
            None
          else
            Some (sub |> simplify_jmps)))
