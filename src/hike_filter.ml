(* Filter pass: drops non-emittable subs, then splits multi-jmp blocks. *)

open Bap.Std
open Bap.Std.Bil.Types


module StrSet = Set.Make (String)

let is_goto jmp = match Jmp.kind jmp with Goto _ -> true | _ -> false

(* Intrinsics are owned by the emitter; the filter shares the facts. *)
let is_intrinsic = Hike_stack_model.is_intrinsic
let is_emittable_intrinsic = Hike_stack_model.is_emittable_intrinsic

let simplify_jmps sub =
  Term.concat_map blk_t sub ~f:(fun blk ->
      let jmps = Term.enum jmp_t blk |> Seq.to_list in
      match jmps with
      | [ _ ] -> [ blk ]
      | _ ->
        let blk_builder =
          Blk.Builder.init ~copy_phis:true ~copy_defs:true blk
        in
        let children =
          Base.List.filter_map jmps ~f:(fun jmp ->
              if is_goto jmp then (
                Blk.Builder.add_jmp blk_builder jmp;
                None)
              else
                let cond = Jmp.cond jmp in
                let new_jmp = Jmp.with_cond jmp (Int (Word.one 1)) in
                let new_blk = Blk.create ~jmps:[ new_jmp ] () in
                let goto = Jmp.create_goto ~cond (Direct (Term.tid new_blk)) in
                Blk.Builder.add_jmp blk_builder goto;
                Some new_blk)
        in
        let new_blk = Blk.Builder.result blk_builder in
        let new_blk = Term.with_attrs new_blk (Term.attrs blk) in
        children @ [ new_blk ])

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

(* What stays filtered: the intrinsic subs themselves — BAP's bodyless
   @intrinsic:* placeholders are not code; call targets map through
   the emitter's table. *)
let should_filter syms sub =
  (* Emittable intrinsics (the soft-float bodies) stay. *)
  if is_emittable_intrinsic sub then false
  else
    Base.List.mem ~equal:String.equal excluded_subs (Sub.name sub)
    || Term.has_attr sub Sub.stub
    || Term.has_attr sub Sub.extern
    || Term.has_attr sub Sub.entry_point
    || is_intrinsic sub
    || (not @@ StrSet.mem (Sub.name sub) syms)

let filter_subs proj =
  let syms =
    Symtab.to_sequence (Project.symbols proj)
    |> Seq.fold ~init:StrSet.empty ~f:(fun set (name, _, _) ->
        StrSet.add name set)
  in
  Project.map_program proj ~f:(fun prog ->
      Term.filter_map sub_t prog ~f:(fun sub ->
          if should_filter syms sub then
            None
          else
            Some (sub |> simplify_jmps)))
