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

(* The intrinsic-callers exclusion is DELETED (T10 part 1): it was a
   relic of the incomplete-FP-table era, and already structurally dead —
   [is_emittable_intrinsic] and [is_llvm_x86_intrinsic] partition the
   intrinsics by body-ness, so the exclusion's predicate was a
   contradiction and the set it built was always empty.  Callers of
   intrinsics lift; the promotion, thunks, and window lanes are
   callee-agnostic.  What stays filtered: the intrinsic SUBS themselves
   (BAP's bodyless @intrinsic:* placeholders are not code — call TARGETS
   map through the emitter's table; the placeholder subs are never
   lifted). *)
let should_filter syms sub =
  (* Emittable intrinsics (the soft-float bodies) stay; their calls
     inline. *)
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
