(* The emission signature, and the home of each lane's TYPE.  Every sub's
   arguments and returns are computed once here and written onto the sub's
   own [arg] terms (the returns are the [Out] intents); each lane carries
   its pointer-ness.  The emitter reads them off the sub — no side table. *)

open Bap.Std

module Model = Hike_stack_model
module Abi = Hike_abi

let is_fp_returning ~(abi : Abi.t) (sub : sub term) : bool =
  let is_value_reg v =
    Abi.is_return_reg abi v || Abi.is_vector_param_reg abi v
  in
  let is_epilogue blk =
    Term.enum jmp_t blk
    |> Seq.exists ~f:(fun j ->
        match Jmp.kind j with
        | Call _ when Hike_return.is_jmp j -> true
        | Call c -> (
            match Call.target c with
            | Indirect _ -> Option.is_none (Call.return c)
            | _ -> false)
        | _ -> false)
  in
  let value_defs blk =
    Term.enum def_t blk
    |> Seq.fold ~init:[] ~f:(fun acc d ->
        if is_value_reg (Def.lhs d) then d :: acc else acc)
  in
  let cfg = Sub.to_graph sub in
  let blocks =
    Term.enum blk_t sub
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun acc blk ->
           Core.Map.set acc ~key:(Term.tid blk) ~data:blk)
  in
  let return_path_defs =
    Term.enum blk_t sub
    |> Seq.fold ~init:[] ~f:(fun acc blk ->
        if not (is_epilogue blk) then acc
        else
          let preds = Graphs.Tid.Node.preds (Term.tid blk) cfg in
          let pred_defs =
            Seq.fold preds ~init:[] ~f:(fun acc p ->
                match Core.Map.find blocks p with
                | Some pb -> value_defs pb @ acc
                | None -> acc)
          in
          value_defs blk @ pred_defs @ acc)
  in
  Base.List.exists return_path_defs ~f:(fun d ->
      Abi.is_vector_param_reg abi (Def.lhs d))

(* A lane is a pointer when it is an address lane: a by-reference
   argument, a memory var (its storage), or the caller window. *)
let tag_lane (a : Arg.t) : Arg.t =
  let v = Arg.lhs a in
  if
    Arg.intent a = Some Both
    || Model.is_mem v
    || Model.is_window_var v
  then Model.set_ptr_arg a
  else a

let compute_sub_sig (target : Bap_core_theory.Theory.Target.t)
    (sub : sub term) : Arg.t list * Arg.t list =
  let abi = Abi.of_target target in
  let free_vars = Model.free_regs sub in
  let rets =
    (if Abi.is_primary_target target then abi.return_regs else [])
    |> Base.List.map ~f:(fun reg -> Arg.create ~intent:Out reg (Var reg))
  in
  let rets =
    (* Double returns arrive via [%YMM0]. *)
    if is_fp_returning ~abi sub then
      let ymm0 = Abi.fp_return_reg abi in
      rets @ [ Arg.create ~intent:Out ymm0 (Var ymm0) ]
    else rets
  in
  let rets, args =
    (* A sub reading its incoming window carries the caller-window
       base: its above-entry accesses materialize against the
       caller's frame. *)
    let window_arg =
      match Term.get_attr sub Model.layout_tag with
      | Some { Model.window_param = true; _ } ->
        let w = abi.Abi.word in
        [ Arg.create ~intent:In (Model.hike_window_var ~word:w)
            (Bil.Var (Model.hike_window_var ~word:w)) ]
      | _ -> []
    in
    if Model.is_emittable_intrinsic sub then begin
      let args =
        Base.List.map free_vars ~f:(fun reg -> Arg.create ~intent:In reg (Var reg))
      in
      let rets =
        Term.enum blk_t sub
        |> Seq.fold ~init:[] ~f:(fun acc blk ->
            Term.enum def_t blk
            |> Seq.fold ~init:acc ~f:(fun acc d ->
                let v = Def.lhs d in
                let is_input =
                  Base.List.exists free_vars ~f:(fun fv -> Var.same fv v)
                in
                let already =
                  Base.List.exists acc ~f:(fun a -> Var.same (Arg.lhs a) v)
                in
                if is_input || already then acc
                else Arg.create ~intent:Out v (Var v) :: acc))
      in
      (rets, args)
    end
    else if Model.fixed_signature sub then
      let rdi, rsi = Abi.argc_argv_regs abi in
      let args =
        [
          Arg.create ~intent:In rdi (Var rdi);
          Arg.create ~intent:In rsi (Var rsi);
        ]
      in
      (rets, args)
    else
      (* The signature transcribes the sub term's own BIR args
         (promoted slots included). *)
      let arg_terms = Term.enum arg_t sub |> Base.Sequence.to_list in
      let args =
        (* Non-parameters sort after every convention register; the
           register list is hoisted out of the sort comparator. *)
        let nonparam_rank = 100 in
        let param_regs = Abi.param_regs abi in
        let rank_of_var (v : var) : int * string =
          let n = Var.name (Var.base v) in
          match Base.List.findi param_regs ~f:(fun _ r -> Var.same r v) with
          | Some (i, _) -> (i, n)
          | None -> (nonparam_rank, n)
        in
        Base.List.filter free_vars ~f:(fun reg ->
            let n = Var.name (Var.base reg) in
            let is_callee_saved = Abi.is_callee_saved abi reg in
            (* Filters non-parameter lanes: callee-saved regs, the
               self-basing TLS base, the emitter's own promoted
               names. *)
            not
              (Var.same reg (Abi.sp target)
              || Var.same reg abi.thread_pointer
              || is_callee_saved
              || Hike_abi.is_intrinsic_name n
              || Model.is_arg_slot (Var.base reg)
              || Model.is_call_arg (Var.base reg)))
        |> Base.List.sort ~compare:(fun a b ->
            let ra, na = rank_of_var a in
            let rb, nb = rank_of_var b in
            match Int.compare ra rb with
            | 0 -> String.compare na nb
            | c -> c)
        |> Base.List.map ~f:(fun reg -> Arg.create ~intent:In reg (Var reg))
        |> fun regs -> regs @ arg_terms
      in
      (* A call can consume an incoming register that the BIL body never
         mentions; retain the complete native integer-parameter ABI. *)
      let has_call =
        let is_native_call c =
          match Call.target c with
          | Indirect _ -> true
          | Direct t ->
              not (Hike_return.is_target t && Option.is_none (Call.return c))
        in
        Term.enum blk_t sub
        |> Seq.exists ~f:(fun blk ->
               Term.enum jmp_t blk
               |> Seq.exists ~f:(fun j ->
                      match Jmp.kind j with
                      | Call c -> is_native_call c
                      | _ -> false))
      in
      let args =
        if has_call then
          let is_plt_sig = args = [] in
          let params =
            if is_plt_sig then Abi.param_regs abi else abi.Abi.int_param_regs
          in
          let is_param v = Base.List.exists params ~f:(Var.same v) in
          let param_args =
            Base.List.map params ~f:(fun reg ->
                Arg.create ~intent:In reg (Var reg))
          in
          let other_args =
            Base.List.filter args ~f:(fun arg -> not (is_param (Arg.lhs arg)))
          in
          param_args @ other_args
        else args
      in
      (rets, args @ window_arg)
  in
  ( Base.List.map rets ~f:tag_lane,
    Base.List.map args ~f:tag_lane )

(* The program-level entry: the pipeline's pass, and any direct emitter
   caller (the fixtures), run exactly this. *)
let sign_program ~(target : Bap_core_theory.Theory.Target.t)
    (prog : program term) : program term =
  Term.map sub_t prog ~f:(fun sub ->
      let rets, args = compute_sub_sig target sub in
      Model.set_sig sub (rets @ args))

(* The pass: write every sub's signature, with its lane types, onto the
   sub's own [arg] terms. *)
let run (proj : Project.t) : Project.t =
  let target = Project.target proj in
  Project.map_program proj ~f:(fun prog -> sign_program ~target prog)
