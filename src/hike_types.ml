(* The emission signature, and the home of each lane's TYPE.  Every sub's
   arguments and returns are computed once here and written onto the sub's
   own [arg] terms (the returns are the [Out] intents); each lane carries
   its pointer-ness.  The emitter reads them off the sub — no side table. *)

open Bap.Std

module Model = Hike_stack_model
module Abi = Hike_abi

let free_vars sub =
  Sub.free_vars sub
  |> Core.Set.filter ~f:(fun var -> not @@ Model.is_mem var)
  |> Core.Set.to_list

let fp_returning ~(abi : Abi.t) (sub : sub term) : bool =
  let is_value_reg v =
    Base.List.mem Abi.value_return_names (Var.name (Var.base v))
      ~equal:String.equal
    || Abi.is_vector_param_reg abi v
  in
  let is_epilogue blk =
    Term.enum jmp_t blk
    |> Seq.exists ~f:(fun j ->
        match Jmp.kind j with
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
  let return_path_defs =
    Term.enum blk_t sub
    |> Seq.fold ~init:[] ~f:(fun acc blk ->
        if not (is_epilogue blk) then acc
        else
          let preds = Graphs.Tid.Node.preds (Term.tid blk) cfg in
          let pred_defs =
            Seq.fold preds ~init:[] ~f:(fun acc p ->
                match Term.find blk_t sub p with
                | Some pb -> value_defs pb @ acc
                | None -> acc)
          in
          value_defs blk @ pred_defs @ acc)
  in
  match return_path_defs with
  | [] -> false
  | d :: _ -> Abi.is_vector_param_reg abi (Def.lhs d)

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

let compute_sub_sig (target : Bap_core_theory.Theory.Target.t) ~(abi : Abi.t)
    (sub : sub term) : Arg.t list * Arg.t list =
  let free_vars = free_vars sub in
  let rets =
    (if Bap_core_theory.Theory.Target.matches target "x86_64-gnu-elf" then
       abi.return_regs
     else [])
    |> Base.List.map ~f:(fun reg -> Arg.create ~intent:Out reg (Var reg))
  in
  let rets =
    (* Double returns arrive via [%YMM0]. *)
    if fp_returning ~abi sub then
      let ymm0 = Base.List.nth_exn abi.vector_param_regs 0 in
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
      let rdi = Base.List.nth_exn abi.int_param_regs 0 in
      let rsi = Base.List.nth_exn abi.int_param_regs 1 in
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
        let rank_of_var (v : var) : int * string =
          let n = Var.name (Var.base v) in
          match
            Base.List.findi (Abi.param_regs abi) ~f:(fun _ r -> Var.same r v)
          with
          | Some (i, _) -> (i, n)
          | None -> (100, n)
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
              || Model.is_intrinsic_name n
              || Base.String.is_prefix n ~prefix:"hike_slot"
              || Base.String.is_prefix n ~prefix:"hike_arg"))
        |> Base.List.sort ~compare:(fun a b ->
            let ra, na = rank_of_var a in
            let rb, nb = rank_of_var b in
            match Int.compare ra rb with
            | 0 -> String.compare na nb
            | c -> c)
        |> Base.List.map ~f:(fun reg -> Arg.create ~intent:In reg (Var reg))
        |> fun regs -> regs @ arg_terms
      in
      (* Signature-shape PLT rule (args = [] + any call); distinct
         from [is_plt_trampoline]'s BIL-shape rule — different
         inputs, do not merge. *)
      let is_plt_sig =
        args = []
        && Term.enum blk_t sub
           |> Seq.exists ~f:(fun blk ->
                  Term.enum jmp_t blk
                  |> Seq.exists ~f:(fun j ->
                         match Jmp.kind j with
                         | Call _ -> true
                         | _ -> false))
      in
      let args =
        if is_plt_sig then
          Base.List.map (Abi.param_regs abi) ~f:(fun reg ->
              Arg.create ~intent:In reg (Var reg))
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
  let abi = Abi.of_target target in
  Term.map sub_t prog ~f:(fun sub ->
      let rets, args = compute_sub_sig target ~abi sub in
      Model.set_sig sub (rets @ args))

(* The pass: write every sub's signature, with its lane types, onto the
   sub's own [arg] terms. *)
let run (proj : Project.t) : Project.t =
  let target = Project.target proj in
  Project.map_program proj ~f:(fun prog -> sign_program ~target prog)
