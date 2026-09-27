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

let compute_sub_sig (target : Bap_core_theory.Theory.Target.t)
    (sub : sub term) : Arg.t list * Arg.t list =
  let abi = Abi.of_target target in
  let free_vars = Hike_split_blocks.free_regs sub in
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

(* ---- The value kind (ptr vs int) ----
   A value is a pointer when any part of its denotation is a bounded
   stack or VLA address.  Computed here, pre-SSA, where the denotation
   resolves; the emitter's ptr discipline consumes it. *)

module Vsa = Cbat_vsa

let ptr_kind_of ~(facts : Hike_kb.facts) ~(blk : blk term) ?def (e : exp) :
    bool =
  match facts.Hike_kb.denote ~blk ?def e with
  | Ok ws -> Vsa.WordSet.in_stack_segment ws
  | Error _ -> false

(* The defs whose value denotes a stack or VLA address, with the storage
   each lives in. *)
let ptr_defs ~(facts : Hike_kb.facts) (sub : sub term) :
    Tid.Set.t * Hike_stack_model.ptr_storage Tid.Map.t =
  let layout =
    Base.Option.value (Term.get_attr sub Hike_stack_model.layout_tag)
      ~default:
        { Hike_stack_model.Sub_layout.regions = []; anchor = None;
          window_param = false }
  in
  let word = facts.Hike_kb.abi.Hike_abi.word in
  let a_base =
    Hike_stack_model.args_base ~entry:Hike_stack_model.segment_base ~word
  in
  let storage_of (ws : Vsa.WordSet.t) : Hike_stack_model.ptr_storage =
    match Hike_stack_model.positions_of_offsets ws with
    | Some (lo, _) when Stdlib.Int64.compare lo a_base >= 0 ->
        Hike_stack_model.Ptr_window
    | Some (lo, hi) -> (
        match
          Base.List.find layout.Hike_stack_model.Sub_layout.regions
            ~f:(fun (_, (rlo, rhi), _) ->
              Stdlib.Int64.compare lo rlo >= 0
              && Stdlib.Int64.compare hi rhi <= 0)
        with
        | Some (id, _, _) -> Hike_stack_model.Ptr_region id
        | None -> Hike_stack_model.Ptr_residue)
    | None -> Hike_stack_model.Ptr_residue
  in
  Term.enum blk_t sub
  |> Seq.fold ~init:(Tid.Set.empty, Tid.Map.empty)
       ~f:(fun (tids, stors) blk ->
         Term.enum def_t blk
         |> Seq.fold ~init:(tids, stors) ~f:(fun (tids, stors) d ->
             match facts.Hike_kb.denote ~blk ~def:d (Def.rhs d) with
             | Error _ -> (tids, stors)
             | Ok ws ->
                 if not (Vsa.WordSet.in_stack_segment ws) then (tids, stors)
                 else
                   ( Core.Set.add tids (Term.tid d),
                     Core.Map.set stors ~key:(Term.tid d)
                       ~data:(storage_of ws) )))

let sub_of_program (prog : program term) : sub term Tid.Map.t =
  Term.enum sub_t prog
  |> Seq.fold ~init:Tid.Map.empty ~f:(fun m s ->
      Core.Map.set m ~key:(Term.tid s) ~data:s)

(* The callee's In lanes: its own signature, or the ABI integer
   parameters for an extern. *)
let callee_lanes ~(facts : Hike_kb.facts) ~(sub_of : sub term Tid.Map.t)
    (t : tid) : Arg.t list =
  match Core.Map.find sub_of t with
  | Some callee -> Hike_stack_model.sig_args callee
  | None ->
      Base.List.map facts.Hike_kb.abi.Hike_abi.int_param_regs
        ~f:(fun reg -> Arg.create ~intent:In reg (Var reg))

(* A callee parameter is a pointer when any caller passes a stack or VLA
   address at that lane (NULL counts as an address; a genuine address/
   integer mix is a buggy program and is typed a pointer). *)
let param_kinds ~(facts : Hike_kb.facts) ~(sub_of : sub term Tid.Map.t)
    (prog : program term) : Var.Set.t Tid.Map.t =
  let add acc t v =
    Core.Map.update acc t ~f:(function
        | None -> Var.Set.singleton v
        | Some s -> Core.Set.add s v)
  in
  Term.enum sub_t prog
  |> Seq.fold ~init:Tid.Map.empty ~f:(fun acc caller ->
      Term.enum blk_t caller
      |> Seq.fold ~init:acc ~f:(fun acc blk ->
          Term.enum jmp_t blk
          |> Seq.fold ~init:acc ~f:(fun acc j ->
              match Jmp.kind j with
              | Call c -> (
                  match Call.target c with
                  | Direct t ->
                      Base.List.fold (callee_lanes ~facts ~sub_of t)
                        ~init:acc ~f:(fun acc a ->
                          if Hike_stack_model.is_ret a then acc
                          else if ptr_kind_of ~facts ~blk (Arg.rhs a) then
                            add acc t (Arg.lhs a)
                          else acc)
                  | Indirect _ -> acc)
              | _ -> acc)))

(* Stamps each In lane's kind: the mem/window lanes are pointers by
   construction; a value lane is a pointer when its parameter is. *)
let stamp_arg_kinds ~(param_kinds : Var.Set.t Tid.Map.t)
    (prog : program term) : program term =
  Term.map sub_t prog ~f:(fun sub ->
      let kinds =
        Core.Map.find param_kinds (Term.tid sub)
        |> Base.Option.value ~default:Var.Set.empty
      in
      Term.map arg_t sub ~f:(fun a ->
          if Hike_stack_model.is_ret a then a
          else if
            Hike_stack_model.is_ptr_arg a
            || Hike_stack_model.is_window_var (Arg.lhs a)
            || Core.Set.mem kinds (Arg.lhs a)
          then Hike_stack_model.set_arg_ptr_kind a
          else a))

#ifdef VSA_DEBUG
let kind_census (prog : program term) : unit =
  let defs = ref 0 and ptrs = ref 0 and wins = ref 0 in
  Term.enum sub_t prog
  |> Seq.iter ~f:(fun sub ->
      Term.enum blk_t sub
      |> Seq.iter ~f:(fun blk ->
          Term.enum def_t blk
          |> Seq.iter ~f:(fun d ->
              incr defs;
              if Hike_def_slots.def_ptr_kind d then incr ptrs;
              if Hike_def_slots.def_is_window_value d then incr wins)));
  Printf.eprintf "hike-kinds: defs=%d ptr=%d window=%d\n%!" !defs !ptrs !wins
#endif

(* The pass: write every sub's signature, with its lane types, onto the
   sub's own [arg] terms, then stamp the value/lane kinds (when the
   analysis ran). *)
let run (proj : Project.t) : Project.t =
  let target = Project.target proj in
  Project.map_program proj ~f:(fun prog ->
      let prog = sign_program ~target prog in
      match Hike_kb.facts_opt () with
      | None -> prog
      | Some facts ->
          let sub_of = sub_of_program prog in
          let pks = param_kinds ~facts ~sub_of prog in
          let prog = stamp_arg_kinds ~param_kinds:pks prog in
          let prog =
            Term.map sub_t prog ~f:(fun sub ->
                let tids, stors = ptr_defs ~facts sub in
                let sub = Hike_def_slots.stamp_ptr_kinds ~ptr_tids:tids sub in
                Hike_def_slots.stamp_ptr_storages ~storages:stors sub)
          in
#ifdef VSA_DEBUG
          kind_census prog;
#endif
          prog)
