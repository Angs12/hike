(* Emitter memory lane: tag dispatch, fission markers, region accesses. *)

open Bap.Std
open Bap.Std.Bil.Types
module Abi = Hike_abi
module KB = Bap_knowledge.Knowledge
open Bil2llvm_env
open Bil2llvm_exp
open Bil2llvm_section


(* The def's slim section tag: the tag rides the DEF'S VALUE — the
   producer stamped it; no per-sub record reaches the emitter. *)
let find_def_tag (def : def term) : Hike_stack_model.Tag.t option =
  Hike_stack_model.sec_tag def

(* Tests for PLT stubs. *)
let is_plt_trampoline ctx (sub : sub term) : bool =
  let free_vars =
    Sub.free_vars sub
    |> Core.Set.filter ~f:(fun var -> not @@ Hike_stack_model.is_mem var)
    |> Core.Set.to_list
  in
  let reg_vars =
    (* SP-only: a stub genuinely using RBP is not a pure trampoline. *)
    Base.List.filter free_vars ~f:(fun reg ->
        not (Var.same reg ctx.sp))
  in
  reg_vars = []
  && Term.enum blk_t sub
     |> Seq.exists ~f:(fun blk ->
            Term.enum jmp_t blk
            |> Seq.exists ~f:(fun j ->
                   match Jmp.kind j with
                   | Call _ -> true
                   | _ -> false))

(* Emits runtime-sized allocas — the dynamic-allocation lane.  The
   event def's own value is the post-event SP; the alloca's size is the
   distance the SP moved down (the pre-def SP binding minus the def's
   value), so any spelling of the size resolves — the values carry it. *)
let create_dynamic_alloc llvm_builder blk_tid (def : def term) exp =
  let open KB in
  let* old_sp = create_exp llvm_builder blk_tid (Bil.Var (Def.lhs def)) in
  let* new_sp = create_exp llvm_builder blk_tid exp in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let size = Llvm.build_sub old_sp new_sp "vla_size" llvm_builder in
  let vla =
    Llvm.build_array_alloca (Llvm.i8_type llvm_ctx) size "vla"
      llvm_builder
  in
  Llvm.set_alignment 16 vla;
  return
  @@ Llvm.build_ptrtoint vla (Llvm.i64_type llvm_ctx) "vla_i64"
       llvm_builder

(* The region and incoming-window lanes live in [Bil2llvm_exp] (the
   generic exp lane's twin arms route there too); this module owns the
   def-level dispatch and the tag arms. *)

(* The mem node's region var, when the rewrite re-pointed it. *)
let region_mem_of (e : exp) : var option =
  let vis =
    object
      inherit [ var option ] Exp.visitor
      method! visit_load ~mem ~addr:_ _ _ acc =
        (match mem with
         | Bil.Var v when Hike_stack_model.is_region_mem v -> Some v
         | _ -> None)
        |> Base.Option.first_some acc
      method! visit_store ~mem ~addr:_ ~exp:_ _ _ acc =
        (match mem with
         | Bil.Var v when Hike_stack_model.is_region_mem v -> Some v
         | _ -> None)
        |> Base.Option.first_some acc
    end
  in
  vis#visit_exp e None

(* The mem node's window var, when the rewrite re-pointed it. *)
let window_mem_of (e : exp) : var option =
  let vis =
    object
      inherit [ var option ] Exp.visitor
      method! visit_load ~mem ~addr:_ _ _ acc =
        (match mem with
         | Bil.Var v when Hike_stack_model.is_window_mem v -> Some v
         | _ -> None)
        |> Base.Option.first_some acc
      method! visit_store ~mem ~addr:_ ~exp:_ _ _ acc =
        (match mem with
         | Bil.Var v when Hike_stack_model.is_window_mem v -> Some v
         | _ -> None)
        |> Base.Option.first_some acc
    end
  in
  vis#visit_exp e None

(* Dispatches accesses to storage: the rewrite's region mems route to
   their materialization (one normalization per world); the slim tag
   keeps only its two raw arms — the return-address cell (dies with
   the real ret) and producer-proven Dead (poison); everything else is
   the foreign raw lane. *)
let mem_access llvm_builder blk_tid sub_tid fr def_tag
    (def : def term) (exp : exp) =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  let var = Def.lhs def in
  match region_mem_of exp with
  | Some mv -> region_mem_access llvm_builder blk_tid fr mv exp
  | None -> (
    match window_mem_of exp with
    | Some mv -> window_mem_access llvm_builder blk_tid fr mv exp
    | None -> (
      match def_tag with
      | Some Hike_stack_model.Tag.Dead ->
          if not (Core.Set.mem !(ctx.dead_warned) sub_tid) then begin
            ctx.dead_warned := Core.Set.add !(ctx.dead_warned) sub_tid;
            (* Warning text is a grepped contract. *)
            Hike_diag.warn
              "guarded: sub %s: stack access classified Dead (empty range): def %s rhs=%s"
              (Tid.name sub_tid) (Var.name var) (Format.asprintf "%a" Exp.pp exp)
          end;
          let* typ = typ_lltype_m (Var.typ var) in
          return @@ Llvm.poison typ
      | Some def_tag when Hike_stack_model.is_return_address_tag def_tag -> (
          (* The return-address cell: dies with the real ret. *)
          match find_mem_node (Def.rhs def) with
          | Some (`Load (addr, size))
            when Size.in_bits size <= 8 * ctx.abi.Abi.word
                 && Base.Option.is_none
                      (Hike_stack_model.store_data_of_rhs (Def.rhs def)) ->
              let marker = marker_of_size size in
              let emit () =
                let* llvm_ctx = Context.get llvm_ctx_var in
                KB.return
                @@ Llvm.undef
                     (Llvm.integer_type llvm_ctx (Size.in_bits size))
              in
              let rewrite marker = rewrite_mem_node exp addr size marker in
              emit_with_marker llvm_builder blk_tid ctx marker ~emit ~rewrite
          | _ -> create_exp llvm_builder blk_tid exp)
      | _ -> create_exp llvm_builder blk_tid exp))

let create_def blk_tid llvm_builder sub_tid fr def =

  let open KB in
  let* ctx = Context.get emit_ctx_var in
  let var = Def.lhs def in

  let v = Def.value def in
  let exp = Def.rhs def in
  let def_tag = find_def_tag def in
  let* res =
    (* Runtime-sized SP decrements become real allocas —
       the dynamic-allocation fact rides the def's value. *)
    if Hike_stack_model.def_is_dyn_alloc def then
      create_dynamic_alloc llvm_builder blk_tid def exp
    else if KB.Value.get rip_relative_addr v then
      create_rip_relative_addr llvm_builder blk_tid exp
    else mem_access llvm_builder blk_tid sub_tid fr def_tag def exp
  in
  (* The window-value re-base (D4b): a def whose VALUE lives at/above
     the entry line computes an address in the CALLER's window — the
     emitted integer re-bases from this sub's anchor world to the
     hike_window parameter, so derefs of the stored pointer stay
     additive-safe.  Memory-node defs are skipped: their value is
     loaded data, not an address. *)
  let* res =
    if Hike_stack_model.def_is_window_value def then
      let* w =
        let wv = Hike_stack_model.hike_window_var ~word:ctx.abi.Abi.word in
        match get_local ctx blk_tid wv with
        | Some v -> KB.return v
        | None ->
          let* ty = typ_lltype_m (Var.typ wv) in
          KB.return (Llvm.undef ty)
      in
      let stack0 = Base.Option.value fr.stack0 ~default:fr.anchor_i64 in
      let* llvm_ctx = Context.get llvm_ctx_var in
      let rel = Llvm.build_sub res stack0 "" llvm_builder in
      KB.return (Llvm.build_add w rel "" llvm_builder)
    else KB.return res
  in
  (* The def's value is the variable's declared width: an over-wide rhs
     (the -O2 lane extracts, e.g. [low:128] feeding a 64-bit var)
     contributes the variable's low bits; a narrow one zero-fills.  The
     contract is enforced where the value is BORN, so every phi joining
     the variable receives the declared type by construction. *)
  let* res =
    let lw = match Var.typ var with Type.Imm n -> n | _ -> 0 in
    match Llvm.classify_type (Llvm.type_of res) with
    | Llvm.TypeKind.Integer when lw > 0 ->
        let* llvm_ctx = Context.get llvm_ctx_var in
        return
        @@ coerce_int_width llvm_ctx llvm_builder
             ~bits:(Llvm.integer_bitwidth (Llvm.type_of res)) res lw
    | _ -> return res
  in
  insert_local ctx blk_tid var res;
  return ()
