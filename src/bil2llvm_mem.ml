(* Emitter memory lane: tag dispatch, fission markers, region accesses. *)

open Bap.Std
open Bap.Std.Bil.Types
module Abi = Hike_abi
open Bil2llvm_env
open Bil2llvm_exp
open Bil2llvm_section

let find_def_tag (def : def term) : Hike_stack_model.Tag.t option =
  Hike_stack_model.sec_tag def

let is_plt_trampoline ctx (sub : sub term) : bool =
  let free_vars =
    Sub.free_vars sub
    |> Core.Set.filter ~f:(fun var -> not @@ Hike_stack_model.is_mem var)
    |> Core.Set.to_list
  in
  let reg_vars =
    (* A stub using the frame pointer is not a pure trampoline. *)
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

(* Runtime-sized allocas: the def's value is the post-event SP, so
   the alloca size is (old SP − new SP) however the size was spelled. *)
let create_dynamic_alloc ctx scope llvm_builder blk_tid (def : def term) exp =
  let old_sp =
    create_exp ctx scope llvm_builder blk_tid (Bil.Var (Def.lhs def))
  in
  let new_sp = create_exp ctx scope llvm_builder blk_tid exp in
  let size = Llvm.build_sub old_sp new_sp "vla_size" llvm_builder in
  let vla =
    Llvm.build_array_alloca (Llvm.i8_type ctx.llvm_ctx) size "vla"
      llvm_builder
  in
  Llvm.set_alignment Hike_abi.stack_align vla;
  Llvm.build_ptrtoint vla (Llvm.i64_type ctx.llvm_ctx) "vla_i64"
    llvm_builder

(* Region/window access emission lives in [Bil2llvm_exp]. *)

(* The mem node's region/window var, when the rewrite re-pointed it. *)
let region_mem_of (e : exp) : var option =
  match Hike_stack_model.mem_node_where Hike_stack_model.is_region_mem e with
  | Some (`Load (Bil.Var v, _, _)) | Some (`Store (Bil.Var v, _, _, _)) ->
    Some v
  | _ -> None

let window_mem_of (e : exp) : var option =
  match Hike_stack_model.mem_node_where Hike_stack_model.is_window_mem e with
  | Some (`Load (Bil.Var v, _, _)) | Some (`Store (Bil.Var v, _, _, _)) ->
    Some v
  | _ -> None

(* Dispatches an access: region/window mems to their storage, Dead
   to poison, the return-address cell to undef; everything else
   emits raw. *)
let mem_access ctx scope llvm_builder blk_tid sub_tid fr def_tag
    (def : def term) (exp : exp) =
  let var = Def.lhs def in
  match region_mem_of exp with
  | Some mv -> region_mem_access ctx scope llvm_builder blk_tid fr mv exp
  | None -> (
    match window_mem_of exp with
    | Some mv -> window_mem_access ctx scope llvm_builder blk_tid fr mv exp
    | None -> (
      match def_tag with
      | Some Hike_stack_model.Tag.Dead ->
          if not (Core.Set.mem !(scope.dead_warned) sub_tid) then begin
            scope.dead_warned := Core.Set.add !(scope.dead_warned) sub_tid;
            (* Warning text is a grepped contract. *)
            Hike_diag.warn
              "guarded: sub %s: stack access classified Dead (empty range): def %s rhs=%s"
              (Tid.name sub_tid) (Var.name var) (Format.asprintf "%a" Exp.pp exp)
          end;
          Llvm.poison (typ_lltype ctx (Var.typ var))
      | Some def_tag when Hike_stack_model.is_return_address_tag def_tag -> (
          match find_mem_node (Def.rhs def) with
          | Some (`Load (addr, size))
            when Size.in_bits size <= 8 * ctx.abi.Abi.word
                 && Base.Option.is_none
                      (Hike_stack_model.store_data_of_rhs (Def.rhs def)) ->
              let marker = marker_of_size size in
              let emit () =
                Llvm.undef
                  (Llvm.integer_type ctx.llvm_ctx (Size.in_bits size))
              in
              let rewrite marker = rewrite_mem_node exp addr size marker in
              emit_with_marker ctx scope llvm_builder blk_tid marker ~emit ~rewrite
          | _ -> create_exp ctx scope llvm_builder blk_tid exp)
      | _ -> create_exp ctx scope llvm_builder blk_tid exp))

let create_def ctx scope blk_tid llvm_builder sub_tid fr def =
  let var = Def.lhs def in
  let exp = Def.rhs def in
  let def_tag = find_def_tag def in
  let res =
    if Hike_stack_model.def_is_dyn_alloc def then
      create_dynamic_alloc ctx scope llvm_builder blk_tid def exp
    else if Hike_stack_model.def_is_rip_relative def then
      create_rip_relative_addr ctx scope llvm_builder blk_tid exp
    else mem_access ctx scope llvm_builder blk_tid sub_tid fr def_tag def exp
  in
  (* A def whose value lives at/above the entry line addresses the
     caller's window: re-base from this sub's anchor to the
     hike_window parameter.  Memory-node defs are skipped — their
     value is loaded data, not an address. *)
  let res =
    if Hike_stack_model.def_is_window_value def then
      let w_i64 =
        let wv = Hike_stack_model.hike_window_var ~word:ctx.abi.Abi.word in
        match get_local scope blk_tid wv with
        | Some v ->
            Llvm.build_ptrtoint v (Llvm.i64_type ctx.llvm_ctx) "" llvm_builder
        | None -> Llvm.undef (Llvm.i64_type ctx.llvm_ctx)
      in
      let stack0 = Base.Option.value fr.stack0 ~default:fr.anchor_i64 in
      let rel = Llvm.build_sub res stack0 "" llvm_builder in
      Llvm.build_add w_i64 rel "" llvm_builder
    else res
  in
  (* The def's value is coerced to the variable's declared width
     where the value is born, so every phi joining the variable sees
     the declared type. *)
  let res =
    let lw = match Var.typ var with Type.Imm n -> n | _ -> 0 in
    match Llvm.classify_type (Llvm.type_of res) with
    | Llvm.TypeKind.Integer when lw > 0 ->
        coerce_int_width ctx.llvm_ctx llvm_builder
          ~bits:(Llvm.integer_bitwidth (Llvm.type_of res)) res lw
    | _ -> res
  in
  insert_local scope blk_tid var res
