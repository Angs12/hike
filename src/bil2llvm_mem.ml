(* Emitter memory lane: tag dispatch, fission markers, region accesses. *)

open Bap.Std
open Bap.Std.Bil.Types
open Convutils
module Abi = Hike_abi
module KB = Bap_knowledge.Knowledge
open Bil2llvm_env
open Bil2llvm_exp
open Bil2llvm_section


(* Looks up a def VSA tag. *)
let find_def_tag sub_info def =
  Core.Map.find sub_info.Convutils.offsets (Term.tid def)

(* Tests for visible storage via the stack model. *)
let is_abi_visible sub_info def =
  Hike_stack_model.abi_visibility_of sub_info def

(* Tests for PLT stubs. *)
let is_plt_trampoline ctx (sub : sub term) : bool =
  let free_vars =
    Sub.free_vars sub
    |> Core.Set.filter ~f:(fun var -> not @@ is_mem var)
    |> Core.Set.to_list
  in
  let reg_vars =
    (* SP-only: a stub genuinely using RBP is not a pure trampoline. *)
    Base.List.filter free_vars ~f:(fun reg ->
        not (Var.same reg ctx.Convutils.sp))
  in
  reg_vars = []
  && Term.enum blk_t sub
     |> Seq.exists ~f:(fun blk ->
            Term.enum jmp_t blk
            |> Seq.exists ~f:(fun j ->
                   match Jmp.kind j with
                   | Call _ -> true
                   | _ -> false))

(* Finds the first memory node using Exp.visitor. *)
type mem_node = [ `Load of exp * Size.t | `Store of exp * exp * Size.t ]

let find_mem_node (exp : exp) : mem_node option =
  let vis =
    object
      inherit [ mem_node option ] Exp.visitor
      method! visit_load ~mem:_ ~addr _ size acc =
        Base.Option.first_some acc (Some (`Load (addr, size)))
      method! visit_store ~mem:_ ~addr ~exp:x _ size acc =
        Base.Option.first_some acc (Some (`Store (addr, x, size)))
    end
  in
  vis#visit_exp exp None

let mem_node_addr = function
  | `Load (addr, _) | `Store (addr, _, _) -> addr

(* Name of the accumulator marker var the pointer-access lane binds. *)
let marker_name = "hike_acc"

(* Marker var for one pointer-access lane. *)
let marker_of_size size =
  Var.create ~is_virtual:true ~fresh:false marker_name
    (Type.Imm (Size.in_bits size))

(* Shared skeleton: bind the arm's value to the marker, then re-emit
   with the arm's rewrite. Insertion order is the arm's order. *)
let emit_with_marker llvm_builder blk_tid ctx marker ~emit ~rewrite =
  let open KB in
  let* v = emit () in
  insert_local ctx blk_tid marker v;
  create_exp llvm_builder blk_tid (rewrite marker)

(* Dispatches memory load/store through a pointer using Exp.mapper. *)
let mem_access_at_ptr llvm_builder blk_tid ptr exp =
  let open KB in
  let* ctx, llvm_ctx = emit_env () in
  match find_mem_node exp with
  | Some (`Load (addr, size)) ->
      let marker = marker_of_size size in
      let emit () =
        KB.return
        @@ Llvm.build_load
             (Llvm.integer_type llvm_ctx (Size.in_bits size))
             ptr "" llvm_builder
      in
      let rewrite marker =
        let v =
          object
            inherit Exp.mapper
            method! map_load ~mem ~addr:a e s =
              if Exp.equal a addr && Size.equal s size then Bil.Var marker
              else Bil.Load (mem, a, e, s)
          end
        in
        v#map_exp exp
      in
      emit_with_marker llvm_builder blk_tid ctx marker ~emit ~rewrite
  | Some (`Store (addr, data, size)) ->
      let marker = marker_of_size size in
      let emit () =
        let open KB in
        let* d = create_exp llvm_builder blk_tid data in
        let _ : Llvm.llvalue = Llvm.build_store d ptr llvm_builder in
        (* Store nodes bind data, not void stores. *)
        return d
      in
      let rewrite marker =
        let v =
          object
            inherit Exp.mapper
            method! map_store ~mem ~addr:a ~exp:x e s =
              if Exp.equal a addr && Size.equal s size then Bil.Var marker
              else Bil.Store (mem, a, x, e, s)
          end
        in
        v#map_exp exp
      in
      emit_with_marker llvm_builder blk_tid ctx marker ~emit ~rewrite
  | None -> create_exp llvm_builder blk_tid exp

(* Emits a singleton-tagged access. *)
let create_static_mem_access llvm_builder blk_tid fr lo exp =
  let open KB in
  let* ctx, llvm_ctx = emit_env () in
  let gep_opt =
    if Int64.compare lo 0L > 0 then
      match fr.stack with
      | Some stack ->
          let addr =
            Llvm.build_add stack
              (Llvm.const_of_int64 (Llvm.i64_type llvm_ctx) lo false)
              "" llvm_builder
          in
          Some (Llvm.build_inttoptr addr (Llvm.pointer_type llvm_ctx) "" llvm_builder)
      | None -> None
    else
      match fr.frame with
      | Some frame ->
          Some
            (Llvm.build_gep (Llvm.i8_type llvm_ctx) frame
               [|
                 Llvm.const_of_int64 (Llvm.i64_type llvm_ctx)
                   (Int64.add fr.anchor_idx lo) false;
               |]
               "" llvm_builder)
      | None -> None
  in
  match gep_opt with
  | Some gep -> mem_access_at_ptr llvm_builder blk_tid gep exp
  | None ->
#ifdef VSA_DEBUG
      Printf.eprintf "hike: create_static_mem_access fallback lo=%Ld no frame/stack -> dynamic\n" lo;
#endif
      create_exp llvm_builder blk_tid exp

(* Singleton tags use const GEPs. *)
(* Rebases positive-interval addresses onto the stack. *)
let rebase_addr llvm_builder fr addr =
  let open KB in
  match fr.stack with
  | None -> return addr
  | Some stack ->
    let offset = Llvm.build_sub addr fr.anchor_i64 "arg_off" llvm_builder in
    let* llvm_ctx = Context.get llvm_ctx_var in
    let zero = Llvm.const_int (Llvm.i64_type llvm_ctx) 0 in
    let is_caller = Llvm.build_icmp Llvm.Icmp.Sge offset zero "is_caller_arg" llvm_builder in
    let caller_addr = Llvm.build_add stack offset "caller_addr" llvm_builder in
    return @@ Llvm.build_select is_caller caller_addr addr "arg_addr" llvm_builder

(* Emits runtime-sized allocas. *)
let create_dynamic_alloc llvm_builder blk_tid exp =
  let open KB in
  match exp with
  | Bil.BinOp (Bil.MINUS, _, size) ->
      let* llvm_ctx = Context.get llvm_ctx_var in
      let* size_v = create_exp llvm_builder blk_tid size in
      let vla =
        Llvm.build_array_alloca (Llvm.i8_type llvm_ctx) size_v "vla"
          llvm_builder
      in
      Llvm.set_alignment 16 vla;
      return
      @@ Llvm.build_ptrtoint vla (Llvm.i64_type llvm_ctx) "vla_i64"
           llvm_builder
  | _ -> create_exp llvm_builder blk_tid exp

(* Loads/stores through a computed address. *)
let mem_access_via_ptr llvm_builder blk_tid addr_v exp =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let p =
    Llvm.build_inttoptr addr_v (Llvm.pointer_type llvm_ctx) "" llvm_builder
  in
  mem_access_at_ptr llvm_builder blk_tid p exp

(* Finds the region containing an offset. *)
let region_of_offset (regions : (Convutils.region * Llvm.llvalue) list)
    (lo : int64) : (Convutils.region * Llvm.llvalue) option =
  Base.List.find regions ~f:(fun (r, _) ->
      let rlo, rhi = r.Convutils.span in
      Int64.compare lo rlo >= 0 && Int64.compare lo rhi <= 0)

(* Dispatches tagged accesses to storage. *)
let mem_access llvm_builder blk_tid sub_tid sub_info fr def_tag
    (def : def term) (exp : exp) =
  
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  let var = Def.lhs def in
  match def_tag with
  | Some (Convutils.Range (lo, hi)) when Int64.equal lo hi ->
      if Int64.compare lo 0L > 0 then
        (* Incoming-arg cells read via [hike_stack]. *)
        (match fr.stack with
        | Some _ -> create_static_mem_access llvm_builder blk_tid fr lo exp
        | None -> create_exp llvm_builder blk_tid exp)
      else if is_abi_visible sub_info def then
        (* Outgoing cells use their own address. *)
        (match find_mem_node (Def.rhs def) with
        | Some node ->
            let* addr_v = create_exp llvm_builder blk_tid (mem_node_addr node) in
            mem_access_via_ptr llvm_builder blk_tid addr_v exp
        | None -> create_exp llvm_builder blk_tid exp)
      else
        (* Locals use static frame GEPs. *)
        create_static_mem_access llvm_builder blk_tid fr lo exp
  | Some (Convutils.Range (lo, _) | Convutils.Infinite (lo, _))
    when Int64.compare lo 0L >= 0 ->
      (* Positive intervals rebase onto the stack. *)
      (match find_mem_node (Def.rhs def) with
      | Some node ->
          let* addr_v = create_exp llvm_builder blk_tid (mem_node_addr node) in
          let* addr_v = rebase_addr llvm_builder fr addr_v in
          mem_access_via_ptr llvm_builder blk_tid addr_v exp
      | None -> create_exp llvm_builder blk_tid exp)
  | Some (Convutils.VLA _) -> create_exp llvm_builder blk_tid exp
  | Some Convutils.Unbounded ->
      if not (Core.Set.mem !(ctx.Convutils.guarded_warned) sub_tid) then begin
        ctx.Convutils.guarded_warned :=
          Core.Set.add !(ctx.Convutils.guarded_warned) sub_tid;
        (* Warning text is a grepped contract. *)
        Hike_diag.warn
          "guarded: sub %s: stack access is Unbounded (unconstrained / TOP): def %s rhs=%s"
          (Tid.name sub_tid) (Var.name var) (Format.asprintf "%a" Exp.pp exp)
      end;
      create_exp llvm_builder blk_tid exp
  | Some (Convutils.Range _) | Some (Convutils.Infinite _) ->
      create_exp llvm_builder blk_tid exp
  | Some Convutils.Dead ->
      if not (Core.Set.mem !(ctx.Convutils.dead_warned) sub_tid) then begin
        ctx.Convutils.dead_warned :=
          Core.Set.add !(ctx.Convutils.dead_warned) sub_tid;
        (* Warning text is a grepped contract. *)
        Hike_diag.warn
          "guarded: sub %s: stack access classified Dead (empty range): def %s rhs=%s"
          (Tid.name sub_tid) (Var.name var) (Format.asprintf "%a" Exp.pp exp)
      end;
      let* typ = typ_lltype_m (Var.typ var) in
      return @@ Llvm.poison typ
  | None -> create_exp llvm_builder blk_tid exp

let create_def blk_tid llvm_builder sub_tid sub_info fr alloc_tids def =

  let open KB in
  let* ctx = Context.get emit_ctx_var in
  let var = Def.lhs def in
  let v = Def.value def in
  let exp = Def.rhs def in
  let def_tag = find_def_tag sub_info def in
  (* The address-materialization license (ticket T1): the def's tag is
     the producer's frame-residency proof.  A Range/Infinite with a
     negative lower bound proves the rhs's accesses live in THIS sub's
     frame — create_addr_ptr may route their addresses through the frame
     base as GEPs.  Unbounded, VLA and untagged (none) prove nothing:
     their addresses may be foreign pointers (the sret pointer, a
     reloaded pointer), so the typed wrap is not licensed and the
     identity materialization (inttoptr) applies. *)
  ctx.Convutils.frame_wrap_license :=
    (match def_tag with
     | Some (Convutils.Range (lo, _) | Convutils.Infinite (lo, _)) ->
         Int64.compare lo 0L < 0
     | _ -> false);
  let* res =
    (* Runtime-sized SP decrements become real allocas (spec §2.3). *)
    if Core.Set.mem alloc_tids (Term.tid def) then
      create_dynamic_alloc llvm_builder blk_tid exp
    else if KB.Value.get rip_relative_addr v then
      create_rip_relative_addr llvm_builder blk_tid exp
    else if fr.is_precise then
      (* Split-model accesses use region GEPs. *)
      (match def_tag with
       | Some (Convutils.Range (lo, hi)) when Int64.equal lo hi ->
           (match region_of_offset fr.regions lo with
            | Some (r, base) ->
                let offset = Int64.sub lo (fst r.Convutils.span) in
                let* llvm_ctx = Context.get llvm_ctx_var in
                let gep =
                  Llvm.build_gep (Llvm.i8_type llvm_ctx) base
                    [| Llvm.const_of_int64 (Llvm.i64_type llvm_ctx) offset false |]
                    "" llvm_builder
                in
                 mem_access_at_ptr llvm_builder blk_tid gep exp
            | None -> mem_access llvm_builder blk_tid sub_tid sub_info fr def_tag def exp)
       | _ -> mem_access llvm_builder blk_tid sub_tid sub_info fr def_tag def exp)
    else mem_access llvm_builder blk_tid sub_tid sub_info fr def_tag def exp
  in
  (* The def's value is the variable's declared width: an over-wide rhs
     (the -O2 lane extracts, e.g. [low:128] feeding a 64-bit var)
     contributes the variable's low bits; a narrow one zero-fills.  The
     contract is enforced where the value is BORN, so every phi joining
     the variable receives the declared type by construction. *)
  let* res =
    let lw = match Var.typ var with Type.Imm n -> n | _ -> 0 in
    let rt = Llvm.type_of res in
    match Llvm.classify_type rt with
    | Llvm.TypeKind.Integer when lw > 0 ->
        let rw = Llvm.integer_bitwidth rt in
        if rw = lw then return res
        else if rw > lw then
          let* llvm_ctx = Context.get llvm_ctx_var in
          return @@ Llvm.build_trunc res
              (Llvm.integer_type llvm_ctx lw) "" llvm_builder
        else
          let* llvm_ctx = Context.get llvm_ctx_var in
          return @@ Llvm.build_zext res
              (Llvm.integer_type llvm_ctx lw) "" llvm_builder
    | _ -> return res
  in
  (* The license scopes to this def's rhs emission only. *)
  ctx.Convutils.frame_wrap_license := false;
  insert_local ctx blk_tid var res;
  return ()
