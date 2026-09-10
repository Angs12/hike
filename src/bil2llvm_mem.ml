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

(* The caller-window materialization (D1's ONE form, no select):
   ptr = hike_stack + (word − stack_0) — stack_0 is the emitted
   entry-RSP value (anchor_i64 for frame subs, the hike_stack parameter
   itself for precise subs), so the runtime difference is the exact
   ABI-visible offset however wide the tag. *)
let caller_mem_access llvm_builder blk_tid fr addr exp =
  let open KB in
  match fr.stack with
  | Some stack ->
    let* addr_v = create_exp llvm_builder blk_tid addr in
    let* llvm_ctx = Context.get llvm_ctx_var in
    let stack0 =
      (* Precise subs bind the SP local to hike_stack: that IS their
         emitted entry-RSP value (their anchor_i64 is the unused 0). *)
      match fr.is_precise with
      | true -> stack
      | false -> fr.anchor_i64 in
    let offset = Llvm.build_sub addr_v stack0 "caller_off" llvm_builder in
    let base = Llvm.build_add stack offset "caller_addr" llvm_builder in
    let ptr =
      Llvm.build_inttoptr base (Llvm.pointer_type llvm_ctx) "" llvm_builder in
    mem_access_at_ptr llvm_builder blk_tid ptr exp
  | None ->
      (* No hike_stack lane (main): the raw address is the real one. *)
      create_exp llvm_builder blk_tid exp

(* The mixed-class materialization — the COMPLETE rule for a span that
   is two-sided or wrapped at runtime (a va_list pointer denoting the
   reg-save area OR the overflow area, an ITE'd address, a widened hull
   crossing the entry RSP): the runtime word chooses the base.  A
   word at/above the emitted entry RSP is caller-window traffic
   (hike_stack + (word − stack_0)); below it, the word is an anchor-
   linear frame address (inttoptr of it IS the frame cell — the
   ptrtoint round-trip).  This is not a conservative select: the class
   is genuinely either-based and BOTH arms are exact. *)
let mixed_mem_access llvm_builder blk_tid fr addr exp =
  let open KB in
  match fr.stack with
  | Some stack ->
    let* addr_v = create_exp llvm_builder blk_tid addr in
    let* llvm_ctx = Context.get llvm_ctx_var in
    let stack0 =
      match fr.is_precise with
      | true -> stack
      | false -> fr.anchor_i64 in
    let offset = Llvm.build_sub addr_v stack0 "mixed_off" llvm_builder in
    let zero = Llvm.const_int (Llvm.i64_type llvm_ctx) 0 in
    let is_caller =
      Llvm.build_icmp Llvm.Icmp.Sge offset zero "is_caller_arg" llvm_builder in
    let caller_addr =
      Llvm.build_add stack offset "caller_addr" llvm_builder in
    let base =
      Llvm.build_select is_caller caller_addr addr_v "arg_addr" llvm_builder in
    let ptr =
      Llvm.build_inttoptr base (Llvm.pointer_type llvm_ctx) "" llvm_builder in
    mem_access_at_ptr llvm_builder blk_tid ptr exp
  | None ->
      (* No hike_stack lane (main): the raw address is the real one. *)
      create_exp llvm_builder blk_tid exp

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

(* Finds the region containing an offset. *)
let region_of_offset (regions : (Convutils.region * Llvm.llvalue) list)
    (lo : int64) : (Convutils.region * Llvm.llvalue) option =
  Base.List.find regions ~f:(fun (r, _) ->
      let rlo, rhi = r.Convutils.span in
      Int64.compare lo rlo >= 0 && Int64.compare lo rhi <= 0)

(* Dispatches tagged accesses to storage.  The producer's tag IS the
   lane (T3): no sign tests in the emitter.
   - Range/Infinite (spans entirely below the entry RSP — this sub's
     own frame): the ONE uniform rule — the address integer flows
     through create_exp into create_addr_ptr's licensed arm,
     ptr = frame + (word − stack_0) + anchor_idx, total over all signs
     and widths (the emitted entry-RSP value IS stack_0, so the runtime
     index is exact however imprecise the tag).
   - Caller (spans entirely at/above the entry RSP — the producer's
     ABI-visible window split): the hike_stack form, one base.
   - Mixed (two-sided/wrapped spans): the two-base rule — the runtime
     word chooses (the recorded deviation from the ticket's no-select
     letter; no single-base rule is sound for the class).
   - VLA/Unbounded/Dead/untagged: their existing complete lanes. *)
let mem_access llvm_builder blk_tid sub_tid sub_info fr def_tag
    (def : def term) (exp : exp) =
  
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  let var = Def.lhs def in
  match def_tag with
  | Some (Convutils.Range _ | Convutils.Infinite _) ->
      (* The uniform materialization rule. *)
      create_exp llvm_builder blk_tid exp
  | Some (Convutils.Caller _) ->
      (match find_mem_node (Def.rhs def) with
      | Some node ->
          caller_mem_access llvm_builder blk_tid fr (mem_node_addr node) exp
      | None -> create_exp llvm_builder blk_tid exp)
  | Some (Convutils.Mixed _) ->
      (match find_mem_node (Def.rhs def) with
      | Some node ->
          mixed_mem_access llvm_builder blk_tid fr (mem_node_addr node) exp
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
  (* The address-materialization license (tickets T1 + T3): the def's
     tag kind IS the producer's frame-residency proof.  Range/Infinite
     (the frame lane — spans reaching below the entry RSP, post-split)
     license the frame GEP in create_addr_ptr; Caller, Unbounded, VLA
     and untagged do not (their addresses may be caller-window or
     foreign pointers — the sret pointer, a reloaded pointer), so the
     identity materialization (inttoptr) applies. *)
  ctx.Convutils.frame_wrap_license :=
    (match def_tag with
     | Some (Convutils.Range _ | Convutils.Infinite _) -> true
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
