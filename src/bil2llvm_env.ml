(* Emitter environment: KB context vars, the env reader, LLtype helpers. *)

open Bap.Std
open Bap.Std.Bil.Types
open Convutils
module Abi = Hike_abi
module KB = Bap_knowledge.Knowledge


(* Per-sub frame state. *)
type sub_frame = {
  (* The sub's anchor address integer: the SP Slot's stored value for
     storage-carrying subs; the constant 0 anchor for storage-free
     subs (the [stack0 = None] fallback readers). *)
  anchor_i64 : Llvm.llvalue;
  (* The caller-window base local (the Caller-Window Parameter), when
     the sub carries one (variadic/mixed — the T4 residual). *)
  stack : Llvm.llvalue option;
  (* The per-invocation anchor: the SP entry value bound from the SP
     Slot (T4).  None = the sub owns no SP storage (SP binds to the
     anchor constant, 0 for storage-free subs). *)
  stack0 : Llvm.llvalue option;
  regions : (Convutils.region * Llvm.llvalue) list;
  is_precise : bool;
  (* T4: per call block, the outgoing slot site (the slot index ->
     storing-def map from the producer's record). *)
  outgoing : Convutils.call_site Tid.Map.t;
  (* T4b: the outgoing slot stores' values, recorded by the STORE's own
     emission (def tid -> the LLVM value written).  The call passes the
     value the store wrote — never a re-evaluation of the stored exp at
     the call, which would read a var the block redefined after the
     store. *)
  store_vals : (Tid.t, Llvm.llvalue) EHashtbl.t;
  (* T4: per indirect call jmp, the VSA's singleton resolution. *)
  resolved : Tid.t option Tid.Map.t;
}
(* Emission context threaded as a KB var. *)
let llvm_ctx_var : Llvm.llcontext KB.Context.var =
  KB.Context.declare ~package:"hike" "llvm-ctx" (KB.return (Obj.magic 0))

let llvm_module_var : Llvm.llmodule KB.Context.var =
  KB.Context.declare ~package:"hike" "llvm-module" (KB.return (Obj.magic 0))

let section_list_var : section list KB.Context.var =
  KB.Context.declare ~package:"hike" "section-list" (KB.return [])

(* Default emission context. *)
let emit_ctx_var : Convutils.emit_ctx KB.Context.var =
  KB.Context.declare ~package:"hike" "emit-ctx"
    (KB.return (Convutils.empty_emit_ctx ()))

(* One reader for the context-get pairs opening most emitters. *)
let emit_env () =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  let* llvm_ctx = Context.get llvm_ctx_var in
  return (ctx, llvm_ctx)

let typ_lltype_m typ =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  match typ with
  | Imm n -> return @@ Llvm.integer_type llvm_ctx n
  | _ -> return @@ Llvm.pointer_type llvm_ctx

let var_lltype var = typ_lltype_m (Var.typ var)

(* Tests for FP arg registers. *)
let is_fp_param (v : var) : bool =
  Base.String.is_prefix (Var.name (Var.base v)) ~prefix:Abi.vector_param_prefix

let is_extern ctx (sub_tid : tid) : bool =
  not (Core.Map.mem ctx.Convutils.subs sub_tid)
