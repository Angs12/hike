(* Emitter environment: KB context vars, the env reader, LLtype helpers. *)

open Bap.Std
open Bap.Std.Bil.Types
open Convutils
module Abi = Hike_abi
module KB = Bap_knowledge.Knowledge
module Ws = Cbat_clp_set_composite


(* Per-sub frame state. *)
type sub_frame = {
  frame : Llvm.llvalue option;
  (* Anchor byte index. *)
  anchor_idx : int64;
  anchor_i64 : Llvm.llvalue;
  stack : Llvm.llvalue option;
  regions : (Convutils.region * Llvm.llvalue) list;
  is_precise : bool;
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
