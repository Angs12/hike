(* The emitter's one home for a stack/VLA address: the pointer/state
   predicate, the operand-level pointer semantics (the D4 table), the
   storage materialization, and the as_int escape.  The expression lane
   asks it for values; it never asks back, so the pointer representation
   is not spread through the other emitter lanes. *)

open Bap.Std
open Bil2llvm_env

let is_ptr_value (v : Llvm.llvalue) : bool =
  Llvm.classify_type (Llvm.type_of v) = Llvm.TypeKind.Pointer

let as_pointer ctx llvm_builder v =
  if is_ptr_value v then v
  else Llvm.build_inttoptr v ctx.ptr_ty "" llvm_builder

let as_integer ctx llvm_builder v =
  if is_ptr_value v then
    Llvm.build_ptrtoint v (Llvm.integer_type ctx.llvm_ctx ctx.addr_bits)
      "" llvm_builder
  else v

let coerce_to_addr ctx llvm_builder v =
  let b = Llvm.integer_bitwidth (Llvm.type_of v) in
  if b = ctx.addr_bits then v
  else if b > ctx.addr_bits then
    Llvm.build_trunc v (Llvm.integer_type ctx.llvm_ctx ctx.addr_bits) ""
      llvm_builder
  else
    Llvm.build_zext v (Llvm.integer_type ctx.llvm_ctx ctx.addr_bits) ""
      llvm_builder

(* The byte GEP: [base] is a pointer, [idx] a byte offset.  Not
   inbounds — a model address may leave its storage. *)
let gep_i8 ctx llvm_builder base idx =
  Llvm.build_gep (Llvm.i8_type ctx.llvm_ctx) base
    [| coerce_to_addr ctx llvm_builder idx |]
    "" llvm_builder

(* The one dispatch on operand LLVM types. *)
let binop ctx llvm_builder ~(null1 : bool) ~(null2 : bool) (op, v1, v2) =
  let p1 = is_ptr_value v1 and p2 = is_ptr_value v2 in
  let both_int () =
    let v1 = as_integer ctx llvm_builder v1 in
    let v2 = as_integer ctx llvm_builder v2 in
    let v1, v2 =
      if p1 || p2 then
        (coerce_to_addr ctx llvm_builder v1, coerce_to_addr ctx llvm_builder v2)
      else (v1, v2)
    in
    create_binop llvm_builder (op, v1, v2)
  in
  match op with
  | PLUS when p1 && not p2 ->
      gep_i8 ctx llvm_builder v1 (as_integer ctx llvm_builder v2)
  | PLUS when p2 && not p1 ->
      gep_i8 ctx llvm_builder v2 (as_integer ctx llvm_builder v1)
  | MINUS when p1 && not p2 ->
      let n = Llvm.build_neg (as_integer ctx llvm_builder v2) "" llvm_builder in
      gep_i8 ctx llvm_builder v1 n
  | EQ when p1 && p2 -> Llvm.build_icmp Llvm.Icmp.Eq v1 v2 "" llvm_builder
  | NEQ when p1 && p2 -> Llvm.build_icmp Llvm.Icmp.Ne v1 v2 "" llvm_builder
  | (EQ | NEQ) when p1 && null2 ->
      Llvm.build_icmp (if op = EQ then Llvm.Icmp.Eq else Llvm.Icmp.Ne) v1
        (Llvm.const_null ctx.ptr_ty) "" llvm_builder
  | (EQ | NEQ) when p2 && null1 ->
      Llvm.build_icmp (if op = EQ then Llvm.Icmp.Eq else Llvm.Icmp.Ne) v2
        (Llvm.const_null ctx.ptr_ty) "" llvm_builder
  | LT when p1 && p2 -> Llvm.build_icmp Llvm.Icmp.Ult v1 v2 "" llvm_builder
  | LE when p1 && p2 -> Llvm.build_icmp Llvm.Icmp.Ule v1 v2 "" llvm_builder
  | _ -> both_int ()

(* An ite/select over values: a pointer if either branch is (D13's
   sanctioned inttoptr for a genuine pointer/integer mix). *)
let select ctx llvm_builder ?want cond tv fv =
  let tv, fv =
    if Llvm.type_of tv = Llvm.type_of fv then (tv, fv)
    else
      let target =
        match want with
        | Some t -> t
        | None ->
            if is_ptr_value tv || is_ptr_value fv then ctx.ptr_ty
            else Llvm.type_of tv
      in
      let cast v =
        if Llvm.type_of v = target then v
        else if
          is_ptr_value v
          && not (Llvm.classify_type target = Llvm.TypeKind.Pointer)
        then Llvm.build_ptrtoint v target "" llvm_builder
        else if
          (not (is_ptr_value v))
          && Llvm.classify_type target = Llvm.TypeKind.Pointer
        then Llvm.build_inttoptr v target "" llvm_builder
        else v
      in
      (cast tv, cast fv)
  in
  Llvm.build_select cond tv fv "" llvm_builder

(* A ptr value's real address (D6/D7): the storage's base GEP'd at the
   entry-line offset minus the storage's own base.  The window's base IS
   the entry line ([rel = 0]). *)
let materialize ctx scope llvm_builder blk_tid
    (storage : Hike_stack_model.ptr_storage) (off : Llvm.llvalue) :
    Llvm.llvalue =
  let entry =
    match !(scope.cur_frame) with
    | Some fr -> fr.entry_line
    | None ->
        Llvm.const_of_int64 (ctx.i64_ty) Hike_stack_model.segment_base false
  in
  let rel_off rel =
    let d = Llvm.build_sub off entry "entry_rel" llvm_builder in
    if Stdlib.Int64.equal rel 0L then d
    else
      Llvm.build_sub d (Llvm.const_of_int64 (ctx.i64_ty) rel false) ""
        llvm_builder
  in
  let region_ptr id =
    match !(scope.cur_frame) with
    | Some fr -> (
        match
          Base.List.find fr.regions ~f:(fun (m, _) ->
              Var.equal m (Hike_stack_model.region_mem id))
        with
        | Some (_, (base, rel)) -> gep_i8 ctx llvm_builder base (rel_off rel)
        | None -> as_pointer ctx llvm_builder off)
    | None -> as_pointer ctx llvm_builder off
  in
  match storage with
  | Hike_stack_model.Ptr_region id -> region_ptr id
  | Hike_stack_model.Ptr_residue -> region_ptr Hike_stack_model.residue_id
  | Hike_stack_model.Ptr_window -> (
      let wv = Hike_stack_model.hike_window_var ~word:ctx.abi.Abi.word in
      match
        (match get_ssaval scope wv with
         | Some x -> Some x
         | None -> get_local scope blk_tid wv)
      with
      | Some wp ->
          gep_i8 ctx llvm_builder wp
            (Llvm.build_sub off entry "entry_rel" llvm_builder)
      | None -> as_pointer ctx llvm_builder off)
  | Hike_stack_model.Ptr_vla -> as_pointer ctx llvm_builder off

(* The ONE as_int boundary (D10): a pointer escaping into an integer
   context becomes its integer form; nothing else changes. *)
let as_int ctx llvm_builder v = as_integer ctx llvm_builder v
