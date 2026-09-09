(* Emitter section lane: symtab remap, section globals, const-address loads. *)

open Bap.Std
open Convutils
module Abi = Hike_abi
module KB = Bap_knowledge.Knowledge
open Bil2llvm_env


(* Finds the LLVM function at a native address. *)
let lookup_native_fn ctx llvm_module v =
  match ctx.Convutils.symtab with
  | Some symtab -> (
      match Symtab.find_by_start symtab (Word.of_int64 ~width:64 v) with
      | Some (name, _, _) -> Llvm.lookup_function name llvm_module
      | None -> None)
  | None -> None

(* Remaps a native address to its lifted value. *)
let remap_native_addr ctx llvm_ctx llvm_module v =
  match lookup_native_fn ctx llvm_module v with
  | Some f -> Some (Llvm.const_ptrtoint f (Llvm.i64_type llvm_ctx))
  | None -> (
      match
        Base.List.find ctx.Convutils.section_remap ~f:(fun (lo, hi, _) ->
            Int64.compare lo v <= 0 && Int64.compare v hi <= 0)
      with
      | Some (lo, _, g) ->
          let offset =
            Llvm.const_of_int64 (Llvm.i64_type llvm_ctx)
              (Int64.sub v lo) false
          in
          let gep =
            Llvm.const_in_bounds_gep (Llvm.i8_type llvm_ctx) g
              [| offset |]
          in
          Some (Llvm.const_ptrtoint gep (Llvm.i64_type llvm_ctx))
      | None -> None)

(* Declares a section global as [n x i64]. *)
let create_section_global llvm_ctx llvm_module size name ~is_const =
  let n64 = (size + 7) / 8 in
  let ret =
    Llvm.declare_global
      (Llvm.array_type (Llvm.i64_type llvm_ctx) n64)
      name llvm_module
  in
  Llvm.set_global_constant is_const ret;
  ret

(* Reads a stashed .text constant. *)
let text_load_constant ctx llvm_ctx llvm_module addr w =
  let v = Word.to_int64_exn addr in
  match ctx.Convutils.text_section with
  | Some (arr, tmin, tmax)
    when Int64.compare v tmin >= 0 && Int64.compare v tmax <= 0 ->
      let off = Int64.to_int (Int64.sub v tmin) in
      let bytes =
        Base.Sequence.fold
          (Base.Sequence.range 0 (w / 8))
          ~init:0L
          ~f:(fun acc i ->
            let b =
              if off + i < Array.length arr then
                Int64.of_int arr.(off + i)
              else 0L
            in
            Int64.logor acc (Int64.shift_left b (i * 8)))
      in
      let remapped = lookup_native_fn ctx llvm_module bytes in
      let c =
        match remapped with
        | Some f -> Llvm.const_ptrtoint f (Llvm.i64_type llvm_ctx)
        | None ->
            Llvm.const_of_int64 (Llvm.integer_type llvm_ctx w) bytes false
      in
      Some c
  | _ -> None

(* Builds a remapped section initializer. *)
let set_section_initializer ctx llvm_ctx llvm_module g arr min_addr =
  let n64 = (Array.length arr + 7) / 8 in
  let slot_at i =
    let v =
      Base.List.fold [ 7; 6; 5; 4; 3; 2; 1; 0 ] ~init:0L ~f:(fun acc k ->
          let b =
            if (i * 8) + k < Array.length arr then
              Int64.of_int arr.((i * 8) + k)
            else 0L
          in
          Int64.logor (Int64.shift_left acc 8) b)
    in
    match remap_native_addr ctx llvm_ctx llvm_module v with
    | Some c -> c
    | None ->
        Llvm.const_of_int64 (Llvm.i64_type llvm_ctx) v false
  in
  let slots = Array.init n64 slot_at in
  Llvm.set_initializer (Llvm.const_array (Llvm.i64_type llvm_ctx) slots) g

(* Finds the section containing a word address. *)
let section_of_addr sections (addr : word) =
  Base.List.find sections ~f:(fun section ->
      Word.between ~low:section.min_addr addr ~high:section.max_addr)

(* GEPs into a found section (no scan). *)
let resolve_addr_in llvm_builder section addr =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let offset =
    Llvm.const_of_int64 (Llvm.i64_type llvm_ctx)
      (Word.sub addr section.min_addr |> Word.to_int64_exn)
      false
  in
  return
  @@ Llvm.build_gep (Llvm.i8_type llvm_ctx) section.base [| offset |] ""
       llvm_builder

let resolve_addr llvm_builder addr =
  let open KB in
  let* sections = Context.get section_list_var in
  let section = section_of_addr sections addr in
  match section with
  | None -> failwith "load: addr not found"
  | Some section -> resolve_addr_in llvm_builder section addr

let create_inttoptr llvm_builder llvm_val =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  return
  @@ Llvm.build_inttoptr llvm_val (Llvm.pointer_type llvm_ctx) "" llvm_builder

(* Section load with copy-reloc through-load. *)
let section_load_in llvm_builder llvm_ctx ctx section addr addr_i64 size =
  let open KB in
  let* base = resolve_addr_in llvm_builder section addr in
  if
    Base.List.exists ctx.Convutils.copy_relocs ~f:(fun a ->
        Int64.equal a addr_i64)
  then
    (* Loads through copy-relocated pointers. *)
    let p =
      Llvm.build_load (Llvm.i64_type llvm_ctx) base "" llvm_builder
    in
    let pp =
      Llvm.build_inttoptr p (Llvm.pointer_type llvm_ctx) "" llvm_builder
    in
    return
    @@ Llvm.build_load (Llvm.integer_type llvm_ctx size) pp ""
         llvm_builder
  else
    return
    @@ Llvm.build_load (Llvm.integer_type llvm_ctx size) base ""
         llvm_builder

let section_load llvm_builder llvm_ctx addr addr_i64 size =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  let* sections = Context.get section_list_var in
  match section_of_addr sections addr with
  | None -> failwith "load: addr not found"
  | Some section -> section_load_in llvm_builder llvm_ctx ctx section addr addr_i64 size

(* Const-address loads: stashed .text bytes, then the found section, else
   the fallback. The found section passes through (one scan). *)
let const_addr_load llvm_builder addr_w size ~fallback =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let* llvm_module = Context.get llvm_module_var in
  let* ctx = Context.get emit_ctx_var in
  let* sections = Context.get section_list_var in
  (* Reads stashed .text bytes first. *)
  let v = Word.to_int64_exn addr_w in
  match text_load_constant ctx llvm_ctx llvm_module addr_w size with
  | Some c -> return c
  | None -> (
      match section_of_addr sections addr_w with
      | Some section ->
          section_load_in llvm_builder llvm_ctx ctx section addr_w v size
      | None -> fallback ())

(* Const-address stores into the found section, else the fallback. The
   stored value arrives as a thunk so the section GEP keeps its emission
   order ahead of value-lane instructions. *)
let const_addr_store llvm_builder addr_w ~data ~fallback =
  let open KB in
  let* sections = Context.get section_list_var in
  match section_of_addr sections addr_w with
  | Some section ->
      let* base = resolve_addr_in llvm_builder section addr_w in
      let* llvm_var = data () in
      return @@ Llvm.build_store llvm_var base llvm_builder
  | None -> fallback ()

let create_empty_llvm_i8array llvm_ctx size =
  Array.init size (fun _ -> Llvm.const_int (Llvm.i8_type llvm_ctx) 0)
  |> Llvm.const_array (Llvm.i8_type llvm_ctx)

let create_uninitialized_global llvm_ctx llvm_module size name =
  let size = Int64.to_int size in
  let ret =
    Llvm.declare_global
      (Llvm.array_type (Llvm.i8_type llvm_ctx) size)
      name llvm_module
  in
  Llvm.set_initializer (create_empty_llvm_i8array llvm_ctx size) ret;
  Llvm.set_global_constant false ret;
  ret

(* Builds bss with copy-relocated slots. *)
let create_copy_reloc_bss llvm_ctx llvm_module size name copy_relocs =
  let size = Int64.to_int size in
  let n64 = (size + 7) / 8 in
  let ret =
    Llvm.declare_global
      (Llvm.array_type (Llvm.i64_type llvm_ctx) n64)
      name llvm_module
  in
  let arr =
    Array.init n64 (fun _ -> Llvm.const_int (Llvm.i64_type llvm_ctx) 0)
  in
  Base.List.iter copy_relocs ~f:(fun (off, sym_name) ->
      let extern =
        Llvm.declare_global (Llvm.i8_type llvm_ctx) sym_name llvm_module
      in
      arr.(off / 8)
      <- Llvm.const_ptrtoint extern (Llvm.i64_type llvm_ctx));
  Llvm.set_initializer (Llvm.const_array (Llvm.i64_type llvm_ctx) arr) ret;
  Llvm.set_global_constant false ret;
  ret
