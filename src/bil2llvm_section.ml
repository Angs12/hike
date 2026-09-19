(* Emitter section lane: symtab remap, section globals, const-address loads. *)

open Bap.Std
module Abi = Hike_abi
module KB = Bap_knowledge.Knowledge
open Bil2llvm_env


(* Finds the LLVM function at a native address.  A promoted sub's
   address renders to its Thunk (the memory-convention twin): the
   twin is what a pointer call can enter with no provable arguments,
   so unresolvable sites stay sound; resolved sites call the promoted
   body directly and never consult this rendering. *)
let lookup_native_fn ctx llvm_module v =
  match ctx.symtab with
  | Some symtab -> (
      match Symtab.find_by_start symtab (Word.of_int64 ~width:64 v) with
      | Some (name, _, _) ->
          let fn = Llvm.lookup_function name llvm_module in
          (match fn with
           | Some f ->
               (match Base.List.Assoc.find ~equal:String.equal
                        !(ctx.thunks) name with
                | Some twin -> Some twin
                | None -> Some f)
           | None -> None)
      | None -> None)
  | None -> None

(* The owning global and byte offset of [v]: the base map picks the
   owner covering [v]; the identity (the section base at [lo]) covers
   the unsplit shape. *)
let section_target ~sec_base lo owners v =
  match
    Base.List.find owners ~f:(fun o ->
        Int64.compare o.own_lo v <= 0 && Int64.compare v o.own_hi <= 0)
  with
  | Some o -> (o.base, Int64.sub v o.own_lo)
  | None -> (sec_base, Int64.sub v lo)

(* The one address map: a function start renders to its function, a
   section byte to its OWNING global (the section base map — components
   and gap runs tile the section byte-exactly, so the base map is total
   and every rendered pointer is self-valid).  [finish] picks the form:
   the found value itself (the pointer form), or its ptrtoint (the
   integer form the address arithmetic consumes). *)
let remap_native ctx llvm_ctx llvm_module v ~finish =
  match lookup_native_fn ctx llvm_module v with
  | Some f -> Some (finish f)
  | None -> (
      match
        Base.List.find ctx.section_remap ~f:(fun (lo, hi, _, _) ->
            Int64.compare lo v <= 0 && Int64.compare v hi <= 0)
      with
      | Some (lo, _, g, owners) ->
        let base, offset = section_target ~sec_base:g lo owners v in
        Some
          (finish
             (Llvm.const_in_bounds_gep (Llvm.i8_type llvm_ctx) base
                [| Llvm.const_of_int64 (Llvm.i64_type llvm_ctx) offset false |]))
      | None -> None)

(* Remaps a native address to its lifted value: a function start to its
   Thunk/function, a section byte to its owning global. *)
let remap_native_addr ctx llvm_ctx llvm_module v =
  remap_native ctx llvm_ctx llvm_module v
    ~finish:(fun f -> Llvm.const_ptrtoint f (Llvm.i64_type llvm_ctx))

(* Declares a section global as [n x iN], [word] bytes per cell. *)
let create_section_global llvm_ctx llvm_module size name ~is_const ~word =
  let n64 = (size + word - 1) / word in
  let ret =
    Llvm.declare_global
      (Llvm.array_type (Llvm.integer_type llvm_ctx (word * 8)) n64)
      name llvm_module
  in
  Llvm.set_global_constant is_const ret;
  ret

(* The little-endian word assembler: the [len] bytes at [off] (bytes
   past the image read 0). *)
let word_of_bytes ~(arr : int array) ~(off : int) ~(len : int) : int64 =
  Base.List.fold
    (Base.List.init len ~f:(fun k -> len - 1 - k))
    ~init:0L
    ~f:(fun acc k ->
      let b =
        if off + k < Array.length arr then Int64.of_int arr.(off + k)
        else 0L
      in
      Int64.logor (Int64.shift_left acc 8) b)

(* A section initializer over the byte image — components, gap runs,
   and unsplit sections: the element width is [typed_w]; word-sized
   elements render through the one address map (remapped targets),
   ptr-typed elements render the target ADDRESS itself (the
   devirtualization prize), narrower elements chunk the raw bytes.
   BSS components are zero. *)
let set_owner_initializer ctx llvm_ctx llvm_module g
    (arr : int array) ~(word_lo : int) ~(word_hi : int)
    ~(typed_w : int) ~(bss : bool) ~word =
  let words = word_hi - word_lo + 1 in
  let word_ty = Llvm.integer_type llvm_ctx (word * 8) in
  let elem_ty =
    if typed_w >= word then word_ty
    else Llvm.integer_type llvm_ctx (typed_w * 8)
  in
  (* A word whose start boundary a printable string run crosses yields
     its raw bits: the value is text — remapping it would relocate the
     string's own bytes and corrupt the data (the model's
     [string_text_word] is the one home of the rule). *)
  let word64 (w : int) : Llvm.llvalue =
    let off = w * word in
    let v = word_of_bytes ~arr ~off ~len:word in
    if Hike_stack_model.string_text_word ~arr ~off then
      Llvm.const_of_int64 word_ty v false
    else
      match remap_native_addr ctx llvm_ctx llvm_module v with
      | Some c -> c
      | None -> Llvm.const_of_int64 word_ty v false
  in
  if bss then Llvm.set_initializer (Llvm.const_null elem_ty) g
  else if typed_w >= word then
    let slots = Base.Array.init words ~f:(fun i -> word64 (word_lo + i)) in
    Llvm.set_initializer (Llvm.const_array elem_ty slots) g
  else
    (* Narrow elements chunk the raw bytes (sub-word reads of
       relocated words keep the native bits). *)
    let chunks = words * (word / typed_w) in
    let elems =
      Base.Array.init chunks ~f:(fun i ->
          let byte_idx = (word_lo * word) + (i * typed_w) in
          let v = word_of_bytes ~arr ~off:byte_idx ~len:typed_w in
          Llvm.const_of_int64 elem_ty v false)
    in
    Llvm.set_initializer (Llvm.const_array elem_ty elems) g

(* Finds the section containing a word address. *)
let section_of_addr sections (addr : word) =
  Base.List.find sections ~f:(fun section ->
      Word.between ~low:section.min_addr addr ~high:section.max_addr)

(* The owner of [addr_i64] in [section]: (global, native base of the
   owner).  The identity arm is the whole-section array. *)
let owner_of section (addr_i64 : int64) : Llvm.llvalue * int64 =
  match section.owners with
  | [] -> (section.base, Word.to_int64_exn section.min_addr)
  | owners -> (
      match
        Base.List.find owners ~f:(fun o ->
            Int64.compare o.own_lo addr_i64 <= 0
            && Int64.compare addr_i64 o.own_hi <= 0)
      with
      | Some o -> (o.base, o.own_lo)
      | None -> (section.base, Word.to_int64_exn section.min_addr))

(* GEPs into the owner of the address (no scan). *)
let resolve_addr_in llvm_builder section addr =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let base, own_lo =
    owner_of section (Word.to_int64_exn addr)
  in
  let offset =
    Llvm.const_of_int64 (Llvm.i64_type llvm_ctx)
      (Int64.sub (Word.to_int64_exn addr) own_lo)
      false
  in
  return
  @@ Llvm.build_gep (Llvm.i8_type llvm_ctx) base [| offset |] ""
       llvm_builder

let resolve_addr llvm_builder addr =
  let open KB in
  let* sections = Context.get section_list_var in
  let section = section_of_addr sections addr in
  match section with
  | None ->
      (* Out-of-section address: the identity — the raw native
         constant inttoptr'd. *)
      let* llvm_ctx = Context.get llvm_ctx_var in
      let v =
        Llvm.const_of_int64 (Llvm.i64_type llvm_ctx)
          (Word.to_int64_exn addr) false
      in
      return
      @@ Llvm.build_inttoptr v (Llvm.pointer_type llvm_ctx) "" llvm_builder
  | Some section -> resolve_addr_in llvm_builder section addr

(* Materializes the pointer for an address integer: a real (foreign)
   address — the sret pointer, a reloaded pointer, a VLA address, a
   section/global constant — inttoptrs to itself; an already-pointer
   value is the identity. *)
let create_addr_ptr llvm_builder llvm_val =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  if
    Llvm.classify_type (Llvm.type_of llvm_val) = Llvm.TypeKind.Pointer
  then
    (* Already a pointer (a component's loaded value): the identity —
       the pointer IS the address. *)
    return llvm_val
  else
      return
      @@ Llvm.build_inttoptr llvm_val (Llvm.pointer_type llvm_ctx) ""
           llvm_builder

(* Section load with copy-reloc through-load. *)
let section_load_in llvm_builder llvm_ctx ctx section addr addr_i64 size =
  let open KB in
  let* base = resolve_addr_in llvm_builder section addr in
  if
    Base.List.exists ctx.copy_relocs ~f:(fun a ->
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
  | None ->
      (* Out-of-section address: the identity — load through the raw
         native pointer. *)
      let v =
        Llvm.const_of_int64 (Llvm.i64_type llvm_ctx) addr_i64 false
      in
      let p =
        Llvm.build_inttoptr v (Llvm.pointer_type llvm_ctx) "" llvm_builder
      in
      return
      @@ Llvm.build_load (Llvm.integer_type llvm_ctx size) p ""
           llvm_builder
  | Some section -> section_load_in llvm_builder llvm_ctx ctx section addr addr_i64 size

(* Const-address loads: the found section, else the fallback. The
   found section passes through (one scan). *)
let const_addr_load llvm_builder addr_w size ~fallback =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let* ctx = Context.get emit_ctx_var in
  let* sections = Context.get section_list_var in
  let v = Word.to_int64_exn addr_w in
  match section_of_addr sections addr_w with
  | Some section ->
      section_load_in llvm_builder llvm_ctx ctx section addr_w v size
  | None -> fallback ()

(* Const-address stores into the found section, else the fallback. The
   stored value arrives as a thunk so the section GEP keeps its emission
   order ahead of value-lane instructions.  The form's VALUE is the
   stored data (Bil.Store's type is the data's), never the void store
   instruction.  A store at a copy-relocated slot address goes THROUGH
   the slot's relocated pointer (the through-load's matching arm). *)
let const_addr_store llvm_builder addr_w ~data ~fallback =
  let open KB in
  let* sections = Context.get section_list_var in
  match section_of_addr sections addr_w with
  | Some section ->
      let* base = resolve_addr_in llvm_builder section addr_w in
      let* llvm_ctx = Context.get llvm_ctx_var in
      let* ctx = Context.get emit_ctx_var in
      let* llvm_var = data () in
      if
        Base.List.exists ctx.copy_relocs ~f:(fun a ->
            Int64.equal a (Word.to_int64_exn addr_w))
      then
        let p =
          Llvm.build_load (Llvm.i64_type llvm_ctx) base "" llvm_builder in
        let pp =
          Llvm.build_inttoptr p (Llvm.pointer_type llvm_ctx) "" llvm_builder in
        let _ : Llvm.llvalue = Llvm.build_store llvm_var pp llvm_builder in
        return llvm_var
      else
        let _ : Llvm.llvalue = Llvm.build_store llvm_var base llvm_builder in
        return llvm_var
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
let create_copy_reloc_bss llvm_ctx llvm_module size name copy_relocs ~word
    =
  let size = Int64.to_int size in
  let n64 = (size + word - 1) / word in
  let word_ty = Llvm.integer_type llvm_ctx (word * 8) in
  let ret =
    Llvm.declare_global (Llvm.array_type word_ty n64) name llvm_module
  in
  let arr = Array.init n64 (fun _ -> Llvm.const_int word_ty 0) in
  Base.List.iter copy_relocs ~f:(fun (off, sym_name) ->
      let extern =
        Llvm.declare_global (Llvm.i8_type llvm_ctx) sym_name llvm_module
      in
      arr.(off / word)
      <- Llvm.const_ptrtoint extern word_ty);
  Llvm.set_initializer (Llvm.const_array word_ty arr) ret;
  Llvm.set_global_constant false ret;
  ret

(* Per-object alignment from the native address (ctz, capped at 16). *)
let align_of native_lo =
  let rec ctz v n =
    if n < 4 && Int64.equal (Int64.logand v 1L) 0L then
      ctz (Int64.shift_right_logical v 1) (n + 1)
    else n
  in
  1 lsl ctz native_lo 0

(* The section construction, from the spec: per section, the plan's
   components tile the span byte-exactly into component globals and
   gap runs; a span with no components stays the identity (one
   whole-section array).  The gap runs draw their names from ONE
   counter across sections — per-section numbering would name two
   sections' runs alike, and the linker would fuse them into one
   global — and the counter consumes in the fixed tiling order, which
   is also the globals' declaration order. *)
let build_sections llvm_ctx llvm_module (spec : section_spec) : section list =
  let module Model = Hike_stack_model in
  let word = spec.spec_word in
  let comps_of lo hi =
    Base.List.filter spec.spec_comps ~f:(fun c ->
        Int64.equal c.Model.sec_lo lo && Int64.equal c.Model.sec_hi hi)
  in
  (* A span served whole: its own image global is the shared region
     id's storage, and one owner row wires the id to it (the converted
     lane GEPs the same global the raw lane resolves). *)
  let whole_id lo hi =
    Base.List.find_map spec.spec_whole ~f:(fun (i, l, h) ->
        if Int64.equal l lo && Int64.equal h hi then Some i else None)
  in
  let counter = ref (Base.List.length spec.spec_comps) in
  let create_run_global name ~words ~bss =
    let ty = Llvm.array_type (Llvm.integer_type llvm_ctx (word * 8)) words in
    let g = Llvm.declare_global ty name llvm_module in
    Llvm.set_linkage Llvm.Linkage.Internal g;
    Llvm.set_alignment 16 g;
    if bss then Llvm.set_initializer (Llvm.const_null ty) g;
    g
  in
  let create_comp_global name (c : Model.sec_comp) ~is_const ~bss =
    let words = c.Model.hi_w - c.Model.lo_w + 1 in
    let ty =
      if c.Model.typed_w >= word then
        Llvm.array_type (Llvm.integer_type llvm_ctx (word * 8)) words
      else
        Llvm.array_type
          (Llvm.integer_type llvm_ctx (c.Model.typed_w * 8))
          (words * (word / c.Model.typed_w))
    in
    let g = Llvm.declare_global ty name llvm_module in
    Llvm.set_linkage Llvm.Linkage.Internal g;
    Llvm.set_global_constant (is_const && not bss) g;
    Llvm.set_alignment
      (align_of (Int64.add c.Model.sec_lo (Int64.of_int (c.Model.lo_w * word))))
      g;
    if bss then Llvm.set_initializer (Llvm.const_null ty) g;
    g
  in
  let tile name ~(comps : Model.sec_comp list) ~lo ~hi ~words ~is_const ~bss
      ~arr =
    let sorted =
      Base.List.sort comps ~compare:(fun a b ->
          Int.compare a.Model.lo_w b.Model.lo_w)
    in
    let owners = ref [] in
    let cursor = ref 0 in
    Base.List.iter sorted ~f:(fun c ->
        if c.Model.lo_w > !cursor then begin
          let g =
            create_run_global (Model.sec_res_name !counter)
              ~words:(c.Model.lo_w - !cursor) ~bss
          in
          owners :=
            { own_id = None;
              own_lo = Int64.add lo (Int64.of_int (!cursor * word));
              own_hi =
                Int64.add lo (Int64.of_int (c.Model.lo_w * word - 1));
              base = g;
              typed_w = word;
            }
            :: !owners;
          counter := !counter + 1
        end;
        let g =
          create_comp_global (Model.sec_comp_name c.Model.comp_id) c
            ~is_const ~bss
        in
        owners :=
          { own_id = Some c.Model.comp_id;
            own_lo = Int64.add lo (Int64.of_int (c.Model.lo_w * word));
            own_hi =
              Int64.add lo
                (Int64.of_int (c.Model.hi_w * word + (word - 1)));
            base = g;
            typed_w = c.Model.typed_w;
          }
          :: !owners;
        cursor := c.Model.hi_w + 1);
    if !cursor < words then begin
      let g =
        create_run_global (Model.sec_res_name !counter)
          ~words:(words - !cursor) ~bss
      in
      owners :=
        { own_id = None;
          own_lo = Int64.add lo (Int64.of_int (!cursor * word));
          own_hi = hi;
          base = g;
          typed_w = word;
        }
        :: !owners;
      counter := !counter + 1
    end;
    let owners = Base.List.rev !owners in
#ifdef VSA_DEBUG
    Printf.eprintf "t18tile: %s words=%d owners=%d\n" name words
      (Base.List.length owners);
    Base.List.iter owners ~f:(fun o ->
        Printf.eprintf "  owner id=%s lo=%Lx hi=%Lx base=%s\n"
          (match o.own_id with Some i -> Int.to_string i | None -> "gap")
          o.own_lo o.own_hi (Llvm.value_name o.base));
#endif
    let base = match owners with o :: _ -> o.base | [] -> assert false in
    { base; min_addr = Word.of_int64 ~width:64 lo;
      max_addr = Word.of_int64 ~width:64 hi; bytes = arr; owners }
  in
  let build_entry (entry : sec_input) : section =
    match entry with
    | Sec_bss { si_lo; si_hi; si_words; si_copy_relocs } ->
        let llvm_name = section_type_to_string BSS in
        let comps = comps_of si_lo si_hi in
        let whole = whole_id si_lo si_hi in
        if not (Base.List.is_empty comps) && Option.is_none whole then
          tile llvm_name ~comps ~lo:si_lo ~hi:si_hi ~words:si_words
            ~is_const:false ~bss:true ~arr:None
        else
          let size = Int64.sub (Int64.add si_hi 1L) si_lo in
          let base =
            if si_copy_relocs = [] then
              create_uninitialized_global llvm_ctx llvm_module size llvm_name
            else
              create_copy_reloc_bss llvm_ctx llvm_module size llvm_name
                si_copy_relocs ~word
          in
          let owners =
            match whole with
            | Some id ->
                [ { own_id = Some id;
                    own_lo = si_lo;
                    own_hi = si_hi;
                    base;
                    typed_w = word } ]
            | None -> []
          in
          let addr = Int64.to_int si_lo in
          let size = Int64.to_int size in
          { base;
            min_addr = Word.of_int ~width:64 addr;
            max_addr = Word.of_int ~width:64 (addr + size - 1);
            bytes = None;
            owners }
    | Sec_bytes { si_type; si_lo; si_hi; si_words; si_const; si_image } ->
        let llvm_name = section_type_to_string si_type in
        let comps = comps_of si_lo si_hi in
        let whole = whole_id si_lo si_hi in
        if not (Base.List.is_empty comps) && Option.is_none whole then
          tile llvm_name ~comps ~lo:si_lo ~hi:si_hi ~words:si_words
            ~is_const:si_const ~bss:false ~arr:(Some si_image)
        else
          let base =
            create_section_global llvm_ctx llvm_module
              (Array.length si_image) llvm_name ~is_const:si_const ~word
          in
          let owners =
            match whole with
            | Some id ->
                [ { own_id = Some id;
                    own_lo = si_lo;
                    own_hi = si_hi;
                    base;
                    typed_w = word } ]
            | None -> []
          in
          { base;
            min_addr = Word.of_int64 ~width:64 si_lo;
            max_addr = Word.of_int64 ~width:64 si_hi;
            bytes = Some si_image;
            owners }
  in
  let key_of = function
    | Sec_bss _ -> BSS
    | Sec_bytes { si_type; _ } -> si_type
  in
  let built =
    Base.List.filter_map
      [ BSS; GOT; GOTPLT; RODATA_REL; DATA; RODATA; TEXT ]
      ~f:(fun t ->
        Base.List.find_map spec.spec_sections ~f:(fun e ->
            match e with
            | Some si when key_of si = t -> Some (t, build_entry si)
            | _ -> None))
  in
  (* The output order is the fixed section-list order; an absent
     section warns with its index. *)
  Base.List.filter_mapi spec.spec_sections ~f:(fun i e ->
      match e with
      | None ->
          Hike_diag.warn "section %d was not found in binary" i;
          None
      | Some si ->
          let t = key_of si in
          Base.List.find_map built ~f:(fun (bt, s) ->
              if bt = t then Some s else None))
