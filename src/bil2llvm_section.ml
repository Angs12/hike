(* Emitter section lane: symtab remap, section globals, const-address loads. *)

open Bap.Std
module Abi = Hike_abi
open Bil2llvm_env


(* Finds the LLVM function at a native address; a promoted sub
   renders to its thunk so unresolvable pointer sites stay sound. *)
let lookup_native_fn ctx llvm_module v =
  (* The start-set precheck: the initializer path asks per word and
     the vast majority name data, not functions. *)
  if not (Core.Set.mem ctx.native_starts v) then None
  else Base.Option.bind ctx.symtab ~f:(fun symtab ->
      Base.Option.bind
        (Symtab.find_by_start symtab (Word.of_int64 ~width:64 v))
        ~f:(fun (name, _, _) ->
          let fn = Llvm.lookup_function name llvm_module in
          Base.Option.map fn ~f:(fun f ->
              Base.Option.value
                (Base.List.Assoc.find ~equal:String.equal !(ctx.thunks) name)
                ~default:f)))

(* (global, owner base) for the address; no owners = the
   whole-section array. *)
let owner_of section (addr_i64 : int64) : Llvm.llvalue * int64 =
  let identity = (section.base, Word.to_int64_exn section.min_addr) in
  match section.owners with
  | [] -> identity
  | owners ->
      Base.Option.value
        (Base.Option.map
           (Base.List.find owners ~f:(fun o ->
                Int64.compare o.own_lo addr_i64 <= 0
                && Int64.compare addr_i64 o.own_hi <= 0))
           ~f:(fun o -> (o.base, o.own_lo)))
        ~default:identity

(* The one address map: a function start to its function, a section
   byte to its owning global (owners tile byte-exactly, so every
   rendered pointer is valid).  [finish] picks pointer vs ptrtoint. *)
let remap_native ctx llvm_ctx llvm_module v ~finish =
  Base.Option.first_some
    (Base.Option.map (lookup_native_fn ctx llvm_module v) ~f:finish)
    (Base.Option.bind
       (Base.List.find ctx.sections ~f:(fun s ->
            let lo = Word.to_int64_exn s.min_addr in
            let hi = Word.to_int64_exn s.max_addr in
            Int64.compare lo v <= 0 && Int64.compare v hi <= 0))
       ~f:(fun section ->
         let base, own_lo = owner_of section v in
         Some
           (finish
              (Llvm.const_in_bounds_gep (Llvm.i8_type llvm_ctx) base
                 [| Llvm.const_of_int64 (Llvm.i64_type llvm_ctx)
                      (Int64.sub v own_lo) false |]))))

let remap_native_addr ctx llvm_ctx llvm_module v =
  remap_native ctx llvm_ctx llvm_module v
    ~finish:(fun f -> Llvm.const_ptrtoint f (Llvm.i64_type llvm_ctx))

(* The remapped address integer, else the raw constant. *)
let remapped_const ctx llvm_ctx llvm_module v ty =
  Base.Option.value (remap_native_addr ctx llvm_ctx llvm_module v)
    ~default:(Llvm.const_of_int64 ty v false)

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
let word_of_bytes ~(arr : Bytes.t) ~(off : int) ~(len : int) : int64 =
  (* Shifts fold little-endian bytes; bytes past the image read zero. *)
  let b k =
    if off + k < Bytes.length arr
    then Int64.of_int (Char.code (Bytes.get arr (off + k)))
    else 0L
  in
  let rec go acc k =
    if k = len then acc
    else
      let acc' =
        if k = 0 then b 0 else Stdlib.Int64.logor acc (Stdlib.Int64.shift_left (b k) (8 * k))
      in
      go acc' (k + 1)
  in
  go 0L 0

(* A section initializer over the byte image: word-sized elements
   render through the address map (pointer-valued words render the
   target address itself), narrower elements chunk the raw bytes;
   BSS is zero. *)
let set_owner_initializer ctx llvm_ctx llvm_module g
    (arr : Bytes.t) ~(word_lo : int) ~(word_hi : int)
    ~(typed_w : int) ~(bss : bool) ~word =
  let words = word_hi - word_lo + 1 in
  let word_ty = Llvm.integer_type llvm_ctx (word * 8) in
  let elem_ty =
    if typed_w >= word then word_ty
    else Llvm.integer_type llvm_ctx (typed_w * 8)
  in
  (* A word inside a printable string run keeps its raw bits:
     remapping it would relocate the string's own bytes.  The text
     table is one prepass over the image, not a rescan per word. *)
  let text = Hike_stack_model.string_text_table arr in
  let word64 (w : int) : Llvm.llvalue =
    let off = w * word in
    let v = word_of_bytes ~arr ~off ~len:word in
    if text off then Llvm.const_of_int64 word_ty v false
    else remapped_const ctx llvm_ctx llvm_module v word_ty
  in
  if bss then Llvm.set_initializer (Llvm.const_null elem_ty) g
  else if typed_w >= word then
    let slots = Base.Array.init words ~f:(fun i -> word64 (word_lo + i)) in
    Llvm.set_initializer (Llvm.const_array elem_ty slots) g
  else
    let chunks = words * (word / typed_w) in
    let elems =
      Base.Array.init chunks ~f:(fun i ->
          let byte_idx = (word_lo * word) + (i * typed_w) in
          let v = word_of_bytes ~arr ~off:byte_idx ~len:typed_w in
          Llvm.const_of_int64 elem_ty v false)
    in
    Llvm.set_initializer (Llvm.const_array elem_ty elems) g

let section_of_addr sections (addr : word) =
  Base.List.find sections ~f:(fun section ->
      Word.between ~low:section.min_addr addr ~high:section.max_addr)

let resolve_addr_in ctx llvm_builder section addr =
  let base, own_lo =
    owner_of section (Word.to_int64_exn addr)
  in
  let offset =
    Llvm.const_of_int64 (ctx.i64_ty)
      (Int64.sub (Word.to_int64_exn addr) own_lo)
      false
  in
  Llvm.build_gep (Llvm.i8_type ctx.llvm_ctx) base [| offset |] ""
    llvm_builder

let resolve_addr ctx llvm_builder addr =
  match section_of_addr ctx.sections addr with
  | None ->
      (* Out-of-section address: inttoptr of the raw constant. *)
      let v =
        Llvm.const_of_int64 (ctx.i64_ty)
          (Word.to_int64_exn addr) false
      in
      Llvm.build_inttoptr v (Llvm.pointer_type ctx.llvm_ctx) "" llvm_builder
  | Some section -> resolve_addr_in ctx llvm_builder section addr

(* Materializes the pointer for an address integer; an
   already-pointer value passes through. *)
let create_addr_ptr ctx llvm_builder llvm_val =
  if Llvm.classify_type (Llvm.type_of llvm_val) = Llvm.TypeKind.Pointer
  then llvm_val
  else
    Llvm.build_inttoptr llvm_val (Llvm.pointer_type ctx.llvm_ctx) ""
      llvm_builder

(* Section load with copy-reloc through-load. *)
let section_load_in llvm_builder llvm_ctx ctx section addr addr_i64 size =
  let base = resolve_addr_in ctx llvm_builder section addr in
  if
    Base.List.exists ctx.copy_relocs ~f:(fun a ->
        Int64.equal a addr_i64)
  then begin
    let p =
      Llvm.build_load (Llvm.i64_type llvm_ctx) base "" llvm_builder
    in
    let pp =
      Llvm.build_inttoptr p (Llvm.pointer_type llvm_ctx) "" llvm_builder
    in
    Llvm.build_load (Llvm.integer_type llvm_ctx size) pp ""
      llvm_builder
  end
  else
    Llvm.build_load (Llvm.integer_type llvm_ctx size) base ""
      llvm_builder

let section_load ctx llvm_builder llvm_ctx addr addr_i64 size =
  match section_of_addr ctx.sections addr with
  | None ->
      (* Out-of-section address: load through the raw native pointer. *)
      let v =
        Llvm.const_of_int64 (Llvm.i64_type llvm_ctx) addr_i64 false
      in
      let p =
        Llvm.build_inttoptr v (Llvm.pointer_type llvm_ctx) "" llvm_builder
      in
      Llvm.build_load (Llvm.integer_type llvm_ctx size) p ""
        llvm_builder
  | Some section -> section_load_in llvm_builder llvm_ctx ctx section addr addr_i64 size

(* Const-address loads through the found section, else the fallback. *)
let const_addr_load ctx llvm_builder addr_w size ~fallback =
  let v = Word.to_int64_exn addr_w in
  match section_of_addr ctx.sections addr_w with
  | Some section ->
      section_load_in llvm_builder ctx.llvm_ctx ctx section addr_w v size
  | None -> fallback ()

(* Const-address stores: the stored value arrives as a thunk so the
   section GEP precedes it and the form's value is the stored data.
   A copy-relocated slot address stores through the slot's pointer. *)
let const_addr_store ctx llvm_builder addr_w ~data ~fallback =
  match section_of_addr ctx.sections addr_w with
  | Some section ->
      let base = resolve_addr_in ctx llvm_builder section addr_w in
      let llvm_var = data () in
      if
        Base.List.exists ctx.copy_relocs ~f:(fun a ->
            Int64.equal a (Word.to_int64_exn addr_w))
      then begin
        let p =
          Llvm.build_load (ctx.i64_ty) base "" llvm_builder in
        let pp =
          Llvm.build_inttoptr p (Llvm.pointer_type ctx.llvm_ctx) "" llvm_builder in
        let _ : Llvm.llvalue = Llvm.build_store llvm_var pp llvm_builder in
        llvm_var
      end
      else
        let _ : Llvm.llvalue = Llvm.build_store llvm_var base llvm_builder in
        llvm_var
  | None -> fallback ()

(* A global [n x elem_ty] array; [None] zero-initializes. *)
let create_array_global llvm_ctx llvm_module name elem_ty n slots =
  let g = Llvm.declare_global (Llvm.array_type elem_ty n) name llvm_module in
  let init =
    Base.Option.value_map slots
      ~default:(Llvm.const_null (Llvm.array_type elem_ty n))
      ~f:(Llvm.const_array elem_ty)
  in
  Llvm.set_initializer init g;
  Llvm.set_global_constant false g;
  g

let create_uninitialized_global llvm_ctx llvm_module size name =
  create_array_global llvm_ctx llvm_module name (Llvm.i8_type llvm_ctx)
    (Int64.to_int size) None

let create_copy_reloc_bss llvm_ctx llvm_module size name copy_relocs ~word
    =
  let size = Int64.to_int size in
  let n64 = (size + word - 1) / word in
  let word_ty = Llvm.integer_type llvm_ctx (word * 8) in
  match copy_relocs with
  | [] -> create_array_global llvm_ctx llvm_module name word_ty n64 None
  | _ ->
      let arr = Array.init n64 (fun _ -> Llvm.const_int word_ty 0) in
      Base.List.iter copy_relocs ~f:(fun (off, sym_name) ->
          let extern =
            Llvm.declare_global (Llvm.i8_type llvm_ctx) sym_name llvm_module
          in
          arr.(off / word)
          <- Llvm.const_ptrtoint extern word_ty);
      create_array_global llvm_ctx llvm_module name word_ty n64 (Some arr)

(* Per-object alignment from the native address (ctz, capped at 16). *)
let align_of native_lo =
  let rec ctz v n =
    if n < 4 && Int64.equal (Int64.logand v 1L) 0L then
      ctz (Int64.shift_right_logical v 1) (n + 1)
    else n
  in
  1 lsl ctz native_lo 0

(* Builds the sections from the spec: components tile each span
   byte-exactly into component globals and gap runs; a span with no
   components stays one whole-section array.  Gap runs draw names
   from ONE counter across sections — colliding names would let the
   linker fuse two runs into one global. *)
let build_sections llvm_ctx llvm_module (spec : section_spec) : section list =
  let module Model = Hike_stack_model in
  let word = spec.spec_word in
  let comps_of lo hi =
    Base.List.filter spec.spec_comps ~f:(fun c ->
        Int64.equal c.Model.sec_lo lo && Int64.equal c.Model.sec_hi hi)
  in
  (* A span served whole: its image global is the region id's
     storage, wired by one owner row. *)
  let whole_id lo hi =
    Base.List.find_map spec.spec_whole ~f:(fun (i, l, h) ->
        if Int64.equal l lo && Int64.equal h hi then Some i else None)
  in
  let counter = ref (Base.List.length spec.spec_comps) in
  (* One internal array global: the gap runs and the components share
     the declaration; the run path pins the 16 alignment (its spans
     are word-grid filler), the component path aligns to the native
     base. *)
  let declare_internal_array name ~elem_ty ~n ~align ~const ~init =
    let g = Llvm.declare_global (Llvm.array_type elem_ty n) name llvm_module in
    Llvm.set_linkage Llvm.Linkage.Internal g;
    Llvm.set_global_constant const g;
    Llvm.set_alignment align g;
    Option.iter (fun v -> Llvm.set_initializer v g) init;
    g
  in
  let create_run_global name ~words ~bss =
    let ty = Llvm.integer_type llvm_ctx (word * 8) in
    declare_internal_array name ~elem_ty:ty ~n:words
      ~align:Abi.stack_align ~const:false
      ~init:(if bss then Some (Llvm.const_null (Llvm.array_type ty words)) else None)
  in
  let create_comp_global name (c : Model.sec_comp) ~is_const ~bss =
    let words = c.Model.hi_w - c.Model.lo_w + 1 in
    let elem_ty =
      if c.Model.typed_w >= word then Llvm.integer_type llvm_ctx (word * 8)
      else Llvm.integer_type llvm_ctx (c.Model.typed_w * 8)
    in
    let n =
      if c.Model.typed_w >= word then words
      else words * (word / c.Model.typed_w)
    in
    let ty = Llvm.array_type elem_ty n in
    declare_internal_array name ~elem_ty ~n
      ~align:(align_of (Int64.add c.Model.sec_lo (Int64.of_int (c.Model.lo_w * word))))
      ~const:(is_const && not bss)
      ~init:(if bss then Some (Llvm.const_null ty) else None)
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
    Printf.eprintf "sections: %s words=%d owners=%d\n" name words
      (Base.List.length owners);
    Base.List.iter owners ~f:(fun o ->
        Printf.eprintf "  owner id=%s lo=%Lx hi=%Lx base=%s\n"
          (Base.Option.value_map o.own_id ~default:"gap" ~f:Int.to_string)
          o.own_lo o.own_hi (Llvm.value_name o.base));
#endif
    let base = match owners with o :: _ -> o.base | [] -> assert false in
    { base; min_addr = Word.of_int64 ~width:64 lo;
      max_addr = Word.of_int64 ~width:64 hi; bytes = arr; owners }
  in
  let build_entry (entry : sec_input) : section =
    match entry with
    | Sec_bss { si_lo; si_hi; si_words; si_copy_relocs } ->
        let llvm_name = section_type_to_string Model.Bss in
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
            Base.Option.value_map whole ~default:[] ~f:(fun id ->
                [ { own_id = Some id;
                    own_lo = si_lo;
                    own_hi = si_hi;
                    base;
                    typed_w = word } ])
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
              (Bytes.length si_image) llvm_name ~is_const:si_const ~word
          in
          let owners =
            Base.Option.value_map whole ~default:[] ~f:(fun id ->
                [ { own_id = Some id;
                    own_lo = si_lo;
                    own_hi = si_hi;
                    base;
                    typed_w = word } ])
          in
          { base;
            min_addr = Word.of_int64 ~width:64 si_lo;
            max_addr = Word.of_int64 ~width:64 si_hi;
            bytes = Some si_image;
            owners }
  in
  (* One pass over the spec: each present section builds and lands in
     the spec's own order; a section the binary lacks warns and emits
     nothing. *)
  Base.List.filter_mapi spec.spec_sections ~f:(fun i e ->
      match e with
      | None ->
          Hike_diag.warn "section %d was not found in binary" i;
          None
      | Some si -> Some (build_entry si))
