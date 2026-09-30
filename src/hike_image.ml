(* The ELF-image readers: named-section lookup, section bytes,
   copy-relocated bss slots, the relocated-word substitution, and named
   regions. *)

open Bap.Std

type region = { addr : int64; size : int64; name : string }

let get_section_mem name proj =
  Project.memory proj |> Memmap.to_sequence
  |> Seq.find ~f:(fun (_, v) ->
      Base.Option.value_map (Value.get Image.section v) ~default:false
        ~f:(fun n -> String.equal n name))

(* Eta-expanded so the weak type variable of the point-free spelling
   resolves here, not at a use site. *)
let get_section_data x =
  Base.Option.map x ~f:(fun (mem, _) ->
      let length = Memory.length mem in
      let buf = Memory.to_buffer mem in
      let arr = Bytes.create length in
      for i = 0 to length - 1 do
        Bytes.set arr i (Core.Bigsubstring.get buf i)
      done;
      (arr, Memory.min_addr mem, Memory.max_addr mem))

let get_copy_relocations proj ~bss_addr ~bss_size =
  let rows =
    let open Ogre in
    let at = Type.("at" %: int) in
    let name = Type.("name" %: str) in
    let nr_tbl = Type.(scheme at $ name) in
    let name_ref () =
      Ogre.declare ~name:"llvm:name-reference" nr_tbl (fun a n -> (a, n))
    in
    let c = Ogre.collect Query.(select (from name_ref)) in
    fst (Ogre.run c (Project.specification proj) |> Core.Or_error.ok_exn)
  in
  Base.Sequence.to_list rows
  |> Base.List.filter_map ~f:(fun (fixup, name) ->
         let off = Stdlib.Int64.sub fixup bss_addr in
         if
           Stdlib.Int64.compare off 0L >= 0
           && Stdlib.Int64.compare off bss_size < 0
         then Some (Stdlib.Int64.to_int off, name)
         else None)
  |> Base.List.dedup_and_sort ~compare:(fun (a, _) (b, _) -> Int.compare a b)

(* Every word the loader's relocation facts name: a load-time relocation
   result, so a word at one of these addresses is not its file bytes. *)
let get_relocated_words (proj : Project.t) : int64 list =
  let open Ogre in
  let collect attr = Ogre.collect Query.(select (from attr)) in
  let relr = collect Image.Scheme.relative_relocation in
  let rel = collect Image.Scheme.relocation in
  let ext = collect Image.Scheme.external_reference in
  let spec = Project.specification proj in
  let rows q = fst (Ogre.run q spec |> Core.Or_error.ok_exn) in
  let relr = Base.Sequence.to_list (rows relr) in
  let rel = Base.Sequence.to_list (rows rel) |> Base.List.map ~f:fst in
  let ext = Base.Sequence.to_list (rows ext) |> Base.List.map ~f:fst in
  relr @ rel @ ext

(* A RELA-format relocation section ([.rela.dyn], [.rela.plt], ...):
   its entries carry the addend the loader's facts omit. *)
let is_rela_section (name : string) : bool =
  String.length name >= 5 && String.equal (String.sub name 0 5) ".rela"

(* x86-64 [R_X86_64_RELATIVE]: the stored word is [base + addend],
   the addend a link-time in-module address. *)
let r_x86_64_relative = 8L

(* The RELA entry layout: r_offset, r_info, r_addend, 8 bytes each. *)
let rela_stride = 24
let rela_info_off = 8
let rela_addend_off = 16

(* The (site, type, addend) rows of a RELA section's bytes. *)
let rela_rows (bytes : Bytes.t) : (int64 * int64 * int64) list =
  let len = Bytes.length bytes in
  let u64 off =
    let acc = ref 0L in
    for k = 0 to 7 do
      acc :=
        Int64.logor !acc
          (Int64.shift_left
             (Int64.of_int (Char.code (Bytes.get bytes (off + k))))
             (8 * k))
    done;
    !acc
  in
  let rec go off acc =
    if off + rela_stride > len then Base.List.rev acc
    else
      let site = u64 off in
      let typ = Int64.logand (u64 (off + rela_info_off)) 0xffffffffL in
      let addend = u64 (off + rela_addend_off) in
      go (off + rela_stride) ((site, typ, addend) :: acc)
  in
  go 0 []

(* The loader's load bias: the memory image's addresses are the file
   vaddrs plus it, so a RELATIVE value [base + addend] reads as the
   addend plus it. *)
let get_bias (proj : Project.t) : int64 =
  let open Ogre in
  let c = Ogre.collect Query.(select (from Image.Scheme.bias)) in
  match
    Base.Sequence.to_list
      (fst (Ogre.run c (Project.specification proj) |> Core.Or_error.ok_exn))
  with
  | b :: _ -> b
  | [] -> 0L

(* Every RELATIVE site with its runtime value (an in-module address):
   the RELA addend plus the bias, read from the relocation section bytes
   rather than the target bytes. *)
let relative_values (proj : Project.t) ~(bias : int64) : (int64 * int64) list
    =
  Project.memory proj |> Memmap.to_sequence
  |> Seq.filter_map ~f:(fun (mem, v) ->
      match Value.get Image.section v with
      | Some name when is_rela_section name ->
        get_section_data (Some (mem, v))
      | _ -> None)
  |> Seq.concat_map ~f:(fun (bytes, _, _) ->
      Seq.of_list (rela_rows bytes))
  |> Seq.filter_map ~f:(fun (site, typ, addend) ->
      if Int64.equal typ r_x86_64_relative
      then Some (Int64.add site bias, Int64.add addend bias)
      else None)
  |> Seq.to_list

(* The image fragments of one section: a RELATIVE word takes its runtime
   value, an externally-relocated word is dropped (the abstract read is
   the sound identity — the value is not a module address), and every
   other word keeps the file bytes.  A fragment is a maximal run of
   bytes no dropped word interrupts, so a load spanning a dropped word
   finds no image and stays abstract. *)
let substitute_relocated_words ~(bytes : Bytes.t) ~(lo : int64)
    ~(hi : int64) ~(relocated : int64 list) ~(relative : (int64 * int64) list)
    : (Bytes.t * int64 * int64) list =
  let len = Bytes.length bytes in
  if Base.List.is_empty relocated then [ (bytes, lo, hi) ]
  else begin
    let out = Bytes.copy bytes in
    let dropped = Array.make len false in
    Base.List.iter relocated ~f:(fun a ->
        let off = Int64.to_int (Int64.sub a lo) in
        if off >= 0 && off < len then
          match
            Base.List.Assoc.find relative ~equal:Int64.equal a
          with
          | Some v ->
            for k = 0 to 7 do
              if off + k < len then
                Bytes.set out (off + k)
                  (Char.chr
                     (Int64.to_int
                        (Int64.logand
                           (Int64.shift_right_logical v (8 * k))
                           0xffL)))
            done
          | None ->
            for k = 0 to 7 do
              if off + k < len then dropped.(off + k) <- true
            done);
    let rec runs i acc =
      if i >= len then Base.List.rev acc
      else if dropped.(i) then runs (i + 1) acc
      else begin
        let j = ref i in
        while !j < len && not dropped.(!j) do
          incr j
        done;
        let frag = Bytes.sub out i (!j - i) in
        runs !j
          ((frag, Int64.add lo (Int64.of_int i),
            Int64.add lo (Int64.of_int (!j - 1)))
          :: acc)
      end
    in
    runs 0 []
  end

(* Every section's image: the relocation-free sections whole, a section
   holding relocated words as its substituted fragments. *)
let get_section_images (proj : Project.t) : (Bytes.t * int64 * int64) list =
  let bias = get_bias proj in
  let relative = relative_values proj ~bias in
  let relocated = get_relocated_words proj in
  Project.memory proj |> Memmap.to_sequence
  |> Seq.filter_map ~f:(fun (mem, v) ->
      match Value.get Image.section v with
      | None -> None
      | Some _ ->
        Base.Option.map (get_section_data (Some (mem, v)))
          ~f:(fun (bytes, min_addr, max_addr) ->
            (bytes, Word.to_int64_exn min_addr, Word.to_int64_exn max_addr)))
  |> Seq.concat_map ~f:(fun (bytes, lo, hi) ->
      let sites =
        Base.List.filter relocated ~f:(fun a ->
            Int64.compare a lo >= 0 && Int64.compare a hi <= 0)
      in
      Seq.of_list
        (substitute_relocated_words ~bytes ~lo ~hi ~relocated:sites
           ~relative))
  |> Seq.to_list

let get_named_region_info proj =
  let query =
    let open Ogre in
    let region addr size name = { addr; size; name } in
    let addr = Type.("addr" %: int) in
    let size = Type.("size" %: int) in
    let name = Type.("name" %: str) in
    let table_type = Type.(scheme addr $ size $ name) in
    let named_region () = Ogre.declare ~name:"named-region" table_type region in
    Query.(select (from named_region))
  in
  let regions = Ogre.collect query in
  fst (Ogre.run regions (Project.specification proj) |> Core.Or_error.ok_exn)

