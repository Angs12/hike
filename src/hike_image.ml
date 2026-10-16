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

(* The rows of one declared Ogre fact table in the project's spec. *)
let ogre_rows (proj : Project.t) table =
  let open Ogre in
  fst (run (collect Query.(select (from table))) (Project.specification proj)
       |> Core.Or_error.ok_exn)
  |> Base.Sequence.to_list

let get_copy_relocations proj ~bss_addr ~bss_size =
  let rows =
    let open Ogre in
    let at = Type.("at" %: int) in
    let name = Type.("name" %: str) in
    let nr_tbl = Type.(scheme at $ name) in
    let name_ref () =
      Ogre.declare ~name:"llvm:name-reference" nr_tbl (fun a n -> (a, n))
    in
    ogre_rows proj name_ref
  in
  rows
  |> Base.List.filter_map ~f:(fun (fixup, name) ->
         let off = Stdlib.Int64.sub fixup bss_addr in
         if
           Stdlib.Int64.compare off 0L >= 0
           && Stdlib.Int64.compare off bss_size < 0
         then Some (Stdlib.Int64.to_int off, name)
         else None)
  |> Core.Int.Map.of_alist_reduce ~f:(fun first _ -> first)
  |> Core.Map.to_alist

(* Every word the loader's relocation facts name: a load-time relocation
   result, so a word at one of these addresses is not its file bytes. *)
let get_relocated_words (proj : Project.t) : int64 list =
  let relr = ogre_rows proj Image.Scheme.relative_relocation in
  let rel = ogre_rows proj Image.Scheme.relocation |> Base.List.map ~f:fst in
  let ext = ogre_rows proj Image.Scheme.external_reference
            |> Base.List.map ~f:fst in
  relr @ rel @ ext

(* Every symbol-bearing relocation site and the symbol named there: the
   loader emits this for each relocation carrying a symbol, whatever its
   type.  A site inside an image section holds the symbol's address — a
   GLOB_DAT/JUMP_SLOT slot in .got/.got.plt, or an R_X86_64_64 in a
   shared object's .data.  A COPY site is in .bss, which carries no
   image and is served by the copy-relocation path instead. *)
let external_references (proj : Project.t) : (int64 * string) list =
  ogre_rows proj Image.Scheme.external_reference

(* The loader's load bias: the memory image's addresses are the file
   vaddrs plus it, so a RELATIVE value [base + addend] reads as the
   addend plus it. *)
let get_bias (proj : Project.t) : int64 =
  match ogre_rows proj Image.Scheme.bias with
  | b :: _ -> b
  | [] -> 0L

(* The image's entry address, biased like every memory address. *)
let entry_point (proj : Project.t) : int64 option =
  let open Ogre in
  let c = Ogre.collect Query.(select (from Image.Scheme.entry_point)) in
  match Ogre.run c (Project.specification proj) with
  | Ok (s, _) -> Base.Option.map (Base.Sequence.hd s) ~f:(Int64.add (get_bias proj))
  | Error _ -> None

(* Every RELATIVE site with its runtime value (an in-module address):
   the loader's (site, addend) fact — [R_X86_64_RELATIVE]'s r_offset and
   r_addend — plus the bias. *)
let relative_values (proj : Project.t) ~(bias : int64) : (int64 * int64) list
    =
  let open Ogre in
  let at = Type.("at" %: int) in
  let addend = Type.("addend" %: int) in
  let rel_addend () =
    Ogre.declare ~name:"llvm:relative-relocation-addend"
      Type.(scheme at $ addend) (fun site addend -> (site, addend))
  in
  ogre_rows proj rel_addend
  |> Base.List.map ~f:(fun (site, addend) ->
         (Int64.add site bias, Int64.add addend bias))

(* The image fragments of one section: a RELATIVE word takes its runtime
   value, an externally-relocated word is dropped (the abstract read is
   the sound identity — the value is not a module address), and every
   other word keeps the file bytes.  A fragment is a maximal run of
   bytes no dropped word interrupts, so a load spanning a dropped word
   finds no image and stays abstract. *)
let substitute_relocated_words ~(bytes : Bytes.t) ~(lo : int64)
    ~(hi : int64) ~(relocated : int64 list) ~(relative : (int64 * int64) list)
    ~(word : int) : (Bytes.t * int64 * int64) list =
  let len = Bytes.length bytes in
  if Base.List.is_empty relocated then [ (bytes, lo, hi) ]
  else begin
    let relative = Core.Map.of_alist_reduce (module Core.Int64) relative
        ~f:(fun first _ -> first) in
    let out = Bytes.copy bytes in
    let dropped = Array.make len false in
    Base.List.iter relocated ~f:(fun a ->
        let off = Int64.to_int (Int64.sub a lo) in
        if off >= 0 && off < len then
          match Core.Map.find relative a with
          | Some v ->
            for k = 0 to word - 1 do
              if off + k < len then
                Bytes.set out (off + k)
                  (Char.chr
                     (Int64.to_int
                        (Int64.logand
                           (Int64.shift_right_logical v (8 * k))
                           0xffL)))
            done
          | None ->
            for k = 0 to word - 1 do
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

let pt_load = 1L
let pt_tls = 7L
let pt_gnu_relro = 0x6474e552L

(* The runtime ranges the process never writes once relocation is done,
   with their access: every PT_LOAD segment without PF_W is [Read_only],
   each PT_GNU_RELRO range [Relro], its end rounded down to a page as the
   loader's mprotect does.  Inclusive, bias applied. *)
let protections_at (proj : Project.t) ~(page : int64) ~(bias : int64) :
    (int64 * int64 * Hike_section.access) list =
  let open Ogre in
  let name = Type.("name" %: str) in
  let addr = Type.("addr" %: int) in
  let size = Type.("size" %: int) in
  let typ = Type.("type" %: int) in
  let align = Type.("align" %: int) in
  let flag n = Type.(n %: bool) in
  let types () = declare ~name:"llvm:elf-program-header-type"
      Type.(scheme name $ typ $ align) (fun n t _ -> (n, t)) in
  let virtuals () = declare ~name:"llvm:elf-virtual-program-header"
      Type.(scheme name $ addr $ size) (fun n a s -> (n, (a, s))) in
  let flags () = declare ~name:"llvm:elf-program-header-flags"
      Type.(scheme name $ flag "ld" $ flag "r" $ flag "w" $ flag "x")
      (fun n _ _ w _ -> (n, w)) in
  let writable = ogre_rows proj flags in
  let extent = ogre_rows proj virtuals in
  Base.List.filter_map (ogre_rows proj types) ~f:(fun (id, t) ->
      match Base.List.Assoc.find extent ~equal:String.equal id with
      | None -> None
      | Some (vaddr, memsz) ->
        let lo = Int64.add vaddr bias in
        let range hi access =
          if Int64.compare hi lo >= 0 then Some (lo, hi, access) else None in
        if Int64.equal t pt_load
        && not (Base.Option.value ~default:true
                  (Base.List.Assoc.find writable ~equal:String.equal id))
        then range (Int64.pred (Int64.add lo memsz)) Hike_section.Read_only
        else if Int64.equal t pt_gnu_relro then
          range (Int64.pred (Int64.logand (Int64.add lo memsz) (Int64.neg page)))
            Hike_section.Relro
        else None)

let protections (proj : Project.t) ~(page : int64) :
    (int64 * int64 * Hike_section.access) list =
  protections_at proj ~page ~bias:(get_bias proj)

(* The access of the bytes [lo, hi]: the protection of a range covering
   them wholly, [Read_only] before [Relro]; any other byte may be
   written. *)
let access (prot : (int64 * int64 * Hike_section.access) list) ~(lo : int64)
    ~(hi : int64) : Hike_section.access =
  let covering =
    Base.List.filter_map prot ~f:(fun (plo, phi, a) ->
        Base.Option.some_if
          (Int64.unsigned_compare plo lo <= 0
           && Int64.unsigned_compare hi phi <= 0) a)
  in
  if Base.List.mem covering Hike_section.Read_only ~equal:Hike_section.equal_access
  then Hike_section.Read_only
  else if Base.List.mem covering Hike_section.Relro
      ~equal:Hike_section.equal_access
  then Hike_section.Relro
  else Hike_section.Writable

(* The fragments of [img] inside [ranges]. *)
let clip_image ((bytes, lo, hi) : Bytes.t * int64 * int64)
    (ranges : (int64 * int64) list) : (Bytes.t * int64 * int64) list =
  Base.List.filter_map ranges ~f:(fun (rlo, rhi) ->
      let a = if Int64.compare rlo lo > 0 then rlo else lo in
      let b = if Int64.compare rhi hi < 0 then rhi else hi in
      if Int64.compare a b > 0 then None
      else
        let off = Int64.to_int (Int64.sub a lo) in
        let len = Int64.to_int (Int64.sub b a) + 1 in
        Some (Bytes.sub bytes off len, a, b))

(* The images the analysis may read: each section's bytes, its relocated
   words substituted, restricted to the never-written ranges.  A
   writable byte has no image, so a load that finds no stored cell there
   reads the abstract value, never the file contents. *)
let get_section_images (proj : Project.t) ~(page : int64) :
    (Bytes.t * int64 * int64) list =
  let bias = get_bias proj in
  let readonly =
    Base.List.map (protections_at proj ~page ~bias)
      ~f:(fun (lo, hi, _) -> (lo, hi)) in
  let relative = relative_values proj ~bias in
  let relocated = get_relocated_words proj in
  let word = (Hike_abi.of_target (Project.target proj)).Hike_abi.word in
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
           ~relative ~word))
  |> Seq.concat_map ~f:(fun img -> Seq.of_list (clip_image img readonly))
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

(* A loaded section's bytes: the stack lines have none, the bss is the
   loader's named region, every other section its memory-map image. *)
let section_range (proj : Project.t) (s : Hike_section.t) :
    (int64 * int64) option =
  match s with
  | Stack | Args | Vla -> None
  | Bss ->
    Seq.find (get_named_region_info proj) ~f:(fun { name; _ } ->
        String.equal name ("." ^ Hike_section.name Bss))
    |> Base.Option.bind ~f:(fun { addr; size; _ } ->
        Base.Option.some_if (Int64.compare size 0L > 0)
          (addr, Int64.pred (Int64.add addr size)))
  | Text | Rodata | Data | Got | Gotplt | Datarelro ->
    get_section_mem ("." ^ Hike_section.name s) proj
    |> Base.Option.map ~f:(fun (mem, _) ->
        (Word.to_int64_exn (Memory.min_addr mem),
         Word.to_int64_exn (Memory.max_addr mem)))

(* A section's runtime access: the one rule the analysis images and the
   emitted globals' constness both follow.  A section with no bytes may
   be written. *)
let section_access (prot : (int64 * int64 * Hike_section.access) list)
    (proj : Project.t) (s : Hike_section.t) : Hike_section.access =
  match section_range proj s with
  | Some (lo, hi) -> access prot ~lo ~hi
  | None -> Hike_section.Writable


(* Header type and alignment come from the ELF producer; joining by the
   producer's header index keeps this independent of section/symbol names. *)
let tls_spec (proj : Project.t) : Hike_spec.tls_spec option =
  let open Ogre in
  let name = Type.("name" %: str) in
  let off = Type.("off" %: int) in
  let size = Type.("size" %: int) in
  let addr = Type.("addr" %: int) in
  let typ = Type.("type" %: int) in
  let align = Type.("align" %: int) in
  let types () = declare ~name:"llvm:elf-program-header-type"
      Type.(scheme name $ typ $ align) (fun n t a -> (n, (t, a))) in
  let files () = declare ~name:"llvm:elf-program-header"
      Type.(scheme name $ off $ size) (fun n o s -> (n, (o, s))) in
  let virtuals () = declare ~name:"llvm:elf-virtual-program-header"
      Type.(scheme name $ addr $ size) (fun n a s -> (n, (a, s))) in
  let rows table = ogre_rows proj table in
  let headers = rows types in
  if Base.List.is_empty headers then
    failwith "hike-image: missing ELF program-header type/alignment facts";
  let tls = Base.List.filter headers ~f:(fun (_, (t, _)) -> Int64.equal t pt_tls) in
  match tls with
  | [] -> None
  | [ (id, (_, alignment)) ] ->
    let lookup table =
      Base.List.Assoc.find (rows table) ~equal:String.equal id
      |> Base.Option.value_exn ~message:"hike-image: incomplete PT_TLS header" in
    let _, filesz = lookup files in
    let vaddr, memsz = lookup virtuals in
    let alignment = Int64.max 1L alignment in
    if filesz < 0L || memsz < filesz
       || Int64.logand alignment (Int64.sub alignment 1L) <> 0L then
      failwith "hike-image: invalid PT_TLS extent or alignment";
    let prefix = Int64.rem vaddr alignment in
    let span = Int64.add memsz prefix in
    let rounded = Int64.logand (Int64.add span (Int64.sub alignment 1L))
        (Int64.neg alignment) in
    let lo = Int64.add vaddr (get_bias proj) in
    (* Materialise the memory regions once; a per-byte [Memmap.to_sequence]
       would re-walk the map for every TLS byte. *)
    let mems =
      Project.memory proj |> Memmap.to_sequence |> Base.Sequence.to_list in
    let current = ref None in
    let image = Bytes.init (Int64.to_int filesz) (fun i ->
        let a = Word.of_int64 ~width:(8 * (Hike_abi.of_target (Project.target proj)).Hike_abi.word)
            (Int64.add lo (Int64.of_int i)) in
        let mem =
          match !current with
          | Some mem when Memory.contains mem a -> mem
          | _ ->
            let mem =
              Base.List.find mems ~f:(fun (mem, _) -> Memory.contains mem a)
              |> Base.Option.value_exn ~message:"hike-image: unreadable PT_TLS image"
              |> fst in
            current := Some mem;
            mem
        in
        Memory.get ~addr:a mem |> Core.Or_error.ok_exn |> Word.to_int_exn
        |> Char.chr) in
    Some { Hike_spec.tls_lo = lo; tls_memsz = memsz;
           tls_align = Int64.to_int alignment;
           tls_base = Int64.sub prefix rounded;
           tls_prefix = Int64.to_int prefix; tls_image = image }
  | _ -> failwith "hike-image: multiple PT_TLS headers"
