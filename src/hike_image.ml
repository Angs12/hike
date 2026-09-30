(* The ELF-image readers: named-section lookup, section bytes,
   copy-relocated bss slots, and named regions. *)

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

(* Every word the loader's relocation facts name.  A word at one of
   these addresses is a load-time relocation result; a section holding
   one is not its static image. *)
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

(* The sections whose runtime content IS the static image: every section
   span with no relocated word inside it.  The bytes come from the
   loader's memory image. *)
let get_section_images (proj : Project.t) : (Bytes.t * int64 * int64) list =
  let relocated = get_relocated_words proj in
  Project.memory proj |> Memmap.to_sequence
  |> Seq.filter_map ~f:(fun (mem, v) ->
      match Value.get Image.section v with
      | None -> None
      | Some _ ->
        let lo = Word.to_int64_exn (Memory.min_addr mem) in
        let hi = Word.to_int64_exn (Memory.max_addr mem) in
        if
          Base.List.exists relocated ~f:(fun a ->
              Int64.compare a lo >= 0 && Int64.compare a hi <= 0)
        then None
        else
          Base.Option.map (get_section_data (Some (mem, v)))
            ~f:(fun (bytes, _, _) -> (bytes, lo, hi)))
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

