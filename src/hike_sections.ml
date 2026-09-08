(* Section prep: native data-section bytes, BSS/copy-reloc slots, region info. *)

open Bap.Std
open Bil2llvm
open Convutils

type 'a region = { addr : int64; size : int64; info : 'a }

let get_section_mem name proj =
  Project.memory proj |> Memmap.to_sequence
  |> Seq.find ~f:(fun (_, v) ->
      Base.Option.value_map (Value.get Image.section v) ~default:false
        ~f:(fun n -> String.equal n name))

(* Eta-expanded: the point-free spelling leaves a weak type variable that
   only unifies at a use site (which now lives in another module). *)
let get_section_data x =
  Option.map begin fun (mem, _) ->
      let length = Memory.length mem in
      let min_addr = Memory.min_addr mem in
      let arr = Base.Array.init length ~f:(fun _ -> 0) in
      Memory.iteri ~word_size:`r8 mem ~f:(fun index v ->
          arr.(Word.to_int_exn (Word.( - ) index min_addr)) <- Word.to_int_exn v);
      (arr, Memory.min_addr mem, Memory.max_addr mem)
    end x

let create_uninitialized_section llvm_ctx llvm_module proj section_type
    region_info copy_relocs =
  let llvm_name = section_type_to_string section_type in
  let name = "." ^ llvm_name in
  Seq.find region_info ~f:(fun { info; _ } -> info = name)
  |> Option.map (fun { addr; size; _ } ->
      let base =
        if copy_relocs = [] then
          create_uninitialized_global llvm_ctx llvm_module size llvm_name
        else
          Bil2llvm.create_copy_reloc_bss llvm_ctx llvm_module size llvm_name
            copy_relocs
      in
      let addr = Int64.to_int addr in
      let size = Int64.to_int size in
      let min_addr = Word.of_int ~width:64 addr in
      let max_addr = Word.of_int ~width:64 (addr + size - 1) in
      { base; min_addr; max_addr })

(* Collects copy-relocated bss slots. *)
let get_copy_relocations proj ~bss_addr ~bss_size =
  let open Ogre in
  let at = Type.("at" %: int) in
  let name = Type.("name" %: str) in
  let nr_tbl = Type.(scheme at $ name) in
  let name_ref () =
    Ogre.declare ~name:"llvm:name-reference" nr_tbl (fun a n -> (a, n))
  in
  let rows =
    Ogre.collect Query.(select (from name_ref)) |> fun c ->
    fst
      (Ogre.run c (Project.specification proj) |> Core.Or_error.ok_exn)
  in
  Base.Sequence.to_list rows
  |> Base.List.filter_map ~f:(fun (fixup, name) ->
         let off = Int64.sub fixup bss_addr in
         if
           Int64.compare off 0L >= 0
           && Int64.compare off bss_size < 0
         then Some (Int64.to_int off, name)
         else None)
  |> Base.List.dedup_and_sort ~compare:(fun (a, _) (b, _) ->
         Int64.compare (Int64.of_int a) (Int64.of_int b))

(* Copy-relocated BSS slots needing fresh values: relocated slots minus
   slots with an authoritative same-sub store that no load mirrors.
   Pure in (relocs, program). NOTE: the Load/Store matches below are
   deliberately top-level-rhs-only — a load nested inside a larger
   expression (e.g. an address computation) is NOT a slot access. An
   [Exp.visitor] would fire on nested nodes and silently widen the set. *)
let copy_reloc_slots ~bss_addr (copy_relocs : (int * string) list)
    (prog : program term) : int64 list =
  let all =
    Base.List.map copy_relocs ~f:(fun (off, _) ->
        Int64.add bss_addr (Int64.of_int off))
  in
  if all = [] then []
  else
    let slot_of_addr (v : int64) : bool =
      Base.List.mem all v ~equal:Int64.equal
    in
    (* Per-sub (loads, stores) of relocated slots, in one walk. *)
    let sub_slots (sub : sub term) : int64 list * int64 list =
      Term.enum blk_t sub
      |> Seq.fold ~init:([], []) ~f:(fun (loads, stores) blk ->
          Term.enum def_t blk
          |> Seq.fold ~init:(loads, stores) ~f:(fun (loads, stores) d ->
              match Def.rhs d with
              | Bil.Load (_, Bil.Int w, _, _) ->
                  let v = Word.to_int64_exn w in
                  ((if slot_of_addr v then v :: loads else loads), stores)
              | Bil.Store (_, Bil.Int w, _, _, _) ->
                  let v = Word.to_int64_exn w in
                  (loads, (if slot_of_addr v then v :: stores else stores))
              | _ -> (loads, stores)))
    in
    (* Mirroring is per-sub: a load keeps the through-load only when its
       own sub stores the same slot. *)
    let mirrored, stored =
      Term.enum sub_t prog
      |> Seq.fold ~init:([], []) ~f:(fun (mirrored, stored) sub ->
          let loads, stores = sub_slots sub in
          let mirrored =
            Base.List.fold_left loads ~init:mirrored ~f:(fun m v ->
                if Base.List.mem stores v ~equal:Int64.equal then v :: m
                else m)
          in
          (mirrored, stores @ stored))
    in
    if stored = [] then all
    else
      Base.List.filter all ~f:(fun a ->
          (* Mirrored slots keep the through-load. *)
          not
            (Base.List.mem stored a ~equal:Int64.equal
            && not (Base.List.mem mirrored a ~equal:Int64.equal)))

let get_named_region_info proj =
  let quary =
    let open Ogre in
    let region addr size info = { addr; size; info } in
    let addr = Type.("addr" %: int) in
    let size = Type.("size" %: int) in
    let name = Type.("name" %: str) in
    let table_type = Type.(scheme addr $ size $ name) in
    let named_region () = Ogre.declare ~name:"named-region" table_type region in
    Query.(select (from named_region))
  in
  let regions = Ogre.collect quary in
  fst (Ogre.run regions (Project.specification proj) |> Core.Or_error.ok_exn)
