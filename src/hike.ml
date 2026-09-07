open Bap.Std
open Bap_main
open Bap.Std.Bil.Types
open Bap_core_theory
open Bil2llvm
open Convutils
open Hike_abi
module Abi = Hike_abi


(* Public re-exports; consumers use [Hike.Abi], etc. *)
module Vsa = Hike_vsa
module Dce = Hike_dce
module Stack_model = Hike_stack_model
module Stack_to_locals = Hike_stack_to_locals
module Kb = Hike_kb
module Convutils = Convutils
module Bil2llvm = Bil2llvm

module StrSet = Set.Make (String)

let get_section_mem name proj =
  Project.memory proj |> Memmap.to_sequence
  |> Seq.find ~f:(fun (_, v) ->
      Base.Option.value_map (Value.get Image.section v) ~default:false
        ~f:(fun n -> String.equal n name))

let get_section_data =
  Option.map begin fun (mem, _) ->
      let length = Memory.length mem in
      let min_addr = Memory.min_addr mem in
      let arr = Base.Array.init length ~f:(fun _ -> 0) in
      Memory.iteri ~word_size:`r8 mem ~f:(fun index v ->
          arr.(Word.to_int_exn (Word.( - ) index min_addr)) <- Word.to_int_exn v);
      (arr, Memory.min_addr mem, Memory.max_addr mem)
    end

(* Intrinsics and free-vars are owned by the emitter; the filter shares. *)
let free_vars = Bil2llvm.free_vars
let is_intrinsic = Bil2llvm.is_intrinsic
let is_emittable_intrinsic = Bil2llvm.is_emittable_intrinsic
let is_llvm_x86_intrinsic = Bil2llvm.is_llvm_x86_intrinsic

type 'a region = { addr : int64; size : int64; info : 'a }

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



let simplify_jmps sub =
  let new_sub =
    Sub.Builder.create ~tid:(Term.tid sub) ~name:(Sub.name sub) ()
  in
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun blk ->
      let jmps = Term.enum jmp_t blk in
      if Seq.length jmps = 1 then Sub.Builder.add_blk new_sub blk
      else
        let blk_builder =
          Blk.Builder.init ~copy_phis:true ~copy_defs:true blk
        in
        Seq.iter jmps ~f:(fun jmp ->
            if is_goto jmp then Blk.Builder.add_jmp blk_builder jmp
            else
              let cond = Jmp.cond jmp in
              let new_jmp = Jmp.with_cond jmp (Int (Word.one 1)) in
              let new_blk = Blk.create ~jmps:[ new_jmp ] () in
              Sub.Builder.add_blk new_sub new_blk;
              let goto = Jmp.create_goto ~cond (Direct (Term.tid new_blk)) in
              Blk.Builder.add_jmp blk_builder goto);
        let new_blk = Blk.Builder.result blk_builder in
        (* Copies block attrs. *)
        let new_blk = Term.with_attrs new_blk (Term.attrs blk) in
        Sub.Builder.add_blk new_sub new_blk);
  let res = Sub.Builder.result new_sub in
  (* Copies sub attrs. *)
  Term.with_attrs res (Term.attrs sub)

let filter_subs =
  [
    "_init";
    "_fini";
    "__cxa_finalize";
    "_start";
    "__libc_start_main";
    "register_tm_clones";
    "deregister_tm_clones";
    "__do_global_dtors_aux";
    "frame_dummy";
  ]

(* FP instructions modeled as soft-float calls. *)
let calls_intrinsic prog =
  let callgraph = Program.to_graph prog in
  let visit_edge _ edge filter_set =
    let caller = Graphs.Callgraph.Edge.src edge in
    let callee = Graphs.Callgraph.Edge.dst edge in
    let term = Term.find sub_t prog callee in
    if
      Base.Option.value_map term ~default:false ~f:(fun term ->
          is_intrinsic term
          && not (is_emittable_intrinsic term)
          && not (is_llvm_x86_intrinsic term))
    then Core.Set.add filter_set caller
    else filter_set
  in
  Graphlib.Std.Graphlib.depth_first_search
    (module Graphs.Callgraph)
    callgraph ~init:Tid.Set.empty ~enter_edge:visit_edge

let should_filter filter_set syms sub =
  (* Emittable intrinsics stay; their calls inline. *)
  if is_emittable_intrinsic sub then false
  else
    Base.List.mem ~equal:String.equal filter_subs (Sub.name sub)
    || Term.has_attr sub Sub.stub
    || Term.has_attr sub Sub.extern
    || Term.has_attr sub Sub.entry_point
    || is_intrinsic sub
    || Core.Set.mem filter_set (Term.tid sub)
    || (not @@ StrSet.mem (Sub.name sub) syms)

let setup proj =
  let target = Project.target proj in
  (* Forwards the address width. *)
  Hike_vsa.set_addr_bits (addr_size_bits target)

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

let filter_subs proj =
  let syms =
    Symtab.to_sequence (Project.symbols proj)
    |> Seq.fold ~init:StrSet.empty ~f:(fun set (name, _, _) ->
        StrSet.add name set)
  in
  Project.map_program proj ~f:(fun prog ->
      let filter_set = calls_intrinsic prog in
      Term.filter_map sub_t prog ~f:(fun sub ->
          if should_filter filter_set syms sub then
            None
          else
            Some (sub |> simplify_jmps)))

(* Setup and filter form their own pass. *)

let convert_binary output_program proj =
  let llvm_ctx = Llvm.create_context () in
  let llvm_module = Llvm.create_module llvm_ctx "Convlir" in
  setup proj;
  let target = Project.target proj in
  let ptrsize = Theory.Target.bits target in
  let regions = get_named_region_info proj in
  (* Pass 1: data-section globals. *)
  let mk_section section_type ~is_const =
    let llvm_name = section_type_to_string section_type in
    let name = "." ^ llvm_name in
    get_section_mem name proj |> get_section_data
    |> Option.map (fun (arr, min_addr, max_addr) ->
        let base =
          Bil2llvm.create_section_global llvm_ctx llvm_module
            (Array.length arr) llvm_name ~is_const
        in
        (arr, min_addr, max_addr, base))
  in
  let data_section = mk_section DATA ~is_const:false in
  let rodata_section = mk_section RODATA ~is_const:true in
  let bss_region =
    Seq.find regions ~f:(fun { info; _ } -> String.equal info ".bss")
  in
  let copy_relocs =
    match bss_region with
    | Some { addr; size; _ } ->
        get_copy_relocations proj ~bss_addr:addr ~bss_size:size
    | None -> []
  in
  let bss_section =
    create_uninitialized_section llvm_ctx llvm_module proj BSS regions
      copy_relocs
  in
  let copy_reloc_addrs_val =
    match bss_region with
    | Some { addr; _ } ->
        copy_reloc_slots ~bss_addr:addr copy_relocs (Project.program proj)
    | None -> []
  in
  let got_section = mk_section GOT ~is_const:true in
  let gotplt_section = mk_section GOTPLT ~is_const:true in
  let rodata_rel_section = mk_section RODATA_REL ~is_const:true in
  (* Stashes .text bytes for compile-time loads. *)
  let text_section = mk_section TEXT ~is_const:true in
  let text_section_val =
    Base.Option.map text_section ~f:(fun (arr, min, max, _base) ->
      (arr, Word.to_int64_exn min, Word.to_int64_exn max))
  in
  (* Maps native function addresses to lifted functions. *)
  let symtab_val = Some (Project.symbols proj) in
  (* Maps native section addresses to lifted globals. *)
  let sec_lo_hi_base sec =
    Base.Option.map sec ~f:(fun (arr, min_addr, max_addr, base) ->
        let lo = Word.to_int64_exn min_addr in
        let hi = Word.to_int64_exn max_addr in
        ignore arr;
        (lo, hi, base))
  in
  let bss_lo_hi_base =
    match bss_section with
    | Some { base; min_addr; max_addr; _ } ->
        Some
          (Word.to_int64_exn min_addr, Word.to_int64_exn max_addr, base)
    | None -> None
  in
  let section_remap_val =
    Base.List.filter_map
      [
        sec_lo_hi_base data_section;
        sec_lo_hi_base rodata_section;
        bss_lo_hi_base;
        sec_lo_hi_base got_section;
        sec_lo_hi_base gotplt_section;
        sec_lo_hi_base rodata_rel_section;
      ]
      ~f:(fun x -> x)
  in
  let section_of_sec sec =
    Base.Option.map sec ~f:(fun (_, min_addr, max_addr, base) ->
        { base; min_addr; max_addr })
  in
  let section_list =
    Base.List.filter_mapi
      ~f:(fun i section ->
        match section with
        | None ->
            Hike_diag.warn "section %d was not found in binary" i;
            None
        | Some s -> Some s)
      [
        section_of_sec data_section;
        section_of_sec rodata_section;
        bss_section;
        section_of_sec got_section;
        section_of_sec gotplt_section;
        section_of_sec rodata_rel_section;
      ]
  in
  let ctx =
    {
      (Convutils.empty_emit_ctx ()) with
      Convutils.symtab = symtab_val;
      text_section = text_section_val;
      section_remap = section_remap_val;
      copy_relocs = copy_reloc_addrs_val;
      target;
      abi = Abi.of_target target;
      sp = Abi.sp target;
      fp = Abi.fp target;
      ptrsize;
    }
  in
  (* Pass 2: data-section initializers. *)
  Base.List.iter
    [
      data_section;
      rodata_section;
      got_section;
      gotplt_section;
      rodata_rel_section;
    ]
    ~f:(fun sec ->
        Base.Option.iter sec ~f:(fun (arr, min_addr, _, base) ->
            Bil2llvm.set_section_initializer ctx llvm_ctx llvm_module base arr
              (Word.to_int64_exn min_addr)));
  Bil2llvm.emit_program llvm_ctx llvm_module
    ~target ~ptrsize
    ~symtab:symtab_val
    ~text_section:text_section_val
    ~section_remap:section_remap_val
    ~copy_relocs:copy_reloc_addrs_val
    section_list (Project.program proj);
  Llvm.print_module output_program llvm_module;
  Llvm.dispose_module llvm_module;
  Llvm.dispose_context llvm_ctx

let output =
  Extension.Configuration.parameter ~aliases:[ "o"; "output" ]
    Extension.Type.("output file" %: string)
    "output-file" ~doc:"File to output LLVM IR"

let () =
  Extension.declare (fun ctx ->
      let output_file = Extension.Configuration.get ctx output in
      Project.register_pass ~name:"filter" ~runonce:true
        (fun proj ->
           setup proj;
           (* Setup and filter run first. *)
           filter_subs proj);
      (* VSA tag pass; depends on the filter only (spec §2.1). *)
      Project.register_pass ~name:"vsa" ~deps:[ "hike-filter" ] ~runonce:true
        (fun proj ->
           (* Skips a second run; the slot already holds results. *)
           let cur = Hike_kb.vsa_info () in
           if not (Core.Map.is_empty cur) then (
#ifdef VSA_DEBUG
             Printf.eprintf "hike: vsa guard: skip second run (cur %d)\n" (Core.Map.length cur);
#endif
             proj)
           else
             let acc = ref Tid.Map.empty in
           Toplevel.exec begin
             KB.Seq.iter
               (Term.enum sub_t (Project.program proj))
               ~f:(fun sub ->
                 (* Computes tags and plan on the pre-rewrite sub. *)
                 let info =
                   Hike_vsa.offsets_of_sub (Project.target proj)
                     (sp (Project.target proj)) sub
                 in
#ifdef VSA_DEBUG
                 Printf.eprintf "hike: vsa: %s -> %d tag(s)\n"
                   (Sub.name sub) (Core.Map.length info.Convutils.offsets);
#endif
                 acc := Core.Map.set !acc ~key:(Term.tid sub) ~data:info;
                 KB.return ())
           end;
           (* Provides all tags in one write. *)
           Hike_kb.provide !acc;
           proj);
      (* Stack-to-locals pass. *)
       Project.register_pass ~name:"stack-to-locals" ~runonce:true
        ~deps:[ "hike-vsa" ]
        (fun proj ->
           let proj =
             Project.map_program proj ~f:(fun prog ->
                 Term.map sub_t prog
                   ~f:(Hike_stack_to_locals.stack_to_locals
                         (Project.target proj) (sp (Project.target proj))))
           in
#ifdef VSA_DEBUG
           Core.Map.iter (Hike_kb.vsa_info ()) ~f:(fun info ->
               Printf.eprintf "hike: stl: %d tag(s)\n"
                 (Core.Map.length info.Convutils.offsets));
#endif
           proj);
      (* Emission pass; runs last. *)
      (* DCE pass. *)
      Project.register_pass ~name:"dce" ~runonce:true
        ~deps:[ "hike-stack-to-locals" ]
        (fun proj ->
           let target = Project.target proj in
           let proj =
             Project.map_program proj ~f:(fun prog ->
                 Term.map sub_t prog ~f:(Hike_dce.dce ~target))
           in
           proj);
      Project.register_pass' ~name:"convlir" ~runonce:true
        ~deps:[ "hike-dce" ]
        (convert_binary output_file);
      Ok ())
