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

module StrMap = Map.Make (String)
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

let free_vars sub =
  Sub.free_vars sub
  |> Core.Set.filter ~f:(fun var -> not @@ is_mem var)
  |> Core.Set.to_list

(* Tests the [Sub.intrinsic] attribute. *)
let is_intrinsic (term : sub term) : bool =
  Term.has_attr term Sub.intrinsic

let is_emittable_intrinsic (term : sub term) : bool =
  is_intrinsic term && not (Seq.is_empty (Term.enum blk_t term))

(* Tests for bodyless LLVM intrinsics. *)
let is_llvm_x86_intrinsic (term : sub term) : bool =
  Term.has_attr term Sub.intrinsic && Seq.is_empty (Term.enum blk_t term)

let fp_returning (sub : sub term) : bool =
  let is_ymm n = Base.String.is_prefix n ~prefix:Abi.vector_param_prefix in
  let is_value_reg v =
    let n = Var.name (Var.base v) in
    Base.List.mem Abi.value_return_names n ~equal:String.equal
    || is_ymm n
  in
  let is_epilogue blk =
    Term.enum jmp_t blk
    |> Seq.exists ~f:(fun j ->
        match Jmp.kind j with
        | Call c -> (
            match Call.target c with
            | Indirect _ -> Option.is_none (Call.return c)
            | _ -> false)
        | _ -> false)
  in
  let value_defs blk =
    Term.enum def_t blk
    |> Seq.fold ~init:[] ~f:(fun acc d ->
        if is_value_reg (Def.lhs d) then d :: acc else acc)
  in
  let cfg = Sub.to_graph sub in
  let return_path_defs =
    Term.enum blk_t sub
    |> Seq.fold ~init:[] ~f:(fun acc blk ->
        if not (is_epilogue blk) then acc
        else
          let preds = Graphs.Tid.Node.preds (Term.tid blk) cfg in
          let pred_defs =
            Seq.fold preds ~init:[] ~f:(fun acc p ->
                match Term.find blk_t sub p with
                | Some pb -> value_defs pb @ acc
                | None -> acc)
          in
          value_defs blk @ pred_defs @ acc)
  in
  match return_path_defs with
  | [] -> false
  | d :: _ -> is_ymm (Var.name (Var.base (Def.lhs d)))

let compute_sub_sig (target : Theory.Target.t) (sub : sub term) :
    Arg.t list * Arg.t list =
  let free_vars = free_vars sub in
  let rets =
    (if Theory.Target.matches target "x86_64-gnu-elf" then
       Abi.return_regs target
     else [])
    |> Base.List.map ~f:(fun reg -> Arg.create ~intent:Out reg (Var reg))
  in
  let rets =
    (* Double returns arrive via [%YMM0]. *)
    if fp_returning sub then
      let ymm0 = Base.List.nth_exn (Abi.vector_param_regs target) 0 in
      rets
      @ [ Arg.create ~intent:Out ymm0 (Var ymm0) ]
    else rets
  in
  let rets, args =
    if is_emittable_intrinsic sub then begin
    (* Intrinsic signature is the model's own interface. *)
    let args =
      Base.List.map free_vars ~f:(fun reg ->
          Arg.create ~intent:In reg (Var reg))
    in
    let rets =
      Term.enum blk_t sub
      |> Seq.fold ~init:[] ~f:(fun acc blk ->
          Term.enum def_t blk
          |> Seq.fold ~init:acc ~f:(fun acc d ->
              let v = Def.lhs d in
              let is_input =
                Base.List.exists free_vars ~f:(fun fv -> Var.same fv v)
              in
              let already =
                Base.List.exists acc ~f:(fun a -> Var.same (Arg.lhs a) v)
              in
              if is_input || already then acc
              else Arg.create ~intent:Out v (Var v) :: acc))
    in
      (rets, args)
    end
  else if Term.name sub = "@main" then
     let abi = Abi.of_target target in
     let rdi = Base.List.nth_exn abi.int_param_regs 0 in
     let rsi = Base.List.nth_exn abi.int_param_regs 1 in
     let args =
       [
         Arg.create ~intent:In rdi (Var rdi);
         Arg.create ~intent:In rsi (Var rsi);
       ]
     in
      (rets, args)
   else
       (* Subs with incoming stack args take [hike_stack]. The VSA verdict
         is the SOLE origin (review #2 grill): the hand-rolled BIL walk
         that used to OR a second opinion here is deleted — two
         mechanisms that can disagree are worse than one, and absent
         info already defaults to false. *)
      let has_positive =
        Core.Map.find (Hike_kb.vsa_info ()) (Term.tid sub)
        |> Base.Option.value_map ~default:false ~f:(fun info ->
            Core.Map.exists info.Convutils.offsets ~f:(fun kind ->
                Convutils.is_positive_kind kind))
      in
      let is_main =
        String.equal (Sub.name sub) "@main"
        || String.equal (Tid.name (Term.tid sub)) "@main"
      in
      let hike_stack_arg =
        if has_positive && not is_main then
          [ Arg.create ~intent:In Convutils.hike_stack_var
              (Var Convutils.hike_stack_var) ]
        else []
      in
      let args =
        let rank_of_var (v : var) : int * string =
          let n = Var.name (Var.base v) in
          let int_order = Base.List.map (Abi.int_param_regs target) ~f:Var.name in
          match Base.List.findi int_order ~f:(fun _ s -> String.equal s n) with
          | Some (i, _) -> (i, n)
          | None ->
            if Base.String.is_prefix n ~prefix:Abi.vector_param_prefix then
              (try
                 let num = int_of_string (String.sub n 3 (String.length n - 3)) in
                 if 0 <= num && num < 8 then (6 + num, n) else (100, n)
               with _ -> (100, n))
            else (100, n)
        in
        Base.List.filter free_vars ~f:(fun reg ->
            let n = Var.name (Var.base reg) in
            let is_callee_saved =
              Abi.is_callee_saved_t target reg
            in
            not
              (Var.same reg (sp target)
              || Var.same reg (fp target)
              || is_callee_saved
              || Convutils.is_intrinsic_name n))
        |> Base.List.sort ~compare:(fun a b ->
            let ra, na = rank_of_var a in
            let rb, nb = rank_of_var b in
            match Int.compare ra rb with
            | 0 -> String.compare na nb
            | c -> c)
        |> Base.List.map ~f:(fun reg -> Arg.create ~intent:In reg (Var reg))
        |> fun regs -> regs @ hike_stack_arg
      in
     (* PLT stubs take the full param list. Signature-shape rule (args = []
        + any call): distinct from the emitter's BIL-shape rule
        (Bil2llvm.is_plt_trampoline: no reg free-vars + call) — the two
        run on different inputs (pre-DCE raw sub vs post-DCE sub) and must
        not be merged blindly. *)
     let is_plt_sig =
       args = []
       && Term.enum blk_t sub
          |> Seq.exists ~f:(fun blk ->
                 Term.enum jmp_t blk
                 |> Seq.exists ~f:(fun j ->
                        match Jmp.kind j with
                        | Call _ -> true
                        | _ -> false))
     in
     let args =
       if is_plt_sig then
         Base.List.map (Abi.param_regs target)
           ~f:(fun reg -> Arg.create ~intent:In reg (Var reg))
       else args
     in
      (rets, args)
  in
  (rets, args)

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

let init_subs ctx llvm_ctx llvm_module section_list proj =
  (* Fills the signature table once. *)
  let sigs =
    Term.enum sub_t (Project.program proj)
    |> Base.Sequence.to_list
    |> Base.List.map ~f:(fun sub ->
           (sub, compute_sub_sig ctx.Convutils.target sub))
  in
  let subs =
    Base.List.fold sigs ~init:ctx.Convutils.subs
      ~f:(fun acc (sub, (rets, args)) ->
          add_sub_sig acc (Term.tid sub) ~rets ~args)
  in
  Toplevel.exec begin
    KB.Context.with_var emit_ctx_var ctx (fun () ->
      KB.Context.with_var llvm_ctx_var llvm_ctx (fun () ->
        KB.Context.with_var llvm_module_var llvm_module (fun () ->
          KB.Context.with_var section_list_var section_list (fun () ->
            KB.List.iter sigs ~f:(fun (sub, (rets, args)) ->
                (* Mapped intrinsics store the sig but define no function. *)
                if
                  Base.Option.is_none
                    (Bil2llvm.native_fp_op (Tid.name (Term.tid sub)))
                then create_fun (Term.tid sub) ~rets ~args
                else KB.return ())))))
  end;
  ({ ctx with Convutils.subs = subs }, proj)

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
       let slot_addr (off, _) = Int64.add addr (Int64.of_int off) in
       let all = Base.List.map copy_relocs ~f:slot_addr in
       (* Slots with authoritative writes get fresh values. *)
       let slot_of_addr (v : int64) : bool =
         Base.List.mem all v ~equal:Int64.equal
       in
       (* Collects slot addresses via shape [f]. *)
       let sub_def_slot_addrs ~(f : exp -> int64 option) (sub : sub term) =
         Term.enum blk_t sub |> Seq.to_list
         |> Base.List.concat_map ~f:(fun blk ->
             Term.enum def_t blk |> Seq.to_list
             |> Base.List.filter_map ~f:(fun d -> f (Def.rhs d)))
       in
       let slot_loads (sub : sub term) =
         sub_def_slot_addrs sub ~f:(function
           | Bil.Load (_, Bil.Int w, _, _) ->
               let v = Word.to_int64_exn w in
               if slot_of_addr v then Some v else None
           | _ -> None)
       in
       let slot_stores (sub : sub term) =
         sub_def_slot_addrs sub ~f:(function
           | Bil.Store (_, Bil.Int w, _, _, _) ->
               let v = Word.to_int64_exn w in
               if slot_of_addr v then Some v else None
           | _ -> None)
       in
       (* Tests for a same-sub load/store mirror. *)
       let loads_and_stores : int64 list =
         Term.enum sub_t (Project.program proj) |> Seq.to_list
         |> Base.List.concat_map ~f:(fun sub ->
             let stores = slot_stores sub in
             Base.List.filter (slot_loads sub) ~f:(fun v ->
                 Base.List.mem stores v ~equal:Int64.equal))
       in
       let stores_only : int64 list =
         Term.enum sub_t (Project.program proj) |> Seq.to_list
         |> Base.List.concat_map ~f:slot_stores
       in
       let authoritative = stores_only in
       if authoritative = [] then all
       else
         Base.List.filter all ~f:(fun a ->
             (* Mirrored slots keep the through-load. *)
             not
               (Base.List.mem authoritative a ~equal:Int64.equal
               && (not (Base.List.mem loads_and_stores a ~equal:Int64.equal))))
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
  let ctx, proj' = init_subs ctx llvm_ctx llvm_module section_list proj in
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
  create_prog ctx llvm_ctx llvm_module section_list proj';
  Llvm.print_module output_program llvm_module;
  Llvm.dispose_module llvm_module;
  Llvm.dispose_context llvm_ctx

let requires = []

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
