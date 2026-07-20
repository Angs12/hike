open Bap.Std
open Bap_main
open Bap.Std.Bil.Types
open Regular.Std
open Bap_core_theory
open Bil2llvm
open Convutils
open Targetutils
open Printf
module Reader = Monads.Std.Monad.Reader
module StrMap = Map.Make (String)
module StrSet = Set.Make (String)

let get_section_mem name proj =
  Project.memory proj |> Memmap.to_sequence
  |> Seq.find ~f:(fun (_, v) ->
      Base.Option.value_map (Value.get Image.section v) ~default:false
        ~f:(fun n -> String.equal n name))

let print_section_names proj =
  Project.memory proj |> Memmap.to_sequence
  |> Seq.iter ~f:(fun (_, v) ->
      Base.Option.iter (Value.get Image.section v) ~f:(fun n ->
          Printf.printf "%s\n" n))

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
  |> Var.Set.filter ~f:(fun var -> not @@ is_mem var)
  |> Var.Set.to_list

let set_sub sub =
  let free_vars = free_vars sub in
  let rets =
    (if Theory.Target.matches !target_ref "x86_64-gnu-elf" then
       Calling_conventions.x86_64_sysv.return_regs
     else [])
    |> Base.List.map ~f:(fun reg -> Arg.create ~intent:Out reg (Var reg))
  in
  (if Term.name sub = "@main" then
     let rdi = Var.create "RDI" (Imm 64) in
     let rsi = Var.create "RSI" (Imm 64) in
     let args =
       [
         Arg.create ~intent:In rdi (Var rdi);
         Arg.create ~intent:In rsi (Var rsi);
       ]
     in
     insert_sub_sig (Term.tid sub) ~rets ~args
   else
     let args =
       Base.List.map
         ~f:(fun reg ->
           if Var.same reg (sp !target_ref) || Var.same reg (fp !target_ref)
           then Arg.create ~intent:Both reg (Var reg)
           else Arg.create ~intent:In reg (Var reg))
         free_vars
     in
     insert_sub_sig (Term.tid sub) ~rets ~args);
  create_fun (Term.tid sub)

let stack_len = 0x2048

let unaliased_reg_exp var =
  let resolved = Targetutils.resolve_alias !target_ref var in
  match resolved with
  | None -> Bil.Var var
  | Some origin ->
      let base_var = Theory.Origin.reg origin |> Var.reify in
      let lo = Theory.Origin.lo origin in
      let hi = Theory.Origin.hi origin in
      Bil.Extract (hi, lo, Bil.Var base_var)

let unalias_sub sub =
  let mapper =
    object
      inherit Exp.mapper

      method! map_var v =
        if Base.List.mem (base_regs !target_ref) v ~equal:Var.same then
          unaliased_reg_exp v
        else Bil.Var v
    end
  in
  Term.map blk_t sub ~f:(fun blk ->
      Term.map def_t blk ~f:(fun def ->
          let rhs = Def.rhs def in
          let new_rhs = mapper#map_exp rhs in
          Def.with_rhs def new_rhs))

let create_stack_ptr llvm_ctx llvm_module =
  let stack_ptr =
    create_uninitialized_global llvm_ctx llvm_module (Int64.of_int stack_len)
      "stack"
  in
  let offset =
    Llvm.const_int
      (typ_lltype llvm_ctx (Var.typ (sp !target_ref)))
      (stack_len - 1)
  in
  let stack_ptr =
    Llvm.const_ptrtoint stack_ptr
      (typ_lltype llvm_ctx (Var.typ (sp !target_ref)))
  in
  Llvm.const_add stack_ptr offset

let create_initialized_section llvm_ctx llvm_module proj section_type ~is_const
    =
  let llvm_name = section_type_to_string section_type in
  let name = "." ^ llvm_name in
  get_section_mem name proj |> get_section_data
  |> Option.map (fun (arr, min_addr, max_addr) ->
      let base = create_global ~is_const llvm_ctx llvm_module arr llvm_name in
      eprintf "Section %s has length %d\n" name (Array.length arr);
      eprintf "Section %s has min addr %a\n" name Word.ppo min_addr;
      eprintf "Section %s has max addr %a\n" name Word.ppo max_addr;
      { base; min_addr; max_addr })

type 'a region = { addr : int64; size : int64; info : 'a }

let create_uninitialized_section llvm_ctx llvm_module proj section_type
    region_info =
  let llvm_name = section_type_to_string section_type in
  let name = "." ^ llvm_name in
  Seq.find region_info ~f:(fun { info; _ } -> info = name)
  |> Option.map (fun { addr; size; _ } ->
      let base =
        create_uninitialized_global llvm_ctx llvm_module size llvm_name
      in
      let addr = Int64.to_int addr in
      let size = Int64.to_int size in
      let min_addr = Word.of_int ~width:64 addr in
      let max_addr = Word.of_int ~width:64 (addr + size - 1) in
      eprintf "Section %s has length %d\n" name size;
      eprintf "Section %s has min addr %a\n" name Word.ppo min_addr;
      eprintf "Section %s has max addr %a\n" name Word.ppo max_addr;
      { base; min_addr; max_addr })

let get_intrinsic_defs sub =
  match Term.first blk_t sub with
  | None -> Seq.empty
  | Some blk -> Term.enum def_t blk

let inline_intrinsics prog sub =
  let cfg = Sub.to_cfg sub in
  Seq.fold (Graphs.Ir.edges cfg) ~init:cfg ~f:(fun cfg edge ->
      let src = Graphs.Ir.Edge.src edge |> Graphs.Ir.Node.label in
      let jmp = Graphs.Ir.Edge.jmp edge in
      let dst = Graphs.Ir.Edge.dst edge |> Graphs.Ir.Node.label in
      match get_direct_call jmp with
      | None -> cfg
      | Some call_tid ->
          let sub = Term.find sub_t prog call_tid |> Base.Option.value_exn in
          if Term.has_attr sub Sub.intrinsic then (
            let intrinsic_defs = get_intrinsic_defs sub in
            let builder =
              Blk.Builder.init ~same_tid:true ~copy_defs:true ~copy_jmps:false
                ~copy_phis:true src
            in
            Seq.iter intrinsic_defs ~f:(fun def ->
                Blk.Builder.add_def builder def);
            Seq.iter (Term.enum jmp_t dst) ~f:(fun jmp ->
                Blk.Builder.add_jmp builder jmp);
            let b = Blk.Builder.result builder in
            Graphs.Ir.Node.remove (Graphs.Ir.Edge.dst edge) cfg
            |> Graphs.Ir.Node.update (Graphs.Ir.Edge.src edge) b)
          else cfg)
  |> Sub.of_cfg

let simplify_jmps sub =
  let new_sub =
    Sub.Builder.create ~tid:(Term.tid sub) ~name:(Sub.name sub) ()
  in
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun blk ->
      let jmps = Term.enum jmp_t blk in
      if Seq.length jmps = 1 then Sub.Builder.add_blk new_sub blk
      else
        let blk = Blk.Builder.init ~copy_phis:true ~copy_defs:true blk in
        Seq.iter jmps ~f:(fun jmp ->
            if is_goto jmp then Blk.Builder.add_jmp blk jmp
            else
              let cond = Jmp.cond jmp in
              let new_jmp = Jmp.with_cond jmp (Int (Word.one 1)) in
              let new_blk = Blk.create ~jmps:[ new_jmp ] () in
              Sub.Builder.add_blk new_sub new_blk;
              let goto = Jmp.create_goto ~cond (Direct (Term.tid new_blk)) in
              Blk.Builder.add_jmp blk goto);
        Sub.Builder.add_blk new_sub (Blk.Builder.result blk));
  Sub.Builder.result new_sub

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

let calls_intrinsic prog =
  let callgraph = Program.to_graph prog in
  let visit_edge _ edge filter_set =
    let caller = Graphs.Callgraph.Edge.src edge in
    let callee = Graphs.Callgraph.Edge.dst edge in
    let term = Term.find sub_t prog callee in
    if
      Base.Option.value_map term ~default:false ~f:(fun term ->
          Term.has_attr term Sub.intrinsic)
    then Tid.Set.add filter_set caller
    else filter_set
  in
  Graphlib.Std.Graphlib.depth_first_search
    (module Graphs.Callgraph)
    callgraph ~init:Tid.Set.empty ~enter_edge:visit_edge

let should_filter filter_set syms sub =
  Base.List.mem ~equal:String.equal filter_subs (Sub.name sub)
  || Term.has_attr sub Sub.stub
  || Term.has_attr sub Sub.extern
  || Term.has_attr sub Sub.intrinsic
  || Tid.Set.mem filter_set (Term.tid sub)
  || (not @@ StrSet.mem (Sub.name sub) syms)

let setup proj =
  let target = Project.target proj in
  set_target_ref target;
  set_ptrsize target

let remove_plt proj =
  let plt = get_section_mem ".plt" proj in
  match plt with
  | None -> proj
  | Some (plt, _) ->
      let plt_syms = Symtab.intersecting (Project.symbols proj) plt in
      Base.List.fold plt_syms ~init:(Project.symbols proj)
        ~f:(fun syms (name, blk, addr) -> Symtab.remove syms (name, blk, addr))
      |> Project.with_symbols proj

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
  let regions =
    let open Ogre.Monad_infix in
    Ogre.collect quary
  in
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
          if should_filter filter_set syms sub then (
            eprintf "Skipping sub %s\n" (Sub.name sub);
            None)
          else
            (* Intrinsics have wrong semantics, for now skip the functions that call an intrinsic and do not inline them *)
            (* let sub = inline_intrinsics prog sub in *)
            Some (sub |> simplify_jmps)))

let init_subs llvm_ctx llvm_module section_list proj =
  Term.enum sub_t (Project.program proj)
  |> Seq.iter ~f:(fun sub ->
      Reader.run (set_sub sub) (llvm_ctx, llvm_module, section_list));
  proj

let convert_binary output_program proj =
  let llvm_ctx = Llvm.create_context () in
  let llvm_module = Llvm.create_module llvm_ctx "Convlir" in
  setup proj;
  eprintf "Creating stack pointer\n";
  let stack_ptr = create_stack_ptr llvm_ctx llvm_module in
  let regions = get_named_region_info proj in
  Seq.iter regions ~f:(fun { addr; size; info } ->
      eprintf "Named region %s has addr %Ld and size %Ld\n" info addr size);
  eprintf "Creating data section\n";
  let data_section =
    create_initialized_section llvm_ctx llvm_module proj DATA ~is_const:false
  in
  eprintf "Creating rodata section\n";
  let rodata_section =
    create_initialized_section llvm_ctx llvm_module proj RODATA ~is_const:true
  in
  eprintf "Creating bss section\n";
  let bss_section =
    create_uninitialized_section llvm_ctx llvm_module proj BSS regions
  in
  eprintf "Creating got section\n";
  let got_section =
    create_initialized_section llvm_ctx llvm_module proj GOT ~is_const:true
  in
  eprintf "Creating gotplt section\n";
  let gotplt_section =
    create_initialized_section llvm_ctx llvm_module proj GOTPLT ~is_const:true
  in
  eprintf "Creating rodata_rel section\n";
  let rodata_rel_section =
    create_initialized_section llvm_ctx llvm_module proj RODATA_REL
      ~is_const:true
  in
  eprintf "Getting symbols\n";
  let section_list =
    Base.List.filter_mapi
      ~f:(fun i section ->
        match section with
        | None ->
            eprintf "Warning: section : %d was not found in binary\n" i;
            None
        | Some _ -> section)
      [
        data_section;
        rodata_section;
        got_section;
        gotplt_section;
        bss_section;
        rodata_rel_section;
      ]
  in
  filter_subs proj
  |> init_subs llvm_ctx llvm_module section_list
  |> create_prog llvm_ctx llvm_module section_list stack_ptr;
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
      Project.register_pass' ~name:"convlir" (convert_binary output_file);
      Ok ())
