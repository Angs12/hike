open Bap.Std
open Bap_main
open Bap.Std.Bil.Types
open Regular.Std
open Bap_core_theory
open Bap_main.Extension.Command
open Format
open Bil2llvm
open Convutils
open Targetutils
module Reader = Monads.Std.Monad.Reader
module StrMap = Map.Make (String)
module StrSet = Set.Make (String)

let get_section_mem name proj =
  let mem, _ =
    Project.memory proj |> Memmap.to_sequence
    |> Seq.find_exn ~f:(fun (_, v) ->
        Base.Option.value_map (Value.get Image.section v) ~default:false
          ~f:(fun n -> String.equal n name))
  in
  mem

let get_section name proj =
  let mem, _ =
    Project.memory proj |> Memmap.to_sequence
    |> Seq.find_exn ~f:(fun (_, v) ->
        Base.Option.value_map (Value.get Image.section v) ~default:false
          ~f:(fun n -> String.equal n name))
  in
  let lenght = Memory.length mem in
  let min_addr = Memory.min_addr mem in
  let arr = Base.Array.init lenght ~f:(fun _ -> 0) in
  Memory.iteri ~word_size:`r8 mem ~f:(fun index v ->
      arr.(Word.to_int_exn (Word.( - ) index min_addr)) <- Word.to_int_exn v);
  arr

let is_mem var = match Var.typ var with Mem _ -> true | _ -> false

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
           if Var.same reg !sp || Var.same reg !fp then
             Arg.create ~intent:Both reg (Var reg)
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
        if Base.List.mem !base_regs v ~equal:Var.same then unaliased_reg_exp v
        else Bil.Var v
    end
  in
  Term.map blk_t sub ~f:(fun blk ->
      Term.map def_t blk ~f:(fun def ->
          let rhs = Def.rhs def in
          let new_rhs = mapper#map_exp rhs in
          Def.with_rhs def new_rhs))

let create_stack_ptr llvm_ctx llvm_module =
  let stack = Base.Array.create ~len:stack_len 0 in
  let stack_ptr =
    create_global ~is_const:false llvm_ctx llvm_module stack "stack"
  in
  let offset =
    Llvm.const_int (typ_lltype llvm_ctx (Var.typ !sp)) (stack_len - 1)
  in
  let stack_ptr =
    Llvm.const_ptrtoint stack_ptr (typ_lltype llvm_ctx (Var.typ !sp))
  in
  Llvm.const_add stack_ptr offset

let update_exp reg_map exp =
  Var.Map.fold reg_map ~init:exp ~f:(fun ~key ~data exp ->
      Exp.map (base_exp_sub key data) exp)

let update_var reg_map var =
  Var.Map.fold !reg_map ~init:var ~f:(fun ~key ~data var ->
      if Var.same var key then (
        let new_index = Var.index data + 1 in
        reg_map :=
          Var.Map.change !reg_map key ~f:(fun _ ->
              Some (Var.with_index data new_index));
        Var.with_index data new_index)
      else var)

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

let transfer_regs sub =
  Term.map blk_t sub ~f:(fun blk ->
      let tid = Term.tid blk in
      let builder =
        Blk.Builder.init ~same_tid:true ~copy_phis:false ~copy_defs:true
          ~copy_jmps:true blk
      in
      let cfg = Sub.to_graph sub in
      let blk_incoming = Graphs.Tid.Node.preds (Term.tid blk) cfg in
      Base.List.iter !base_regs ~f:(fun base ->
          let phi_rhs =
            Seq.fold blk_incoming ~init:[] ~f:(fun prev tid ->
                let reg_var = create_phi_reg base ~typ:(Var.typ base) ~tid in
                (tid, Bil.Var reg_var) :: prev)
          in
          let phi = Phi.of_list base phi_rhs in
          Blk.Builder.add_phi builder phi);
      Base.List.iter !base_regs ~f:(fun base ->
          let reg_var = create_phi_reg base ~typ:(Var.typ base) ~tid in
          let def = Def.create reg_var (Var base) in
          let def = Term.set_attr def is_phi_reg () in
          Blk.Builder.add_def builder def);
      Blk.Builder.result builder)

let is_external sub =
  Base.String.is_substring ~substring:":external" (Sub.name sub)

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

let should_filter syms sub =
  Printf.eprintf "Checking sub %s if it should be filtered\n" (Sub.name sub);
  flush stderr;
  Base.List.mem ~equal:String.equal filter_subs (Sub.name sub)
  || is_external sub || Term.has_attr sub Sub.stub
  || Term.has_attr sub Sub.extern
  || Term.has_attr sub Sub.intrinsic
  || (not @@ StrSet.mem (Sub.name sub) syms)

let setup proj =
  let target = Project.target proj in
  set_target_ref target;
  set_ptrsize target;
  set_base_regs target;
  set_stack target;
  set_fp target;
  set_sp target

let remove_plt proj =
  let plt = get_section_mem ".plt" proj in
  let plt_syms = Symtab.intersecting (Project.symbols proj) plt in
  Base.List.fold plt_syms ~init:(Project.symbols proj)
    ~f:(fun syms (name, blk, addr) ->
      eprintf "Removimg PLT symbol %s \n" name;
      Symtab.remove syms (name, blk, addr))
  |> Project.with_symbols proj

let pp proj output_program =
  let proj = run_pass proj "trivial-condition-form" in
  Project.passes ()
  |> Base.List.iter ~f:(fun pass ->
      eprintf "Project pass :: %s \n" (Project.Pass.name pass));
  let llvm_ctx = Llvm.create_context () in
  let llvm_module = Llvm.create_module llvm_ctx "Convlir" in
  setup proj;
  let stack_ptr = create_stack_ptr llvm_ctx llvm_module in
  let syms =
    Symtab.to_sequence (Project.symbols proj)
    |> Seq.fold ~init:StrSet.empty ~f:(fun set (name, _, _) ->
        StrSet.add name set)
  in
  let proj =
    Project.map_program proj ~f:(fun prog ->
        Term.filter_map sub_t prog ~f:(fun sub ->
            if should_filter syms sub then None
            else (
              Reader.run (set_sub sub) (llvm_ctx, llvm_module);
              Some sub)))
  in
  let proj =
    Project.map_program proj ~f:(fun prog ->
        Term.map sub_t prog ~f:(fun sub ->
            Printf.eprintf "Preparing sub %s\n" (Term.name sub);
            flush stderr;
            sub |> simplify_jmps |> transfer_regs))
  in
  Reader.run
    (create_prog (Project.program proj) stack_ptr)
    (llvm_ctx, llvm_module);
  Llvm.print_module output_program llvm_module;
  Llvm.dispose_module llvm_module;
  Llvm.dispose_context llvm_ctx

let main input_program output_program _ =
  Bil.passes ()
  |> Base.List.iter ~f:(fun pass ->
      eprintf "Bil pass :: %s \n" (Bil.Pass.name pass));
  let passes =
    Base.List.map ~f:get_bil_pass
      [
        "bnf1";
        "constant-folding";
        "constant-propagation";
        "prune-dead-virtuals";
      ]
  in
  Bil.select_passes passes;
  Image.available_backends ()
  |> Base.List.iter ~f:(fun backend ->
      eprintf "Available backend: %s\n" backend);
  let loader = "llvm" in
  let proj =
    Project.create @@ Project.Input.load input_program ~loader
    |> Core.Or_error.ok_exn |> remove_plt
  in
  pp proj output_program;
  Ok ()

let features_used =
  [
    "semantics";
    "function-starts";
    "disassembler";
    "lifter";
    "symbolizer";
    "rooter";
    "reconstructor";
    "brancher";
    "loader";
    "abi";
  ]

let input =
  Extension.Command.argument
    Extension.Type.("input file" %: string)
    ~doc:"Executable to convert to LLVM IR"

let output =
  Extension.Command.argument
    Extension.Type.("output file" %: string)
    ~doc:"File to output LLVM IR"

let () =
  Extension.Command.declare "convlir"
    (args $ input $ output)
    main ~doc:"Convert a binary to LLVM IR" ~requires:features_used

let () = Extension.declare ~provides:[ "command" ] (fun _ -> Ok ())
