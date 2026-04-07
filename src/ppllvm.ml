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
module StrMap = Map.Make (String)

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

let set_sub llvm_ctx llvm_module sub =
  let free_vars = free_vars sub in
  let rets =
    (if Theory.Target.matches !target_ref "x86_64-gnu-elf" then
       Calling_conventions.x86_64_sysv.return_regs
     else [])
    |> Base.List.map ~f:(fun reg -> Arg.create ~intent:Out reg (Var reg))
  in
  if Term.name sub = "@main" then
    let rdi = Var.create "RDI" (Imm 64) in
    let rsi = Var.create "RSI" (Imm 64) in
    subs :=
      StrMap.add (Term.name sub)
        ( [],
          [
            Arg.create ~intent:In rdi (Var rdi);
            Arg.create ~intent:In rsi (Var rsi);
          ] )
        !subs
  else
    subs :=
      StrMap.add (Term.name sub)
        ( rets,
          Base.List.map
            ~f:(fun reg ->
              if Var.same reg !sp || Var.same reg !fp then
                Arg.create ~intent:Both reg (Var reg)
              else Arg.create ~intent:In reg (Var reg))
            free_vars )
        !subs;
  create_fun llvm_ctx llvm_module (Term.tid sub)

module type Abi = sig
  val return : Decl_parser.functype -> var list

  val args :
    Decl_parser.functype list -> Decl_parser.functype -> (exp * intent) list
end

let arg_type (exp : exp) =
  match exp with
  | Int i -> Imm (Word.bitwidth i)
  | Var v -> Var.typ v
  | Load (_, _, _, size) -> Imm (Size.in_bits size)
  | _ -> failwith "pp exp type: non-imm var"

let set_libc llvm_ctx llvm_module target libc =
  let abi =
    if Theory.Target.matches target "x86_64-gnu-elf" then
      (module Gnu64_abi : Abi)
    else failwith "abi not supported"
  in
  let module Abi = (val abi : Abi) in
  StrMap.iter
    (fun name (data : Decl_parser.funcdef) ->
      let ret = Abi.return data.return in
      let args = Abi.args data.args data.return in
      let ret_typ = Decl_parser.functype_to_lltype llvm_ctx data.return in
      let args_typ =
        Base.List.map
          ~f:(fun typ -> Decl_parser.functype_to_lltype llvm_ctx typ)
          data.args
      in
      let fn_typ = Llvm.function_type ret_typ (Array.of_list args_typ) in
      let fn = Llvm.declare_function (sanitize_name name) fn_typ llvm_module in
      ll_funcs := StrMap.add name (fn, fn_typ) !ll_funcs;
      let func_decl =
        ( List.map (fun r -> Arg.create ~intent:Out r (Var r)) ret,
          List.mapi
            (fun i (a, intent) ->
              let arg_var =
                Var.create (name ^ sprintf "arg%d" i) (arg_type a)
              in
              Arg.create ~intent arg_var a)
            args )
      in
      subs := StrMap.add ("@" ^ name) func_decl !subs)
    libc

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

let update_args sub =
  let builder =
    Sub.Builder.create ~tid:(Term.tid sub) ~name:(Sub.name sub) ()
  in
  Seq.iter (Term.enum blk_t sub) ~f:(fun blk -> Sub.Builder.add_blk builder blk);
  Sub.Builder.result builder

(* TODO *)
let update_rets sub =
  let sub_builder =
    Sub.Builder.create ~tid:(Term.tid sub) ~name:(Sub.name sub) ()
  in
  let new_blks = ref [] in
  let sub =
    Term.map blk_t sub ~f:(fun blk ->
        let builder = Blk.Builder.init ~copy_phis:true ~copy_defs:true blk in
        let control_flow = Term.enum jmp_t blk in
        (match cf_type control_flow with
        | Ret -> (
            let jmp =
              Base.Option.value_exn ~message:"ret jmp not found"
                (Term.first jmp_t blk)
            in
            let call = jmp |> call_exn in
            match Call.target call with
            | Direct _ ->
                let temp_builder = Blk.Builder.create () in
                Blk.Builder.add_jmp temp_builder
                  (Jmp.create_ret (Indirect (Var (Var.create "ret" Unk))));
                let new_blk = Blk.Builder.result temp_builder in
                new_blks := new_blk :: !new_blks;
                let call = Call.with_return call (Direct (Term.tid new_blk)) in
                Blk.Builder.add_jmp builder (Jmp.create_call call)
            | Indirect _ -> Blk.Builder.add_jmp builder jmp)
        | _ ->
            Seq.iter (Term.enum jmp_t blk) ~f:(fun jmp ->
                Blk.Builder.add_jmp builder jmp));
        Blk.Builder.result builder)
  in
  Seq.iter (Term.enum blk_t sub) ~f:(fun blk ->
      Sub.Builder.add_blk sub_builder blk);
  Base.List.iter !new_blks ~f:(fun blk -> Sub.Builder.add_blk sub_builder blk);
  Seq.iter (Term.enum arg_t sub) ~f:(fun arg ->
      Sub.Builder.add_arg sub_builder arg);
  Sub.Builder.result sub_builder

let update_main sub =
  if Sub.name sub = "main" then
    let entry_tid =
      Base.Option.value_exn ~message:"Main function has no blocks"
        (Sub.to_graph sub |> Graphs.Tid.Node.succs Graphs.Tid.start |> Seq.hd)
    in
    Term.map blk_t sub ~f:(fun blk ->
        if Term.tid blk = entry_tid then (
          let builder = Blk.Builder.init ~copy_phis:true ~copy_jmps:true blk in
          let arg_var_fp =
            create_arg !fp ~typ:(Var.typ !fp) ~tid:(Term.tid sub)
          in
          let arg_var_sp =
            create_arg !sp ~typ:(Var.typ !sp) ~tid:(Term.tid sub)
          in
          let stack_ptr = Var.create "stack_ptr" (Var.typ !sp) in
          let stack_exp =
            Bil.BinOp
              ( Bil.PLUS,
                Bil.Var stack_ptr,
                Bil.Int (Word.of_int ~width:(var_size !sp) (stack_len - 1)) )
          in
          let sp_def = Def.create arg_var_sp stack_exp in
          let fp_def =
            Def.create arg_var_fp
              (Bil.Int (Word.of_int ~width:(var_size !fp) 0))
          in
          Blk.Builder.add_def builder sp_def;
          Blk.Builder.add_def builder fp_def;
          Term.enum def_t blk
          |> Seq.iter ~f:(fun def -> Blk.Builder.add_def builder def);
          Blk.Builder.result builder)
        else blk)
  else sub

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

let update_label reg_map label =
  match label with
  | Direct _ -> label
  | Indirect exp -> Indirect (update_exp !reg_map exp)

let update_jmp_cond reg_map jmp =
  let cond = Jmp.cond jmp in
  Jmp.with_cond jmp (update_exp !reg_map cond)

let transfer_regs sub =
  Term.map blk_t sub ~f:(fun blk ->
      let tid = Term.tid blk in
      let reg_map =
        ref
        @@ Base.List.fold !base_regs ~init:Var.Map.empty ~f:(fun map base ->
            let reg = create_reg base ~typ:(Var.typ base) ~tid in
            Var.Map.add_exn map ~key:base ~data:reg)
      in
      let blk =
        Blk.map_elts blk ~def:(fun def ->
            let var = Def.lhs def in
            let def = Def.map_exp ~f:(update_exp !reg_map) def in
            Def.with_lhs def (update_var reg_map var))
        |> Blk.map_elts ~jmp:(fun jmp ->
            (match Jmp.kind jmp with
              | Call call ->
                  Jmp.with_kind jmp
                    (Call
                       (Call.with_target call
                          (update_label reg_map (Call.target call))))
              | Goto label ->
                  Jmp.with_kind jmp (Goto (update_label reg_map label))
              | _ -> jmp)
            |> update_jmp_cond reg_map)
      in
      let builder =
        Blk.Builder.init ~same_tid:true ~copy_phis:false ~copy_defs:false
          ~copy_jmps:true blk
      in
      let cfg = Sub.to_graph sub in
      let blk_incoming = Graphs.Tid.Node.preds (Term.tid blk) cfg in
      (if not (Seq.to_list blk_incoming = [ Graphs.Tid.start ]) then
         Base.List.iter !base_regs ~f:(fun base ->
             let var = create_reg base ~typ:(Var.typ base) ~tid in
             let phi_rhs =
               Seq.fold blk_incoming ~init:[] ~f:(fun prev tid ->
                   let reg_var = create_phi_reg base ~typ:(Var.typ base) ~tid in
                   (tid, Bil.Var reg_var) :: prev)
             in
             let phi = Phi.of_list var phi_rhs in
             Blk.Builder.add_phi builder phi)
       else
         let free_vars = free_vars sub in
         Base.List.iter !base_regs ~f:(fun base ->
             if Base.List.mem free_vars base ~equal:Var.same then
               let reg = create_reg base ~typ:(Var.typ base) ~tid in
               let def =
                 let arg =
                   create_arg base ~typ:(Var.typ base) ~tid:(Term.tid sub)
                 in
                 Def.create reg (Var arg)
               in
               Blk.Builder.add_def builder def
             else ()));
      Blk.elts blk
      |> Seq.iter ~f:(fun elt ->
          match elt with `Def def -> Blk.Builder.add_def builder def | _ -> ());
      let rets =
        match cf_type (Term.enum jmp_t blk) with
        | CallFun sub_tid -> get_rets sub_tid
        | CallIndirect ->
            Calling_conventions.x86_64_sysv.return_regs
            |> Base.List.map ~f:(fun reg ->
                Arg.create ~intent:Out reg (Var reg))
        | _ -> []
      in
      Var.Map.iteri !reg_map ~f:(fun ~key ~data ->
          if is_ret_reg rets key then
            let ret_var = create_ret key ~typ:(Var.typ key) ~tid in
            let def = Def.create ret_var (Var data) in
            Blk.Builder.add_def builder def
          else
            let reg_var = create_phi_reg key ~typ:(Var.typ key) ~tid in
            let def = Def.create reg_var (Var data) in
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

let should_filter proj sub =
  let symtab = Project.symbols proj in
  Base.List.mem ~equal:String.equal filter_subs (Sub.name sub)
  || is_external sub || Term.has_attr sub Sub.stub
  || Term.has_attr sub Sub.extern
  || Term.has_attr sub Sub.intrinsic
  || Option.is_none (Symtab.find_by_name symtab (Sub.name sub))

let setup proj =
  let target = Project.target proj in
  set_target_ref target;
  set_ptrsize target;
  set_base_regs target;
  set_stack target;
  set_fp target;
  set_sp target
(* set_libc llvm_ctx llvm_module target libc *)

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
  (* let proj = run_pass proj "glibc-runtime" in *)
  let sym = Project.symbols proj in
  Symtab.to_sequence sym
  |> Seq.iter ~f:(fun (name, _, _) -> eprintf "%s\n" name);
  Project.passes ()
  |> Base.List.iter ~f:(fun pass ->
      eprintf "Project pass :: %s \n" (Project.Pass.name pass));
  let stack = Base.Array.create ~len:stack_len 0 in
  (* let libc = Decl_parser.parse_header_file "stdio_headers.ll" in *)
  let llvm_ctx = Llvm.create_context () in
  let llvm_module = Llvm.create_module llvm_ctx "Convlir" in
  setup proj;
  let prog = Project.program proj in
  Term.enum sub_t prog
  |> Seq.iter ~f:(fun sub ->
      if should_filter proj sub then () else set_sub llvm_ctx llvm_module sub);
  let proj =
    Project.map_program proj ~f:(fun prog ->
        Term.filter_map sub_t prog ~f:(fun sub ->
            if should_filter proj sub then None
            else
              Some
                (sub |> unalias_sub |> update_args |> Sub.ssa |> transfer_regs
               |> update_main)))
  in
  let stack_ptr =
    create_global ~is_const:false llvm_ctx llvm_module stack "stack"
  in
  create_prog llvm_ctx llvm_module (Project.program proj) stack_ptr;
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
