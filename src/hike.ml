open Bap.Std
open Bap_main
open Bap.Std.Bil.Types
open Bap_core_theory
open Bil2llvm
open Convutils
open Targetutils
open Printf
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

(* [is_intrinsic term]: R7 — attribute-preserving mappers guarantee [Sub.intrinsic] survives all term rebuilds (Term.mapper does [{t with self}], Def.with_* preserves dict), so the canonical check is the attribute alone. *)
let is_intrinsic (term : sub term) : bool =
  Term.has_attr term Sub.intrinsic

let is_emittable_intrinsic (term : sub term) : bool =
  is_intrinsic term && not (Seq.is_empty (Term.enum blk_t term))

(* [is_llvm_x86_intrinsic term]: R7 — was a name-prefix hack ([intrinsic:llvm-x86_64:*]). *)
let is_llvm_x86_intrinsic (term : sub term) : bool =
  Term.has_attr term Sub.intrinsic && Seq.is_empty (Term.enum blk_t term)

let fp_returning (sub : sub term) : bool =
  let is_ymm n = Base.String.is_prefix n ~prefix:"YMM" in
  let is_value_reg v =
    let n = Var.name (Var.base v) in
    Base.List.mem ["RAX"; "EAX"; "RDX"; "EDX"] n ~equal:String.equal
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
       Calling_conventions.x86_64_sysv.return_regs
     else [])
    |> Base.List.map ~f:(fun reg -> Arg.create ~intent:Out reg (Var reg))
  in
  let rets =
    (* The FP-return member: a double-returning callee (the -O0 `return <double-expr>` leaves the value in XMM0 with NO RAX binding — the model's [return_regs] are integer-only) delivers the value via [%YMM0] in the ret. *)
    if fp_returning sub then
      rets
      @ [
          Arg.create ~intent:Out (Calling_conventions.r256 "YMM0")
            (Var (Calling_conventions.r256 "YMM0"));
        ]
    else rets
  in
  let rets, args =
    if is_emittable_intrinsic sub then begin
    (* The FP-soft-float intrinsic models: the signature is the MODEL's own interface, not the SysV regs — args = the input vars the body reads ([intrinsic:xN] — the free vars), rets = the output vars the body defines ([intrinsic:yN] — the def lhs vars that are not themselves inputs). *)
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
     let rdi = Var.create "RDI" (Imm 64) in
     let rsi = Var.create "RSI" (Imm 64) in
     let args =
       [
         Arg.create ~intent:In rdi (Var rdi);
         Arg.create ~intent:In rsi (Var rsi);
       ]
     in
      (rets, args)
   else
       (* M2 (ADR 0004): single ptr %hike_stack replaces trailing i64 stack_arg_N arity.
         Subs with incoming stack args (lo>0, positive offsets) get hike_stack; main exempt. *)
      let has_positive =
        let vsa_positive =
          Core.Map.find (Hike_kb.vsa_info ()) (Term.tid sub)
          |> Base.Option.value_map ~default:false ~f:(fun info ->
              Base.List.exists info.Convutils.offsets ~f:(fun (_, kind) ->
                  Convutils.is_positive_kind kind))
        in
        let bil_positive =
          let rec has_pos (e : exp) : bool =
            match e with
            | Bil.BinOp (Bil.PLUS, Bil.Var b, Bil.Int c)
              when Var.same b (Targetutils.fp target) ->
                Int64.compare (Int64.sub (Word.to_int64_exn c) 8L) 0L >= 0
            | Bil.BinOp (_, a, b) -> has_pos a || has_pos b
            | Bil.Cast (_, _, e') -> has_pos e'
            | _ -> false
          in
          Term.enum blk_t sub
          |> Seq.exists ~f:(fun blk ->
              Term.enum def_t blk
              |> Seq.exists ~f:(fun d -> has_pos (Def.rhs d)))
        in
        vsa_positive || bil_positive
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
          let int_order = ["RDI"; "RSI"; "RDX"; "RCX"; "R8"; "R9"] in
          match Base.List.findi int_order ~f:(fun _ s -> String.equal s n) with
          | Some (i, _) -> (i, n)
          | None ->
            if Base.String.is_prefix n ~prefix:"YMM" then
              (try
                 let num = int_of_string (String.sub n 3 (String.length n - 3)) in
                 if 0 <= num && num < 8 then (6 + num, n) else (100, n)
               with _ -> (100, n))
            else (100, n)
        in
        Base.List.filter free_vars ~f:(fun reg ->
            let n = Var.name (Var.base reg) in
            let is_callee_saved =
              Base.List.mem
                ["RBX"; "R12"; "R13"; "R14"; "R15"]
                n ~equal:String.equal
            in
            not
              (Var.same reg (sp target)
              || Var.same reg (fp target)
              || is_callee_saved
              || Base.String.is_prefix n ~prefix:"intrinsic:"))
        |> Base.List.sort ~compare:(fun a b ->
            let ra, na = rank_of_var a in
            let rb, nb = rank_of_var b in
            match Int.compare ra rb with
            | 0 -> String.compare na nb
            | c -> c)
        |> Base.List.map ~f:(fun reg -> Arg.create ~intent:In reg (Var reg))
        |> fun regs -> regs @ hike_stack_arg
      in
     (* The PLT-TRAMPOLINE subs (the BAP-resolved PLT stubs — the atexit/setlocale class): their BIL is `...; call @real with noreturn` and their free vars are just {mem} — the stub never READS the incoming register state, so. *)
     let is_plt_trampoline =
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
       if is_plt_trampoline then
         Base.List.map Calling_conventions.x86_64_sysv.param_regs
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
      eprintf "Section %s has length %d\n" name size;
      eprintf "Section %s has min addr %a\n" name Word.ppo min_addr;
      eprintf "Section %s has max addr %a\n" name Word.ppo max_addr;
      { base; min_addr; max_addr })

(* [get_copy_relocations proj]: The COPY-RELOCATED bss symbols — the Ogre [llvm:name-reference] rows whose fixup falls inside the .bss (the R_X86_64_COPY class: the .bss slots the DYNAMIC LINKER fills with the real symbol's data at startup — the stdout/stderr FILE structs). *)
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

let rename_intrinsics sub =
  let rename_var v =
    let n = Var.name v in
    if Base.String.is_prefix n ~prefix:"intrinsic:" then
      let w = match Var.typ v with Imm w -> w | Mem _ -> 0 | Unk -> 0 in
      Var.create (Printf.sprintf "%s_%d" n w) (Var.typ v)
    else v
  in
  let exp_mapper = object
    inherit Exp.mapper
    method! map_var v = Bil.Var (rename_var v)
  end in
  Term.map blk_t sub ~f:(fun blk ->
    Term.map def_t blk ~f:(fun d ->
      let lhs = Def.lhs d in
      let rhs = Def.rhs d in
      let lhs' = rename_var lhs in
      let rhs' = exp_mapper#map_exp rhs in
      if Var.same lhs lhs' && Exp.equal rhs rhs' then d
      else Def.with_lhs (Def.with_rhs d rhs') lhs'
    )
  )

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
        (* Builder starts from empty dict — copy block attrs. *)
        let new_blk = Term.with_attrs new_blk (Term.attrs blk) in
        Sub.Builder.add_blk new_sub new_blk);
  let res = Sub.Builder.result new_sub in
  (* Builder starts from empty dict — copy sub attrs (intrinsic/stub/extern). *)
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

(* The FP-soft-float intrinsic class : BAP models x86 FP instructions (mulsd/addsd/divsd/ subsd/cvtsi2sd/cvttsd2si) as CALLS to `intrinsic:*` subs whose bodies are bit-precise IEEE-754 soft-float BIL (the. *)
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
  (* an emittable intrinsic (the FP-soft-float models) is NEVER filtered — not even when a later pass marks it [Sub.stub] (the stub marking is the no-symbol heuristic, not a body absence; the soft-float bodies are real BIL and must be emitted). *)
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
  (* the memmap's native key width = the program architecture's address size (no hardcoded 64). *)
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
          if should_filter filter_set syms sub then (
            eprintf "Skipping sub %s\n" (Sub.name sub);
            None)
          else
            Some (sub |> rename_intrinsics |> simplify_jmps)))

(* The per-project setup + the sub FILTER are their OWN pass (see the registration below) — no pass calls another pass's logic directly; the chain is expressed in the ~deps of each registration and bap runs them in order. *)

let init_subs ctx llvm_ctx llvm_module section_list proj =
  (* The sub-signature table [ctx.subs] is filled ONCE here (set-once, then read-only during emission). *)
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
                (* the NATIVE-FP-mapped intrinsics: the signature is stored (the calls' arg shapes derive from it) but the soft-float function is NOT defined — [create_sub] skips it (the calls are intercepted in [create_call] and emitted as native LLVM FP ops). *)
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
  let addr_bits = addr_size_bits target in
  let regions = get_named_region_info proj in
  Seq.iter regions ~f:(fun { addr; size; info } ->
      eprintf "Named region %s has addr %Ld and size %Ld\n" info addr size);
  (* pass 1: the data-section GLOBALS (typed [n x i64] so the pointer-slot initializers can hold [ptrtoint] constants) — the initializers themselves are set in pass 3, AFTER the subs exist (the function-pointer slots reference the defined functions). *)
  let mk_section section_type ~is_const =
    let llvm_name = section_type_to_string section_type in
    let name = "." ^ llvm_name in
    get_section_mem name proj |> get_section_data
    |> Option.map (fun (arr, min_addr, max_addr) ->
        eprintf "Section %s has length %d\n" name (Array.length arr);
        eprintf "Section %s has min addr %a\n" name Word.ppo min_addr;
        eprintf "Section %s has max addr %a\n" name Word.ppo max_addr;
        let base =
          Bil2llvm.create_section_global llvm_ctx llvm_module
            (Array.length arr) llvm_name ~is_const
        in
        (arr, min_addr, max_addr, base))
  in
  eprintf "Creating data section\n";
  let data_section = mk_section DATA ~is_const:false in
  eprintf "Creating rodata section\n";
  let rodata_section = mk_section RODATA ~is_const:true in
  eprintf "Creating bss section\n";
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
       (* The AUTHORITATIVE-write scan: a copy-reloc slot whose lifted stores do NOT participate in a same-sub read-modify-write mirror ([load slot; ...; store slot] — head's optarg) receives a fresh VALUE (the lifted. *)
       let slot_of_addr (v : int64) : bool =
         Base.List.mem all v ~equal:Int64.equal
       in
       (* the shared traversal: collect the copy-reloc-slot addresses a sub's memory defs reference via shape [f] (a constant- address Load or Store). *)
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
       (* per-slot: does any sub BOTH load and store it (in the SAME sub — the read-modify-write mirror)? *)
       let loads_and_stores : int64 list =
         Term.enum sub_t (Project.program proj) |> Seq.to_list
         |> Base.List.concat_map ~f:(fun sub ->
             Base.List.filter (slot_loads sub) ~f:(fun v ->
                 Base.List.mem (slot_stores sub) v ~equal:Int64.equal))
       in
       let stores_only : int64 list =
         Term.enum sub_t (Project.program proj) |> Seq.to_list
         |> Base.List.concat_map ~f:slot_stores
       in
       let authoritative = stores_only in
       if authoritative = [] then all
       else
         Base.List.filter all ~f:(fun a ->
             (* a slot that some sub BOTH loads AND stores is the read-modify-write mirror — the &var shape survives, the through-load stays. Only stores-only slots become plain. *)
             not
               (Base.List.mem authoritative a ~equal:Int64.equal
               && (not (Base.List.mem loads_and_stores a ~equal:Int64.equal))))
    | None -> []
  in
  eprintf "Creating got section\n";
  let got_section = mk_section GOT ~is_const:true in
  eprintf "Creating gotplt section\n";
  let gotplt_section = mk_section GOTPLT ~is_const:true in
  eprintf "Creating rodata_rel section\n";
  let rodata_rel_section = mk_section RODATA_REL ~is_const:true in
  (* The .text inline constant-pool (see Bil2llvm.create_load / create_rip_relative_addr): stashed into [text_section_ref] and NOT added to section_list/section_remap_ref, so compile-time .text loads (the constant-pool / format-string reads -- e.g. *)
  let text_section = mk_section TEXT ~is_const:true in
  let text_section_val =
    Base.Option.map text_section ~f:(fun (arr, min, max, _base) ->
      (arr, Word.to_int64_exn min, Word.to_int64_exn max))
  in
  eprintf "Getting symbols\n";
  (* the NATIVE function-pointer remap table: the symbol table's (addr → name) lookup lets the emitter turn native function-address constants (the `atexit (close_stdout)` arg) into the LIFTED functions' addresses ([ptrtoint @close_stdout]) — see [Bil2llvm.create_immidiate]. *)
  let symtab_val = Some (Project.symbols proj) in
  (* the DATA-section pointer-slot remap: every section's native (min, max) → the lifted global — [Bil2llvm.set_section_initializer] rewrites the slots holding native addresses. *)
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
            eprintf "Warning: section : %d was not found in binary\n" i;
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
      ptrsize;
      addr_bits;
    }
  in
  let ctx, proj' = init_subs ctx llvm_ctx llvm_module section_list proj in
  (* pass 2: the data-section INITIALIZERS — AFTER the subs exist, so the function-pointer slots resolve to the defined functions. *)
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
           (* the per-project setup + the sub FILTER — its own pass, FIRST in the chain (the relevance pass's dep), so the relevance tagging and the VSA fixpoints never touch the subs that would be dropped anyway (the user's design). *)
           filter_subs proj);
      (* The relevance analysis as its OWN always-run pass (registered pass "relevance", the D-2f L1 lane). *)
      Project.register_pass ~name:"relevance" ~deps:[ "hike-filter" ] ~runonce:true
        (fun proj ->
           Project.map_program proj ~f:(fun prog ->
               Term.map sub_t prog
                 ~f:(Hike_vsa_relevance.analyze (sp (Project.target proj)))));
      (* Per-sub VSA tag computation (registered pass "vsa", depends on "hike-relevance" — the relevance pass already filtered + tagged, so this pass runs on the already-filtered program). *)
      Project.register_pass ~name:"vsa" ~deps:[ "hike-relevance" ] ~runonce:true
        (fun proj ->
           (* M2 (ADR 0004): single fixpoint, no arity pre-pass — hike_stack threading replaces stack_arg_N. *)
           let cur = Hike_kb.vsa_info () in
           if not (Core.Map.is_empty cur) then (
             if Sys.getenv_opt "HIKE_VSA_DEBUG" <> None then
               Printf.eprintf "hike: vsa guard: skip second run (cur %d)\n" (Core.Map.length cur);
             proj)
           else
             let acc = ref Tid.Map.empty in
           Toplevel.exec begin
             KB.Seq.iter
               (Term.enum sub_t (Project.program proj))
               ~f:(fun sub ->
                 let info =
                   Hike_vsa.offsets_of_sub (sp (Project.target proj)) sub
                 in
                 (* compute the regions ONCE here (on the PRE-stack-to-locals sub — the converted slots vanish later, so the emitter cannot recompute them) and store them alongside the tags. *)
                 let info =
                   { info with
                     Convutils.regions =
                       Hike_stack_to_locals.regions_of_sub (sp (Project.target proj)) sub info }
                 in
                 if Sys.getenv_opt "HIKE_VSA_DEBUG" <> None then
                   Printf.eprintf "hike: vsa: %s -> %d tag(s)\n"
                     (Sub.name sub) (List.length info.Convutils.offsets);
                 acc := Core.Map.set !acc ~key:(Term.tid sub) ~data:info;
                 KB.return ())
           end;
           (* store every sub's tags into the project Knowledge Base in ONE write — the consumers (stack-to-locals / convlir) read it back via [Hike_kb.vsa_info ()] over the same global KB state (see hike_kb.ml). *)
           Hike_kb.provide !acc;
           proj);
      (* The BIL stack-to-locals pass (registered pass "stack-to-locals", the D-2c lane, oracle rev-2 — the user's design: free locals become function args through the EXISTING free-vars-as-args mechanism, zero new emitter code). *)
       Project.register_pass ~name:"stack-to-locals" ~runonce:true
        ~deps:[ "hike-vsa" ]
        (fun proj ->
           let proj =
             Project.map_program proj ~f:(fun prog ->
                 Term.map sub_t prog
                   ~f:(Hike_stack_to_locals.stack_to_locals
                         (sp (Project.target proj))))
           in
           (if Sys.getenv_opt "HIKE_VSA_DEBUG" <> None then
              Core.Map.iter (Hike_kb.vsa_info ()) ~f:(fun info ->
                  Printf.eprintf "hike: stl: %d tag(s)\n"
                    (List.length info.Convutils.offsets)));
           proj);
      (* The emitting pass: runs last, on the filtered + stack-to-locals + VSA-tagged project its deps deliver (the dep chain enforces vsa -> stack-to-locals -> convlir). *)
      (* The aggressive DCE — [Hike_dce.dce] eliminates the lifted RETURN epilogue (`#t := mem[RSP]; RSP := RSP + 8; call #t with noreturn` — the emitter emits a real LLVM [ret] anyway; the retaddr slot read drops out of the free-vars-as- args signature with it) and sweeps never-used defs. *)
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
