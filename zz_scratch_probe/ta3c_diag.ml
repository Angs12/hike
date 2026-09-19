(* TA-3c Lane A probe: the section-image load rule.  Three reports over
   one binary or a whole corpus directory:
   - the image-backed loads' exact value denotations (the table-entry
     words),
   - the dispatch registers' per-block entry words (the kill-summary
     question) and the indirect targets' denotations vs the sub's block
     addresses (the Lane B flip inputs),
   - --tagdiff: every sub's seam-derived kinds computed with and
     without the threaded images — the classification
     proxy (emissions move only if this diff moves).
   Usage:
     ta3c_diag.exe [--no-images] <binary> [sub]
     ta3c_diag.exe --tagdiff <corpus-dir> *)

open Bap.Std
open Probe_common

module Model = Hike__Hike_stack_model
module Vsa = Cbat_vsa
module Ws = Cbat_clp_set_composite

let word_of_i64 v = Word.of_int64 ~width:64 v

let i64_of_word w = Word.to_int64_exn w

(* The address words of a word set: exact enumeration up to the cap,
   otherwise the extrema. *)
let ws_words (ws : Ws.t) : string =
  if Ws.is_top ws then "TOP"
  else if Ws.is_bottom ws then "BOTTOM"
  else
    let i64 w =
      match Cbat_word.to_int64 w with Ok v -> Some v | Error _ -> None
    in
    let card =
      match i64 (Ws.cardinality ws) with Some c -> c | None -> Int64.max_int
    in
    let one w = match i64 w with Some v -> Printf.sprintf "%Lx" v | None -> "?" in
    if Int64.compare card 64L <= 0 then
      String.concat ","
        (Base.List.map (Ws.iter ws) ~f:one)
    else
      Printf.sprintf "hull[%s..%s]"
        (one (Option.value (Ws.min_elem ws) ~default:(Cbat_word.of_int ~width:64 0)))
        (one (Option.value (Ws.max_elem ws) ~default:(Cbat_word.of_int ~width:64 0)))

let reg name = Var.create ~is_virtual:false ~fresh:false name (Type.Imm 64)

(* Loads whose address the images cover — the image-backed loads. *)
let image_backed ~(images : Vsa.section_image list) (st : AI.t)
    (rhs : exp) : bool =
  match Model.addr_of_rhs rhs with
  | None -> false
  | Some (addr, _size) -> (
      match Vsa.Test_seam.denote_imm_exp addr st with
      | Error _ -> false
      | Ok ws ->
        if Ws.is_top ws || Ws.is_bottom ws then false
        else
          let i64 w =
            match Cbat_word.to_int64 w with Ok v -> Some v | Error _ -> None
          in
          let mn = Base.Option.bind (Ws.min_elem ws) ~f:i64 in
          let mx = Base.Option.bind (Ws.max_elem ws) ~f:i64 in
          match mn, mx with
          | Some lo, Some hi ->
            Base.List.exists images ~f:(fun im ->
                Stdlib.Int64.unsigned_compare lo im.Vsa.img_lo >= 0
                && Stdlib.Int64.unsigned_compare hi im.Vsa.img_hi <= 0)
          | _ -> false)

let report_sub ~(images : Vsa.section_image list) ~(sol : Vsa.vsa_sol)
    ~(prog : program term) ~(sp : var)
    ~(symtab : Symtab.t option) ~(target : Bap_core_theory.Theory.Target.t)
    (sub : sub term) : unit =
  let name = Sub.name sub in
  Printf.printf "sub %s\n" name;
  (* The sub's block addresses (the Lane B block_addrs source). *)
  let blk_addrs =
    Term.enum blk_t sub
    |> Seq.to_list
    |> Base.List.filter_map ~f:(fun b ->
        match Term.get_attr b address with
        | Some a -> Some (i64_of_word a, Tid.name (Term.tid b))
        | None -> None)
  in
  Base.List.iter blk_addrs ~f:(fun (a, n) ->
      Printf.printf "  block %s @ %Lx\n" n a);
  (* The dispatch registers' per-block entry and exit words. *)
  let r8 = reg "R8" and rax = reg "RAX" in
  Term.enum blk_t sub |> Seq.to_list
  |> Base.List.iter ~f:(fun b ->
      let st0 = Graphlib.Std.Solution.get sol (Term.tid b) in
      let (), st1 =
        Vsa.Test_seam.fold_block_states ~sol b ~init:() ~f:(fun _ _ _ () -> ())
      in
      let w st v = ws_words (AI.find_word 64 st v) in
      Printf.printf "  state %s in-R8=%s out-R8=%s in-RAX=%s out-RAX=%s\n"
        (Tid.name (Term.tid b))
        (w st0 r8) (w st1 r8) (w st0 rax) (w st1 rax));
  (* The image-backed loads: address and value denotations per def —
     the queries run image-armed (the rule's view), the states above
     stay the fixpoint's own (image-blind). *)
  Vsa.set_section_images images;
  Term.enum blk_t sub |> Seq.to_list
  |> Base.List.iter ~f:(fun b ->
      Vsa.Test_seam.fold_block_states ~sol b ~init:()
        ~f:(fun st_before _st d () ->
            let rhs = Def.rhs d in
            if image_backed ~images st_before rhs then
              Printf.printf "  imgload %s (def %s) addr=[%s] value=[%s] rhs=%s\n"
                (Var.name (Def.lhs d)) (Tid.name (Term.tid d))
                (match Model.addr_of_rhs rhs with
                 | Some (a, _) ->
                   ws_words
                     (match Vsa.Test_seam.denote_imm_exp a st_before with
                      | Ok w -> w
                      | Error _ -> Ws.top 64)
                 | None -> "?")
                (match Vsa.Test_seam.denote_imm_exp rhs st_before with
                 | Ok w -> ws_words w
                 | Error _ -> "type-error")
                (Exp.to_string rhs))
        |> ignore);
  (* The indirect transfers: the target denotation at the block's end. *)
  ignore
    (Hike.Vsa.fixpoint target sp ~prog ~images ~block_addrs:[] sub);
  Term.enum blk_t sub |> Seq.to_list
  |> Base.List.iter ~f:(fun b ->
      let (), st_end =
        Vsa.Test_seam.fold_block_states ~sol b ~init:() ~f:(fun _ _ _ () -> ())
      in
      Term.enum jmp_t b |> Seq.to_list
      |> Base.List.iter ~f:(fun j ->
          let target_exp =
            match Jmp.kind j with
            | Goto (Indirect e) -> Some e
            | Call c -> (
                match Call.target c with Indirect e -> Some e | _ -> None)
            | _ -> None
          in
          match target_exp with
          | None -> ()
          | Some e ->
            let words =
              match Vsa.Test_seam.denote_imm_exp e st_end with
              | Ok ws -> ws_words ws
              | Error _ -> "type-error"
            in
            Printf.printf "  indjmp %s (jmp %s) target=[%s]\n"
              (Tid.name (Term.tid b)) (Tid.name (Term.tid j)) words))

let rodata_image (proj : Project.t) : Vsa.section_image list =
  Project.memory proj |> Memmap.to_sequence
  |> Seq.find ~f:(fun (_, v) ->
         Base.Option.value_map (Value.get Image.section v) ~default:false
           ~f:(String.equal ".rodata"))
  |> Base.Option.map ~f:(fun (mem, _) ->
         let length = Memory.length mem in
         let min_addr = Memory.min_addr mem in
         let arr = Base.Array.init length ~f:(fun _ -> 0) in
         Memory.iteri ~word_size:`r8 mem
           ~f:(fun index v ->
               arr.(Word.to_int_exn (Word.( - ) index min_addr))
               <- Word.to_int_exn v);
         [ { Vsa.img_lo = Word.to_int64_exn min_addr;
             img_hi = Word.to_int64_exn (Memory.max_addr mem);
             img_bytes = arr } ])
  |> Base.Option.value ~default:[]

(* One binary's per-sub kinds and classes with and without images. *)
let tagdiff_binary ~(use_images : bool) (path : string) : unit =
  let proj = load_project path in
  let images = if use_images then rodata_image proj else [] in
  let target = Project.target proj in
  let sp = sp_of proj in
  let prog =
    Hike.Split_mem.normalize
      (Term.map sub_t (Project.program proj) ~f:(Hike.Jump.compile_sub target))
  in
  let n = ref 0 and diff = ref 0 in
  Term.enum sub_t prog
  |> Seq.iter ~f:(fun sub ->
      let with_img =
        let sol =
          let fixed =
            Hike.Vsa.fixpoint target sp ~prog ~images
              ~block_addrs:[] sub
          in
          ignore fixed;
          Cbat_vsa.static_graph_vsa ~abi:Hike_abi.x86_64_sysv
            ~resolved:Tid.Map.empty []
            (Program.create ~subs:[ sub ] ()) sub
            (Cbat_vsa.init_sol ~abi:Hike_abi.x86_64_sysv sub)
        in
        Cbat_vsa.set_section_images images;
        let ks = seam_kinds_of sol sub in
        Cbat_vsa.set_section_images [];
        ks
      in
      let without_img =
        let sol =
          Cbat_vsa.static_graph_vsa ~abi:Hike_abi.x86_64_sysv
            ~resolved:Tid.Map.empty []
            (Program.create ~subs:[ sub ] ()) sub
            (Cbat_vsa.init_sol ~abi:Hike_abi.x86_64_sysv sub)
        in
        seam_kinds_of sol sub
      in
      incr n;
      if not (Core.Map.equal Model.equal_vsa_kind with_img without_img) then (
        incr diff;
        Printf.printf "tagdiff DIFF sub %s in %s\n" (Sub.name sub) path));
  Printf.printf "tagdiff %s: %d subs, %d diff\n%!" (Filename.basename path) !n !diff


(* The production pass chain in-process (hike.ml's vsa + lift-sections
   + convlir); [use_images] arms the section-image rule.  Returns the
   emitted module's digest — the byte-identity A/B. *)
let emit_digest ?(dump : string option = None) ~(use_images : bool) (path : string) : string =
  let proj = load_project path in
  let images = if use_images then rodata_image proj else [] in
  let open Bap.Std in
  let target = Project.target proj in
  let abi = Hike_abi.of_target target in
  let sp = sp_of proj in
  let word = Bap_core_theory.Theory.Target.bits target / 8 in
  let symtab = Some (Project.symbols proj) in
  let prog =
    Hike.Split_mem.normalize
      (Term.map sub_t (Project.program proj) ~f:(Hike.Jump.compile_sub target))
  in
  let acc =
    Term.enum sub_t prog
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun acc sub ->
        let envs, sub' =
          Hike.Vsa.fixpoint target sp ~prog ~images
            ~block_addrs:[] sub
          |> Base.Option.value ~default:(Tid.Map.empty, sub)
        in
        Core.Map.set acc ~key:(Term.tid sub) ~data:(envs, sub'))
  in
  let all_envs =
    Core.Map.fold acc ~init:Tid.Map.empty
      ~f:(fun ~key:_ ~data:(envs, _) m ->
        Core.Map.fold envs ~init:m
          ~f:(fun ~key ~data m' -> Core.Map.set m' ~key ~data))
  in
  Hike.Kb.install_run ~block_envs:all_envs;
  let dyn_allocs =
    Term.enum sub_t prog
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m sub ->
           Core.Map.set m ~key:(Term.tid sub)
             ~data:(Hike.Sections.dynamic_alloc_tids_of ~sp ~denote:Hike.Vsa.denote_exp_at sub))
  in
  let prog =
    Term.map sub_t prog ~f:(fun sub ->
        let sub =
          match Core.Map.find acc (Term.tid sub) with
          | Some (_, sub') -> sub'
          | None -> sub
        in
        Model.stamp_dyn_allocs
          ~dynamic_alloc_tids:
            (Option.value (Core.Map.find dyn_allocs (Term.tid sub))
               ~default:Tid.Set.empty)
          sub)
  in
  let entry = Model.segment_base in
  let spans = Hike.attrib_spans ~word proj in
  let ctx =
    Hike.Sections.attribute ~word ~entry ~abi ~spans
      ~denote:Hike.Vsa.denote_exp_at prog
  in
  let prog = Term.map sub_t prog ~f:(Hike.Sections.stamp_tags ctx) in
  let prog =
    Hike.Sections.rewrite_program ~word ~entry ~abi ~sp ~symtab ~spans
      ~denote:Hike.Vsa.denote_exp_at ~ctx prog
  in
  let prog = Term.map sub_t prog ~f:(Hike.Dce.dce ~target) in
  let llvm_ctx = Llvm.create_context () in
  let llvm_module = Llvm.create_module llvm_ctx "Convlir" in
  Hike.Bil2llvm.emit_program llvm_ctx llvm_module
    ~target ~ptrsize:(Bap_core_theory.Theory.Target.bits target)
    ~symtab ~copy_relocs:(Hike.copy_reloc_slot_addrs proj)
    (Hike.section_spec_of ~word
       ~comps:(Hike.Sections.global_comps_of ~word ~spans ctx)
       ~whole:(Hike.Sections.whole_comps_of ~word ~spans ctx) proj)
    prog;
  let s = Llvm.string_of_llmodule llvm_module in
  Llvm.dispose_module llvm_module;
  Llvm.dispose_context llvm_ctx;
  (match dump with
   | Some out ->
     let o = Out_channel.open_text out in
     output_string o s;
     Out_channel.close o
   | None -> ());
  Digest.string s |> Digest.to_hex

(* The merge-gate proxy: the emitted IR digest with and without the
   image rule. *)
let emitdiff_binary ?(dump_prefix : string option = None) (path : string) : unit =
  let base =
    match dump_prefix with
    | Some p -> emit_digest ~dump:(Some (p ^ "-base.ll")) ~use_images:false path
    | None -> emit_digest ~use_images:false path
  in
  let armed =
    match dump_prefix with
    | Some p -> emit_digest ~dump:(Some (p ^ "-armed.ll")) ~use_images:true path
    | None -> emit_digest ~use_images:true path
  in
  Printf.printf "emitdiff %s: %s base=%s armed=%s\n" (Filename.basename path)
    (if String.equal base armed then "same" else "DIFF") base armed

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  let tagdiff = Base.List.mem args "--tagdiff" ~equal:String.equal in
  let emitdiff = Base.List.mem args "--emitdiff" ~equal:String.equal in
  let no_images = Base.List.mem args "--no-images" ~equal:String.equal in
  let pos =
    Base.List.filter args ~f:(fun a ->
        not
          (String.equal a "--tagdiff" || String.equal a "--no-images"
           || String.equal a "--emitdiff"))
  in
  init ();
  match pos with
  | [] -> usage Sys.argv.(0) "[--no-images] [--tagdiff] <binary|dir> [sub]"
  | path :: rest -> (
      if emitdiff && not (Sys.is_directory path) then
        emitdiff_binary
          ~dump_prefix:
            (if Base.List.length pos > 1 then Some (Base.List.nth_exn pos 1)
             else None)
          path
      else if emitdiff then
        let files =
          Sys.readdir path |> Array.to_list
          |> Base.List.map ~f:(Filename.concat path)
          |> Base.List.filter ~f:(fun f -> not (Sys.is_directory f))
          |> Base.List.sort ~compare:String.compare
        in
        Base.List.iter files ~f:(fun f ->
            try emitdiff_binary f
            with e ->
              Printf.printf "emitdiff CRASH %s: %s\n" f (describe_exn e))
      else if tagdiff then
        let files =
          Sys.readdir path |> Array.to_list
          |> Base.List.map ~f:(Filename.concat path)
          |> Base.List.filter ~f:(fun f -> not (Sys.is_directory f))
          |> Base.List.sort ~compare:String.compare
        in
        Base.List.iter files ~f:(fun f ->
            try tagdiff_binary ~use_images:(not no_images) f
            with e ->
              Printf.printf "tagdiff CRASH %s: %s\n" f (describe_exn e))
      else
        let filter = match rest with f :: _ -> f | [] -> "" in
        let proj = load_project path in
        let images = if no_images then [] else rodata_image proj in
        Base.List.iter images ~f:(fun im ->
            Printf.printf "image %Lx..%Lx (%d bytes)\n" im.Vsa.img_lo
              im.Vsa.img_hi (Array.length im.Vsa.img_bytes));
        let target = Project.target proj in
        let sp = sp_of proj in
        let prog =
          Hike.Split_mem.normalize
            (Term.map sub_t (Project.program proj) ~f:(Hike.Jump.compile_sub target))
        in
        let symtab = Some (Project.symbols proj) in
        let abi = Hike_abi.of_target target in
              Term.enum sub_t prog
        |> Seq.iter ~f:(fun sub ->
            if filter = "" || String.equal (Sub.name sub) filter then (
              let prog' = Program.create ~subs:[ sub ] () in
              let sol =
                Vsa.static_graph_vsa ~abi [] prog' sub
                  (Vsa.init_sol ~abi sub)
              in
              report_sub ~images ~sol ~prog ~sp ~symtab ~target sub)))
