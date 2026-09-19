(* Crash-class pins: the lifted-binary crash verdict's Tier 1-B (the
   PLT-stub self-call definition) and Tier 1-C (the rodata word-remap
   straddle).  Each pin builds the production input shape, emits it
   through [Hike.Bil2llvm.emit_program], and asserts on the textual
   IR.  [--emitdigest <dir>] runs the production pass chain per corpus
   binary and prints the emitted module's digest (the byte-identity
   A/B across an emitter change). *)

open Bap.Std
open Bap.Std.Bil.Types

let failures = ref 0
let checks = ref 0

let verbose = Array.exists (fun a -> a = "--verbose") Sys.argv

let check name cond =
  incr checks;
  if cond then Printf.printf "ok: %s\n%!" name
  else begin
    incr failures;
    Printf.printf "FAIL: %s\n%!" name
  end

let contains_substring s needle =
  let n = String.length needle and len = String.length s in
  let found = ref false in
  if n = 0 then true
  else begin
    for i = 0 to len - n do
      if (not !found) && String.sub s i n = needle then found := true
    done;
    !found
  end

(* Occurrences of [needle] in [s] (the through-lane pins count the
   inttoptr materializations). *)
let count_substring s needle =
  let n = String.length needle and len = String.length s in
  let c = ref 0 in
  if n > 0 then
    for i = 0 to len - n do
      if String.sub s i n = needle then incr c
    done;
  !c

(* The textual IR's define/declare lines naming [llvm_name]. *)
let defines_fn ir llvm_name =
  String.split_on_char '\n' ir
  |> List.exists (fun l ->
         String.length l >= 6 && String.sub l 0 6 = "define"
         && contains_substring l llvm_name)

let declares_fn ir llvm_name =
  String.split_on_char '\n' ir
  |> List.exists (fun l ->
         String.length l >= 7 && String.sub l 0 7 = "declare"
         && contains_substring l llvm_name)

(* BIR builders (the fixture dance: tids are captured from phase-1
   blocks before the jumps are wired). *)
let blk_of_defs (defs : def term list) : blk term =
  let b = Blk.Builder.create () in
  List.iter (Blk.Builder.add_def b) defs;
  Blk.Builder.result b

let with_jmps (b0 : blk term) (jmps : jmp term list) : blk term =
  let b = Blk.Builder.init ~copy_defs:true b0 in
  List.iter (Blk.Builder.add_jmp b) jmps;
  Blk.Builder.result b

let sub_of ?(tid = Tid.create ()) (name : string)
    (nodes : (def term list * (tid array -> jmp term list)) list) :
    sub term =
  let b0s = List.map (fun (defs, _) -> blk_of_defs defs) nodes in
  let tids = Array.of_list (List.map Term.tid b0s) in
  let blks =
    List.map2
      (fun b0 (_, edges) -> with_jmps b0 (edges tids))
      b0s nodes
  in
  let sb = Sub.Builder.create ~tid ~name () in
  List.iter (Sub.Builder.add_blk sb) blks;
  Sub.Builder.result sb

let ret_jmp () : jmp term = Jmp.create (Ret (Direct (Tid.create ())))

let call_jmp ~(callee : tid) ~(return : tid) : jmp term =
  Jmp.create (Call (Call.create ~return:(Direct return) ~target:(Direct callee) ()))

(* The lifted PLT stub after the producer's resolution: no defs, no
   register state, one call whose target is the stub's own tid. *)
let mk_self_call_stub (name : string) : sub term =
  let tid = Tid.for_name name in
  sub_of ~tid name
    [ ([], fun t -> [ call_jmp ~callee:tid ~return:t.(1) ]);
      ([], fun _ -> [ ret_jmp () ]) ]

(* The resolved call site: one arg def, a direct call to [callee]. *)
let mk_caller (name : string) (callee : tid) : sub term =
  let rdi = Var.create ~is_virtual:false ~fresh:false "RDI" (Type.Imm 64) in
  let def =
    Def.create rdi (Bil.Int (Word.of_int64 ~width:64 48L))
  in
  sub_of name
    [ ([ def ], fun t -> [ call_jmp ~callee ~return:t.(1) ]);
      ([], fun _ -> [ ret_jmp () ]) ]

let emit_ir ?(copy_relocs : int64 list = []) (subs : sub term list)
    ~(sections : Hike.Bil2llvm.section_spec) :
    string =
  let llvm_ctx = Llvm.create_context () in
  let llvm_module = Llvm.create_module llvm_ctx "CrashPins" in
  let prog = Program.create ~subs () in
  Hike.Bil2llvm.emit_program llvm_ctx llvm_module
    ~target:Bap_core_theory.Theory.Target.unknown ~ptrsize:64 ~symtab:None
    ~copy_relocs sections prog;
  let s = Llvm.string_of_llmodule llvm_module in
  Llvm.dispose_module llvm_module;
  Llvm.dispose_context llvm_ctx;
  s

let empty_spec : Hike.Bil2llvm.section_spec =
  { Hike.Bil2llvm.spec_comps = [];
    Hike.Bil2llvm.spec_whole = [];
    spec_word = 8;
    spec_sections = [] }

(* Tier 1-B: the stub's definition must not be a same-named self-call;
   the name resolves to the declaration the call sites bind. *)
let pin_plt_self_call () =
  let stub = mk_self_call_stub "malloc" in
  let caller = mk_caller "malloc_caller" (Term.tid stub) in
  let ir = emit_ir [ caller; stub ] ~sections:empty_spec in
  if verbose then print_string ir;
  check
    "TIER1B: the external's stub renders no same-named self-call definition"
    (not (defines_fn ir "@malloc("));
  check "TIER1B: the stub's name carries a declaration"
    (declares_fn ir "@malloc(");
  check "TIER1B: the call site references the declared external"
    (contains_substring ir "call void @malloc(")

(* Tier 1-C: a .rodata word whose bytes are covered by a string run
   renders its raw bytes — the value is text, never a target address.
   The image: zeros, then "cat\0" at byte 7 (the word at byte 8 holds
   the string's tail "at\0" + padding = 0x7461, a plausible address),
   then a clean word at byte 16 holding the same value with no string
   run crossing its start — the clean word still remaps. *)
let straddle_image : int array =
  let n = Array.make 24 0 in
  n.(7) <- 0x63;
  n.(8) <- 0x61;
  n.(9) <- 0x74;
  n.(16) <- 0x61;
  n.(17) <- 0x74;
  n

(* A PROGBITS section at 0x7000 spanning past 0x7461, so the word
   value 0x7461 resolves through the address map's section arm. *)
let data_image : int array = Array.make 2048 0

let sec_bytes t lo img =
  Hike.Bil2llvm.Sec_bytes
    { si_type = t;
      si_lo = lo;
      si_hi = Int64.add lo (Int64.of_int (Array.length img - 1));
      si_words = (Array.length img + 7) / 8;
      si_const = t = Hike.Bil2llvm.RODATA;
      si_image = img }

let straddle_spec : Hike.Bil2llvm.section_spec =
  { Hike.Bil2llvm.spec_comps = [];
    Hike.Bil2llvm.spec_whole = [];
    spec_word = 8;
    spec_sections =
      [ Some (sec_bytes Hike.Bil2llvm.DATA 0x7000L data_image);
        Some (sec_bytes Hike.Bil2llvm.RODATA 0xa000L straddle_image) ] }

let pin_rodata_straddle () =
  let ir = emit_ir [] ~sections:straddle_spec in
  if verbose then print_string ir;
  (* The straddled word keeps its raw bytes (0x7461 = 29793). *)
  check "TIER1C: the string-covered word renders raw bytes"
    (contains_substring ir "i64 29793");
  (* The clean word still remaps through the address map
     (0x7461 - 0x7000 = 0x461). *)
  check "TIER1C: the clean word remaps through the address map"
    (contains_substring ir "@data, i64 1121")

(* The pointer-byte shape: a word whose start byte is printable but
   whose preceding byte is a NON-printable, non-NUL byte (pointer
   bytes) — no printable run crosses the start, so the word is a VALUE
   and remaps; covering it would corrupt the relocated address (the
   program-name class). *)
let nonprintable_image : int array =
  let n = Array.make 24 0 in
  n.(7) <- 0xff;
  n.(8) <- 0x61;
  n.(9) <- 0x74;
  n

let nonprintable_spec : Hike.Bil2llvm.section_spec =
  { Hike.Bil2llvm.spec_comps = [];
    Hike.Bil2llvm.spec_whole = [];
    spec_word = 8;
    spec_sections =
      [ Some (sec_bytes Hike.Bil2llvm.DATA 0x7000L data_image);
        Some (sec_bytes Hike.Bil2llvm.RODATA 0xa000L nonprintable_image) ] }

let pin_rodata_nonprintable () =
  let ir = emit_ir [] ~sections:nonprintable_spec in
  if verbose then print_string ir;
  (* The word at byte 8 (0x7461) follows the 0xff byte: it REMAPS
     (0x7461 - 0x7000 = 0x461 into @data) and never renders raw. *)
  check
    "TIER1C: a non-printable prev byte (pointer bytes) does not cover the word — it remaps"
    (contains_substring ir "@data, i64 1121"
     && not (contains_substring ir "i64 29793"))

(* The copy-reloc through lane: a slot's content is a relocated
   pointer, and EVERY access at the slot's address goes through it —
   the load AND the store (the seq class: a store-only or cross-sub
   slot never loses the lane). *)
let w64 v = Word.of_int64 ~width:64 v

let memv name =
  Var.create ~is_virtual:false ~fresh:false name (Type.Mem (`r64, `r64))

let slot_spec : Hike.Bil2llvm.section_spec =
  { Hike.Bil2llvm.spec_comps = [];
    Hike.Bil2llvm.spec_whole = [];
    spec_word = 8;
    spec_sections =
      [ Some
          (Hike.Bil2llvm.Sec_bss
             { si_lo = 0x1000L;
               si_hi = 0x101FL;
               si_words = 4;
               si_copy_relocs = [ (0x10, "ext_var") ] });
        Some (sec_bytes Hike.Bil2llvm.DATA 0x7000L data_image) ] }

let pin_copy_reloc_lane () =
  let m = memv "ptr_m" in
  let t = Var.create ~is_virtual:false ~fresh:false "ptr_t" (Type.Imm 64) in
  (* One sub STORES at the slot; a DIFFERENT sub loads it — the
     unmirrored, cross-sub shape. *)
  let store_sub =
    sub_of "ptr_store"
      [ [ Def.create m
            (Bil.Store (Bil.Var m, Bil.Int (w64 0x1010L),
                        Bil.Int (w64 0x1234L), LittleEndian, `r64)) ],
        fun _ -> [ ret_jmp () ] ]
  in
  let load_sub =
    sub_of "ptr_load"
      [ [ Def.create t
            (Bil.Load (Bil.Var m, Bil.Int (w64 0x1010L), LittleEndian, `r64)) ],
        fun _ -> [ ret_jmp () ] ]
  in
  let ir =
    emit_ir ~copy_relocs:[ 0x1010L ] [ store_sub; load_sub ]
      ~sections:slot_spec
  in
  if verbose then print_string ir;
  (* The @bss image words keep their ptrtoint(extern) initializers. *)
  check "PTR-LANE: the slot's initializer is the extern's address"
    (contains_substring ir "ptrtoint (ptr @ext_var to i64)");
  (* The slot address GEPs into @bss (byte 16 = the slot's word; the
     const GEP folds to a constant expression). *)
  check "PTR-LANE: the slot address resolves into @bss"
    (contains_substring ir "getelementptr (i8, ptr @bss, i64 16)");
  (* BOTH the store and the load materialize the slot's pointer (two
     load-then-inttoptr chains), and the stored constant (0x1234 =
     4660) stores THROUGH the materialized pointer — never into @bss
     directly. *)
  check "PTR-LANE: the store at a slot goes through the relocated pointer"
    (count_substring ir " = inttoptr i64" = 2);
  check "PTR-LANE: the store's value lane is present (4660)"
    (contains_substring ir "store i64 4660, ptr")

(* The production chain drivers: [--emitdigest <dir>] prints each
   binary's emission digest (the byte-identity A/B); [--dumpir <binary>
   <out.ll>] writes one emitted module (the merge-gate artifact). *)
let emit_digest ?(dump : string option) (path : string) : string =
  let proj = Probe_common.load_project path in
  let target = Project.target proj in
  let abi = Hike_abi.of_target target in
  let sp = Probe_common.sp_of proj in
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
          Hike.Vsa.fixpoint target sp ~prog
            ~images:[] sub
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
        Hike.Stack_model.stamp_dyn_allocs
          ~dynamic_alloc_tids:
            (Option.value (Core.Map.find dyn_allocs (Term.tid sub))
               ~default:Tid.Set.empty)
          sub)
  in
  (* The canary strip, as between vsa and attrib in the chain. *)
  let prog =
    let names =
      Term.enum sub_t prog
      |> Seq.fold ~init:Tid.Map.empty ~f:(fun m s ->
          Core.Map.set m ~key:(Term.tid s) ~data:(Sub.name s))
    in
    Term.map sub_t prog
      ~f:(Hike.Strip_canaries.strip_sub ~abi ~names)
  in
  (* The attribution: the trees and slim tags, then the rewrite. *)
  let entry = Hike.Stack_model.segment_base in
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
    ~target ~ptrsize:word ~symtab ~copy_relocs:(Hike.copy_reloc_slot_addrs proj)
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

let run_digest_mode (dir : string) : int =
  Probe_common.init ();
  let files =
    if Sys.is_directory dir then
      Sys.readdir dir |> Array.to_list
      |> Base.List.map ~f:(Filename.concat dir)
      |> Base.List.filter ~f:(fun f -> not (Sys.is_directory f))
      |> Base.List.sort ~compare:String.compare
    else [ dir ]
  in
  List.iter
    (fun f ->
      match emit_digest f with
      | d -> Printf.printf "emitdigest %s %s\n%!" (Filename.basename f) d
      | exception e ->
        Printf.printf "emitdigest %s CRASH: %s\n%!" (Filename.basename f)
          (Printexc.to_string e))
    files;
  0

let run_dumpir_mode (path : string) (out : string) : int =
  Probe_common.init ();
  ignore (emit_digest ~dump:out path);
  0

let () =
  match Array.to_list Sys.argv with
  | _ :: "--emitdigest" :: dir :: _ -> exit (run_digest_mode dir)
  | _ :: "--dumpir" :: bin :: out :: _ -> exit (run_dumpir_mode bin out)
  | _ ->
    pin_plt_self_call ();
    pin_rodata_straddle ();
    pin_rodata_nonprintable ();
    pin_copy_reloc_lane ();
    Printf.printf "%d checks, %d failures\n" !checks !failures;
    if !failures = 0 then print_endline "ALL CRASH PINS PASSED";
    exit (if !failures = 0 then 0 else 1)
