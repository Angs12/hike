open Bap.Std
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures
module Synth = Hike.Synth
module Rip = Hike.Rip
module KB = Bap_knowledge.Knowledge

let int a = Bil.Int (Word.of_int64 ~width:64 a)
let tagged d =
  Def.with_value d (KB.Value.put rip_relative_addr (Def.value d) true)
let region = { Hike_synth_addr.id = 7; lo = 0x4008L; hi = 0x401fL }
let is_address a = Hike_synth_addr.contains region a || Int64.equal a 0x2000L
let resolve ?slots program =
  Rip.prepare_program ~addr_bits:64 ~is_address program
  |> Rip.resolve_program ?slots ~addr_bits:64 ~regions:[region]
let defs program = Term.enum sub_t program
    |> Seq.concat_map ~f:(Term.enum blk_t)
    |> Seq.concat_map ~f:(Term.enum def_t) |> Seq.to_list

let tests = [
  pin "SYN-01" "all synthetic families construct and classify through one vocabulary"
    (fun () ->
       let env = Base.List.hd_exn Hike.Abi.x86_64_sysv.env_regs in
       let families = [
         Synth.module_addr ~addr_bits:64 0x4010L;
         Synth.thread_addr ~addr_bits:64 (-8L);
         Synth.base ~addr_bits:64 (Synth.Slot 2);
         Synth.base ~addr_bits:64 (Synth.Argument 3);
         Synth.base ~addr_bits:64 Synth.Window;
         Synth.bytes ~addr_bits:64 Synth.Window;
         Synth.base ~addr_bits:64 (Synth.Stack 4);
         Synth.bytes ~addr_bits:64 (Synth.Stack 4);
         Synth.base ~addr_bits:64 (Synth.Global 7);
         Synth.bytes ~addr_bits:64 (Synth.Global 7);
         Synth.environment env;
         Synth.fp_lane ~addr_bits:64 Synth.Input 0;
         Synth.fp_lane ~addr_bits:64 Synth.Output 1;
         Synth.accumulator ~addr_bits:64;
         Synth.let_var ~addr_bits:64 9 (Type.Imm 32);
         Synth.fresh ~bits:64 Synth.Comparison;
         Synth.fresh ~bits:64 Synth.Load;
         Synth.fresh ~bits:64 Synth.Refinement;
       ] in
       let program = Program.create ~subs:[straight_sub "synth_table"
           (Base.List.map families ~f:(fun v -> Def.create v (Bil.Var v)))] () in
       let table = Synth.table_of_program program in
       Base.List.iter families ~f:(fun v ->
           check "stable non-virtual identity" (not (Var.is_virtual v));
           check "one classification covers every family"
             (Option.is_some (Synth.classify table v));
           check "every synthetic variable is recorded" (Synth.mem table v));
       check "the address and storage families are bases"
         (Synth.is_base_var table (Synth.module_addr ~addr_bits:64 0x4010L)
          && Synth.is_base_var table (Synth.base ~addr_bits:64 (Synth.Slot 2))
          && Synth.is_base_var table (Synth.base ~addr_bits:64 (Synth.Argument 3)));
       check "the bytes families are memory"
         (Synth.is_memory_var table (Synth.bytes ~addr_bits:64 (Synth.Global 7))
          && not (Synth.is_memory_var table (Synth.base ~addr_bits:64 (Synth.Global 7))));
       check "the base/memory pairing is one operation"
         (Var.equal
            (Option.get
               (Synth.memory_var ~addr_bits:64
                  (Synth.base ~addr_bits:64 (Synth.Global 7))))
            (Synth.bytes ~addr_bits:64 (Synth.Global 7))
          && Var.equal
               (Option.get
                  (Synth.base_var ~addr_bits:64
                     (Synth.bytes ~addr_bits:64 (Synth.Stack 4))))
               (Synth.base ~addr_bits:64 (Synth.Stack 4)));
       let pointer = Synth.base ~addr_bits:32 (Synth.Stack 4) in
       check "constructor uses the target address width"
         (Type.equal (Var.typ pointer) (Type.Mem (`r32, `r8)));
       let a = Synth.fresh ~bits:64 Synth.Load in
       let b = Synth.fresh ~bits:64 Synth.Load in
       check "fresh synthetic temporaries have distinct identities"
         (not (Var.equal a b) && Synth.is_temporary a && Synth.is_temporary b));
  pin "RIP-01" "values, loads and stores resolve to stable variables and byte indices"
    (fun () ->
       let mem = memv "rip_mem" in
       let value = tagged (Def.create (v64 "rip_value") (int 0x4010L))
           |> Cbat_vsa.set_env_tag AI.top
           |> Cbat_vsa.Def_origin.with_origin (Hike_origin.Rip Hike_section.Data) in
       let load = tagged (Def.create (v64 "rip_load")
           (Bil.Load (Bil.Var mem, int 0x4010L, LittleEndian, `r32))) in
       let store = tagged (Def.create mem
           (Bil.Store (Bil.Var mem, int 0x4014L, int 9L, LittleEndian, `r64))) in
       let raw = tagged (Def.create (v64 "rip_raw") (int 42L)) in
       let control = Def.create (v64 "rip_control") (int 0x4010L) in
       let program = resolve (Program.create
           ~subs:[straight_sub "rip_shapes" [value; load; store; raw; control]] ()) in
       let find d = Base.List.find_exn (defs program)
           ~f:(fun x -> Tid.equal (Term.tid x) (Term.tid d)) in
       check "analysis facts survive resolution"
         (Option.is_some (Cbat_vsa.env_tag (find value))
          && KB.Value.get rip_relative_addr (Def.value (find value))
          && Base.Option.equal Hike_origin.equal
               (Cbat_vsa.Def_origin.def_origin (find value)) (Some (Hike_origin.Rip Hike_section.Data)));
       let mv = Hike.Stack_model.sec_comp_mem ~addr_bits:64 7 in
       check "value is a synthetic address" (match Def.rhs (find value) with
           | Bil.Var v -> Var.equal v (Synth.module_addr ~addr_bits:64 0x4010L)
                          && not (Var.is_virtual v)
           | _ -> false);
       check "load uses component and byte index"
         (Exp.equal (Def.rhs (find load))
            (Bil.Load (Bil.Var mv, int 8L, LittleEndian, `r32)));
       check "store uses the same storage and preserves its data"
         (Var.equal (Def.lhs (find store)) mv
          && Exp.equal (Def.rhs (find store))
               (Bil.Store (Bil.Var mv, int 12L, int 9L, LittleEndian, `r64)));
       check "unclassified and untagged bits stay exact"
         (Exp.equal (Def.rhs (find raw)) (int 42L)
          && Exp.equal (Def.rhs (find control)) (int 0x4010L));
       check "resolution is idempotent" (Program.equal program (resolve program)));
  pin "RIP-02" "nested and guard variables share singleton denotation and table lookup"
    (fun () ->
       let address = Synth.module_addr ~addr_bits:64 0x2000L in
       let sub = straight_sub "rip_table"
           [Def.create (v64 "rip_sum") (Bil.BinOp (Bil.PLUS, Bil.Var address, int 3L))] in
       let program = Program.create ~subs:[sub] () in
       let table = Synth.table_of_program program in
       check "nested synthetic variable is in the table" (Synth.mem table address);
       check "VSA sees its module address"
         (match Vsa.Test_seam.denote_imm_exp (Bil.Var address) AI.top with
          | Ok ws -> Ws.equal ws (Ws.singleton (Cbat_word.of_word (Word.of_int64 ~width:64 0x2000L)))
          | Error _ -> false);
       check "synthetic constants are not signature inputs"
         (not (Base.List.exists (Hike.Split_blocks.free_regs ~abi:Hike.Abi.x86_64_sysv sub)
                  ~f:(Var.equal address)));
       check "resolved linker slots remain recognizable as transfer targets"
         (Base.Option.equal Int64.equal
            (Hike_transfer.slot_of_target ~synth:table
               (Bil.Load (Bil.Var (memv "rip_linker"), Bil.Var address, LittleEndian, `r64)))
            (Some 0x2000L)));
  pin "RIP-03" "resolved section values and accesses emit through the owning global"
    (fun () ->
       let meta = { B2l.sm_type = Hike.Stack_model.Data; sm_access = Hike_section.Writable;
                    sm_lo = 0x4000L; sm_hi = 0x401fL; sm_words = 4;
                    sm_image = Some (Bytes.make 32 '\000'); sm_copy_relocs = [] } in
       let comp = { Hike.Stack_model.comp_id = 7; sec_lo = 0x4000L;
                    sec_hi = 0x401fL; lo_w = 1; hi_w = 3; typed_w = 8 } in
       let spec = { empty_spec with spec_sections = [Some meta];
                                   spec_comps = [comp] } in
       let sub = straight_sub "rip_emit"
           [tagged (Def.create (int_ret 0) (int 0x4010L));
            tagged (Def.create (int_ret 1)
                (Bil.Load (Bil.Var (memv "rip_emit_mem"), int 0x4010L, LittleEndian, `r64)));
            tagged (Def.create (memv "rip_emit_mem")
                (Bil.Store (Bil.Var (memv "rip_emit_mem"), int 0x4018L,
                            Bil.Var (int_ret 0), LittleEndian, `r64)))] in
       let program = resolve (Program.create ~subs:[sub] ()) in
       let ir = emit_ir_spec spec (Term.enum sub_t program |> Seq.to_list) in
       check "value renders the owning global and its index"
         (contains_substring ir "ptrtoint (ptr getelementptr inbounds (i8, ptr @sec_comp_7, i64 8) to i64)");
       check "load renders the same component index"
         (contains_substring ir "load i64, ptr getelementptr (i8, ptr @sec_comp_7, i64 8)");
       check "synthetic address does not become an argument or undef"
         (not (contains_substring ir "hike_synth_")));
  pin "RIP-04" "function pointer guards and data words render the same public face"
    (fun () ->
       let callee = fst (sub_of ~tid:(Tid.for_name "rip_callee") "rip_callee"
                             [[], [(0, mk_ret)]]) in
       let callee = Term.map blk_t callee ~f:(fun blk ->
           Term.set_attr blk address (Word.of_int64 ~width:64 0x2000L)) in
       let address = Synth.module_addr ~addr_bits:64 0x2000L in
       let mem = Synth.bytes ~addr_bits:64 (Synth.Global 0) in
       let body, _ = sub_of "rip_face"
           [ [Def.create (int_ret 0)
                 (Bil.Load (Bil.Var mem, int 0L, LittleEndian, `r64))],
              [(1, fun t -> mk_jmp_to t
                     (Bil.BinOp (Bil.EQ, Bil.Var (int_ret 0), Bil.Var address)));
               (2, mk_goto)];
              [], [(0, mk_ret)]; [], [(0, mk_ret)] ] in
       let meta = { B2l.sm_type = Hike.Stack_model.Data; sm_access = Hike_section.Writable;
                    sm_lo = 0x4008L; sm_hi = 0x400fL; sm_words = 1;
                    sm_image = Some (Bytes.make 8 '\000'); sm_copy_relocs = [] } in
       let spec = { empty_spec with spec_sections = [Some meta];
                                   spec_whole = [(0, 0x4008L, 0x400fL)];
                                   spec_relative = [(0x4008L, 0x2000L)] } in
       let ir = emit_ir_spec spec [body; callee] in
       let ptr = "ptrtoint (ptr @rip_callee_hike_thunk to i64)" in
       check "guard uses the function's public face"
         (contains_substring ir ("icmp eq i64 %" ) && contains_substring ir ptr);
       check "initializer and guard use the same face"
         (Base.List.length (Base.String.substr_index_all ir ~pattern:ptr
                               ~may_overlap:false) >= 2));
  pin "RIP-05" "indexed accesses subtract their owning runtime base exactly once"
    (fun () ->
       let mem = Synth.bytes ~addr_bits:64 (Synth.Global 7) in
       let base = Synth.base ~addr_bits:64 (Synth.Global 7) in
       let addr = Bil.BinOp (Bil.PLUS,
           Bil.Var (Synth.module_addr ~addr_bits:64 0x4010L),
           Bil.Var (int_param 0)) in
       let program = resolve (Program.create ~subs:[straight_sub "rip_index"
           [Def.create (int_ret 0)
              (Bil.Load (Bil.Var mem, addr, LittleEndian, `r64))]] ()) in
       check "the component has a runtime-relative byte index"
         (Exp.equal (Def.rhs (Base.List.hd_exn (defs program)))
             (Bil.Load (Bil.Var mem,
                        Bil.BinOp (Bil.MINUS, addr, Bil.Var base), LittleEndian, `r64)));
       check "indexed resolution is idempotent" (Program.equal program (resolve program)));
  pin "RIP-06" "a marked RMW addresses the same component global and byte index as ordinary accesses; an unmarked RMW stays plain"
    (fun () ->
       let mem = Synth.bytes ~addr_bits:64 (Synth.Global 7) in
       let loaded = int_ret 1 in
       let meta = { B2l.sm_type = Hike.Stack_model.Data; sm_access = Hike_section.Writable;
                    sm_lo = 0x4008L; sm_hi = 0x401fL; sm_words = 3;
                    sm_image = Some (Bytes.make 24 '\000'); sm_copy_relocs = [] } in
       let spec = { empty_spec with spec_sections = [Some meta];
                                   spec_whole = [(7, 0x4008L, 0x401fL)] } in
       let resolve subs =
         let prog = Program.create ~subs:subs ()
             |> Hike.Atomic.normalize ~addr_bits:64 |> resolve in
         Term.enum sub_t prog |> Seq.to_list in
       let marked, _ = sub_of "rip_atomic"
           [ [Def.create (Hike.Atomic.lane "address" 64) (int 0x4010L);
              Def.create (Hike.Atomic.lane "input0" 64) (int 5L)],
             [(1,fun cont -> Jmp.create (Call (Call.create ~return:(Direct cont)
                 ~target:(Direct (Tid.for_name "intrinsic:x86:atomic_add_64")) ())))];
             [], [(0,mk_ret)] ] in
       (* The unmarked twin: the same load/store pair, no markers. *)
       let unmarked, _ = sub_of "rip_plain"
           [ [Def.create loaded (Bil.Int (Cbat_word.to_word (w64 5)));
              Def.create mem (Bil.Store (Bil.Var mem, int 8L,
                  Bil.BinOp (Bil.PLUS,
                      Bil.Load (Bil.Var mem, int 8L, LittleEndian, `r64),
                      Bil.Var loaded), LittleEndian, `r64))],
             [(0, mk_ret)] ] in
       let ir_marked = emit_ir_spec spec (resolve [marked]) in
       let ir_plain = emit_ir_spec spec (resolve [unmarked]) in
       check "an explicit atomic addresses the owning global at its byte index"
         (contains_substring ir_marked "atomicrmw add ptr"
          && contains_substring ir_marked "ptr @data, i64 8)"
         && contains_substring ir_marked "seq_cst");
       check "the intrinsic renders no external call"
         (not (contains_substring ir_marked "intrinsic:x86"));
       check "an unmarked RMW stays plain"
         (not (contains_substring ir_plain "atomicrmw")));
  pin "RIP-07" "resolved storage accesses recover their module address generally"
    (fun () ->
       let origins =
         [ (Synth.bytes ~addr_bits:64 (Synth.Global 7), 0x4008L);
           (Synth.bytes ~addr_bits:64 (Synth.Stack 3), 0x1000L);
           (Synth.bytes ~addr_bits:64 Synth.Window, 0x2000L);
           (Synth.base ~addr_bits:64 (Synth.Slot 1), 0x3000L);
           (Synth.base ~addr_bits:64 (Synth.Argument 4), 0x5000L) ]
       in
       let origin v = Base.List.Assoc.find origins v ~equal:Var.equal in
       Base.List.iter origins ~f:(fun (mem, lo) ->
           check "base plus index is the module address"
             (Base.Option.equal Int64.equal
                (Hike_synth_addr.access_address ~origin Synth.empty mem (int 8L))
                (Some (Int64.add lo 8L)));
           check "the resolved slot is recognized"
             (Base.Option.equal Int64.equal
                (Hike_transfer.slot_of_target ~synth:Synth.empty ~origin
                   (Bil.Load (Bil.Var mem, int 8L, LittleEndian, `r64)))
                (Some (Int64.add lo 8L))));
       check "a synthetic storage without an origin has no module address"
         (Base.Option.is_none
            (Hike_synth_addr.access_address Synth.empty
               (Synth.bytes ~addr_bits:64 (Synth.Global 7)) (int 8L)));
       check "a plain memory keeps its index as the address"
         (Base.Option.equal Int64.equal
            (Hike_synth_addr.access_address ~origin Synth.empty (memv "plain") (int 8L))
            (Some 8L)));
]

let () = run "rip" tests
