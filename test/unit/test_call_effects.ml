(* Call-effects pass pins. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

let ce_abi = Hike_abi.x86_64_sysv

module Ce = Vsa.Call_effects

let ce_idx = { Mem.addr_width = 64; Mem.addressable_width = 8 }

let ce_mkey lo =
  match Mem.Key.of_wordset (Ws.stack_word_i64 lo) with
  | [ k ] -> k
  | _ -> failwith "key"

let ce_reads m lo post =
  Mem.Val.data (Mem.find (64, LittleEndian) (AI.find_memory ce_idx post m) (ce_mkey lo))

(* The two leading non-return caller-saved GPRs. *)
let ids vs = Cbat_var_id.intern_set vs
let ids1 v = ids (Var.Set.singleton v)

let ce_gprs abi =
  let not_return v = not (Base.List.exists abi.Hike_abi.return_regs ~f:(Var.same v)) in
  match Base.List.filter abi.Hike_abi.caller_saved_gprs ~f:not_return with
  | g1 :: g2 :: _ -> (g1, g2)
  | _ -> assert false

(* The pre-call env: a frame with cells at [0x2000; 0x3000] above the
   call-time RSP {0x1000}, one below it at [0x500], and a memory var. *)
let ce_raw_env ?(lanes = []) () =
  let mem =
    Mem.add
      (Mem.add
         (Mem.add (Mem.top ce_idx)
            ~key:(ce_mkey 0x2000L)
            ~data:(Mem.Val.create (Ws.singleton (w64 42)) LittleEndian))
         ~key:(ce_mkey 0x3000L)
         ~data:(Mem.Val.create (Ws.singleton (w64 7)) LittleEndian))
      ~key:(ce_mkey 0x500L)
      ~data:(Mem.Val.create (Ws.singleton (w64 1)) LittleEndian)
  in
  let m = memv "ce_m" in
  let env =
    AI.add_memory AI.top ~key:m ~data:mem
    |> AI.add_word ~key:ce_abi.Hike_abi.sp
       ~data:(Ws.stack_word_i64 0x1000L)
  in
  let env =
    Base.List.fold lanes ~init:env ~f:(fun acc v ->
        AI.add_word acc ~key:v ~data:(Ws.stack_word_i64 0x2000L))
  in
  (env, m)

(* The VSA C1 call shape: unknown callee, no escapes, no push. *)
let ce_call env preserved =
  Ce.transfer ~abi:ce_abi ~preserved
    ~site:{ Ce.summary = None; read_lanes = [] } env

let ce_call_reads ?(stack_args = []) env read_lanes =
  Ce.transfer ~stack_args ~abi:ce_abi ~preserved:Core.Int.Set.empty
    ~site:{ Ce.summary = None; read_lanes } env

let ce_xy_env () =
  let x = v64 "c1_x" in
  let y = v64 "c1_y" in
  let env =
    AI.add_word
      (AI.add_word AI.top ~key:x ~data:(Ws.singleton (w64 5)))
      ~key:y
      ~data:(Ws.singleton (w64 7))
  in
  (x, y, env)


module Sg = Hike_signatures

let sg_ptr ?(captured = false) access =
  { Sg.ty = Hike_sysv.Scalar Hike_sysv.Pointer; access; captured }

let sg_record ?(memory = Sg.Any) ?returned ?(variadic = false) params =
  { Sg.library = "libc.so.6"; version = "GLIBC_2.2.5"; symbol = "f"; return = Some (Hike_sysv.Scalar Hike_sysv.Long); returned; params; variadic;
    memory; noreturn = false }

let sg_call ?signature ?result env read_lanes =
  Ce.transfer ?signature ?result ~abi:ce_abi ~preserved:Core.Int.Set.empty
    ~site:{ Ce.summary = None; read_lanes } env

let sg_global_key = List.hd (Mem.Key.of_wordset (Ws.singleton (w64 0x7000)))

(* The frame of [ce_raw_env] with a global cell, and the first argument
   lane pointing at [lane]. *)
let sg_env lane =
  let rdi = Base.List.nth_exn ce_abi.Hike_abi.int_param_regs 0 in
  let e, m = ce_raw_env () in
  let mem =
    Mem.add (AI.find_memory ce_idx e m) ~key:sg_global_key
      ~data:(Mem.Val.create (Ws.singleton (w64 9)) LittleEndian) in
  let e = AI.add_memory e ~key:m ~data:mem in
  (AI.add_word e ~key:rdi ~data:(Ws.stack_word_i64 lane), m, rdi)

let sg_global m post =
  Mem.Val.data (Mem.find (64, LittleEndian) (AI.find_memory ce_idx post m) sg_global_key)

let tests : unit Alcotest.test list =
  [
    (* The kill summary keeps non-written caller-saved GPRs and the base. *)
    pin "CE-01" "the kill summary keeps non-written caller-saved GPRs and the base"
      (fun () ->
        let g1, g2 = ce_gprs ce_abi in
        let x = v64 "ce_x" in
        let summary = Cbat_var_id.intern_set (Core.Set.singleton (module Var) g1) in
        let words_env =
          AI.add_word
            (AI.add_word AI.top ~key:g1 ~data:(Ws.singleton (w64 1)))
            ~key:g2
            ~data:(Ws.singleton (w64 2))
        in
        let kept =
          Ce.transfer ~abi:ce_abi ~preserved:(ids1 x)
            ~site:{ Ce.summary = Some summary; read_lanes = [] }
            (AI.add_word words_env ~key:x ~data:(Ws.singleton (w64 5)))
        in
        check "CE-01"
          (Ws.equal (AI.find_word 64 kept x) (Ws.singleton (w64 5))
          && Ws.equal (AI.find_word 64 kept g2) (Ws.singleton (w64 2))
          && Ws.is_top (AI.find_word 64 kept g1)));

    (* No summary (unknown or kill-all) keeps only the base set. *)
    pin "CE-02" "no summary (unknown or kill-all) keeps only the base set"
      (fun () ->
        let g1, g2 = ce_gprs ce_abi in
        let x = v64 "ce_x" in
        let words_env =
          AI.add_word
            (AI.add_word AI.top ~key:g1 ~data:(Ws.singleton (w64 1)))
            ~key:g2
            ~data:(Ws.singleton (w64 2))
        in
        let killed =
          Ce.transfer ~abi:ce_abi ~preserved:(ids1 x)
            ~site:{ Ce.summary = None; read_lanes = [] }
            (AI.add_word words_env ~key:x ~data:(Ws.singleton (w64 5)))
        in
        check "CE-02"
          (Ws.equal (AI.find_word 64 killed x) (Ws.singleton (w64 5))
          && Ws.is_top (AI.find_word 64 killed g1)
          && Ws.is_top (AI.find_word 64 killed g2)));

    (* Frame-keep — cells at/above the call-time RSP survive, below die. *)
    pin "CE-03" "frame-keep — cells at/above the call-time RSP survive, below die"
      (fun () ->
        let e, m = ce_raw_env () in
        let kept_frame =
          Ce.transfer ~abi:ce_abi ~preserved:Core.Int.Set.empty
            ~site:{ Ce.summary = None; read_lanes = [] } e
        in
        check "CE-03"
          (Ws.equal (ce_reads m 0x2000L kept_frame) (Ws.singleton (w64 42))
          && Ws.equal (ce_reads m 0x3000L kept_frame) (Ws.singleton (w64 7))
          && Ws.is_top (ce_reads m 0x500L kept_frame)));

    (* A stack address in a call-read lane clears the whole retained frame. *)
    pin "CE-04" "a stack address in a call-read lane clears the whole retained frame"
      (fun () ->
        let rdi = Base.List.nth_exn ce_abi.Hike_abi.int_param_regs 0 in
        let e, m = ce_raw_env ~lanes:[ rdi ] () in
        let escaped =
          Ce.transfer ~abi:ce_abi ~preserved:Core.Int.Set.empty
            ~site:{ Ce.summary = None; read_lanes = [ rdi ] } e
        in
        check "CE-04"
          (Ws.is_top (ce_reads m 0x2000L escaped)
          && Ws.is_top (ce_reads m 0x3000L escaped)
          && AI.frame_escaped escaped));

    (* A trap restores no SP (it pops no retaddr). *)
    pin "CE-06" "a trap restores no SP (it pops no retaddr)" (fun () ->
        let trap_env, _ = ce_raw_env () in
        let trap =
          Ce.transfer ~abi:ce_abi
            ~preserved:(ids1 ce_abi.Hike_abi.sp)
            ~site:{ Ce.summary = None; read_lanes = [] }
            trap_env
        in
        check "CE-06"
          (Ws.equal (AI.find_word 64 trap ce_abi.Hike_abi.sp)
             (Ws.stack_word_i64 0x1000L)));

    (* A trap with a bounded RSP keeps the frame like any call. *)

    ("indirect callees",
     List.map (fun (name, value, known) ->
         case name (fun () ->
             let target = v64 "callee_target" in
             let callee_tid = Tid.create () in
             let writes = ids1 (List.hd ce_abi.Hike_abi.caller_saved_gprs) in
             let lookup a = if Int64.equal a 0x5000L then Some callee_tid else None in
             let callee t = Ce.Summary
                 (if Tid.equal t callee_tid then Some writes else None) in
             let env = AI.add_word AI.top ~key:target ~data:value in
             let actual =
               Ce.indirect_callee ~synth:Hike.Synth.empty ~lookup ~callee ~env
                 (Bil.Var target)
               |> function Ce.Summary w | Ce.Declared (w, _) -> w
             in
             check "callee's written registers"
               (Base.Option.equal Core.Int.Set.equal
                  (if known then Some writes else None) actual)))
       [ "known singleton", Ws.singleton (w64 0x5000), true;
         "multiple targets", Ws.of_list ~width:64 [ w64 0x5000; w64 0x9000 ], false;
         "foreign singleton", Ws.singleton (w64 0x9000), false;
         "unknown target", Ws.top 64, false ]);

    (* A preserved word keeps its value-set. *)

    (* A non-preserved word is TOPed. *)
    pin "CE-12" "a non-preserved word is TOPed" (fun () ->
        let x, y, env = ce_xy_env () in
        let env' = ce_call env (ids1 x) in
        check "CE-12" (Ws.is_top (AI.find_word 64 env' y)));

    (* RSP is preserved when it is in the preserved set. *)
    pin "CE-13" "RSP is preserved when it is in the preserved set" (fun () ->
        let x, _, env = ce_xy_env () in
        let rsp = sp in
        let env'' = AI.add_word env ~key:rsp ~data:(Ws.singleton (w64 0x10)) in
        let e' = ce_call env'' (ids (Var.Set.of_list [ x; rsp ])) in
        check "CE-13"
          (Ws.equal (AI.find_word 64 e' rsp) (Ws.singleton (w64 0x10))
          && Ws.equal (AI.find_word 64 e' x) (Ws.singleton (w64 5))));

    (* A call with an unbounded RSP keeps no frame. *)
    pin "CE-14" "a call with an unbounded RSP keeps no frame (a stored value reads as top)"
      (fun () ->
        let m0 = memv "c1_m0" in
        let mkey =
          match Mem.Key.of_wordset (Ws.singleton (w64 0x10)) with
          | [ k ] -> k
  | _ -> failwith "key"
        in
        let mem =
          Mem.add
            (Mem.top { addr_width = 64; addressable_width = 8 })
            ~key:mkey
            ~data:(Mem.Val.create (Ws.singleton (w64 0x11)) LittleEndian)
        in
        let env_m = AI.add_memory AI.top ~key:m0 ~data:mem in
        let e_m = ce_call env_m Core.Int.Set.empty in
        check "CE-14"
          (Mem.equal
             (AI.find_memory { addr_width = 64; addressable_width = 8 } e_m m0)
             (Mem.top { addr_width = 64; addressable_width = 8 })));

    (* The frame-keep namespace rule: a plain-top escape cannot name the
       stack line, so the caller's frame survives it. *)
    pin "CE-16" "a plain-top escape keeps the caller's frame" (fun () ->
        let rdi = Base.List.nth_exn ce_abi.Hike_abi.int_param_regs 0 in
        let e, m = ce_raw_env () in
        let env = AI.add_word e ~key:rdi ~data:(Ws.top 64) in
        let kept =
          Ce.transfer ~abi:ce_abi ~preserved:Core.Int.Set.empty
            ~site:{ Ce.summary = None; read_lanes = [ rdi ] }
            env
        in
        check "CE-16"
          (Ws.equal (ce_reads m 0x2000L kept) (Ws.singleton (w64 42))
          && Ws.equal (ce_reads m 0x3000L kept) (Ws.singleton (w64 7))));

    pin "CE-18" "call-frame retention requires a stack-origin SP" (fun () ->
        let env, m = ce_raw_env () in
        let values =
          [ Ws.singleton (w64 0x1000);
            Ws.set_origin (Hike_origin.Rip Hike_section.Rodata) (Ws.stack_word_i64 0x1000L) ] in
        Base.List.iter values ~f:(fun rsp ->
            let post = ce_call (AI.add_word env ~key:ce_abi.Hike_abi.sp ~data:rsp)
                (ids1 ce_abi.Hike_abi.sp) in
            check "a non-stack SP cannot certify caller-frame survival"
              (Ws.is_top (ce_reads m 0x2000L post))));

    pin "CE-19" "a mixed escape clears the whole retained frame" (fun () ->
        let rdi = Base.List.nth_exn ce_abi.Hike_abi.int_param_regs 0 in
        let e, m = ce_raw_env () in
        let env =
          AI.add_word e ~key:rdi
            ~data:(Ws.join (Ws.stack_word_i64 0x2000L) (Ws.singleton (w64 0)))
        in
        let kept =
          Ce.transfer ~abi:ce_abi ~preserved:Core.Int.Set.empty
            ~site:{ Ce.summary = None; read_lanes = [ rdi ] }
            env
        in
        check "CE-19"
          (Ws.is_top (ce_reads m 0x2000L kept)
          && Ws.is_top (ce_reads m 0x3000L kept)));

    pin "CE-21" "a frame escape stays sticky for later calls" (fun () ->
        let rdi = Base.List.nth_exn ce_abi.Hike_abi.int_param_regs 0 in
        let env, m = ce_raw_env ~lanes:[ rdi ] () in
        let first = ce_call_reads env [ rdi ] in
        let memory = AI.find_memory ce_idx first m in
        let memory =
          Mem.add memory ~key:(ce_mkey 0x3000L)
            ~data:(Mem.Val.create (Ws.singleton (w64 9)) LittleEndian)
        in
        let second = ce_call_reads (AI.add_memory first ~key:m ~data:memory) [] in
        check "CE-21"
          (AI.frame_escaped second && Ws.is_top (ce_reads m 0x3000L second)));

    pin "CE-23" "an overlapping memory cell is cleared by an outgoing argument hull" (fun () ->
        let key =
          match
            Mem.Key.of_wordset
              (Ws.stack_word
                 (Clp.interval ~width:64 (w64 0x1ff8) (w64 0x2000)))
          with
          | [ key ] -> key
          | _ -> failwith "key"
        in
        let memory =
          Mem.add (Mem.top ce_idx) ~key
            ~data:(Mem.Val.create (Ws.singleton (w64 3)) LittleEndian)
        in
        let cleared =
          Mem.call_keep memory ~keep_lo:(w64 0x1000)
            ~stack_args:[ (w64 0x2000, w64 0x2007) ] ~clear_frame:false
            ~clear_from:None ~foreign_cells:Mem.Drop_all
        in
        check "CE-23" (List.is_empty (Mem.cells cleared)));

    pin "CE-29" "outgoing stores use their SP before the call's return-address push" (fun () ->
        let entry, m = ce_raw_env () in
        let sp = ce_abi.Hike_abi.sp in
        let store off value =
          Def.create m (Bil.Store
              (Bil.Var m,
               Bil.BinOp (Bil.PLUS, Bil.Var sp,
                          Bil.Int (Cbat_word.to_word (w64 off))),
               Bil.Int (Cbat_word.to_word (w64 value)), LittleEndian, `r64)) in
        let callee = mk_selfloop_callee "ce_pushed_window_callee" in
        let continuation = Tid.create () in
        let block = Blk.create
            ~defs:[store 0 1; store 8 2;
                   Def.create sp (Bil.BinOp (Bil.MINUS, Bil.Var sp,
                       Bil.Int (Cbat_word.to_word (w64 8))));
                   store 0 0x1234]
            ~jmps:[mk_call_jmp continuation (Term.tid callee)] () in
        let post_defs = Vsa.Test_seam.denote_defs ~synth:Hike.Synth.empty block entry in
        let ranges = Ce.stack_arg_ranges ~synth:Hike.Synth.empty ~abi:ce_abi ~block ~entry post_defs in
        check "CE-29 both actual outgoing slots are cleared"
          (ranges = [(w64 0x1000, w64 0x100f)]));

    pin "CE-26" "the call clears the exact hull of outgoing stack-argument stores" (fun () ->
        let m = memv "ce_window_m" in
        let store off value =
          Def.create m
            (Bil.Store
               (Bil.Var m,
                Bil.BinOp (Bil.PLUS, Bil.Var ce_abi.Hike_abi.sp,
                           Bil.Int (Cbat_word.to_word (w64 off))),
                Bil.Int (Cbat_word.to_word (w64 value)),
                LittleEndian, `r64))
        in
        let callee = mk_selfloop_callee "ce_window_callee" in
        let sub, _ =
          sub_of "ce_window_caller"
            [ [ store 8 1; store 16 2 ],
              [ (1, fun t -> mk_call_jmp t (Term.tid callee)) ];
              [], [ (0, mk_ret) ] ]
        in
        let block = Base.List.hd_exn (Term.enum blk_t sub |> Seq.to_list) in
        let env, memory_var = ce_raw_env () in
        let memory = AI.find_memory ce_idx env memory_var in
        let memory =
          Base.List.fold [ (0x1008L, 4); (0x1010L, 5); (0x1018L, 6) ]
            ~init:memory ~f:(fun memory (address, value) ->
                Mem.add memory ~key:(ce_mkey address)
                  ~data:(Mem.Val.create (Ws.singleton (w64 value)) LittleEndian))
        in
        let env = AI.add_memory env ~key:memory_var ~data:memory in
        let stack_args = Ce.stack_arg_ranges ~synth:Hike.Synth.empty ~abi:ce_abi ~block ~entry:env env in
        let post =
          Ce.transfer ~stack_args ~abi:ce_abi ~preserved:Core.Int.Set.empty
            ~site:{ Ce.summary = None; read_lanes = [] } env
        in
        check "CE-26"
          (stack_args = [ (w64 0x1008, w64 0x1017) ]
          && Ws.is_top (ce_reads memory_var 0x1008L post)
          && Ws.is_top (ce_reads memory_var 0x1010L post)
          && Ws.equal (ce_reads memory_var 0x1018L post)
               (Ws.singleton (w64 6))));

    pin "CE-24" "storing a stack address outside the frame raises the escape bit" (fun () ->
        let mem = memv "ce_escape_global_mem" in
        let local = v64 "ce_escape_local" in
        let store =
          Def.create mem
            (Bil.Store
               (Bil.Var mem, Bil.Int (Cbat_word.to_word (w64 0x5000)),
                Bil.Var local, LittleEndian, `r64))
        in
        let env =
          AI.add_word AI.top ~key:local ~data:(Ws.stack_word_i64 (-16L))
        in
        let post = Vsa.Test_seam.denote_def ~synth:Hike.Synth.empty store env in
        check "CE-24" (AI.frame_escaped post));

    pin "CE-25" "a stack address stored in the sub's own frame stays contained" (fun () ->
        let mem = memv "ce_local_store_mem" in
        let local = v64 "ce_local_store_ptr" in
        let store =
          Def.create mem
            (Bil.Store
               (Bil.Var mem,
                Bil.BinOp (Bil.MINUS, Bil.Var ce_abi.Hike_abi.sp,
                           Bil.Int (Cbat_word.to_word (w64 8))),
                Bil.Var local, LittleEndian, `r64))
        in
        let env =
          AI.add_word
            (AI.add_word AI.top ~key:ce_abi.Hike_abi.sp
               ~data:(Ws.stack_word_i64 0L))
            ~key:local ~data:(Ws.stack_word_i64 (-16L))
        in
        let post = Vsa.Test_seam.denote_def ~synth:Hike.Synth.empty store env in
        check "CE-25" (not (AI.frame_escaped post)));

    pin "CE-27" "the frame-escape bit joins by OR and participates in equality" (fun () ->
        let contained = AI.top in
        let escaped = AI.escape_frame contained in
        let joined = AI.join contained escaped in
        let widened = AI.widen_join contained escaped in
        check "CE-27"
          (AI.frame_escaped joined && AI.frame_escaped widened
          && AI.equal joined escaped));

    pin "CE-28" "a call reads a stack pointer set in an earlier block" (fun () ->
        let m = memv "ce_earlier_m" in
        let rdi = Base.List.nth_exn ce_abi.Hike_abi.int_param_regs 0 in
        let callee = mk_selfloop_callee "ce_earlier_callee" in
        let store =
          Def.create m
            (Bil.Store
               (Bil.Var m,
                Bil.BinOp (Bil.MINUS, Bil.Var ce_abi.Hike_abi.sp,
                           Bil.Int (Cbat_word.to_word (w64 8))),
                Bil.Int (Cbat_word.to_word (w64 42)), LittleEndian, `r64))
        in
        let set_rdi =
          Def.create rdi
            (Bil.BinOp (Bil.MINUS, Bil.Var ce_abi.Hike_abi.sp,
                        Bil.Int (Cbat_word.to_word (w64 16))))
        in
        let sub, tids =
          sub_of "ce_earlier_blocks"
            [ [ store; set_rdi ], [ (1, mk_goto) ];
              [], [ (2, fun t -> mk_call_jmp t (Term.tid callee)) ];
              [], [ (0, mk_ret) ] ]
        in
        let sol = run_anchored sub in
        let after_call = Graphlib.Std.Solution.get sol tids.(2) in
        check "CE-28"
          (AI.frame_escaped after_call
          && Ws.is_top (ce_reads m (-8L) after_call)));

    (* The focused call test: one machine call with a result, a memory
       effect, and an outgoing stack argument.  The result is a fresh
       version the continuation receives, the outgoing argument hull is
       the exact span of the stack stores, and the call clears that
       hull while the cell above it survives. *)
    pin "CE-30"
      "a machine call with a result, a memory effect, and stack arguments"
      (fun () ->
        let m = memv "ce_focus_m" in
        let result_m = memv "ce_focus_result_m" in
        let sp = ce_abi.Hike_abi.sp in
        let store off value =
          Def.create m
            (Bil.Store
               (Bil.Var m,
                Bil.BinOp (Bil.PLUS, Bil.Var sp,
                           Bil.Int (Cbat_word.to_word (w64 off))),
                Bil.Int (Cbat_word.to_word (w64 value)), LittleEndian, `r64))
        in
        (* The continuation stores the call's result: the return lane is
           read there, so the SSA form mints it a fresh version. *)
        let keep_result =
          Def.create result_m
            (Bil.Store
               (Bil.Var result_m, Bil.Int (Cbat_word.to_word (w64 0x40)),
                Bil.Var (int_ret 0), LittleEndian, `r64))
        in
        let callee = mk_selfloop_callee "ce_focus_callee" in
        let raw, tids =
          raw_sub_of "ce_focus_caller"
            [ [ store 8 1; store 16 2 ],
              [ (1, fun t -> mk_call_jmp t (Term.tid callee)) ];
              [ keep_result ], [ (0, mk_ret) ] ]
        in
        (* The outgoing argument hull: the span of the stack stores. *)
        let block = Base.List.hd_exn (Term.enum blk_t raw |> Seq.to_list) in
        let env, memory_var = ce_raw_env () in
        let memory = AI.find_memory ce_idx env memory_var in
        let memory =
          Base.List.fold [ (0x1008L, 4); (0x1010L, 5); (0x1018L, 6) ]
            ~init:memory ~f:(fun memory (address, value) ->
                Mem.add memory ~key:(ce_mkey address)
                  ~data:(Mem.Val.create (Ws.singleton (w64 value)) LittleEndian))
        in
        let env = AI.add_memory env ~key:memory_var ~data:memory in
        let stack_args =
          Ce.stack_arg_ranges ~synth:Hike.Synth.empty ~abi:ce_abi ~block ~entry:env env in
        let post =
          Ce.transfer ~stack_args ~abi:ce_abi ~preserved:Core.Int.Set.empty
            ~site:{ Ce.summary = None; read_lanes = [] } env in
        (* The result: the continuation receives the call's return lane as
           a fresh version. *)
        let ssa = ssa_sub raw in
        let cont = Term.find_exn blk_t ssa tids.(1) in
        let result_phi =
          Term.enum phi_t cont
          |> Seq.filter_map ~f:(fun p ->
              if Var.same (Var.base (Phi.lhs p)) (int_ret 0) then Some (Phi.lhs p)
              else None)
          |> Seq.to_list
        in
        check "CE-30"
          (stack_args = [ (w64 0x1008, w64 0x1017) ]
           && Ws.is_top (ce_reads memory_var 0x1010L post)
           && Ws.equal (ce_reads memory_var 0x1018L post) (Ws.singleton (w64 6))
           && (match result_phi with
               | [ p ] -> Var.index p > 0
               | _ -> false)));

    pin "CE-31" "a read-only, uncaptured stack pointer leaves the frame intact"
      (fun () ->
        let e, m, rdi = sg_env 0x2000L in
        let signature =
          sg_record ~memory:(Sg.Argmem Sg.Read_only)
            [ sg_ptr Sg.Read_only ] in
        let post = sg_call ~signature e [ rdi ] in
        check "CE-31"
          (Ws.equal (ce_reads m 0x2000L post) (Ws.singleton (w64 42))
          && Ws.equal (ce_reads m 0x3000L post) (Ws.singleton (w64 7))
          && not (AI.frame_escaped post)));

    pin "CE-32" "a may-write, uncaptured stack pointer drops the frame from the pointer up"
      (fun () ->
        let e, m, rdi = sg_env 0x3000L in
        let signature = sg_record [ sg_ptr Sg.May_write ] in
        let post = sg_call ~signature e [ rdi ] in
        check "CE-32"
          (Ws.equal (ce_reads m 0x2000L post) (Ws.singleton (w64 42))
          && Ws.is_top (ce_reads m 0x3000L post)
          && not (AI.frame_escaped post)));

    pin "CE-33" "a captured stack pointer keeps the sticky whole-frame escape"
      (fun () ->
        let e, m, rdi = sg_env 0x3000L in
        let signature = sg_record [ sg_ptr ~captured:true Sg.Read_only ] in
        let post = sg_call ~signature e [ rdi ] in
        check "CE-33"
          (Ws.is_top (ce_reads m 0x2000L post) && AI.frame_escaped post));

    pin "CE-34" "an Argmem call keeps the global cells its pointers do not name"
      (fun () ->
        let e, m, rdi = sg_env 0x3000L in
        let argmem =
          sg_record ~memory:(Sg.Argmem Sg.May_write) [ sg_ptr Sg.May_write ] in
        let any = sg_record [ sg_ptr Sg.May_write ] in
        check "CE-34"
          (Ws.equal (sg_global m (sg_call ~signature:argmem e [ rdi ]))
             (Ws.singleton (w64 9))
          && Ws.is_top (sg_global m (sg_call ~signature:any e [ rdi ]))));

    pin "CE-35" "a returned parameter's provenance reaches the result lane"
      (fun () ->
        let e, _, rdi = sg_env 0x3000L in
        let result = v64 "sg_result" in
        let signature = sg_record ~returned:0 [ sg_ptr Sg.May_write ] in
        let post = sg_call ~signature ~result e [ rdi ] in
        check "CE-35"
          (Ws.equal (AI.find_word 64 post result) (Ws.stack_word_i64 0x3000L)));

    pin "CE-36" "only declared lanes are read; a variadic tail reads the rest"
      (fun () ->
        let e, m, rdi = sg_env 0x3000L in
        let rsi = Base.List.nth_exn ce_abi.Hike_abi.int_param_regs 1 in
        let e = AI.add_word e ~key:rsi ~data:(Ws.stack_word_i64 0x2000L) in
        let fixed = sg_record [ sg_ptr Sg.Read_only ] in
        let variadic = sg_record ~variadic:true [ sg_ptr Sg.Read_only ] in
        let undeclared = sg_record [] in
        check "CE-36"
          (not (AI.frame_escaped (sg_call ~signature:fixed e [ rdi; rsi ]))
          && not (AI.frame_escaped (sg_call ~signature:undeclared e [ rdi; rsi ]))
          && AI.frame_escaped (sg_call ~signature:variadic e [ rdi; rsi ])
          && Ws.is_top
               (ce_reads m 0x2000L (sg_call ~signature:variadic e [ rdi; rsi ]))));

  ]

let () = run "call_effects" tests
