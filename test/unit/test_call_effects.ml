(* Call-effects pass pins.  One Alcotest group per pin; each pin builds its
   own state, so no state crosses pins. *)

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
    ~site:{ Ce.summary = None; read_lanes = []; pushed = false } env

let ce_call_reads ?(stack_args = []) env read_lanes =
  Ce.transfer ~stack_args ~abi:ce_abi ~preserved:Core.Int.Set.empty
    ~site:{ Ce.summary = None; read_lanes; pushed = false } env

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
            ~site:{ Ce.summary = Some summary; read_lanes = []; pushed = false }
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
            ~site:{ Ce.summary = None; read_lanes = []; pushed = false }
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
            ~site:{ Ce.summary = None; read_lanes = []; pushed = false } e
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
            ~site:{ Ce.summary = None; read_lanes = [ rdi ]; pushed = false } e
        in
        check "CE-04"
          (Ws.is_top (ce_reads m 0x2000L escaped)
          && Ws.is_top (ce_reads m 0x3000L escaped)
          && AI.frame_escaped escaped));

    (* A pushed site's SP gains one word — the popped retaddr. *)
    pin "CE-05" "a pushed site's SP gains one word — the popped retaddr" (fun () ->
        let restored =
          Ce.transfer ~abi:ce_abi ~preserved:Core.Int.Set.empty
            ~site:{ Ce.summary = None; read_lanes = []; pushed = true }
            (AI.add_word AI.top ~key:ce_abi.Hike_abi.sp
               ~data:(Ws.singleton (w64 0x1000)))
        in
        let rsp' = AI.find_word 64 restored ce_abi.Hike_abi.sp in
        check "CE-05" (Ws.elem (w64 0x1000) rsp' && Ws.elem (w64 0x1008) rsp'));

    (* A trap restores no SP (it pops no retaddr). *)
    pin "CE-06" "a trap restores no SP (it pops no retaddr)" (fun () ->
        let trap_env, _ = ce_raw_env () in
        let trap =
          Ce.transfer ~abi:ce_abi
            ~preserved:(ids1 ce_abi.Hike_abi.sp)
            ~site:{ Ce.summary = None; read_lanes = []; pushed = false }
            trap_env
        in
        check "CE-06"
          (Ws.equal (AI.find_word 64 trap ce_abi.Hike_abi.sp)
             (Ws.stack_word_i64 0x1000L)));

    (* A trap with a bounded RSP keeps the frame like any call. *)


    (* A singleton target naming a lifted sub reads its summary. *)
    pin "CE-08" "a singleton target naming a lifted sub reads its summary" (fun () ->
        let tgt = v64 "ce_tgt" in
        let sub_tid = Tid.create () in
        let g = Base.List.nth_exn ce_abi.Hike_abi.caller_saved_gprs 0 in
        let gs = Cbat_var_id.intern_set (Core.Set.singleton (module Var) g) in
        let lookup v = if Int64.equal v 0x5000L then Some sub_tid else None in
        let callee t = Ce.Summary (if Tid.equal t sub_tid then Some gs else None) in
        let bounded =
          AI.add_word AI.top ~key:tgt ~data:(Ws.singleton (w64 0x5000))
        in
        check "CE-08"
          (match Ce.indirect_callee ~lookup ~callee ~env:bounded (Bil.Var tgt) with
          | Ce.Summary (Some ws) -> Core.Int.Set.equal ws gs
          | _ -> false));

    (* An unbounded target resolves to nothing. *)
    pin "CE-09" "an unbounded target resolves to nothing" (fun () ->
        let tgt = v64 "ce_tgt" in
        let sub_tid = Tid.create () in
        let g = Base.List.nth_exn ce_abi.Hike_abi.caller_saved_gprs 0 in
        let gs = Cbat_var_id.intern_set (Core.Set.singleton (module Var) g) in
        let lookup v = if Int64.equal v 0x5000L then Some sub_tid else None in
        let callee t = Ce.Summary (if Tid.equal t sub_tid then Some gs else None) in
        let spread =
          AI.add_word AI.top ~key:tgt
            ~data:(Ws.of_list ~width:64 [ w64 1; w64 2 ])
        in
        check "CE-09"
          (match Ce.indirect_callee ~lookup ~callee ~env:spread (Bil.Var tgt) with
          | Ce.Summary None -> true
          | _ -> false));

    (* A foreign singleton resolves to nothing. *)
    pin "CE-10" "a foreign singleton resolves to nothing" (fun () ->
        let tgt = v64 "ce_tgt" in
        let sub_tid = Tid.create () in
        let g = Base.List.nth_exn ce_abi.Hike_abi.caller_saved_gprs 0 in
        let gs = Cbat_var_id.intern_set (Core.Set.singleton (module Var) g) in
        let lookup v = if Int64.equal v 0x5000L then Some sub_tid else None in
        let callee t = Ce.Summary (if Tid.equal t sub_tid then Some gs else None) in
        let foreign =
          AI.add_word AI.top ~key:tgt ~data:(Ws.singleton (w64 0x9000))
        in
        check "CE-10"
          (match Ce.indirect_callee ~lookup ~callee ~env:foreign (Bil.Var tgt) with
          | Ce.Summary None -> true
          | _ -> false));

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
            ~site:{ Ce.summary = None; read_lanes = [ rdi ]; pushed = false }
            env
        in
        check "CE-16"
          (Ws.equal (ce_reads m 0x2000L kept) (Ws.singleton (w64 42))
          && Ws.equal (ce_reads m 0x3000L kept) (Ws.singleton (w64 7))));

    (* Re-pin CE-17: bounded stack lanes now conservatively clear the frame. *)
    pin "CE-17" "a bounded stack escape clears the whole retained frame" (fun () ->
        let rdi = Base.List.nth_exn ce_abi.Hike_abi.int_param_regs 0 in
        let e, m = ce_raw_env () in
        let env =
          AI.add_word e ~key:rdi ~data:(Ws.stack_word_i64 0x2000L)
        in
        let kept =
          Ce.transfer ~abi:ce_abi ~preserved:Core.Int.Set.empty
            ~site:{ Ce.summary = None; read_lanes = [ rdi ]; pushed = false }
            env
        in
        check "CE-17"
          (Ws.is_top (ce_reads m 0x2000L kept)
          && Ws.is_top (ce_reads m 0x3000L kept)));
    pin "CE-18" "call-frame retention requires a stack-origin SP" (fun () ->
        let env, m = ce_raw_env () in
        let values =
          [ Ws.singleton (w64 0x1000);
            Ws.set_origin Hike_origin.Abs (Ws.stack_word_i64 0x1000L);
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
            ~site:{ Ce.summary = None; read_lanes = [ rdi ]; pushed = false }
            env
        in
        check "CE-19"
          (Ws.is_top (ce_reads m 0x2000L kept)
          && Ws.is_top (ce_reads m 0x3000L kept)));

    pin "CE-20" "a lane set before the call block escapes at the call" (fun () ->
        let rdi = Base.List.nth_exn ce_abi.Hike_abi.int_param_regs 0 in
        let env, m = ce_raw_env ~lanes:[ rdi ] () in
        let post = ce_call_reads env [ rdi ] in
        check "CE-20"
          (AI.frame_escaped post
          && Ws.is_top (ce_reads m 0x2000L post)
          && Ws.is_top (ce_reads m 0x3000L post)));

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
        let post_defs = Vsa.Test_seam.denote_defs block entry in
        let ranges = Ce.stack_arg_ranges ~abi:ce_abi ~block ~entry post_defs in
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
        let stack_args = Ce.stack_arg_ranges ~abi:ce_abi ~block ~entry:env env in
        let post =
          Ce.transfer ~stack_args ~abi:ce_abi ~preserved:Core.Int.Set.empty
            ~site:{ Ce.summary = None; read_lanes = []; pushed = false } env
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
        let post = Vsa.Test_seam.denote_def store env in
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
        let post = Vsa.Test_seam.denote_def store env in
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
  ]

let () = run "call_effects" tests
