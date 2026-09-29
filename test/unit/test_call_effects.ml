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
    ~site:{ Ce.summary = None; written_lanes = []; pushed = false } env

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
            ~site:{ Ce.summary = Some summary; written_lanes = []; pushed = false }
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
            ~site:{ Ce.summary = None; written_lanes = []; pushed = false }
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
            ~site:{ Ce.summary = None; written_lanes = []; pushed = false } e
        in
        check "CE-03"
          (Ws.equal (ce_reads m 0x2000L kept_frame) (Ws.singleton (w64 42))
          && Ws.equal (ce_reads m 0x3000L kept_frame) (Ws.singleton (w64 7))
          && Ws.is_top (ce_reads m 0x500L kept_frame)));

    (* An escape lane's range dies with the call, the rest of the frame survives. *)
    pin "CE-04" "an escape lane's range dies with the call, the rest of the frame survives"
      (fun () ->
        let rdi = Base.List.nth_exn ce_abi.Hike_abi.int_param_regs 0 in
        let e, m = ce_raw_env ~lanes:[ rdi ] () in
        let escaped =
          Ce.transfer ~abi:ce_abi ~preserved:Core.Int.Set.empty
            ~site:{ Ce.summary = None; written_lanes = [ rdi ]; pushed = false } e
        in
        check "CE-04"
          (Ws.is_top (ce_reads m 0x2000L escaped)
          && Ws.equal (ce_reads m 0x3000L escaped) (Ws.singleton (w64 7))));

    (* A pushed site's SP gains one word — the popped retaddr. *)
    pin "CE-05" "a pushed site's SP gains one word — the popped retaddr" (fun () ->
        let restored =
          Ce.transfer ~abi:ce_abi ~preserved:Core.Int.Set.empty
            ~site:{ Ce.summary = None; written_lanes = []; pushed = true }
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
            ~site:{ Ce.summary = None; written_lanes = []; pushed = false }
            trap_env
        in
        check "CE-06"
          (Ws.equal (AI.find_word 64 trap ce_abi.Hike_abi.sp)
             (Ws.stack_word_i64 0x1000L)));

    (* A trap with a bounded RSP keeps the frame like any call. *)
    pin "CE-07" "a trap with a bounded RSP keeps the frame like any call" (fun () ->
        let trap_env, m_trap = ce_raw_env () in
        let trap_frame =
          Ce.transfer ~abi:ce_abi
            ~preserved:(ids1 ce_abi.Hike_abi.sp)
            ~site:{ Ce.summary = None; written_lanes = []; pushed = false }
            trap_env
        in
        check "CE-07"
          (Ws.equal (ce_reads m_trap 0x2000L trap_frame) (Ws.singleton (w64 42))
          && Ws.equal (ce_reads m_trap 0x3000L trap_frame) (Ws.singleton (w64 7))
          && Ws.is_top (ce_reads m_trap 0x500L trap_frame)));

    (* A singleton target naming a lifted sub reads its summary. *)
    pin "CE-08" "a singleton target naming a lifted sub reads its summary" (fun () ->
        let tgt = v64 "ce_tgt" in
        let sub_tid = Tid.create () in
        let g = Base.List.nth_exn ce_abi.Hike_abi.caller_saved_gprs 0 in
        let gs = Cbat_var_id.intern_set (Core.Set.singleton (module Var) g) in
        let lookup v = if Int64.equal v 0x5000L then Some sub_tid else None in
        let summary_of t = if Tid.equal t sub_tid then Some gs else None in
        let bounded =
          AI.add_word AI.top ~key:tgt ~data:(Ws.singleton (w64 0x5000))
        in
        check "CE-08"
          (match Ce.indirect_summary ~lookup ~summary_of ~env:bounded (Bil.Var tgt) with
          | Some ws -> Core.Int.Set.equal ws gs
          | None -> false));

    (* An unbounded target resolves to nothing. *)
    pin "CE-09" "an unbounded target resolves to nothing" (fun () ->
        let tgt = v64 "ce_tgt" in
        let sub_tid = Tid.create () in
        let g = Base.List.nth_exn ce_abi.Hike_abi.caller_saved_gprs 0 in
        let gs = Cbat_var_id.intern_set (Core.Set.singleton (module Var) g) in
        let lookup v = if Int64.equal v 0x5000L then Some sub_tid else None in
        let summary_of t = if Tid.equal t sub_tid then Some gs else None in
        let spread =
          AI.add_word AI.top ~key:tgt
            ~data:(Ws.of_list ~width:64 [ w64 1; w64 2 ])
        in
        check "CE-09"
          (match Ce.indirect_summary ~lookup ~summary_of ~env:spread (Bil.Var tgt) with
          | None -> true
          | Some _ -> false));

    (* A foreign singleton resolves to nothing. *)
    pin "CE-10" "a foreign singleton resolves to nothing" (fun () ->
        let tgt = v64 "ce_tgt" in
        let sub_tid = Tid.create () in
        let g = Base.List.nth_exn ce_abi.Hike_abi.caller_saved_gprs 0 in
        let gs = Cbat_var_id.intern_set (Core.Set.singleton (module Var) g) in
        let lookup v = if Int64.equal v 0x5000L then Some sub_tid else None in
        let summary_of t = if Tid.equal t sub_tid then Some gs else None in
        let foreign =
          AI.add_word AI.top ~key:tgt ~data:(Ws.singleton (w64 0x9000))
        in
        check "CE-10"
          (match Ce.indirect_summary ~lookup ~summary_of ~env:foreign (Bil.Var tgt) with
          | None -> true
          | Some _ -> false));

    (* A preserved word keeps its value-set. *)
    pin "CE-11" "a preserved word keeps its value-set" (fun () ->
        let x, _, env = ce_xy_env () in
        let env' = ce_call env (ids1 x) in
        check "CE-11" (Ws.equal (AI.find_word 64 env' x) (Ws.singleton (w64 5))));

    (* A non-preserved word is TOPed. *)
    pin "CE-12" "a non-preserved word is TOPed" (fun () ->
        let x, y, env = ce_xy_env () in
        let env' = ce_call env (ids1 x) in
        check "CE-12" (Ws.is_top (AI.find_word 64 env' y)));

    (* RSP is preserved when it is in the preserved set. *)
    pin "CE-13" "RSP is preserved when it is in the preserved set" (fun () ->
        let x, _, env = ce_xy_env () in
        let rsp = v64 "RSP" in
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

    (* A virtual var is preserved when it is in the preserved set. *)
    pin "CE-15" "a virtual var is preserved when it is in the preserved set"
      (fun () ->
        let vv = Var.create ~is_virtual:true ~fresh:false "c1_vv" (Type.Imm 64) in
        let env_v = AI.add_word AI.top ~key:vv ~data:(Ws.singleton (w64 3)) in
        let e_v = ce_call env_v (ids1 vv) in
        check "CE-15"
          (Ws.equal (AI.find_word 64 e_v vv) (Ws.singleton (w64 3))));

    (* The frame-keep namespace rule: a plain-top escape cannot name the
       stack line, so the caller's frame survives it. *)
    pin "CE-16" "a plain-top escape keeps the caller's frame" (fun () ->
        let rdi = Base.List.nth_exn ce_abi.Hike_abi.int_param_regs 0 in
        let e, m = ce_raw_env () in
        let env = AI.add_word e ~key:rdi ~data:(Ws.top 64) in
        let kept =
          Ce.transfer ~abi:ce_abi ~preserved:Core.Int.Set.empty
            ~site:{ Ce.summary = None; written_lanes = [ rdi ]; pushed = false }
            env
        in
        check "CE-16"
          (Ws.equal (ce_reads m 0x2000L kept) (Ws.singleton (w64 42))
          && Ws.equal (ce_reads m 0x3000L kept) (Ws.singleton (w64 7))));

    (* A Rel escape of bounded extent carves exactly its range. *)
    pin "CE-17" "a Rel escape of bounded extent carves its range" (fun () ->
        let rdi = Base.List.nth_exn ce_abi.Hike_abi.int_param_regs 0 in
        let e, m = ce_raw_env () in
        let env =
          AI.add_word e ~key:rdi ~data:(Ws.stack_word_i64 0x2000L)
        in
        let kept =
          Ce.transfer ~abi:ce_abi ~preserved:Core.Int.Set.empty
            ~site:{ Ce.summary = None; written_lanes = [ rdi ]; pushed = false }
            env
        in
        check "CE-17"
          (Ws.is_top (ce_reads m 0x2000L kept)
          && Ws.equal (ce_reads m 0x3000L kept) (Ws.singleton (w64 7))));
  ]

let () = run "call_effects" tests
