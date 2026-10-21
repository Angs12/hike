(* Hike_origin pins: the origin ADT, its facts table, and the one-origin
   accessor on the WordSet algebra. *)

open! Core
open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

module Origin = Hike_origin

let abi = Hike_abi.x86_64_sysv

(* ORI-03: the one-origin accessor — a stack value reads Stack, plain
   values read None, a mixed union reads None. *)
let ori_03 () =
  let stk = Ws.stack_word_i64 (-8L) in
  check "stack value reads Stack" (Option.equal Origin.equal (Ws.origin stk) (Some Origin.Stack));
  let plain = Ws.singleton (i2w 5L) in
  check "plain value reads None" (Option.is_none (Ws.origin plain));
  let mixed = Ws.union stk plain in
  check "mixed union reads None" (Option.is_none (Ws.origin mixed));
  let clpv = Ws.of_clp (Clp.interval ~width:64 (i2w 0L) (i2w 16L)) in
  check "absolute clp reads None" (Option.is_none (Ws.origin clpv))

(* ORI-06: the per-def origin slot, stamped at the solve boundary — a
   caller-frame address def reads Stack through the seam. *)
let round_trip (offs : int64) : Origin.t option =
  let m = memv "rt_m" in
  let rsp = Var.create ~is_virtual:false ~fresh:false "RSP" (Type.Imm 64) in
  let x = Var.create ~is_virtual:false ~fresh:false "rt_x" (Type.Imm 64) in
  let ptr = Bil.BinOp (Bil.PLUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (i2w offs))) in
  let store =
    Def.create m
      (Bil.Store (Bil.Var m, ptr, ptr, LittleEndian, `r64))
  in
  let load = Def.create x (Bil.Load (Bil.Var m, ptr, LittleEndian, `r64)) in
  let sub = straight_sub "rt" [ store; load ] in
  let entry = anchored_entry () in
  let sol =
    static_graph_vsa ~synth:Hike.Synth.empty ~abi sub
      (Vsa.init_sol ~abi ~entry sub)
  in
  let _, stamped = Vsa.stamp_envs_of_sol ~synth:Hike.Synth.empty ~sol sub in
  let blk = Term.enum blk_t stamped |> Seq.to_list |> List.hd_exn in
  let defs = Term.enum def_t blk |> Seq.to_list in
  match List.rev defs with
  | load_def :: _ -> Vsa.Def_origin.def_origin load_def
  | _ -> None

(* ORI-07: a frame pointer stored to a cell reads back Stack. *)
let ori_07 () =
  check "stored frame pointer reads back Stack"
    (Option.equal Origin.equal (round_trip (-8L)) (Some Origin.Stack))

(* ORI-18: the D10 namespace test — the stack-line origins answer
   true; a plain or module-relative origin answers false. *)
let ori_18 () =
  check "Stack names the stack line" (Origin.names_stack_line Origin.Stack);
  check "a thread-pointer origin names no stack line"
    (not (Origin.names_stack_line Origin.Fs));
  check "a module-relative origin names no stack line"
    (not (Origin.names_stack_line (Origin.Rip Hike_section.Rodata)))

let ori_19 () =
  let origins =
    [ Origin.Stack; Origin.Fs; Origin.Rip Hike_section.Rodata;
      Origin.Rip Hike_section.Data ]
  in
  let value o = Ws.set_origin o (Ws.stack_word_i64 3L) in
  List.iter origins ~f:(fun a ->
      check "same-origin disjoint offsets do not overlap"
        (not (Ws.overlap (value a) (Ws.set_origin a (Ws.stack_word_i64 4L))));
      List.iter origins ~f:(fun b ->
          check "equal offsets retain distinct origin identities"
            (Bool.equal (Ws.equal (value a) (value b)) (Origin.equal a b));
          check "containment never substitutes a different origin"
            (Bool.equal (Ws.precedes (value a) (value b)) (Origin.equal a b)));
      check "offset arithmetic retains its source origin"
        (Option.equal Origin.equal
           (Ws.origin (Ws.add (value a) (Ws.singleton (i2w 1L))))
           (Some a)));
  let region = Origin.Rip Hike_section.Rodata in
  let rip = value region in
  let plain k = Ws.singleton (i2w k) in
  check "a module address enumerates its link-time words"
    (Option.equal (List.equal Cbat_word.equal)
       (Ws.enumerate ~cap:4 rip) (Some [ i2w 3L ]));
  check "membership is exact on the absolute line"
    (Ws.elem (i2w 3L) rip && not (Ws.elem (i2w 4L) rip));
  check "a join with a plain value keeps the region beside the words"
    (let u = Ws.union rip (plain 5L) in
     Ws.equal u (Ws.union (plain 5L) rip)
     && Ws.equal (Ws.diff u (plain 5L)) rip
     && Ws.elem (i2w 3L) u && Ws.elem (i2w 5L) u);
  check "a displacement and a mask keep the region"
    (Option.equal Origin.equal (Ws.origin (Ws.add rip (plain 8L))) (Some region)
     && Option.equal Origin.equal
          (Ws.origin (Ws.logand rip (plain (-2L)))) (Some region)
     && Ws.equal (Ws.logand rip (plain 15L)) (value region));
  check "subtracting a module address yields plain link-time words"
    (Ws.equal (Ws.sub (plain 12L) rip) (plain 9L)
     && Ws.equal (Ws.sub (Ws.add rip (plain 4L)) rip) (plain 4L));
  check "different regions keep each region"
    (let data = Ws.set_origin (Origin.Rip Hike_section.Data) (Ws.stack_word_i64 5L) in
     let u = Ws.union rip data in
     Ws.equal u (Ws.union data rip)
     && Ws.equal (Ws.diff u (plain 5L)) rip
     && Ws.equal (Ws.diff u (plain 3L)) data);
  List.iter [ region; Origin.Stack ] ~f:(fun o ->
      check "memory namespace follows the carried origin"
        (match Ws.address_groups (value o) with
         | [ (key, _) ] -> Option.equal Origin.equal key (Ws.key_line o)
         | _ -> false))

let ori_20 () =
  let plain k = Ws.singleton (i2w k) in
  List.iter [ 3L; -1L; Stdlib.Int64.min_int ] ~f:(fun k ->
      check "plain union preserves exact absolute bits"
        (Ws.equal (Ws.union (plain k) (plain k)) (plain k));
      check "plain multiplication wraps in 64 bits"
        (Ws.equal (Ws.mul (plain k) (plain 2L)) (plain (Stdlib.Int64.mul k 2L)));
      check "plain negation wraps in 64 bits"
        (Ws.equal (Ws.neg (plain k)) (plain (Stdlib.Int64.neg k))))

let ori_22 () =
  let origins =
    [ None; Some Origin.Stack; Some Origin.Fs;
      Some (Origin.Rip Hike_section.Rodata) ] in
  let name = function None -> "plain" | Some o -> Origin.name o in
  let key_line = Option.bind ~f:Ws.key_line in
  let value = function
    | None -> Ws.singleton (i2w 0L)
    | Some o -> Ws.set_origin o (Ws.stack_word_i64 0L) in
  let key ws = List.hd_exn (Mem.Key.of_wordset ws) in
  let cell = key (Ws.singleton (i2w 0x1000L)) in
  List.iter origins ~f:(fun a ->
      let data = value a in
      let mem = Mem.add
          (Mem.top { Mem.addr_width = 64; addressable_width = 8 })
          ~key:cell ~data:(Mem.Val.create data LittleEndian) in
      let loaded = Mem.Val.data (Mem.find (64, LittleEndian) mem cell) in
      check ("full-width memory preserves " ^ name a) (Ws.equal data loaded);
      List.iter origins ~f:(fun b ->
          check "memory aliases only the explicit shared coordinate line"
            (Bool.equal (Mem.Key.overlap (key data) (key (value b)))
               (Option.equal Origin.equal (key_line a) (key_line b)))))

let ori_23 () =
  List.iter [ Origin.Stack ] ~f:(fun o ->
      let value = Ws.set_origin o
          (Ws.stack_word (Clp.interval ~width:64 (i2w 7L) (i2w 9L))) in
      let rounded = Ws.logand value (Ws.singleton (i2w (-16L))) in
      check "rounding retains both blocks across the certified base boundary"
        (Option.equal Origin.equal (Ws.origin rounded) (Some o)
         && Option.value_map (Ws.stack_offsets rounded) ~default:false
              ~f:(fun offs -> Clp.elem (i2w (-8L)) offs && Clp.elem (i2w 8L) offs)))

let ori_24 () =
  let origins =
    [ Origin.Stack; Origin.Rip Hike_section.Rodata ] in
  List.iter origins ~f:(fun o ->
      let a = Ws.set_origin o (Ws.stack_word_i64 0L) in
      let b = Ws.set_origin o (Ws.stack_word_i64 1L) in
      check "same-origin difference uses exact offsets"
        (Ws.equal (Ws.diff a b) a);
      check "same-origin self-difference is empty" (Ws.is_bottom (Ws.diff a a)));
  let a = Ws.singleton (i2w 42L) in
  let b = Ws.set_origin (Origin.Rip Hike_section.Rodata) (Ws.stack_word_i64 0L) in
  check "a module-address subtrahend removes only its link-time words"
    (Ws.elem (i2w 42L) (Ws.diff a b)
     && Ws.is_bottom
          (Ws.diff a (Ws.set_origin (Origin.Rip Hike_section.Rodata) (Ws.stack_word_i64 42L))))

let ori_26 () =
  let s k = Ws.stack_word_i64 k in
  let c n = Ws.singleton (i2w n) in
  check "OR with a certified constant stays on the stack line"
    (Ws.equal (Ws.logor (s 0L) (c 7L)) (s 7L)
    && Option.equal Origin.equal (Ws.origin (Ws.logor (s 0L) (c 7L)))
         (Some Origin.Stack));
  check "XOR with a certified constant stays on the stack line"
    (Ws.equal (Ws.logxor (s 0L) (c 8L)) (s (-8L)));
  check "OR with a constant above the certified bits answers top"
    (Ws.is_top (Ws.logor (s 0L) (c 0x100L)))

(* ORI-27 (T35): the stack-probe shape — an SP that is a non-singleton
   Stack set (two guarded sizes), then a fixed page decrement.  SP is
   ordinary Stack arithmetic: its origin stays Stack and its offsets are
   the exact shifted set.  The decrementing block owns the SP's
   definitions, so its own post-state holds the shifted value. *)
let ori_27 () =
  let rsp = sp and rax = int_ret 0 in
  let f = v1 "ori27_f" in
  let w (i : int64) = Cbat_word.to_word (i2w i) in
  let sub =
    fst
      (sub_of "ori27"
         [ [ Def.create rax (Bil.Int (w 16L)) ],
           [ (2, fun t -> mk_jmp_to t (Bil.Var f)); (1, mk_goto) ];
           [ Def.create rax (Bil.Int (w 32L)) ],
           [ (2, mk_goto) ];
           [ Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Var rax));
             Def.create rsp
               (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (w 4096L))) ],
           [ (3, mk_goto) ];
           [], [ (2, mk_ret) ] ])
  in
  let entry = anchored_entry () in
  let sol =
    static_graph_vsa ~synth:Hike.Synth.empty ~abi sub (Vsa.init_sol ~abi ~entry sub)
  in
  let dec_tid =
    Term.enum blk_t sub |> Seq.to_list
    |> List.find_map ~f:(fun b ->
           let tid = Term.tid b in
           if Option.is_some (def_version sub tid rsp) then Some tid else None)
  |> Option.value_exn
  in
  let sp_after = value_after sub sol dec_tid rsp in
  check "SP stays on the Stack origin through the fixed decrement"
    (Option.equal Origin.equal (Ws.origin sp_after) (Some Origin.Stack));
  check "the final SP is exactly the two shifted positions"
    (Option.value_map (Ws.stack_offsets sp_after) ~default:false ~f:(fun offs ->
        Clp.elem (i2w (-4128L)) offs && Clp.elem (i2w (-4112L)) offs
        && not (Clp.elem (i2w (-4120L)) offs)
        && Option.equal Cbat_word.equal (Clp.min_elem offs) (Some (i2w (-4128L)))
        && Option.equal Cbat_word.equal (Clp.max_elem offs) (Some (i2w (-4112L)))))

let ori_28 () =
  let m = memv "ori28_mem" and p = v64 "ori28_pointer" in
  let q = v64 "ori28_reloaded" and out = v64 "ori28_value" in
  let w n = Bil.Int (Cbat_word.to_word (i2w n)) in
  let slot = Bil.BinOp (Bil.MINUS, Bil.Var abi.sp, w 8L) in
  let sub = straight_sub "ori28"
      [ Def.create p (Bil.Load (Bil.Var m, Bil.Var abi.thread_pointer,
                                LittleEndian, `r64));
        Def.create p (Bil.BinOp (Bil.MINUS, Bil.Var p, w 8L));
        Def.create m (Bil.Store (Bil.Var m, slot, Bil.Var p, LittleEndian, `r64));
        Def.create q (Bil.Load (Bil.Var m, slot, LittleEndian, `r64));
        Def.create out (Bil.Load (Bil.Var m, Bil.Var q, LittleEndian, `r64)) ] in
  let sol = static_graph_vsa ~synth:Hike.Synth.empty ~abi sub (Vsa.init_sol ~abi sub) in
  let _, stamped = Vsa.stamp_envs_of_sol ~synth:Hike.Synth.empty ~sol sub in
  let defs = Term.enum blk_t stamped |> Seq.concat_map ~f:(Term.enum def_t)
      |> Seq.to_list in
  List.iter defs ~f:(fun d ->
      check ("FS origin survives at " ^ Var.name (Def.lhs d))
        (Option.equal Origin.equal
           (Vsa.Def_origin.def_origin d)
           (Some (if Var.same (Def.lhs d) q then Origin.Stack else Origin.Fs))
         || Var.same (Def.lhs d) m));
  (* The reloaded pointer's own value: the block's state holds the
     definition's version, so the pin reads it there. *)
  let blk = Option.value_exn (Term.first blk_t sub) in
  let pointer = value_after sub sol (Term.tid blk) q in
  check "FS pointers use their own memory namespace"
    (match Ws.address_groups pointer with
     | [(Some o, offs)] -> String.equal (Origin.name o) "fs"
                     && Clp.elem (i2w (-8L)) offs
     | _ -> false)

let ori_29 () =
  let fs k = Ws.set_origin Origin.Fs (Ws.stack_word_i64 k) in
  let p = fs (-8L) and zero = Ws.singleton (i2w 0L) in
  let mixed = Ws.union p zero in
  check "an unknown FS base supplies no absolute bounds or enumeration"
    (Option.is_none (Ws.min_elem mixed) && Option.is_none (Ws.max_elem mixed)
     && Option.is_none (Ws.min_elem_signed mixed)
     && Option.is_none (Ws.enumerate ~cap:64 p));
  check "plain constraints cannot remove FS offsets using an invented base"
    (Ws.equal (Ws.meet p zero) p && Ws.equal (Ws.diff p zero) p
     && Ws.equal (Ws.diff p (Ws.module_address 0L)) p
     && Ws.is_bottom (Ws.meet p (Ws.bottom 64)));
  check "a mixed union and widening keep the FS memory line"
    (List.exists (Ws.address_groups (Ws.widen_join mixed (Ws.union (fs (-16L)) zero)))
       ~f:(fun (o, _) -> Option.equal Origin.equal o (Some Origin.Fs)));
  check "a shared FS base cancels in pointer subtraction"
    (Ws.equal (Ws.sub (fs (-8L)) (fs (-16L))) (Ws.singleton (i2w 8L)));
  let synth, root = Hike.Synth.mint_thread_addr ~addr_bits:64 0L Hike.Synth.empty in
  let root = Bil.Var root in
  check "same-origin pointer equality compares offsets"
    (match Vsa.Test_seam.denote_imm_exp ~synth (Bil.BinOp (Bil.EQ, root, root)) AI.top with
     | Ok v -> Ws.equal v (Ws.singleton Cbat_word.b1)
     | Error _ -> false)

let ori_30 () =
  let m = memv "ori30_mem" and p = v64 "ori30_pointer" in
  let sub = fst (sub_of "ori30"
      [ [], [(1, fun target -> Jmp.create (Call
          (Call.create ~target:(Direct (Tid.for_name "ori30_foreign"))
             ~return:(Direct target) ())))];
        [Def.create p (Bil.Load (Bil.Var m, Bil.Var abi.thread_pointer,
                                 LittleEndian, `r64))], [(0, mk_ret)] ]) in
  let sol = static_graph_vsa ~synth:Hike.Synth.empty ~abi sub (Vsa.init_sol ~abi sub) in
  (* The block that owns the self-pointer load: a block's state holds the
     definition's version, so the pin reads the value there. *)
  let load_tid =
    Term.enum blk_t sub |> Seq.to_list
    |> List.find_map ~f:(fun b ->
           let tid = Term.tid b in
           if Option.is_some (def_version sub tid p) then Some tid else None)
    |> Option.value_exn
  in
  let pointer = value_after sub sol load_tid p in
  check "a foreign call preserves FS and its self-pointer load"
    (Option.equal Origin.equal (Ws.origin pointer) (Some Origin.Fs))

let ori_31 () =
  let m = memv "ori31_mem" in
  let p = Ws.set_origin Origin.Fs (Ws.stack_word_i64 0L) in
  let data = Ws.singleton (i2w 42L) in
  let key = List.hd_exn (Mem.Key.of_wordset p) in
  let mv = Mem.add (Mem.top { Mem.addr_width = 64; addressable_width = 8 })
      ~key ~data:(Mem.Val.create data LittleEndian) in
  let env = AI.add_memory AI.top ~key:m ~data:mv in
  let synth, address = Hike.Synth.mint_thread_addr ~addr_bits:64 0L Hike.Synth.empty in
  let exp = Bil.Load (Bil.Var m, Bil.Var address, LittleEndian, `r64) in
  check "a stored self cell takes precedence over the ABI default"
    (match Vsa.Test_seam.denote_imm_exp ~synth exp env with
     | Ok v -> Ws.equal v data | Error _ -> false)

let () =
  run "hike_origin"
    [ pin "ORI-03" "the one-origin accessor" ori_03;

      pin "ORI-07" "store-to-load round-trip (frame)" ori_07;

      pin "ORI-18" "the D10 namespace test" ori_18;
      pin "ORI-19" "all origins retain identity and use their own facts" ori_19;
      pin "ORI-20" "plain arithmetic preserves high-bit words" ori_20;
      pin "ORI-22" "all-origin memory round trips and alias namespaces" ori_22;
      pin "ORI-23" "rounding crosses base-residue block boundaries" ori_23;
      pin "ORI-24" "difference preserves exact offsets and uncertain survivors" ori_24;
      pin "ORI-26"
        "certified-bit OR/XOR of a stack value stays relative; above the certified bits it is top"
        ori_26;
      pin "ORI-27"
        "a set-valued SP with a fixed decrement stays on the Stack origin"
        ori_27;
      pin "ORI-28" "FS self pointer survives arithmetic and a stack spill" ori_28;
      pin "ORI-29" "FS algebra keeps symbolic bases out of absolute constraints" ori_29;
      pin "ORI-30" "the ABI thread pointer survives a foreign call" ori_30;
      pin "ORI-31" "an explicit TCB self-cell write overrides its default" ori_31 ]
