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

(* ORI-01: the facts table — the stack base sits on the segment line and
   carries the certified entry nibble. *)
let ori_01 () =
  let st = Origin.facts Origin.Stack in
  check "stack base is the segment base"
    (Stdlib.Int64.equal st.Origin.base Origin.segment_base);
  check "entry nibble certified" (st.Origin.certified = 4);
  check "stack span is 8 MiB each way"
    (Stdlib.Int64.equal (Stdlib.Int64.sub st.Origin.hi st.Origin.lo)
       (Stdlib.Int64.mul 2L (Int64.shift_left 1L 23)))

(* ORI-02: the ADT is total and names every origin. *)
let ori_02 () =
  let all =
    [ Origin.Abs;
      Origin.Stack;
      Origin.Rip Hike_section.Rodata ]
  in
  List.iter all ~f:(fun o ->
      let n = Origin.name o in
      check (sprintf "name %s nonempty" n) (String.length n > 0));
  check "three origins" (List.length all = 3)

(* The accessor's name answer, for the pin asserts. *)
let origin_name (o : Origin.t option) : string option =
  Option.map ~f:Origin.name o

(* ORI-03: the one-origin accessor — a stack value reads Stack, plain
   values read None, a mixed union reads None. *)
let ori_03 () =
  let stk = Ws.stack_word_i64 (-8L) in
  check "stack value reads Stack" (Option.equal String.equal (origin_name (Ws.origin stk)) (Some "stack"));
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
    static_graph_vsa ~abi sub
      (Vsa.init_sol ~abi ~entry sub)
  in
  let _, stamped = Vsa.stamp_envs_of_sol ~sol sub in
  let blk = Term.enum blk_t stamped |> Seq.to_list |> List.hd_exn in
  let defs = Term.enum def_t blk |> Seq.to_list in
  match List.rev defs with
  | load_def :: _ -> Vsa.Def_origin.def_origin load_def
  | _ -> None

(* ORI-07: a frame pointer stored to a cell reads back Stack. *)
let ori_07 () =
  check "stored frame pointer reads back Stack"
    (Option.equal Origin.equal (round_trip (-8L)) (Some Origin.Stack))

(* ORI-08: a caller-frame pointer (a Stack value at/above the word)
   stored to a cell reads back Stack. *)
(* ORI-18: the D10 namespace test — the stack-line origins answer
   true; a plain or module-relative origin answers false. *)
let ori_18 () =
  check "Stack names the stack line" (Origin.names_stack_line Origin.Stack);
  check "an absolute origin names no stack line"
    (not (Origin.names_stack_line Origin.Abs));
  check "a module-relative origin names no stack line"
    (not (Origin.names_stack_line (Origin.Rip Hike_section.Rodata)))

let ori_19 () =
  let origins =
    [ Origin.Abs; Origin.Stack; Origin.Rip Hike_section.Rodata;
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
           (if Origin.equal a Origin.Abs then None else Some a)));
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
  List.iter [ Origin.Abs; region; Origin.Stack ] ~f:(fun o ->
      check "memory namespace follows the carried origin"
        (match Ws.address_groups (value o) with
         | [ (key, _) ] -> Origin.equal key (Ws.key_line o)
         | _ -> false))

let ori_20 () =
  let abs k = Ws.set_origin Origin.Abs (Ws.stack_word_i64 k) in
  let plain k = Ws.singleton (i2w k) in
  List.iter [ 3L; -1L; Stdlib.Int64.min_int ] ~f:(fun k ->
      check "Abs union preserves exact absolute bits"
        (Ws.equal (Ws.union (abs k) (plain k)) (plain k));
      check "Abs multiplication uses absolute arithmetic"
        (Ws.equal (Ws.mul (abs k) (plain 2L)) (Ws.mul (plain k) (plain 2L)));
      check "Abs negation uses absolute arithmetic"
        (Ws.equal (Ws.neg (abs k)) (Ws.neg (plain k))))

let ori_22 () =
  let origins =
    [ Origin.Abs; Origin.Stack; Origin.Rip Hike_section.Rodata ] in
  let value o = Ws.set_origin o (Ws.stack_word_i64 0L) in
  let key ws = List.hd_exn (Mem.Key.of_wordset ws) in
  let cell = key (Ws.singleton (i2w 0x1000L)) in
  List.iter origins ~f:(fun a ->
      let data = value a in
      let mem = Mem.add
          (Mem.top { Mem.addr_width = 64; addressable_width = 8 })
          ~key:cell ~data:(Mem.Val.create data LittleEndian) in
      let loaded = Mem.Val.data (Mem.find (64, LittleEndian) mem cell) in
      check ("full-width memory preserves " ^ Origin.name a) (Ws.equal data loaded);
      List.iter origins ~f:(fun b ->
          check "memory aliases only the explicit shared coordinate line"
            (Bool.equal (Mem.Key.overlap (key data) (key (value b)))
               (Origin.equal (Ws.key_line a) (Ws.key_line b)))))

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
   the exact shifted set. *)
let ori_27 () =
  let m = memv "ori27_m" in
  ignore m;
  let rsp = v64 "RSP" and rax = v64 "RAX" in
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
    static_graph_vsa ~abi sub (Vsa.init_sol ~abi ~entry sub)
  in
  let envs, _ = Vsa.stamp_envs_of_sol ~sol sub in
  let post =
    Core.Map.data envs
    |> List.map ~f:(fun (_, post) -> AI.find_word 64 post rsp)
    |> List.filter ~f:(fun ws -> Option.is_some (Ws.stack_offsets ws)
                                 && not (Ws.is_top ws))
  in
  check "SP stays on the Stack origin through the fixed decrement"
    (List.for_all post ~f:(fun ws ->
         Option.equal Origin.equal (Ws.origin ws) (Some Origin.Stack)));
  check "the final SP is exactly the two shifted positions"
    (List.exists post ~f:(fun ws ->
         Option.value_map (Ws.stack_offsets ws) ~default:false ~f:(fun offs ->
             Clp.elem (i2w (-4128L)) offs && Clp.elem (i2w (-4112L)) offs
             && not (Clp.elem (i2w (-4120L)) offs))))

let () =
  run "hike_origin"
    [ pin "ORI-01" "the facts table" ori_01;
      pin "ORI-02" "the ADT is total" ori_02;
      pin "ORI-03" "the one-origin accessor" ori_03;

      pin "ORI-07" "store-to-load round-trip (frame)" ori_07;








      pin "ORI-18" "the D10 namespace test" ori_18;
      pin "ORI-19" "all origins retain identity and use their own facts" ori_19;
      pin "ORI-20" "absolute-origin arithmetic preserves bits" ori_20;
      pin "ORI-22" "all-origin memory round trips and alias namespaces" ori_22;
      pin "ORI-23" "rounding crosses base-residue block boundaries" ori_23;
      pin "ORI-24" "difference preserves exact offsets and uncertain survivors" ori_24;
      pin "ORI-26"
        "certified-bit OR/XOR of a stack value stays relative; above the certified bits it is top"
        ori_26;
      pin "ORI-27"
        "a set-valued SP with a fixed decrement stays on the Stack origin"
        ori_27 ]
