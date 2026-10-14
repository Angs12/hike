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

(* ORI-01: the facts table — every origin's base sits on the segment
   line and carries the certified entry nibble; the VLA frame's clamps
   are the segment's own (its allocation lives on the frame line). *)
let ori_01 () =
  let st = Origin.facts Origin.Stack in
  let vl = Origin.facts (Origin.Vla (Tid.create ())) in
  check "stack base is the segment base"
    (Stdlib.Int64.equal st.Origin.base Origin.segment_base);
  check "entry nibble certified" (st.Origin.certified = 4);
  check "stack span is 8 MiB each way"
    (Stdlib.Int64.equal (Stdlib.Int64.sub st.Origin.hi st.Origin.lo)
       (Stdlib.Int64.mul 2L (Int64.shift_left 1L 23)));
  check "vla frame rides the segment span"
    (Stdlib.Int64.equal vl.Origin.base st.Origin.base
    && Stdlib.Int64.equal vl.Origin.lo st.Origin.lo
    && Stdlib.Int64.equal vl.Origin.hi st.Origin.hi)

(* ORI-02: the ADT is total and names every origin. *)
let ori_02 () =
  let all =
    [ Origin.Abs;
      Origin.Stack;
      Origin.Vla (Tid.create ());
      Origin.Rip Hike_section.Rodata ]
  in
  List.iter all ~f:(fun o ->
      let n = Origin.name o in
      check (sprintf "name %s nonempty" n) (String.length n > 0));
  check "four origins" (List.length all = 4);
  check "distinct tids are distinct origins"
    (not
       (Origin.equal (Origin.Vla (Tid.create ()))
          (Origin.Vla (Tid.create ()))));
  check "same tid is the same origin"
    (let t = Tid.create () in Origin.equal (Origin.Vla t) (Origin.Vla t))

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
type vla_fix = {
  vla_sub : sub term;
  vla_stamped : sub term;
  vla_dec : def term;
  vla_envs : (AI.t * AI.t) Tid.Map.t;
  vla_rsp : var;
  vla_rbp : var;
  vla_m : var;
}

let vla_fixture ?(copy = false) ~(frame : int) ~(sizes : int64 list)
    ~(after : var -> var -> var -> def term list) () : vla_fix =
  let m = memv "vla_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let rax = v64 "RAX" in
  let f = v1 "vla_f" in
  let frame_w = Cbat_word.to_word (w64 frame) in
  let w64_of (i : int64) = Cbat_word.to_word (i2w i) in
  let cell =
    Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 12)))
  in
  let dec = Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Var rax) in
  (* [copy]: the decrement goes through a temporary, [RCX := RSP - RAX;
     RSP := RCX]. *)
  let chain, def_dec =
    if copy then
      let rcx = v64 "RCX" in
      let d = Def.create rsp (Bil.Var rcx) in
      ([ Def.create rcx dec; d ], d)
    else
      let d = Def.create rsp dec in
      ([ d ], d)
  in
  let body =
    [ Def.create rbp (Bil.Var rsp);
      Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int frame_w));
      Def.create m
        (Bil.Store
           ( Bil.Var m,
             cell,
             Bil.Cast (Bil.LOW, 32, Bil.Var rax),
             LittleEndian,
             `r32 ));
      Def.create rax
        (Bil.Load (Bil.Var m, cell, LittleEndian, Size.of_int_exn 32)) ]
    @ chain
    @ after rsp rbp m
  in
  (* Two guarded edges carry the size set into the merge block. *)
  let lo = List.hd_exn sizes in
  let hi = List.nth sizes 1 |> Option.value ~default:lo in
  let sub =
    fst
      (sub_of "vla_fix"
         [ [ Def.create rax (Bil.Int (w64_of lo)) ],
           [ (2, fun t -> mk_jmp_to t (Bil.Var f)); (1, mk_goto) ];
           [ Def.create rax (Bil.Int (w64_of hi)) ],
           [ (2, mk_goto) ];
           body, [ (3, mk_goto) ];
           [], [ (2, mk_ret) ] ])
  in
  let entry = anchored_entry () in
  let sol =
    static_graph_vsa ~abi sub
      (Vsa.init_sol ~abi ~entry sub)
  in
  let envs, stamped = Vsa.stamp_envs_of_sol ~sol sub in
  { vla_sub = sub; vla_stamped = stamped; vla_dec = def_dec;
    vla_envs = envs; vla_rsp = rsp; vla_rbp = rbp; vla_m = m }

(* The frame block's tid — the block holding the decrement def. *)
let body_tid (fix : vla_fix) : Tid.t option =
  Term.enum blk_t fix.vla_sub
  |> Seq.find ~f:(fun b ->
         Term.enum def_t b
         |> Seq.exists ~f:(fun d -> Tid.equal (Term.tid d) (Term.tid fix.vla_dec)))
  |> Base.Option.map ~f:Term.tid

(* The def's stamped origin through the seam, by lhs name inside the
   frame block (the branches define their own RAX). *)
let post_word_named (fix : vla_fix) (name : string) : Ws.t option =
  Base.Option.bind (body_tid fix) ~f:(fun btid ->
      Core.Map.find fix.vla_envs btid
      |> Base.Option.map ~f:(fun (_, post) ->
             AI.find_word 64 post (v64 name)))

(* ORI-09: the seed — the dynamic decrement opens the VLA frame named
   by the def's own tid; the value is the allocation base
   (frame-relative 0) and the extent records the gate and the base's
   entry-line range. *)
let ori_09 () =
  let fix =
    vla_fixture ~frame:16 ~sizes:[ 16L; 32L ] ~after:(fun _ _ _ -> []) ()
  in
  let tid = Term.tid fix.vla_dec in
  check "decrement def stamps its own Vla frame"
    (Base.Option.bind (Term.find blk_t fix.vla_stamped (Base.Option.value_exn (body_tid fix)))
       ~f:(fun blk ->
             Term.enum def_t blk
             |> Seq.fold ~init:None ~f:(fun acc d ->
                    if Tid.equal (Term.tid d) tid then
                      Vsa.Def_origin.def_origin d
                    else acc))
     |> fun o -> Option.equal Origin.equal o (Some (Origin.Vla tid)));
  check "the post value is the allocation base, materialised to its entry-line range"
    (Base.Option.value_map (post_word_named fix "RSP") ~default:false
       ~f:(fun ws ->
         Option.equal Origin.equal (Ws.origin ws) (Some (Origin.Vla tid))
         &&
         match Ws.stack_bounds ws with
         | Some (lo, hi) ->
             Stdlib.Int64.equal lo (-48L) && Stdlib.Int64.equal hi (-32L)
         | None -> false));
  check "the extent records the frame gate and the base range"
    (match Origin.Vla_seed.extent tid with
     | Some e ->
       Stdlib.Int64.equal e.Origin.off_lo 0L
       && Option.equal Int64.equal e.Origin.off_hi (Some 32L)
       && Option.equal Int64.equal e.Origin.base_lo (Some (-48L))
       && Option.equal Int64.equal e.Origin.base_hi (Some (-32L))
     | None -> false)

(* ORI-10: +INT inside the extent shifts the frame-relative offsets
   exactly and keeps the frame. *)
let ori_17 () =
  let before = Ws.stack_word_i64 0L in
  let singleton = Ws.sub before (Ws.stack_word_i64 16L) in
  check "a singleton move is not a VLA event"
    (Option.is_none (Vsa.vla_event ~before ~after:singleton));
  let top = Ws.sub before (Ws.top 64) in
  check "a TOP size is a VLA event"
    (match Vsa.vla_event ~before ~after:top with
     | Some e -> Stdlib.Int64.equal e.Hike_origin.off_lo 0L
                 && Option.is_none e.Hike_origin.off_hi
                 && Option.is_none e.Hike_origin.base_lo
     | None -> false);
  let inf =
    Ws.stack_word
      (Clp.create_descending ~width:64 ~base:(w64 (-8)) ~step:(w64 1))
  in
  check "a directional-infinite size is a VLA event"
    (match Vsa.vla_event ~before ~after:inf with
     | Some e -> Option.is_none e.Hike_origin.off_hi
     | None -> false)

(* ORI-18: the D10 namespace test — the stack-line origins answer
   true; a plain or module-relative origin answers false. *)
let ori_18 () =
  check "Stack names the stack line" (Origin.names_stack_line Origin.Stack);
  check "a VLA frame names the stack line"
    (Origin.names_stack_line (Origin.Vla (Tid.create ())));
  check "an absolute origin names no stack line"
    (not (Origin.names_stack_line Origin.Abs));
  check "a module-relative origin names no stack line"
    (not (Origin.names_stack_line (Origin.Rip Hike_section.Rodata)))

let ori_19 () =
  let origins =
    [ Origin.Abs; Origin.Stack; Origin.Rip Hike_section.Rodata;
      Origin.Rip Hike_section.Data; Origin.Vla (Tid.create ()); Origin.Vla (Tid.create ()) ]
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
  List.iter [ Origin.Abs; region; Origin.Stack; Origin.Vla (Tid.create ()) ] ~f:(fun o ->
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

let ori_21 () =
  let plain k = Ws.singleton (i2w k) in
  let tid = Tid.create () in
  let frame = Ws.vla_frame tid in
  Origin.Vla_seed.record tid
    { Origin.off_lo = 0L; off_hi = Some 32L;
      base_lo = Some (-31L); base_hi = Some (-31L) };
  check "VLA certified bits include the allocation base residue"
    (Ws.equal (Ws.logand frame (plain 15L)) (plain 9L));
  Origin.Vla_seed.record tid
    { Origin.off_lo = 0L; off_hi = Some 32L;
      base_lo = Some (-31L); base_hi = Some (-16L) };
  check "a variable VLA base has no assumed alignment"
    (Ws.is_top (Ws.logand frame (plain 15L)));
  let rounded = Ws.logand frame (plain (-4L)) in
  check "unknown-residue rounding preserves origin with possible slack"
    (Option.equal Origin.equal (Ws.origin rounded) (Some (Origin.Vla tid))
     && Option.value_map (Ws.vla_offsets rounded) ~default:false
          ~f:(fun offs -> Clp.elem (i2w (-3L)) offs && Clp.elem (i2w 0L) offs));
  check "a runtime base is not a complete concrete enumeration"
    (Option.is_none (Ws.enumerate ~cap:100 frame));
  Origin.Vla_seed.reset ()

let ori_22 () =
  let tid = Tid.create () in
  Origin.Vla_seed.record tid
    { Origin.off_lo = 0L; off_hi = Some 32L;
      base_lo = Some 0L; base_hi = Some 0L };
  let origins =
    [ Origin.Abs; Origin.Stack; Origin.Rip Hike_section.Rodata; Origin.Vla tid ] in
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
               (Origin.equal (Ws.key_line a) (Ws.key_line b)))));
  Origin.Vla_seed.reset ()

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
    [ Origin.Stack; Origin.Rip Hike_section.Rodata; Origin.Vla (Tid.create ()) ] in
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

(* ORI-25: the copy chain's producer opens the frame — the temporary
   and the SP it reaches carry it, and an access through the temporary
   routes into the allocation. *)
let ori_25 () =
  let rcx = v64 "RCX" in
  let fix =
    vla_fixture ~copy:true ~frame:16 ~sizes:[ 16L; 32L ]
      ~after:(fun _ _ m ->
        [ Def.create m
            (Bil.Store
               ( Bil.Var m,
                 Bil.BinOp
                   (Bil.PLUS, Bil.Var rcx, Bil.Int (Cbat_word.to_word (w64 8))),
                 Bil.Int (Cbat_word.to_word (Cbat_word.of_int ~width:32 5)),
                 LittleEndian,
                 `r32 )) ])
      ()
  in
  let producer =
    Term.enum blk_t fix.vla_sub |> Seq.concat_map ~f:(Term.enum def_t)
    |> Seq.find ~f:(fun d -> Var.equal (Def.lhs d) rcx)
    |> Option.value_exn |> Term.tid
  in
  let frame ws = Option.equal Origin.equal (Ws.origin ws) (Some (Origin.Vla producer)) in
  check "the temporary and SP carry the producer's frame"
    (Option.value_map (post_word_named fix "RCX") ~default:false ~f:frame
     && Option.value_map (post_word_named fix "RSP") ~default:false ~f:frame);
  check "the SP def confirms it; no second allocation opens"
    (Core.Set.equal (Origin.Vla_seed.allocations ())
       (Core.Set.singleton (module Tid) producer));
  check "an access through the temporary routes into the allocation"
    (Base.Option.bind
       (Term.find blk_t fix.vla_stamped (Base.Option.value_exn (body_tid fix)))
       ~f:(fun blk ->
         Term.enum def_t blk
         |> Seq.find ~f:(fun d ->
                match Def.rhs d with
                | Bil.Store (_, Bil.BinOp (Bil.PLUS, _, _), _, _, _) -> true
                | _ -> false)
         |> Base.Option.bind ~f:Vsa.Def_origin.def_origin)
     |> fun o -> Option.equal Origin.equal o (Some (Origin.Vla producer)))

let () =
  run "hike_origin"
    [ pin "ORI-01" "the facts table" ori_01;
      pin "ORI-02" "the ADT is total" ori_02;
      pin "ORI-03" "the one-origin accessor" ori_03;

      pin "ORI-07" "store-to-load round-trip (frame)" ori_07;

      pin "ORI-09" "the VLA seed (Vla T at the true positions)" ori_09;







      pin "ORI-17" "the D1 shape predicate (singleton / TOP / infinite)" ori_17;
      pin "ORI-18" "the D10 namespace test" ori_18;
      pin "ORI-19" "all origins retain identity and use their own facts" ori_19;
      pin "ORI-20" "absolute-origin arithmetic preserves bits" ori_20;
      pin "ORI-21" "VLA operations require certified base bits" ori_21;
      pin "ORI-22" "all-origin memory round trips and alias namespaces" ori_22;
      pin "ORI-23" "rounding crosses base-residue block boundaries" ori_23;
      pin "ORI-24" "difference preserves exact offsets and uncertain survivors" ori_24;
      pin "ORI-25" "the copy chain's producer opens the frame" ori_25 ]
