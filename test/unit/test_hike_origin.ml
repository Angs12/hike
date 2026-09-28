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
  let wn = Origin.facts Origin.Window in
  check "stack base is the segment base"
    (Stdlib.Int64.equal st.Origin.base Origin.segment_base);
  check "entry nibble certified" (st.Origin.certified = 4);
  check "stack span is 8 MiB each way"
    (Stdlib.Int64.equal (Stdlib.Int64.sub st.Origin.hi st.Origin.lo)
       (Stdlib.Int64.mul 2L (Int64.shift_left 1L 23)));
  check "vla frame rides the segment span"
    (Stdlib.Int64.equal vl.Origin.base st.Origin.base
    && Stdlib.Int64.equal vl.Origin.lo st.Origin.lo
    && Stdlib.Int64.equal vl.Origin.hi st.Origin.hi);
  check "window is the positive side" (Stdlib.Int64.compare wn.Origin.lo 0L > 0)

(* ORI-02: the ADT is total and names every origin. *)
let ori_02 () =
  let all =
    [ Origin.Abs;
      Origin.Stack;
      Origin.Vla (Tid.create ());
      Origin.Window;
      Origin.Rip ]
  in
  List.iter all ~f:(fun o ->
      let n = Origin.name o in
      check (sprintf "name %s nonempty" n) (String.length n > 0));
  check "five origins" (List.length all = 5);
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

(* ORI-04: same-origin unions keep the origin. *)
let ori_04 () =
  let a = Ws.stack_word_i64 (-8L) in
  let b = Ws.stack_word_i64 (-16L) in
  check "stack union reads Stack"
    (Option.equal String.equal (origin_name (Ws.origin (Ws.union a b))) (Some "stack"));
  check "stack meet reads Stack"
    (Option.equal String.equal (origin_name (Ws.origin (Ws.intersection a b))) (Some "stack"))

(* ORI-05: the solve-boundary refinement — window-side values name the
   caller's frame, a VLA-frame value inside its extent keeps the
   frame, and one crossing out re-absorbs onto the entry line. *)
let ori_05 () =
  let window_side = Ws.stack_word_i64 16L in
  let refined = Ws.refine_origin ~word:8 window_side in
  check "window-side value refines to Window"
    (Option.equal Origin.equal (Ws.origin refined) (Some Origin.Window));
  let frame = Ws.stack_word_i64 (-8L) in
  check "below-entry value keeps Stack"
    (Option.equal Origin.equal (Ws.origin (Ws.refine_origin ~word:8 frame)) (Some Origin.Stack));
  let tid = Tid.create () in
  let base = Hike.Stack_model.segment_base in
  Origin.Vla_seed.record tid
    (Stdlib.Int64.add base 8L, Stdlib.Int64.add base 32L);
  let inside =
    Ws.set_origin (Origin.Vla tid) (Ws.stack_word_i64 16L)
    |> Ws.refine_origin ~word:8
  in
  check "in-extent vla value keeps its frame"
    (Option.equal Origin.equal (Ws.origin inside) (Some (Origin.Vla tid)));
  let below =
    Ws.set_origin (Origin.Vla tid) (Ws.stack_word_i64 (-8L))
    |> Ws.refine_origin ~word:8
  in
  check "crossed-out vla value re-absorbs to Stack"
    (Option.equal Origin.equal (Ws.origin below) (Some Origin.Stack));
  let crossing =
    Ws.union (Ws.stack_word_i64 0L) (Ws.stack_word_i64 16L)
  in
  check "value spanning the entry line keeps Stack"
    (Option.equal Origin.equal (Ws.origin (Ws.refine_origin ~word:8 crossing)) (Some Origin.Stack));
  let plain = Ws.singleton (i2w 5L) in
  check "plain values pass through unchanged"
    (Option.is_none (Ws.origin (Ws.refine_origin ~word:8 plain)))

(* ORI-06: the per-def origin slot, stamped at the solve boundary — a
   window-side address def reads Window through the seam. *)
let ori_06 () =
  let rsp = Var.create ~is_virtual:false ~fresh:false "RSP" (Type.Imm 64) in
  let p = Var.create ~is_virtual:false ~fresh:false "ori_p" (Type.Imm 64) in
  let defs =
    [ Def.create p
        (Bil.BinOp (Bil.PLUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (i2w 16L)))) ]
  in
  let sub = straight_sub "ori_stamp" defs in
  let entry = anchored_entry () in
  let sol =
    Vsa.static_graph_vsa ~abi (Program.create ~subs:[ sub ] ()) sub
      (Vsa.init_sol ~abi ~entry sub)
  in
  let _, stamped = Vsa.stamp_envs_of_sol ~sol sub in
  let blk = Term.enum blk_t stamped |> Seq.to_list |> List.hd_exn in
  let d = Term.enum def_t blk |> Seq.to_list |> List.hd_exn in
  check "window-side def stamps Window"
    (Option.equal Origin.equal (Vsa.Def_origin.def_origin d) (Some Origin.Window))


(* The store-to-load round-trip: a relative value stored to a cell
   reads back with its origin.  [offs] is the pointer's offset (the
   cell address too): negative = the sub's frame (Stack), positive =
   the caller's window (Window). *)
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
    Vsa.static_graph_vsa ~abi (Program.create ~subs:[ sub ] ()) sub
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

(* ORI-08: a caller-window pointer stored to a cell reads back Window. *)
let ori_08 () =
  check "stored window pointer reads back Window"
    (Option.equal Origin.equal (round_trip 16L) (Some Origin.Window))

(* The VLA fixture: a runtime-size set joins at a merge block, the
   literal frame decrement opens the static frame, and the dynamic
   decrement seeds the VLA frame.  [after] extends the frame block's
   defs. *)
type vla_fix = {
  vla_sub : sub term;
  vla_stamped : sub term;
  vla_dec : def term;
  vla_envs : (AI.t * AI.t) Tid.Map.t;
  vla_rsp : var;
  vla_rbp : var;
  vla_m : var;
}

let vla_fixture ~(frame : int) ~(sizes : int64 list)
    ~(after : var -> var -> var -> def term list) : vla_fix =
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
  let def_dec =
    Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Var rax))
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
        (Bil.Load (Bil.Var m, cell, LittleEndian, Size.of_int_exn 32));
      def_dec ]
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
    Vsa.static_graph_vsa ~abi (Program.create ~subs:[ sub ] ()) sub
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
let stamped_origin (fix : vla_fix) (name : string) : Origin.t option =
  Base.Option.bind (body_tid fix) ~f:(fun btid ->
      Base.Option.bind (Term.find blk_t fix.vla_stamped btid) ~f:(fun blk ->
          Term.enum def_t blk
          |> Seq.fold ~init:None ~f:(fun acc d ->
                 if String.equal (Var.name (Def.lhs d)) name then
                   Vsa.Def_origin.def_origin d
                 else acc)))

(* The frame block's post-env word for a var name. *)
let post_word_named (fix : vla_fix) (name : string) : Ws.t option =
  Base.Option.bind (body_tid fix) ~f:(fun btid ->
      Core.Map.find fix.vla_envs btid
      |> Base.Option.map ~f:(fun (_, post) ->
             AI.find_word 64 post (v64 name)))

(* ORI-09: the seed — the dynamic decrement's value opens the VLA
   frame named by the def's own tid, at the TRUE entry-line
   positions, with the extent recorded. *)
let ori_09 () =
  let fix = vla_fixture ~frame:16 ~sizes:[ 16L; 32L ] ~after:(fun _ _ _ -> []) in
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
  check "the post value carries the true positions"
    (Base.Option.value_map (post_word_named fix "RSP") ~default:false
       ~f:(fun ws ->
         Option.equal Origin.equal (Ws.origin ws) (Some (Origin.Vla tid))
         &&
         match Ws.stack_bounds ws with
         | Some (lo, hi) ->
             Stdlib.Int64.equal lo (-48L) && Stdlib.Int64.equal hi (-32L)
         | None -> false));
  let base = Hike.Stack_model.segment_base in
  check "the extent covers [frame+min size, frame)"
    (Base.Option.equal
       (fun (a, b) (c, d) -> Stdlib.Int64.equal a c && Stdlib.Int64.equal b d)
       (Origin.Vla_seed.extent tid)
       (Some (Stdlib.Int64.sub base 48L, Stdlib.Int64.sub base 17L)))

(* ORI-10: +INT inside the extent shifts the offsets exactly and
   keeps the frame. *)
let ori_10 () =
  let fix =
    vla_fixture ~frame:16 ~sizes:[ 32L ]
      ~after:(fun rsp _ _ ->
        [ Def.create (v64 "RAX")
            (Bil.BinOp
               (Bil.PLUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 12))));
          Def.create (v64 "RBX")
            (Bil.BinOp
               (Bil.PLUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 24)))) ])
  in
  let tid = Term.tid fix.vla_dec in
  let keeps name at =
    Base.Option.value_map (post_word_named fix name) ~default:false
       ~f:(fun ws ->
         Option.equal Origin.equal (Ws.origin ws) (Some (Origin.Vla tid))
         &&
         match Ws.stack_bounds ws with
         | Some (l, h) -> Stdlib.Int64.equal l at && Stdlib.Int64.equal h at
         | None -> false)
  in
  check "rsp+12 keeps the frame at -36" (keeps "RAX" (-36L));
  check "rsp+24 keeps the frame at -24" (keeps "RBX" (-24L))

(* ORI-11: a value crossing out of the extent re-absorbs to Stack at
   the boundary. *)
let ori_11 () =
  let fix =
    vla_fixture ~frame:16 ~sizes:[ 32L ]
      ~after:(fun rsp _ _ ->
        [ Def.create (v64 "RAX")
            (Bil.BinOp
               (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 12)))) ])
  in
  check "rsp-12 (past the extent's bottom) stamps Stack"
    (Option.equal Origin.equal (stamped_origin fix "RAX") (Some Origin.Stack));
  check "the positions are unchanged entry-line offsets"
    (Base.Option.value_map (post_word_named fix "RAX") ~default:false
       ~f:(fun ws ->
         Option.equal Origin.equal (Ws.origin ws) (Some Origin.Stack)
         &&
         match Ws.stack_bounds ws with
         | Some (l, h) -> Stdlib.Int64.equal l (-60L) && Stdlib.Int64.equal h (-60L)
         | None -> false))

(* ORI-12: same-frame unions stay exact; different frames
   materialise. *)
let ori_12 () =
  let a = Ws.set_origin (Origin.Vla (Tid.create ())) (Ws.stack_word_i64 (-20L)) in
  let b = Ws.set_origin (Origin.Vla (Tid.create ())) (Ws.stack_word_i64 (-8L)) in
  check "same-frame union keeps the frame"
    (let t = Tid.create () in
     let u =
       Ws.union
         (Ws.set_origin (Origin.Vla t) (Ws.stack_word_i64 (-20L)))
         (Ws.set_origin (Origin.Vla t) (Ws.stack_word_i64 (-8L)))
     in
     Option.equal Origin.equal (Ws.origin u) (Some (Origin.Vla t)));
  check "different-frame union materialises"
    (Option.is_none (Ws.origin (Ws.union a b)))

(* ORI-13: a VLA value unioned with a Stack value wraps at Stack. *)
let ori_13 () =
  let t = Tid.create () in
  let u =
    Ws.union
      (Ws.set_origin (Origin.Vla t) (Ws.stack_word_i64 (-20L)))
      (Ws.stack_word_i64 (-8L))
  in
  check "vla+stack union reads Stack"
    (Option.equal Origin.equal (Ws.origin u) (Some Origin.Stack));
  check "the offsets keep both runs"
    (match Ws.stack_bounds u with
     | Some (lo, hi) ->
         Stdlib.Int64.equal lo (-20L) && Stdlib.Int64.equal hi (-8L)
     | None -> false)

(* ORI-14: a VLA pointer stored to a cell reads back its frame and
   tid — the round trip the through-pointer accesses route by. *)
let ori_14 () =
  let rcx = v64 "RCX" in
  let fix =
    vla_fixture ~frame:16 ~sizes:[ 32L ]
      ~after:(fun rsp rbp m ->
        [ Def.create m
            (Bil.Store
               ( Bil.Var m,
                 Bil.BinOp
                   (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))),
                 Bil.Var rsp,
                 LittleEndian,
                 `r64 ));
          Def.create rcx
            (Bil.Load
               ( Bil.Var m,
                 Bil.BinOp
                   (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))),
                 LittleEndian,
                 `r64 )) ])
  in
  let tid = Term.tid fix.vla_dec in
  check "the saved pointer reads back its frame and tid"
    (Option.equal Origin.equal (stamped_origin fix "RCX")
       (Some (Origin.Vla tid)))

let () =
  run "hike_origin"
    [ pin "ORI-01" "the facts table" ori_01;
      pin "ORI-02" "the ADT is total" ori_02;
      pin "ORI-03" "the one-origin accessor" ori_03;
      pin "ORI-04" "same-origin ops keep the origin" ori_04;
      pin "ORI-05" "the boundary refinement" ori_05;
      pin "ORI-06" "the per-def origin stamp" ori_06;
      pin "ORI-07" "store-to-load round-trip (frame)" ori_07;
      pin "ORI-08" "store-to-load round-trip (window)" ori_08;
      pin "ORI-09" "the VLA seed (Vla T at the true positions)" ori_09;
      pin "ORI-10" "+INT/-INT inside the extent" ori_10;
      pin "ORI-11" "crossing out flips to Stack" ori_11;
      pin "ORI-12" "same-frame exact / different-frame materialise" ori_12;
      pin "ORI-13" "vla+stack union wraps at Stack" ori_13;
      pin "ORI-14" "store-to-load round-trip (VLA)" ori_14 ]
