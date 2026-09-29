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
   caller's frame; a VLA frame keeps its origin (the routing gate
   decides routability at the stamp, not here). *)
let ori_05 () =
  let window_side = Ws.stack_word_i64 16L in
  let refined = Ws.refine_origin ~word:8 window_side in
  check "window-side value refines to Window"
    (Option.equal Origin.equal (Ws.origin refined) (Some Origin.Window));
  let frame = Ws.stack_word_i64 (-8L) in
  check "below-entry value keeps Stack"
    (Option.equal Origin.equal (Ws.origin (Ws.refine_origin ~word:8 frame)) (Some Origin.Stack));
  let tid = Tid.create () in
  Origin.Vla_seed.record tid
    { Origin.off_lo = 0L; off_hi = Some 32L;
      base_lo = Some (-48L); base_hi = Some (-32L) };
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
  check "an out-of-frame vla value keeps its frame"
    (Option.equal Origin.equal (Ws.origin below) (Some (Origin.Vla tid)));
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

(* ORI-09: the seed — the dynamic decrement opens the VLA frame named
   by the def's own tid; the value is the allocation base
   (frame-relative 0) and the extent records the gate and the base's
   entry-line range. *)
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
let ori_10 () =
  let fix =
    vla_fixture ~frame:16 ~sizes:[ 16L; 32L ]
      ~after:(fun rsp _ _ ->
        [ Def.create (v64 "RAX")
            (Bil.BinOp
               (Bil.PLUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 12))));
          Def.create (v64 "RBX")
            (Bil.BinOp
               (Bil.PLUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 24)))) ])
  in
  let tid = Term.tid fix.vla_dec in
  let keeps name lo hi =
    Base.Option.value_map (post_word_named fix name) ~default:false
       ~f:(fun ws ->
         Option.equal Origin.equal (Ws.origin ws) (Some (Origin.Vla tid))
         &&
         match Ws.stack_bounds ws with
         | Some (l, h) -> Stdlib.Int64.equal l lo && Stdlib.Int64.equal h hi
         | None -> false)
  in
  check "rsp+12 keeps the frame at the shifted range" (keeps "RAX" (-36L) (-20L));
  check "rsp+24 keeps the frame at the shifted range" (keeps "RBX" (-24L) (-8L))

(* ORI-11: a value crossing below the gate is refused at the origin
   stamp (Abs); the frame-relative value keeps its frame raw. *)
let ori_11 () =
  let fix =
    vla_fixture ~frame:16 ~sizes:[ 16L; 32L ]
      ~after:(fun rsp _ _ ->
        [ Def.create (v64 "RAX")
            (Bil.BinOp
               (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 12)))) ])
  in
  check "rsp-12 (below the gate) stamps Abs"
    (Option.equal Origin.equal (stamped_origin fix "RAX") (Some Origin.Abs));
  check "the frame-relative value keeps its origin and materialises"
    (Base.Option.value_map (post_word_named fix "RAX") ~default:false
       ~f:(fun ws ->
         Option.equal Origin.equal (Ws.origin ws)
           (Some (Origin.Vla (Term.tid fix.vla_dec)))
         &&
         match Ws.stack_bounds ws with
         | Some (l, h) -> Stdlib.Int64.equal l (-60L) && Stdlib.Int64.equal h (-44L)
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

(* ORI-13: a VLA value unioned with an entry-line value materialises
   through the base range (the frames do not merge). *)
let ori_13 () =
  let t = Tid.create () in
  Origin.Vla_seed.record t
    { Origin.off_lo = 0L; off_hi = Some 32L;
      base_lo = Some 0L; base_hi = Some 0L };
  let u =
    Ws.union
      (Ws.set_origin (Origin.Vla t) (Ws.stack_word_i64 (-20L)))
      (Ws.stack_word_i64 (-8L))
  in
  check "vla+stack union materialises (no single origin)"
    (Option.is_none (Ws.origin u));
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
    vla_fixture ~frame:16 ~sizes:[ 16L; 32L ]
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
  check "the saved pointer value reads back its frame and tid"
    (Base.Option.value_map (post_word_named fix "RCX") ~default:false
       ~f:(fun ws -> Option.equal Origin.equal (Ws.origin ws) (Some (Origin.Vla tid))))


(* ORI-15 (experiment): a VLA pointer saved before a machine call reads
   back its frame after it — the call keep reads the VLA-frame SP's own
   extent. *)
let ori_15 () =
  let rcx = v64 "RCX" in
  let callee = mk_selfloop_callee "vla_callee" in
  let after rsp rbp m =
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
             `r64 )) ]
  in
  ignore after;
  let m = memv "vla_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let rax = v64 "RAX" in
  let f = v1 "vla_f" in
  let frame_w = Cbat_word.to_word (w64 16) in
  let cell =
    Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 12)))
  in
  let def_dec =
    Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Var rax))
  in
  let save =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp
             (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))),
           Bil.Var rsp,
           LittleEndian,
           `r64 ))
  in
  let load =
    Def.create rcx
      (Bil.Load
         ( Bil.Var m,
           Bil.BinOp
             (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))),
           LittleEndian,
           `r64 ))
  in
  let lo = 32L in
  let hi = 16L in
  let w64_of (i : int64) = Cbat_word.to_word (i2w i) in
  let sub, tids =
    sub_of "vla_call"
      [ [ Def.create rax (Bil.Int (w64_of lo)) ],
        [ (2, fun t -> mk_jmp_to t (Bil.Var f)); (1, mk_goto) ];
        [ Def.create rax (Bil.Int (w64_of hi)) ],
        [ (2, mk_goto) ];
        [ Def.create rbp (Bil.Var rsp);
          Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int frame_w));
          Def.create m
            (Bil.Store
               ( Bil.Var m, cell,
                 Bil.Cast (Bil.LOW, 32, Bil.Var rax),
                 LittleEndian, `r32 ));
          Def.create rax
            (Bil.Load (Bil.Var m, cell, LittleEndian, Size.of_int_exn 32));
          def_dec;
          save ],
        [ (3, mk_goto) ];
        [],
        [ (4, fun t -> mk_call_jmp t (Term.tid callee)) ];
        [ load ],
        [ (0, mk_ret) ] ]
  in
  ignore sub;
  ignore tids;
  ignore (Term.tid def_dec);
  let entry = anchored_entry () in
  let prog = Program.create ~subs:[ sub; callee ] () in
  let sol =
    Vsa.static_graph_vsa ~abi prog sub (Vsa.init_sol ~abi ~entry sub)
  in
  let envs, stamped = Vsa.stamp_envs_of_sol ~sol sub in
  ignore stamped;
  (* The load's def stamp is its ADDRESS's origin (a frame cell); the
     loaded pointer VALUE keeps the VLA frame. *)
  let got =
    Term.enum blk_t sub
    |> Seq.find_map ~f:(fun blk ->
           if
             Term.enum def_t blk
             |> Seq.exists ~f:(fun d -> Var.equal (Def.lhs d) rcx)
           then
             Core.Map.find envs (Term.tid blk)
             |> Base.Option.map ~f:(fun (_, post) -> AI.find_word 64 post rcx)
             |> Base.Option.bind ~f:Ws.origin
           else None)
  in
  check "ORI-15 saved pointer survives the call"
    (Option.equal Origin.equal got
       (Some (Origin.Vla (Term.tid def_dec))))



(* ORI-16: the pointer load at a LOOP head — the join/widen of the back
   edge must keep the cell's VLA frame. *)
let ori_16 () =
  let rcx = v64 "RCX" in
  let callee = mk_selfloop_callee "vla_callee2" in
  let m = memv "vla_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let rax = v64 "RAX" in
  let f = v1 "vla_f" in
  let g = v1 "vla_g" in
  let ng = Bil.UnOp (Bil.NOT, Bil.Var g) in
  let frame_w = Cbat_word.to_word (w64 16) in
  let cell =
    Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 12)))
  in
  let def_dec =
    Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Var rax))
  in
  let save =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp
             (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))),
           Bil.Var rsp,
           LittleEndian,
           `r64 ))
  in
  let load =
    Def.create rcx
      (Bil.Load
         ( Bil.Var m,
           Bil.BinOp
             (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))),
           LittleEndian,
           `r64 ))
  in
  let w64_of (i : int64) = Cbat_word.to_word (i2w i) in
  let sub, _ =
    sub_of "vla_loop"
      [ [ Def.create rax (Bil.Int (w64_of 32L)) ],
        [ (2, fun t -> mk_jmp_to t (Bil.Var f)); (1, mk_goto) ];
        [ Def.create rax (Bil.Int (w64_of 16L)) ],
        [ (2, mk_goto) ];
        [ Def.create rbp (Bil.Var rsp);
          Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int frame_w));
          Def.create m
            (Bil.Store
               ( Bil.Var m, cell,
                 Bil.Cast (Bil.LOW, 32, Bil.Var rax),
                 LittleEndian, `r32 ));
          Def.create rax
            (Bil.Load (Bil.Var m, cell, LittleEndian, Size.of_int_exn 32));
          def_dec;
          save ],
        [ (3, mk_goto) ];
        [ load ],
        [ (4, fun t -> mk_jmp_to t ng); (5, mk_goto) ];
        [],
        [ (3, mk_goto) ];
        [],
        [ (3, mk_ret) ] ]
  in
  ignore sub;
  let entry = anchored_entry () in
  let prog = Program.create ~subs:[ sub; callee ] () in
  let sol = Vsa.static_graph_vsa ~abi prog sub (Vsa.init_sol ~abi ~entry sub) in
  let envs, stamped = Vsa.stamp_envs_of_sol ~sol sub in
  ignore stamped;
  let got =
    Term.enum blk_t sub
    |> Seq.find_map ~f:(fun blk ->
           if
             Term.enum def_t blk
             |> Seq.exists ~f:(fun d -> Var.equal (Def.lhs d) rcx)
           then
             Core.Map.find envs (Term.tid blk)
             |> Base.Option.map ~f:(fun (_, post) -> AI.find_word 64 post rcx)
             |> Base.Option.bind ~f:Ws.origin
           else None)
  in
  check "ORI-16 loop-head load keeps the frame"
    (Option.equal Origin.equal got (Some (Origin.Vla (Term.tid def_dec))))


(* ORI-17: the D1 predicate — a singleton move is a static frame adjust,
   a TOP size and a directional-infinite size are events. *)
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

(* ORI-18: the D10 namespace test — the three stack-line origins answer
   true; a plain or module-relative origin answers false. *)
let ori_18 () =
  check "Stack names the stack line" (Origin.names_stack_line Origin.Stack);
  check "Window names the stack line" (Origin.names_stack_line Origin.Window);
  check "a VLA frame names the stack line"
    (Origin.names_stack_line (Origin.Vla (Tid.create ())));
  check "an absolute origin names no stack line"
    (not (Origin.names_stack_line Origin.Abs));
  check "a module-relative origin names no stack line"
    (not (Origin.names_stack_line Origin.Rip))

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
      pin "ORI-14" "store-to-load round-trip (VLA)" ori_14;
      pin "ORI-15" "round-trip across a call" ori_15;
      pin "ORI-16" "round-trip across a loop" ori_16;
      pin "ORI-17" "the D1 shape predicate (singleton / TOP / infinite)" ori_17;
      pin "ORI-18" "the D10 namespace test" ori_18 ]
