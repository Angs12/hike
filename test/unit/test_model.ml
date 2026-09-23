(* The model/producer surface pins: the composed producer end-to-end, the
   layout from the finalized tree, stack-to-locals fission, the emitter's
   alloca shapes, the printable-run rule, and the Abi/Kb domains.  One
   Alcotest group per pin; each pin builds its own fixture, so no state
   crosses pins. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

module Abi = Hike.Abi

(* A register list names exactly [names]. *)
let names_are (vs : var list) (names : string list) : bool =
  Base.List.map vs ~f:(fun v -> Var.name v) = names

(* 64-bit literal word (native-int [w64] covers 63 bits only). *)
let q64 (v : int64) : Cbat_word.t = Cbat_word.of_int64 ~width:64 v

let minus_addr sp (off : int64) : exp =
  Bil.BinOp
    ( Bil.MINUS,
      Bil.Var sp,
      Bil.Int (Cbat_word.to_word (w64 (Int64.to_int off))) )

let tid_set (tids : tid list) : Tid.Set.t =
  List.fold_left (fun s t -> Core.Set.add s t) Tid.Set.empty tids

(* The def with the given tid in the sub. *)
let def_of_tid (sub : sub term) (dtid : tid) : def term option =
  Term.enum blk_t sub
  |> Seq.concat_map ~f:(Term.enum def_t)
  |> Seq.find ~f:(fun d -> Tid.equal (Term.tid d) dtid)

(* The def with the given lhs in the sub. *)
let def_of_lhs (sub : sub term) (v : var) : def term option =
  Term.enum blk_t sub
  |> Seq.concat_map ~f:(Term.enum def_t)
  |> Seq.find ~f:(fun d -> Var.equal (Def.lhs d) v)

(* The layout tree of a fixture sub. *)
let tree_of (sub : sub term) =
  let ctx = fixture_ctx [ sub ] in
  Base.Option.value_exn
    (Core.Map.find ctx.Hike.Sections.sub_trees (Term.tid sub))

(* The fixture stamp: the dyn-alloc facts and the layout tag onto the
   terms; the def's slim tag is stamped at the fixture site (the emitter
   consumes no record). *)
let stamp_shape
    ?(dynamic_alloc_tids : Tid.Set.t option)
    ~(layout : Sm.sub_layout)
    (sub : sub term) : sub term =
  let sub =
    Sm.stamp_dyn_allocs
      ~dynamic_alloc_tids:
        (Base.Option.value dynamic_alloc_tids ~default:Tid.Set.empty)
      sub
  in
  Sm.set_layout layout sub

(* The storage-free layout: no frame, no regions, no window. *)
let empty_layout : Sm.sub_layout =
  { regions = []; anchor = None; window_param = false }

(* Stamps the production tag onto a fixture def. *)
let tag_def (t : Sm.sec_tag) (d : def term) : def term = Sm.set_sec_tag t d

(* The stack-to-locals fixture mem var and its MINUS/rsp-rooted store. *)
let pr_c_m = memv "pr_c_m"

let mk_store off data (sz : size) : def term =
  Def.create pr_c_m
    (Bil.Store
       ( Bil.Var pr_c_m,
         minus_addr sp off,
         Bil.Int (Cbat_word.to_word (w64 data)),
         LittleEndian,
         sz ))

(* The [pr_b] layout fixture mem var, frame base, and MINUS/rbp load. *)
let pr_b_m = memv "pr_b_m"
let pr_b_rbp = v64 "RBP"

let pr_b_mk_ld name off : def term =
  Def.create (v64 name)
    (Bil.Load
       ( Bil.Var pr_b_m,
         Bil.BinOp
           ( Bil.MINUS,
             Bil.Var pr_b_rbp,
             Bil.Int (Cbat_word.to_word (q64 off)) ),
         LittleEndian,
         `r64 ))

(* The [pr_c] args fixture frame base and PLUS/rbp load. *)
let pr_c_rbp = v64 "RBP"

let pr_c_args_ld name off (sz : size) : def term =
  Def.create (v64 name)
    (Bil.Load
       ( Bil.Var pr_c_m,
         Bil.BinOp
           ( Bil.PLUS,
             Bil.Var pr_c_rbp,
             Bil.Int (Cbat_word.to_word (w64 off)) ),
         LittleEndian,
         sz ))

(* A SysV register by name. *)
let named n = Var.create ~is_virtual:false ~fresh:false n (Type.Imm 64)

let tests : unit Alcotest.test list =
  [
    (* Lane A: the producer record (the composed producer end-to-end). *)
    pin "MOD-01"
      "PR-A5: neither the literal decrement nor the chain-resolved constant is the event"
      (fun () ->
        let a5_rbx = v64 "pr_a5_rbx" in
        let a5_lit =
          Def.create sp
            (Bil.BinOp
               ( Bil.MINUS,
                 Bil.Var sp,
                 Bil.Int (Cbat_word.to_word (w64 0x28)) ))
        in
        let a5_rbx_def =
          Def.create a5_rbx (Bil.Int (Cbat_word.to_word (w64 0x80)))
        in
        let a5_bnd =
          Def.create sp (Bil.BinOp (Bil.MINUS, Bil.Var sp, Bil.Var a5_rbx))
        in
        let a5 = straight_sub "pr_a5_vla" [ a5_lit; a5_rbx_def; a5_bnd ] in
        check "MOD-01"
          (Core.Set.is_empty
             (Hike.Sections.dynamic_alloc_tids_of ~facts:top_facts a5)));

    pin "MOD-02"
      "PR-A5: the runtime-unbounded decrement is the event; the literal decrement is not"
      (fun () ->
        let a5_rcx = v64 "pr_a5_rcx" in
        let a5_vla =
          Def.create sp (Bil.BinOp (Bil.MINUS, Bil.Var sp, Bil.Var a5_rcx))
        in
        let a5u = straight_sub "pr_a5_vla_unb" [ a5_vla ] in
        let a5u_events =
          Hike.Sections.dynamic_alloc_tids_of ~facts:top_facts a5u
        in
        check "MOD-02"
          (Core.Set.equal a5u_events (tid_set [ Term.tid a5_vla ])));

    pin "MOD-03"
      "PR-A5: the dynamic-allocation fact rides the def's value through the stamp"
      (fun () ->
        let a5_rcx = v64 "pr_a5_rcx" in
        let a5_vla =
          Def.create sp (Bil.BinOp (Bil.MINUS, Bil.Var sp, Bil.Var a5_rcx))
        in
        let a5u = straight_sub "pr_a5_vla_unb" [ a5_vla ] in
        let a5u_events =
          Hike.Sections.dynamic_alloc_tids_of ~facts:top_facts a5u
        in
        let a5_stamped =
          Sm.stamp_dyn_allocs ~dynamic_alloc_tids:a5u_events a5u
        in
        check "MOD-03"
          (Sm.def_is_dyn_alloc
             (Base.Option.value_exn
                (def_of_tid a5_stamped (Term.tid a5_vla)))));

    pin "MOD-04"
      "PR-A5c: a VLA spelled through TWO temps is still the event (the chain resolves through the sequential state)"
      (fun () ->
        let a5_rcx = v64 "pr_a5_rcx" in
        let a5c_t1 = v64 "pr_a5c_t1" in
        let a5c_t2 = v64 "pr_a5c_t2" in
        let a5c_d1 =
          Def.create a5c_t1
            (Bil.BinOp (Bil.MINUS, Bil.Var sp, Bil.Var a5_rcx))
        in
        let a5c_d2 = Def.create a5c_t2 (Bil.Var a5c_t1) in
        let a5c_sp = Def.create sp (Bil.Var a5c_t2) in
        let a5c = straight_sub "pr_a5c_chain" [ a5c_d1; a5c_d2; a5c_sp ] in
        check "MOD-04"
          (Core.Set.equal
             (Hike.Sections.dynamic_alloc_tids_of ~facts:top_facts a5c)
             (tid_set [ Term.tid a5c_sp ])));

    pin "MOD-05"
      "PR-A5d: the lea-computed adjustment (a negative size ADDED) is the event"
      (fun () ->
        let a5_rcx = v64 "pr_a5_rcx" in
        let a5d_t = v64 "pr_a5d_t" in
        let a5d_d1 =
          Def.create a5d_t
            (Bil.BinOp
               ( Bil.MINUS,
                 Bil.Int (Cbat_word.to_word (w64 0)),
                 Bil.Var a5_rcx ))
        in
        let a5d_sp =
          Def.create sp (Bil.BinOp (Bil.PLUS, Bil.Var sp, Bil.Var a5d_t))
        in
        let a5d = straight_sub "pr_a5d_plus" [ a5d_d1; a5d_sp ] in
        check "MOD-05"
          (Core.Set.equal
             (Hike.Sections.dynamic_alloc_tids_of ~facts:top_facts a5d)
             (tid_set [ Term.tid a5d_sp ])));

    pin "MOD-06"
      "PR-A5e: a provably-above PLUS adjustment is not the VLA event (the value's direction)"
      (fun () ->
        let a5e_y = v64 "pr_a5e_y" in
        let a5e_r8 = v64 "pr_a5e_r8" in
        let a5e_y_def =
          Def.create a5e_y
            (Bil.BinOp
               ( Bil.AND,
                 Bil.Var a5e_r8,
                 Bil.Int (Cbat_word.to_word (w64 63)) ))
        in
        let a5e_sp =
          Def.create sp (Bil.BinOp (Bil.PLUS, Bil.Var sp, Bil.Var a5e_y))
        in
        let a5e = straight_sub "pr_a5e_plus_above" [ a5e_y_def; a5e_sp ] in
        let fa5e, a5e = fixture_facts_sub a5e in
        check "MOD-06"
          (Core.Set.is_empty
             (Hike.Sections.dynamic_alloc_tids_of ~facts:fa5e a5e)));

    pin "MOD-07"
      "PR-A5b: the LOOP-CARRIED VLA is the event — the widened head does not hide it"
      (fun () ->
        let a5_rcx = v64 "pr_a5_rcx" in
        let a5b_loop =
          Bil.BinOp
            (Bil.LT, Bil.Var a5_rcx, Bil.Int (Cbat_word.to_word (w64 5)))
        in
        let a5b, _ =
          sub_of "pr_a5b_loop_vla"
            [ [], [ (1, mk_goto) ];
              [ Def.create sp
                  (Bil.BinOp (Bil.MINUS, Bil.Var sp, Bil.Var a5_rcx)) ],
              [ (2, mk_goto) ];
              [],
              [ (3, fun t -> mk_jmp_to t (Bil.UnOp (Bil.NOT, a5b_loop)));
                (1, fun t -> mk_jmp_to t a5b_loop) ];
              [], [] ]
        in
        let a5b_events =
          Hike.Sections.dynamic_alloc_tids_of ~facts:top_facts a5b
        in
        let a5b_body_sp =
          Term.enum blk_t a5b
          |> Seq.find_map ~f:(fun blk ->
                 Term.enum def_t blk
                 |> Seq.find_map ~f:(fun d ->
                        if Var.same (Def.lhs d) sp then Some (Term.tid d)
                        else None))
          |> Base.Option.value_exn
        in
        check "MOD-07"
          (Core.Set.equal a5b_events (tid_set [ a5b_body_sp ])));

    (* Lane B: the layout from the finalized tree ([layout_of_tree]). *)
    pin "MOD-08"
      "PR-B1: the precise tree carries its Region components and no residue region"
      (fun () ->
        let abi = Hike.Abi.x86_64_sysv in
        let entry = Sm.segment_base in
        let d_rbp = Def.create pr_b_rbp (Bil.Var sp) in
        let sub1 =
          straight_sub "pr_b1"
            [ d_rbp; pr_b_mk_ld "pr_b1_t1" 24L; pr_b_mk_ld "pr_b1_t2" 16L ]
        in
        let l1 =
          Hike.Sections.layout_of_tree ~word:8 ~entry ~abi ~sub:sub1
            (tree_of sub1)
        in
        check "MOD-08"
          (l1.Sm.anchor = Some (1, 8L)
          && l1.Sm.regions =
             [ (1, (pos (-24L), pos (-17L)), 16L);
               (2, (pos (-16L), pos (-9L)), 16L) ]));

    pin "MOD-09" "PR-B2: bytes are the occupied span aligned once, never span*width"
      (fun () ->
        let abi = Hike.Abi.x86_64_sysv in
        let entry = Sm.segment_base in
        let d_rbp = Def.create pr_b_rbp (Bil.Var sp) in
        let sub1 =
          straight_sub "pr_b1"
            [ d_rbp; pr_b_mk_ld "pr_b1_t1" 24L; pr_b_mk_ld "pr_b1_t2" 16L ]
        in
        let l1 =
          Hike.Sections.layout_of_tree ~word:8 ~entry ~abi ~sub:sub1
            (tree_of sub1)
        in
        check "MOD-09"
          (Base.List.for_all l1.Sm.regions ~f:(fun (_, (lo, hi), b) ->
               Int64.equal (Int64.add (Int64.sub hi lo) 1L) 8L
               && Int64.equal b 16L)));

    pin "MOD-10"
      "PR-B3: a plain-TOP identity member forces the residue region with the 64K unbounded floors"
      (fun () ->
        let abi = Hike.Abi.x86_64_sysv in
        let entry = Sm.segment_base in
        let d_rbp = Def.create pr_b_rbp (Bil.Var sp) in
        let u = v64 "pr_b_u" in
        let top_store =
          Def.create pr_b_m
            (Bil.Store
               ( Bil.Var pr_b_m,
                 Bil.Var u,
                 Bil.Int (Cbat_word.to_word (w64 1)),
                 LittleEndian,
                 `r64 ))
        in
        let sub2 =
          straight_sub "pr_b3" [ d_rbp; pr_b_mk_ld "pr_b3_t" 24L; top_store ]
        in
        let l2 =
          Hike.Sections.layout_of_tree ~word:8 ~entry ~abi ~sub:sub2
            (tree_of sub2)
        in
        check "MOD-10"
          ((match l2.Sm.anchor with
           | Some (0, idx) -> Int64.equal idx 65544L
           | _ -> false)
          && Base.List.exists l2.Sm.regions ~f:(fun (id, _, b) ->
                 Int.equal id 0 && Int64.equal b 131088L)));

    pin "MOD-11" "PR-B6: a plain-TOP-only residue sub takes the same unbounded floor"
      (fun () ->
        let abi = Hike.Abi.x86_64_sysv in
        let entry = Sm.segment_base in
        let d_rbp = Def.create pr_b_rbp (Bil.Var sp) in
        let u = v64 "pr_b_u" in
        let top_store =
          Def.create pr_b_m
            (Bil.Store
               ( Bil.Var pr_b_m,
                 Bil.Var u,
                 Bil.Int (Cbat_word.to_word (w64 1)),
                 LittleEndian,
                 `r64 ))
        in
        let sub3 = straight_sub "pr_b6" [ d_rbp; top_store ] in
        let l3 =
          Hike.Sections.layout_of_tree ~word:8 ~entry ~abi ~sub:sub3
            (tree_of sub3)
        in
        check "MOD-11"
          (Base.List.exists l3.Sm.regions ~f:(fun (id, _, b) ->
               Int.equal id 0 && Int64.equal b 131088L)));

    (* Lane C: stack-to-locals fission. *)
    pin "MOD-12"
      "PR-C1: the whole-access store rebinds lhs and mem node to the region mem, keeping the SP address arithmetic"
      (fun () ->
        let c1_st0 = mk_store 24L 1 `r64 in
        let c1_st1 = mk_store 16L 2 `r64 in
        let c1_t = v64 "pr_c1_t" in
        let c1_ld_nested =
          Def.create c1_t
            (Bil.BinOp
               ( Bil.PLUS,
                 Bil.Load
                   (Bil.Var pr_c_m, minus_addr sp 16L, LittleEndian, `r64),
                 Bil.Int (Cbat_word.to_word (w64 1)) ))
        in
        let c1 =
          straight_sub "pr_c1_fission" [ c1_st0; c1_st1; c1_ld_nested ]
        in
        let c1' = rewrite_one c1 in
        check_bound "MOD-12"
          (def_of_lhs c1' (Sm.region_mem 1))
          (fun d ->
            match Def.rhs d with
            | Bil.Store
                ( Bil.Var mem,
                  Bil.BinOp (Bil.MINUS, Bil.Var b, Bil.Int _),
                  _,
                  _,
                  _ ) ->
                Var.same mem (Sm.region_mem 1) && Var.same b sp
            | _ -> false));

    pin "MOD-13"
      "PR-C1: the nested load inside a BinOp def reads the region mem too (the -O0 cmp pattern)"
      (fun () ->
        let c1_st0 = mk_store 24L 1 `r64 in
        let c1_st1 = mk_store 16L 2 `r64 in
        let c1_t = v64 "pr_c1_t" in
        let c1_ld_nested =
          Def.create c1_t
            (Bil.BinOp
               ( Bil.PLUS,
                 Bil.Load
                   (Bil.Var pr_c_m, minus_addr sp 16L, LittleEndian, `r64),
                 Bil.Int (Cbat_word.to_word (w64 1)) ))
        in
        let c1 =
          straight_sub "pr_c1_fission" [ c1_st0; c1_st1; c1_ld_nested ]
        in
        let c1' = rewrite_one c1 in
        check_bound "MOD-13" (def_of_lhs c1' c1_t) (fun d ->
            match Def.rhs d with
            | Bil.BinOp (Bil.PLUS, Bil.Load (Bil.Var mem, _, _, _), Bil.Int _)
              ->
                Var.same mem (Sm.region_mem 2)
            | _ -> false));

    pin "MOD-14"
      "PR-C2: the full-cell args read (width 64) becomes the bare hike_slot0 var"
      (fun () ->
        let d_rbp = Def.create pr_c_rbp (Bil.Var sp) in
        let slot0 = Sm.arg_slot ~word:8 0 in
        let c2_full = pr_c_args_ld "pr_c2_full" 8 `r64 in
        let c2_narrow = pr_c_args_ld "pr_c2_narrow" 8 `r32 in
        let c2_intra = pr_c_args_ld "pr_c2_intra" 12 `r32 in
        let c2 =
          straight_sub "pr_c2_slot" [ d_rbp; c2_full; c2_narrow; c2_intra ]
        in
        let c2' = rewrite_one c2 in
        check_bound "MOD-14" (def_of_tid c2' (Term.tid c2_full)) (fun d ->
            match Def.rhs d with Bil.Var v -> Var.equal v slot0 | _ -> false));

    pin "MOD-15"
      "PR-C2: the aligned narrow args read (width 32 at cell start) splices the LOW cast"
      (fun () ->
        let d_rbp = Def.create pr_c_rbp (Bil.Var sp) in
        let slot0 = Sm.arg_slot ~word:8 0 in
        let c2_full = pr_c_args_ld "pr_c2_full" 8 `r64 in
        let c2_narrow = pr_c_args_ld "pr_c2_narrow" 8 `r32 in
        let c2_intra = pr_c_args_ld "pr_c2_intra" 12 `r32 in
        let c2 =
          straight_sub "pr_c2_slot" [ d_rbp; c2_full; c2_narrow; c2_intra ]
        in
        let c2' = rewrite_one c2 in
        check_bound "MOD-15" (def_of_tid c2' (Term.tid c2_narrow)) (fun d ->
            match Def.rhs d with
            | Bil.Cast (Bil.LOW, 32, Bil.Var v) -> Var.equal v slot0
            | _ -> false));

    pin "MOD-16" "PR-C2: the intra-cell args read (width 32 at byte 4) selects bits [32,63]"
      (fun () ->
        let d_rbp = Def.create pr_c_rbp (Bil.Var sp) in
        let slot0 = Sm.arg_slot ~word:8 0 in
        let c2_full = pr_c_args_ld "pr_c2_full" 8 `r64 in
        let c2_narrow = pr_c_args_ld "pr_c2_narrow" 8 `r32 in
        let c2_intra = pr_c_args_ld "pr_c2_intra" 12 `r32 in
        let c2 =
          straight_sub "pr_c2_slot" [ d_rbp; c2_full; c2_narrow; c2_intra ]
        in
        let c2' = rewrite_one c2 in
        check_bound "MOD-16" (def_of_tid c2' (Term.tid c2_intra)) (fun d ->
            match Def.rhs d with
            | Bil.Extract (63, 32, Bil.Var v) -> Var.equal v slot0
            | _ -> false));

    pin "MOD-17"
      "PR-C3: an Args read in a stored cell converts with the store to the incoming-window memory (write-closed)"
      (fun () ->
        let d_rbp = Def.create pr_c_rbp (Bil.Var sp) in
        let c3_rd = pr_c_args_ld "pr_c3_rd" 8 `r64 in
        let c3_st =
          Def.create pr_c_m
            (Bil.Store
               ( Bil.Var pr_c_m,
                 Bil.BinOp
                   ( Bil.PLUS,
                     Bil.Var pr_c_rbp,
                     Bil.Int (Cbat_word.to_word (w64 8)) ),
                 Bil.Int (Cbat_word.to_word (w64 9)),
                 LittleEndian,
                 `r64 ))
        in
        let c3 = straight_sub "pr_c3_abi" [ d_rbp; c3_rd; c3_st ] in
        let c3' = rewrite_one c3 in
        check_bound "MOD-17" (def_of_tid c3' (Term.tid c3_rd)) (fun d ->
            match Def.rhs d with
            | Bil.Load (Bil.Var mem, _, _, _) -> Var.same mem (Sm.window_mem)
            | _ -> false));

    pin "MOD-18"
      "PR-N3: the split RMW's hoisted read converts with the store to the incoming-window memory (write-closed)"
      (fun () ->
        let n3_rbp = v64 "RBP" in
        let n3_d_rbp = Def.create n3_rbp (Bil.Var sp) in
        let n3_addr =
          Bil.BinOp
            ( Bil.PLUS,
              Bil.Var n3_rbp,
              Bil.Int (Cbat_word.to_word (w64 8)) )
        in
        let n3_rmw =
          Def.create (v64 "pr_n3_rmw")
            (Bil.Store
               ( Bil.Var pr_c_m,
                 n3_addr,
                 Bil.BinOp
                   ( Bil.PLUS,
                     Bil.Load (Bil.Var pr_c_m, n3_addr, LittleEndian, `r64),
                     Bil.Int (Cbat_word.to_word (w64 1)) ),
                 LittleEndian,
                 `r64 ))
        in
        let n3 =
          straight_sub "pr_n3_rmw" [ n3_d_rbp; n3_rmw ]
          |> fun sub -> Program.create ~subs:[ sub ] ()
          |> Hike.Split_mem.normalize
          |> Term.first sub_t
          |> Base.Option.value_exn
        in
        let n3' = rewrite_one n3 in
        let n3_defs =
          Term.enum blk_t n3'
          |> Seq.concat_map ~f:(Term.enum def_t)
          |> Seq.to_list
        in
        let is_original d =
          Base.List.exists [ n3_rbp; v64 "pr_n3_rmw" ] ~f:(Var.equal (Def.lhs d))
        in
        let all_window =
          Base.List.for_all n3_defs ~f:(fun d ->
              let vis =
                object
                  inherit [ bool ] Exp.visitor

                  method! visit_load ~mem ~addr:_ _ _ acc =
                    acc
                    && (match mem with
                       | Bil.Var v -> Var.same v (Sm.window_mem)
                       | _ -> false)

                  method! visit_store ~mem ~addr:_ ~exp:_ _ _ acc =
                    acc
                    && (match mem with
                       | Bil.Var v -> Var.same v (Sm.window_mem)
                       | _ -> false)
                end
              in
              vis#visit_exp (Def.rhs d) true)
        in
        check "MOD-18"
          (Base.List.exists n3_defs ~f:(fun d -> not (is_original d))
          && all_window));

    pin "MOD-19"
      "PR-C4: the compiled guard is a value comparison — no memory node rides a cond"
      (fun () ->
        let c4_st = mk_store 16L 7 `r64 in
        let c4_t = v64 "pr_c4_t" in
        let c4_ld =
          Def.create c4_t
            (Bil.Load (Bil.Var pr_c_m, minus_addr sp 16L, LittleEndian, `r64))
        in
        let c4_zf = v1 "ZF" in
        let c4_flag =
          Def.create c4_zf
            (Bil.BinOp
               ( Bil.EQ,
                 Bil.Var c4_t,
                 Bil.Int (Cbat_word.to_word (w64 0)) ))
        in
        let c4_pre, _ =
          sub_of "pr_c4_cond"
            [ [ c4_st; c4_ld; c4_flag ],
              [ (1, fun t -> mk_jmp_to t (Bil.Var c4_zf)); (1, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let c4 = Hike.Jump.compile_sub jump_target c4_pre in
        let has_load (e : exp) : bool =
          let vis =
            object
              inherit [ bool ] Exp.visitor
              method! visit_load ~mem:_ ~addr:_ _ _ _ = true
            end
          in
          vis#visit_exp e false
        in
        check "MOD-19"
          (Term.enum blk_t c4
          |> Seq.concat_map ~f:(Term.enum jmp_t)
          |> Seq.for_all ~f:(fun j -> not (has_load (Jmp.cond j)))));

    pin "MOD-20" "PR-C4: the load def converts to the region mem and the guard reads its temp"
      (fun () ->
        let c4_st = mk_store 16L 7 `r64 in
        let c4_t = v64 "pr_c4_t" in
        let c4_ld =
          Def.create c4_t
            (Bil.Load (Bil.Var pr_c_m, minus_addr sp 16L, LittleEndian, `r64))
        in
        let c4_zf = v1 "ZF" in
        let c4_flag =
          Def.create c4_zf
            (Bil.BinOp
               ( Bil.EQ,
                 Bil.Var c4_t,
                 Bil.Int (Cbat_word.to_word (w64 0)) ))
        in
        let c4_pre, _ =
          sub_of "pr_c4_cond"
            [ [ c4_st; c4_ld; c4_flag ],
              [ (1, fun t -> mk_jmp_to t (Bil.Var c4_zf)); (1, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        let c4 = Hike.Jump.compile_sub jump_target c4_pre in
        let c4' = rewrite_one c4 in
        check_bound "MOD-20" (def_of_tid c4' (Term.tid c4_ld)) (fun d ->
            match Def.rhs d with
            | Bil.Load (Bil.Var mem, _, _, _) ->
                Var.same mem (Sm.region_mem 1)
                && (Term.enum blk_t c4'
                   |> Seq.concat_map ~f:(Term.enum jmp_t)
                   |> Seq.exists ~f:(fun j ->
                          match Jmp.cond j with
                          | Bil.BinOp (Bil.EQ, Bil.Var v, Bil.Int _) ->
                              Var.equal v c4_t
                          | _ -> false))
            | _ -> false));

    (* Lane D: the emitter's alloca shapes — the VLA lane, the SP Slot /
       stack_0 anchoring per storage class, and the frame-request clamp. *)
    pin "MOD-21" "PR-D1: the VLA def emits a real runtime-sized i8 alloca"
      (fun () ->
        let m = memv "pr_d_m" in
        let d_rbx =
          Def.create (v64 "pr_d_rbx") (Bil.Int (Cbat_word.to_word (w64 0x80)))
        in
        let d_vla =
          Def.create sp
            (Bil.BinOp (Bil.MINUS, Bil.Var sp, Bil.Var (Def.lhs d_rbx)))
        in
        let d_st =
          Def.create m
            (Bil.Store
               ( Bil.Var m,
                 Bil.Var sp,
                 Bil.Int (Cbat_word.to_word (w64 7)),
                 LittleEndian,
                 `r64 ))
        in
        let d1 = straight_sub "pr_d1_vla" [ d_rbx; d_vla; d_st ] in
        let ir1 =
          emit_ir
            [ stamp_shape
                ~dynamic_alloc_tids:(tid_set [ Term.tid d_vla ])
                ~layout:empty_layout d1 ]
        in
        check "MOD-21" (contains_substring ir1 "%vla = alloca i8, i64"));

    pin "MOD-22" "PR-D1: the model SP binds to the alloca's integer (vla_i64)"
      (fun () ->
        let m = memv "pr_d_m" in
        let d_rbx =
          Def.create (v64 "pr_d_rbx") (Bil.Int (Cbat_word.to_word (w64 0x80)))
        in
        let d_vla =
          Def.create sp
            (Bil.BinOp (Bil.MINUS, Bil.Var sp, Bil.Var (Def.lhs d_rbx)))
        in
        let d_st =
          Def.create m
            (Bil.Store
               ( Bil.Var m,
                 Bil.Var sp,
                 Bil.Int (Cbat_word.to_word (w64 7)),
                 LittleEndian,
                 `r64 ))
        in
        let d1 = straight_sub "pr_d1_vla" [ d_rbx; d_vla; d_st ] in
        let ir1 =
          emit_ir
            [ stamp_shape
                ~dynamic_alloc_tids:(tid_set [ Term.tid d_vla ])
                ~layout:empty_layout d1 ]
        in
        check "MOD-22" (contains_substring ir1 "%vla_i64 = ptrtoint"));

    pin "MOD-23"
      "PR-D2: residue storage anchors through the entry SP Slot (per-invocation stack_0)"
      (fun () ->
        let residue_layout bytes idx : Sm.sub_layout =
          { regions = [ (0, (pos (-16L), pos (-9L)), bytes) ];
            anchor = Some (0, idx);
            window_param = false }
        in
        let d_ld =
          Def.create (v64 "pr_d2_t")
            (Bil.Load
               ( Bil.Var (Sm.region_mem 0),
                 minus_addr sp 16L,
                 LittleEndian,
                 `r64 ))
          |> tag_def (Sm.Tag.Stack (pos (-16L), pos (-16L)))
        in
        let d2 = straight_sub "pr_d2_residue" [ d_ld ] in
        let ir2 =
          emit_ir [ stamp_shape ~layout:(residue_layout 32L 8192L) d2 ]
        in
        check "MOD-23"
          (contains_substring ir2 "%sp_slot = alloca i64"
          && contains_substring ir2 "%stack_0 = load i64, ptr %sp_slot"));

    pin "MOD-24"
      "PR-D2b: region storage anchors the SP Slot at region-0 + 8 (the SysV residue)"
      (fun () ->
        let d2b_ld =
          Def.create (v64 "pr_d2b_t")
            (Bil.Load
               ( Bil.Var (Sm.region_mem 0),
                 minus_addr sp 16L,
                 LittleEndian,
                 `r64 ))
        in
        let d2b = straight_sub "pr_d2b_region" [ d2b_ld ] in
        let region_layout : Sm.sub_layout =
          { regions = [ (0, (pos (-16L), pos (-9L)), 16L) ];
            anchor = Some (0, 8L);
            window_param = false }
        in
        let ir2b = emit_ir [ stamp_shape ~layout:region_layout d2b ] in
        check "MOD-24"
          (contains_substring ir2b
             "getelementptr i8, ptr %stack_r0, i64 8"
          && contains_substring ir2b
               "%anchor_i64 = ptrtoint ptr %anchor to i64"
          && contains_substring ir2b "%sp_slot = alloca i64"));

    pin "MOD-25" "PR-D2c: a storage-free sub emits no SP Slot and no region"
      (fun () ->
        let d2c = straight_sub "pr_d2c_free" [] in
        let ir2c = emit_ir [ stamp_shape ~layout:empty_layout d2c ] in
        check "MOD-25"
          (not (contains_substring ir2c "%sp_slot")
          && not (contains_substring ir2c "%stack_r")));

    pin "MOD-26"
      "PR-D3: an over-bound region request names itself on the channel and clamps"
      (fun () ->
        let d3_ld =
          Def.create (v64 "pr_d3_t")
            (Bil.Load
               ( Bil.Var (memv "pr_d_m"),
                 minus_addr sp 0x80000000L,
                 LittleEndian,
                 `r64 ))
          |> tag_def
               (Sm.Tag.Stack (pos (-0x80000000L), pos (-0x80000000L)))
        in
        let d3 = straight_sub "pr_d3_huge" [ d3_ld ] in
        let clamp_layout : Sm.sub_layout =
          { regions = [ (0, (pos (-16L), pos (-9L)), 0x8000_0000L) ];
            anchor = Some (0, 8192L);
            window_param = false }
        in
        let d3_err =
          capture_stderr (fun () ->
              ignore (emit_ir [ stamp_shape ~layout:clamp_layout d3 ]))
        in
        let ir3 = emit_ir [ stamp_shape ~layout:clamp_layout d3 ] in
        check "MOD-26"
          (contains_substring d3_err "hike: frame:"
          && contains_substring d3_err "clamped"
          && contains_substring ir3 "alloca [2147483632 x i8]"));

    (* The printable-run rule (the model's one home): a word is string
       text iff a printable run crosses its start boundary. *)
    pin "MOD-27" "STRING-TEXT: a printable run crossing the start covers the word"
      (fun () ->
        let txt = Bytes.of_string "\x63\x61\x74\x00\x61\xff\x74\x00" in
        check "MOD-27" (Sm.string_text_word ~arr:txt ~off:1));

    pin "MOD-28" "STRING-TEXT: a NUL directly before the word means no crossing"
      (fun () ->
        let txt = Bytes.of_string "\x63\x61\x74\x00\x61\xff\x74\x00" in
        check "MOD-28" (not (Sm.string_text_word ~arr:txt ~off:4)));

    pin "MOD-29" "STRING-TEXT: pointer bytes before the word mean no crossing"
      (fun () ->
        let txt = Bytes.of_string "\x63\x61\x74\x00\x61\xff\x74\x00" in
        check "MOD-29" (not (Sm.string_text_word ~arr:txt ~off:6)));

    pin "MOD-30" "STRING-TEXT: a non-printable start byte never covers"
      (fun () ->
        let txt = Bytes.of_string "\x63\x61\x74\x00\x61\xff\x74\x00" in
        check "MOD-30" (not (Sm.string_text_word ~arr:txt ~off:5)));

    pin "MOD-31" "STRING-TEXT: the first word of the image never crosses"
      (fun () ->
        let txt = Bytes.of_string "\x63\x61\x74\x00\x61\xff\x74\x00" in
        check "MOD-31" (not (Sm.string_text_word ~arr:txt ~off:0)));

    pin "MOD-32"
      "STRING-TEXT: running off the front crosses iff the prefix is all printable"
      (fun () ->
        let all_txt = Bytes.of_string "\x63\x61\x74\x20\x7e" in
        check "MOD-32" (Sm.string_text_word ~arr:all_txt ~off:4));

    (* Lane E: the register/convention facts (Hike_abi, ADR 0008: SP is the
       only stack-semantics register, fp an ordinary callee-saved GPR) and
       the KB carrier's table semantics. *)
    pin "MOD-33" "PR-E1: the stack pointer is RSP, and only RSP (SP-only, ADR 0008)"
      (fun () ->
        let abi = Hike.Abi.x86_64_sysv in
        check "MOD-33"
          (Var.equal (Var.base abi.Abi.sp) (Var.base (named "RSP"))
          && Abi.is_sp abi (named "RSP")
          && not (Abi.is_sp abi (named "RBP"))));

    pin "MOD-34"
      "PR-E1: RBP is an ordinary callee-saved GPR — no frame-pointer fact exists"
      (fun () ->
        let abi = Hike.Abi.x86_64_sysv in
        check "MOD-34"
          (Abi.is_callee_saved abi (named "RBP")
          && names_are abi.Abi.callee_saved
               [ "RBX"; "RBP"; "R12"; "R13"; "R14"; "R15" ]));

    pin "MOD-35"
      "PR-E1: the SysV lanes — 6 integer args, 8 vector args, RAX/RDX returns"
      (fun () ->
        let abi = Hike.Abi.x86_64_sysv in
        check "MOD-35"
          (names_are abi.Abi.int_param_regs
             [ "RDI"; "RSI"; "RDX"; "RCX"; "R8"; "R9" ]
          && Base.List.length abi.Abi.vector_param_regs = 8
          && String.equal
               (Var.name (Base.List.nth_exn abi.Abi.vector_param_regs 0))
               "YMM0"
          && names_are abi.Abi.return_regs [ "RAX"; "RDX" ]
          && Base.List.length
               (let unk = Abi.of_target Theory.Target.unknown in
                unk.Abi.int_param_regs @ unk.Abi.vector_param_regs)
             = 14));

    pin "MOD-36" "PR-E1: the structural predicates partition the lanes"
      (fun () ->
        let abi = Hike.Abi.x86_64_sysv in
        check "MOD-36"
          (Abi.is_return_reg abi (named "RAX")
          && not (Abi.is_return_reg abi (named "RCX"))
          && Abi.is_vector_param_reg abi (named "YMM3")
          && not (Abi.is_vector_param_reg abi (named "RDI"))));

    pin "MOD-37" "PR-E1: an unknown target falls back to the SysV record (total)"
      (fun () ->
        check "MOD-37"
          (Abi.is_sp
             (Hike.Abi.of_target Theory.Target.unknown)
             (named "RSP")
          && Hike.Abi.addr_size_bits Theory.Target.unknown = 0));

    pin "MOD-38" "PR-E1: the x86_64-gnu-elf target reifies RSP as the SP"
      (fun () ->
        let x86 = Theory.Target.of_string "x86_64-gnu-elf" in
        check "MOD-38"
          (Theory.Target.matches x86 "x86_64-gnu-elf"
          && Abi.is_sp (Hike.Abi.of_target x86) (Hike.Abi.sp x86)));

    pin "MOD-39"
      "PR-E1: the word size — SysV carries the x86-64 word; of_target derives bits/8"
      (fun () ->
        let abi = Hike.Abi.x86_64_sysv in
        let x86 = Theory.Target.of_string "x86_64-gnu-elf" in
        check "MOD-39"
          (abi.Abi.word = 8
          && Hike.Abi.((of_target x86).Abi.word) = Theory.Target.bits x86 / 8));
  ]

let () = run "model" tests
