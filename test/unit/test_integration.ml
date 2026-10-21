(* CFG-level refinement, memory constraints and landmark-directed widening. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

module W = Cbat_word

(* VSK-02 fixture: an acyclic diamond over a ranged counter; the entry
   state carries the range, so the guard edges refine to absolute halves.
   The two arms read the counter, so the SSA construction gives them a
   phi for it: a block's state holds the values it receives, and the
   refinement of an edge is visible in the destination's state.
   Returns (sub, guard_tid, then_tid, else_tid, x). *)
let vsk_diamond () : sub term * tid * tid * tid * var =
  let x = Var.create ~is_virtual:false ~fresh:false "vsk_x" (Type.Imm 32) in
  let guard_e = Bil.BinOp (Bil.LT, Bil.Var x, Bil.Int (Cbat_word.to_word (w32 10))) in
  let y = Var.create ~is_virtual:false ~fresh:false "vsk_y" (Type.Imm 32) in
  let sub, tids =
    sub_of "vsk_diamond"
      [ [], [ (1, mk_goto) ];
        [], [ (2, fun t -> mk_jmp_to t guard_e);
              (3, fun t -> mk_jmp_to t (Bil.UnOp (Bil.NOT, guard_e))) ];
        [ Def.create y (Bil.Var x) ], [];
        [ Def.create y (Bil.Var x) ], [] ]
  in
  (sub, tids.(1), tids.(2), tids.(3), x)

(* The sub's memory variable: the first memory-typed definition's
   left-hand side (the memory variables keep their name across the SSA
   renaming, so the pin reads the same cell the analysis wrote). *)
let mem_var_of (sub : sub term) : var =
  Term.enum blk_t sub
  |> Seq.concat_map ~f:(Term.enum def_t)
  |> Seq.filter_map ~f:(fun d ->
         match Var.typ (Def.lhs d) with
         | Type.Mem _ -> Some (Def.lhs d)
         | Type.Imm _ | Type.Unk -> None)
  |> Seq.to_list
  |> function [] -> failwith "mem_var_of: the sub has no memory definition" | v :: _ -> v

(* The word key the landmark pins use: each pin builds its own table, so
   one base variable serves them all. *)
let lw_var = v64 "lm_word"
let lw = Cbat_landmarks.Word lw_var

let tests : unit Alcotest.test list =
  [

    (* VSK-02: the diamond's entry state carries x in [0,20]; the
       constant-true identity edge is the empty-seed shape and the guard's
       taken/fallthrough edges refine to the absolute halves.  Each arm
       reads x, so the refinement is visible in the state the arm
       receives. *)
    pin "INT-04"
      "VSK-02 empty-seed/mixed-seed oracle: the constant-true guard seeds nothing and the \
       diamond's edges refine to the absolute halves"
      (fun () ->
        let sub, guard_tid, then_tid, else_tid, x = vsk_diamond () in
        let range lo hi = Ws.of_clp (Clp.interval ~width:32 (w32 lo) (w32 hi)) in
        let entry = AI.add_word (anchored_entry ()) ~key:x ~data:(range 0 20) in
        check
          "property LM VSK-EMPTY-SEED: a constant-true guard produces no seeds (the early-exit \
           shape)"
          (AI.equal
             (Vsa.Test_seam.constrain_operands ~synth:Hike.Synth.empty ~landmarks:(Cbat_landmarks.create ()) ~env:entry (Bil.Int (W.to_word W.b1)) (Ws.singleton W.b1))
             entry);
        check "property LM VSK-MIXED-SEED: the taken guard produces the single Var seed x in [0,9]"
          (Ws.equal
             (AI.find_word 32
                (Vsa.Test_seam.constrain_operands ~synth:Hike.Synth.empty ~landmarks:(Cbat_landmarks.create ()) ~env:entry
                   (Bil.BinOp (Bil.LT, Bil.Var x, Bil.Int (Cbat_word.to_word (w32 10))))
                   (Ws.singleton W.b1))
                x)
             (range 0 9));
        let sol =
          static_graph_vsa ~synth:Hike.Synth.empty ~abi:Hike_abi.x86_64_sysv sub
            (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv ~entry sub)
        in
        check
          "property LM VSK-EMPTY: the unconditional edge is the identity transfer — the guard \
           block receives the seeded range unchanged (the destination's state is built from the \
           values it receives, not copied from the source)"
          (Ws.equal (value_at sub sol guard_tid x) (AI.find_word 32 entry x));
        check "property LM VSK-MIXED-TAKEN: the taken edge refines x to [0,9] exactly"
          (Ws.equal (value_at sub sol then_tid x) (range 0 9));
        check "property LM VSK-MIXED-FALL: the fallthrough edge refines x to [10,20] exactly"
          (Ws.equal (value_at sub sol else_tid x) (range 10 20)));

    (* F2a: landmark consumption at CLP level — never lands short of the join. *)
    pin "INT-05" "LM F2a: widen_join soundness over the landmark-input pair"
      (fun () ->
        let p1 = Clp.interval ~width:32 (w32 0) (w32 100) in
        let p2 = Clp.interval ~width:32 (w32 0) (w32 101) in
        let r = Clp.widen_join p1 p2 in
        check "property LM F2a: widen_join sound on p2" (Clp.subset p2 r);
        check "property LM F2a: widen_join sound on p1" (Clp.subset p1 r));

    (* F2c: acquisition + per-cycle scoping — landmarks scoped to their own WTO cycle. *)
    pin "INT-06"
      "LM F2c: two sequential landmarks loops refine independently (loop 2's head is loop 1's \
       exact exit value K1+1)"
      (fun () ->
        let sub, l1_tid, _, l2_tid = lm_jle_loop ~k1:(w32 40) ~k2:(w32 100) () in
        let sol = run_anchored sub in
        let i = Var.create ~is_virtual:false ~fresh:false "lm_i" (Type.Imm 32) in
        let l2_tid = match l2_tid with Some t -> t | None -> failwith "F2c: missing L2" in
        let i1 = value_at sub sol l1_tid i in
        let i2 = value_at sub sol l2_tid i in
        check_bound "property LM F2c: loop 1's head lower bound is the entry constant 0"
          (Ws.min_elem i1) (fun lo -> Cbat_word.equal lo (w32 0));
        check_bound
          "property LM F2c: loop 2's head lower bound is loop 1's exact exit value K1+1 (the \
           compiled fallthrough comparison partitions the exit edge)"
          (Ws.min_elem i2) (fun lo -> Cbat_word.equal lo (Cbat_word.succ (w32 40))));

    (* T01: single-pass trace partitioning — every out-edge transfers a
       branch-refined state; the when-chain splits ladder seeds {5,15,25}. *)
    pin "INT-07"
      "T01: the when-chain's edges partition by their accumulated conditions and a lone \
       unconditional goto is the identity transfer"
      (fun () ->
        let sub, l1_tid, l2_tid, l3_tid, chain_tid, x = mk_when_chain () in
        let sol = run_anchored sub in
        (* The chain's cell: the guard's refinement meets the cell the
           chain reads, and the destination's state carries the memory
           the edge delivers — so the partition is visible there. *)
        let chain_mem = mem_var_of sub in
        let midx = { Mem.addr_width = 64; Mem.addressable_width = 8 } in
        let key =
          match Mem.Key.of_wordset (Ws.stack_word_i64 (-8L)) with
          | [ k ] -> k
          | _ -> failwith "T01: no stack key"
        in
        let cell_of (t : tid) : Ws.t =
          let mv = AI.find_memory midx (Graphlib.Std.Solution.get sol t) chain_mem in
          Mem.Val.data (Mem.find (32, LittleEndian) mv key)
        in
        check
          "T01-0 (when-chain): the chain block reads the ladder {5,15,25} — the cell's whole \
           value, before the edges split it"
          (Ws.equal (value_after sub sol chain_tid x)
             (Ws.of_list ~width:32 [ w32 5; w32 15; w32 25 ]));
        check
          "T01-1a (when-chain): the FIRST edge's destination receives the cell refined by its own \
           cond (x < 10 over {5,15,25} = {5} exactly)"
          (Ws.equal (cell_of l1_tid) (Ws.singleton (w32 5)));
        check
          "T01-1b (when-chain): the MID-CHAIN edge's destination receives the cell refined by the \
           ACCUMULATED `c2 & ~c1`, not the jmp's own cond ({15} exactly — not {5,15})"
          (Ws.equal (cell_of l2_tid) (Ws.singleton (w32 15)));
        check
          "T01-1c (when-chain): the unconditional chain TAIL's destination receives the cell \
           refined by the accumulated negatives `~c1 & ~c2` ({25} exactly)"
          (Ws.equal (cell_of l3_tid) (Ws.singleton (w32 25)));
        let m = memv "t01_m" in
        let rbp = frame_ptr in
        let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
        let sub2, tids =
          sub_of "t01_straight"
            [ [ Def.create rbp (Bil.Var sp);
                Def.create m
                  (Bil.Store
                     ( Bil.Var m, addr_e, Bil.Int (Cbat_word.to_word (w32 3)), LittleEndian, `r32 )) ],
              [ (1, mk_goto) ];
              [], [ (2, mk_goto) ];
              [], [] ]
        in
        let mid_tid = tids.(1) in
        let exit_tid = tids.(2) in
        let sol2 = run_anchored sub2 in
        (* The straight-line fixture stores 3 at the same frame offset. *)
        let cell t =
          let mv = AI.find_memory midx (Graphlib.Std.Solution.get sol2 t) m in
          Mem.Val.data (Mem.find (32, LittleEndian) mv key)
        in
        check
          "T01-2 (uniform rule): a lone unconditional goto's accumulated cond is the literal TRUE \
           — the identity transfer: EXIT's state equals MID's (both read the stored {3} exactly; \
           no spurious refinement, no bottom)"
          (Ws.equal (cell mid_tid) (Ws.singleton (w32 3))
          && Ws.equal (cell exit_tid) (Ws.singleton (w32 3))));

    (* T5-1 (prefix states): a store, then a load whose ADDRESS the same
       block defines; the walk's cell meet keys by the same-iteration
       address and lands {5}. *)
    pin "INT-08"
      "T5-1 prefix states: the deep walk's cell meet keys by the same-iteration address — the load \
       after the store meets the cell down to {5}"
      (fun () ->
        let mem = memv "t5_m" in
        let rbp = frame_ptr in
        let addr = Var.create ~is_virtual:true ~fresh:false "t5_addr" (Type.Imm 64) in
        let t = Var.create ~is_virtual:true ~fresh:false "t5_t" (Type.Imm 32) in
        let addr_e = Bil.Var addr in
        let addr_lit = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
        let sub, tids =
          sub_of "t5_store_load"
            [ [ Def.create rbp (Bil.Var sp);
                Def.create addr addr_lit;
                Def.create mem
                  (Bil.Store
                     ( Bil.Var mem, addr_e, Bil.Int (Cbat_word.to_word (w32 5)), LittleEndian, `r32 ));
                Def.create t (Bil.Load (Bil.Var mem, addr_e, LittleEndian, `r32)) ],
              [ (1, fun tt ->
                    mk_jmp_to tt
                      (Bil.BinOp (Bil.EQ, Bil.Var t, Bil.Int (Cbat_word.to_word (w32 5))))) ];
              [], [ (0, mk_ret) ] ]
        in
        let blk = List.nth (Term.enum blk_t sub |> Seq.to_list) 0 in
        let key =
          match Mem.Key.of_wordset (Ws.stack_word_i64 (-8L)) with
          | [ k ] -> k
  | _ -> failwith "key"
        in
        let wide = Ws.of_clp (Clp.interval ~width:32 (w32 0) (w32 200)) in
        let wide_mem =
          Mem.add
            (Mem.top { Mem.addr_width = 64; Mem.addressable_width = 8 })
            ~key ~data:(Mem.Val.create wide LittleEndian)
        in
        let entry = AI.add_memory (anchored_entry ()) ~key:mem ~data:wide_mem in
        let sol =
          static_graph_vsa ~synth:Hike.Synth.empty ~abi:Hike_abi.x86_64_sysv
            sub
            (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv ~entry sub)
        in
        let rctx = mk_rctx ~synth:Hike.Synth.empty ~abi:Hike_abi.x86_64_sysv sub in
        (* The walk follows the exact SSA definition: the seed is the
           version the block defines, and the state carries its value. *)
        let t_v =
          match def_version sub (Term.tid blk) t with
          | Some v -> v
          | None -> failwith "T5-1: no version of t"
        in
        let entry = AI.add_word entry ~key:t_v ~data:(Ws.singleton (w32 5)) in
        let refined =
          Vsa.Test_seam.refine_edge ~sol ~rctx
            ~seeds:(Var.Set.singleton t_v)
            entry blk
        in
        let cell =
          let open Cbat_vsa.Mem in
          let mv = AI.find_memory { addr_width = 64; addressable_width = 8 } refined mem in
          Val.data (find (32, LittleEndian) mv key)
        in
        check
          "T5-1 (prefix states): the deep walk's cell meet keys by the same-iteration address — the \
           load after the store meets the cell down to {5}"
          (Ws.equal cell (Ws.singleton (w32 5))));

    (* T5-2 (the Store row): a cell constraint flows into the stored data's
       producers — load KA, copy, store KB, load KB. *)
    pin "INT-09"
      "T5-2 Store row: the constrained cell meets {6} and the constraint flows into the stored \
       data's producing load"
      (fun () ->
        let mem = memv "t5r_m" in
        let rbp = frame_ptr in
        let ta = Var.create ~is_virtual:true ~fresh:false "t5r_a" (Type.Imm 32) in
        let tb = Var.create ~is_virtual:true ~fresh:false "t5r_b" (Type.Imm 32) in
        let t2 = Var.create ~is_virtual:true ~fresh:false "t5r_t" (Type.Imm 32) in
        let ka = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 16))) in
        let kb = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
        let sub, _ =
          sub_of "t5_store_row"
            [ [ Def.create rbp (Bil.Var sp);
                Def.create ta (Bil.Load (Bil.Var mem, ka, LittleEndian, `r32));
                Def.create tb (Bil.Var ta);
                Def.create mem (Bil.Store (Bil.Var mem, kb, Bil.Var tb, LittleEndian, `r32));
                Def.create t2 (Bil.Load (Bil.Var mem, kb, LittleEndian, `r32)) ],
              [ (1, fun tt ->
                    mk_jmp_to tt
                      (Bil.BinOp (Bil.EQ, Bil.Var t2, Bil.Int (Cbat_word.to_word (w32 6))))) ];
              [], [ (0, mk_ret) ] ]
        in
        let blk = List.nth (Term.enum blk_t sub |> Seq.to_list) 0 in
        let key_of w =
          match Mem.Key.of_wordset (Ws.stack_word_i64 (Stdlib.Int64.of_int w)) with
          | [ k ] -> k
  | _ -> failwith "key"
        in
        let k16 = key_of (-16) and k8 = key_of (-8) in
        let wide = Ws.of_clp (Clp.interval ~width:32 (w32 0) (w32 200)) in
        let wide_mem =
          Mem.add
            (Mem.add
               (Mem.top { Mem.addr_width = 64; Mem.addressable_width = 8 })
               ~key:k16 ~data:(Mem.Val.create wide LittleEndian))
            ~key:k8 ~data:(Mem.Val.create wide LittleEndian)
        in
        let entry = AI.add_memory (anchored_entry ()) ~key:mem ~data:wide_mem in
        let sol =
          static_graph_vsa ~synth:Hike.Synth.empty ~abi:Hike_abi.x86_64_sysv
            sub
            (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv ~entry sub)
        in
        let rctx = mk_rctx ~synth:Hike.Synth.empty ~abi:Hike_abi.x86_64_sysv sub in
        (* The walk follows the exact SSA definition: the seed is the
           version the block defines, and the state carries its value.
           The addresses are the frame-pointer version the block holds. *)
        let t2_v =
          match def_version sub (Term.tid blk) t2 with
          | Some v -> v
          | None -> failwith "T5-2: no version of t2"
        in
        let rbp_v = version_at sub (Term.tid blk) frame_ptr in
        let ka_v =
          Bil.BinOp (Bil.MINUS, Bil.Var rbp_v, Bil.Int (Cbat_word.to_word (w64 16)))
        in
        let kb_v =
          Bil.BinOp (Bil.MINUS, Bil.Var rbp_v, Bil.Int (Cbat_word.to_word (w64 8)))
        in
        let entry = AI.add_word entry ~key:t2_v ~data:(Ws.singleton (w32 6)) in
        let refined =
          Vsa.Test_seam.refine_edge ~sol ~rctx
            ~seeds:(Var.Set.singleton t2_v)
            entry blk
        in
        let cell_of_key k =
          Result.fold
            (Vsa.Test_seam.denote_imm_exp ~synth:Hike.Synth.empty (Bil.Load (Bil.Var mem, k, LittleEndian, `r32)) refined)
            ~ok:Fun.id ~error:(fun _ -> Ws.top 32)
        in
        check "T5-2 (Store row): the constrained cell (the store's key) meets {6}"
          (Ws.equal (cell_of_key kb_v) (Ws.singleton (w32 6)));
        check
          "T5-2 (Store row): the constraint flows into the stored data's producers — the \
           producing load's cell meets {6}"
          (Ws.equal (cell_of_key ka_v) (Ws.singleton (w32 6)));
        (* The hull case: the consuming load's address is a SET whose hull
           contains the store's key without equalling it.  The handshake's
           match is interval intersection, so the store row still delivers —
           sound by the join ruling (a load's value is the join over the
           cells its addresses can read, so the constraint contains every
           contributing cell). *)
        let hull_case ~(store_off : int) :
            AI.t * AI.t * var * var * var * exp * exp =
          let hmem = memv "t5r_hm" in
          let ha = Var.create ~is_virtual:true ~fresh:false "t5r_ha" (Type.Imm 32) in
          let hb = Var.create ~is_virtual:true ~fresh:false "t5r_hb" (Type.Imm 32) in
          let ht = Var.create ~is_virtual:true ~fresh:false "t5r_ht" (Type.Imm 32) in
          let hu = Var.create ~is_virtual:true ~fresh:false "t5r_hu" (Type.Imm 64) in
          let hka =
            Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 16)))
          in
          let hkb =
            Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 store_off)))
          in
          (* hu ∈ [0,8]: the load address rbp - hu is the hull [rbp-8, rbp]. *)
          let hull_addr = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Var hu) in
          let sub_h, _ =
            sub_of "t5_store_row_hull"
              [ [ Def.create rbp (Bil.Var sp);
                  Def.create ha (Bil.Load (Bil.Var hmem, hka, LittleEndian, `r32));
                  Def.create hb (Bil.Var ha);
                  Def.create hmem (Bil.Store (Bil.Var hmem, hkb, Bil.Var hb, LittleEndian, `r32));
                  Def.create ht (Bil.Load (Bil.Var hmem, hull_addr, LittleEndian, `r32)) ],
                [ (1, fun tt ->
                      mk_jmp_to tt
                        (Bil.BinOp (Bil.EQ, Bil.Var ht, Bil.Int (Cbat_word.to_word (w32 6))))) ];
                [], [ (0, mk_ret) ] ]
          in
          let k16 = key_of (-16) and k8 = key_of (-8) in
          let wide_h = Ws.of_clp (Clp.interval ~width:32 (w32 0) (w32 200)) in
          let wide_mem_h =
            Mem.add
              (Mem.add
                 (Mem.top { Mem.addr_width = 64; Mem.addressable_width = 8 })
                 ~key:k16 ~data:(Mem.Val.create wide_h LittleEndian))
              ~key:k8 ~data:(Mem.Val.create wide_h LittleEndian)
          in
          let entry_h =
            AI.add_memory
              (AI.add_word (anchored_entry ()) ~key:hu
                 ~data:(Ws.of_clp (Clp.interval ~width:64 (w64 0) (w64 8))))
              ~key:hmem ~data:wide_mem_h
          in
          let sol_h =
            static_graph_vsa ~synth:Hike.Synth.empty ~abi:Hike_abi.x86_64_sysv
              sub_h
              (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv ~entry:entry_h sub_h)
          in
          let rctx_h = mk_rctx ~synth:Hike.Synth.empty ~abi:Hike_abi.x86_64_sysv sub_h in
          let blk_h = List.nth (Term.enum blk_t sub_h |> Seq.to_list) 0 in
          let forward = Vsa.Test_seam.denote_defs ~synth:Hike.Synth.empty blk_h entry_h in
          let entry_h = AI.add_word entry_h ~key:ht ~data:(Ws.singleton (w32 6)) in
          let refined =
            Vsa.Test_seam.refine_edge ~sol:sol_h ~rctx:rctx_h
              ~seeds:(Var.Set.singleton ht)
              entry_h blk_h
          in
          (refined, forward, ha, hb, hmem, hka, hkb)
        in
        (* S6: the store at rbp-8 sits inside the hull [rbp-8, rbp], but the
           read's set spans past the store's cell, so the read does not read
           the store on every path — the delivery is the identity. *)
        let refined_p, forward_p, ha_p, hb_p, hmem_p, hka_p, hkb_p = hull_case ~store_off:8 in
        let cell_p addr =
          Result.fold
            (Vsa.Test_seam.denote_imm_exp ~synth:Hike.Synth.empty (Bil.Load (Bil.Var hmem_p, addr, LittleEndian, `r32)) refined_p)
            ~ok:Fun.id ~error:(fun _ -> Ws.top 32)
        in
        check
          "T5-2 (Store row, hull): S6 — a set-valued load address spanning past the store's \
           cell delivers nothing; the store's key cell keeps its wide value"
          (Ws.equal (cell_p hkb_p) (Ws.of_clp (Clp.interval ~width:32 (w32 0) (w32 200))));
        check
          "T5-2 (Store row, hull): S6 — the store's data producers keep their forward values"
          (Ws.equal (AI.find_word 32 refined_p hb_p) (AI.find_word 32 forward_p hb_p)
          && Ws.equal (AI.find_word 32 refined_p ha_p) (AI.find_word 32 forward_p ha_p));
        (* Negative: the store at rbp-16 is outside the hull [rbp-8, rbp]. *)
        let refined_n, forward_n, ha_n, hb_n, hmem_n, _hka_n, hkb_n =
          hull_case ~store_off:16 in
        let cell_n addr =
          Result.fold
            (Vsa.Test_seam.denote_imm_exp ~synth:Hike.Synth.empty (Bil.Load (Bil.Var hmem_n, addr, LittleEndian, `r32)) refined_n)
            ~ok:Fun.id ~error:(fun _ -> Ws.top 32)
        in
        check
          "T5-2 (Store row, hull negative): a store outside the hull is untouched — its key \
           cell stays wide"
          (Ws.equal (cell_n hkb_n) (Ws.of_clp (Clp.interval ~width:32 (w32 0) (w32 200))));
        check
          "T5-2 (Store row, hull negative): a store outside the hull leaves the data \
           producers at their forward values"
          (Ws.equal (AI.find_word 32 refined_n hb_n) (AI.find_word 32 forward_n hb_n)
          && Ws.equal (AI.find_word 32 refined_n ha_n) (AI.find_word 32 forward_n ha_n)));

    (* The cross-block cell carry: the store that wrote the cell is in
       ANOTHER block; the guard block's walk still delivers the load's
       constraint across the boundary — the walked block's state (and
       the taken view's state after the fixpoint, whose memory rides
       the edge) holds the constrained cell. *)
    pin "INT-33"
      "C3: a cell constraint crosses the block boundary — the store is in another block, and the \
       guard block's walk delivers the constrained cell"
      (fun () ->
        let mem = memv "cb_m" in
        let rbp = frame_ptr in
        let ta = Var.create ~is_virtual:true ~fresh:false "cb_a" (Type.Imm 32) in
        let tb = Var.create ~is_virtual:true ~fresh:false "cb_b" (Type.Imm 32) in
        let t2 = Var.create ~is_virtual:true ~fresh:false "cb_t" (Type.Imm 32) in
        let ka = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 16))) in
        let kb = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
        let sub, tids =
          sub_of "cb_carry"
            [ [ Def.create rbp (Bil.Var sp);
                Def.create ta (Bil.Load (Bil.Var mem, ka, LittleEndian, `r32));
                Def.create tb (Bil.Var ta);
                Def.create mem (Bil.Store (Bil.Var mem, kb, Bil.Var tb, LittleEndian, `r32)) ],
              [ (1, mk_goto) ];
              [ Def.create t2 (Bil.Load (Bil.Var mem, kb, LittleEndian, `r32)) ],
              [ (2, fun tt ->
                    mk_jmp_to tt (Bil.BinOp (Bil.EQ, Bil.Var t2, Bil.Int (Cbat_word.to_word (w32 6)))));
                (3, fun tt ->
                    mk_jmp_to tt
                      (Bil.UnOp (Bil.NOT, Bil.BinOp (Bil.EQ, Bil.Var t2, Bil.Int (Cbat_word.to_word (w32 6)))))) ];
              [], [ (0, mk_ret) ];
              [], [ (0, mk_ret) ] ]
        in
        (* The guard block (it loads the cell and guards on it) and the
           block its taken edge leads to. *)
        let guard_tid = tids.(1) and taken_tid = tids.(2) in
        let key_ofw w =
          match Mem.Key.of_wordset (Ws.stack_word_i64 (Stdlib.Int64.of_int w)) with
          | [ k ] -> k
          | _ -> failwith "key"
        in
        let k8 = key_ofw (-8) in
        let wide = Ws.of_clp (Clp.interval ~width:32 (w32 0) (w32 200)) in
        let wide_mem =
          Mem.add
            (Mem.add
               (Mem.top { Mem.addr_width = 64; Mem.addressable_width = 8 })
               ~key:(key_ofw (-16)) ~data:(Mem.Val.create wide LittleEndian))
            ~key:k8 ~data:(Mem.Val.create wide LittleEndian)
        in
        let entry = AI.add_memory (anchored_entry ()) ~key:mem ~data:wide_mem in
        let sol =
          static_graph_vsa ~synth:Hike.Synth.empty ~abi:Hike_abi.x86_64_sysv sub
            (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv ~entry sub)
        in
        (* The walk follows the exact SSA definition: the seed is the
           version the block defines, and the state carries its value.
           The address is the frame-pointer version the block holds. *)
        let t2_v =
          match def_version sub guard_tid t2 with
          | Some v -> v
          | None -> failwith "C3: no version of t2"
        in
        let rbp_v = version_at sub guard_tid frame_ptr in
        let kb_v =
          Bil.BinOp (Bil.MINUS, Bil.Var rbp_v, Bil.Int (Cbat_word.to_word (w64 8)))
        in
        let cell_of env =
          Result.fold
            (Vsa.Test_seam.denote_imm_exp ~synth:Hike.Synth.empty
               (Bil.Load (Bil.Var mem, kb_v, LittleEndian, `r32)) env)
            ~ok:Fun.id ~error:(fun _ -> Ws.top 32)
        in
        let rctx = mk_rctx ~synth:Hike.Synth.empty ~abi:Hike_abi.x86_64_sysv sub in
        let blk1 = Term.find_exn blk_t sub guard_tid in
        (* Walk-level: the guard block's walk returns the block's state
           with the constrained cell. *)
        let refined =
          Vsa.Test_seam.refine_edge ~sol ~rctx
            ~seeds:(Var.Set.singleton t2_v)
            (AI.add_word entry ~key:t2_v ~data:(Ws.singleton (w32 6))) blk1
        in
        check
          "C3: the constraint crosses the block boundary — the walked block's state holds the \
           constrained cell {6}"
          (Ws.equal (cell_of refined) (Ws.singleton (w32 6)));
        (* Fixpoint-level: the taken view's state carries it too — the
           memory rides the edge, and the edge's walk constrained the
           cell. *)
        let midx = { Mem.addr_width = 64; Mem.addressable_width = 8 } in
        let taken_cell =
          let mv = AI.find_memory midx (Graphlib.Std.Solution.get sol taken_tid) mem in
          Mem.Val.data (Mem.find (32, LittleEndian) mv k8)
        in
        check
          "C3: the taken view's state holds the constrained cell {6} (the store is in another \
           block)"
          (Ws.equal taken_cell (Ws.singleton (w32 6))));

    (* Pin F: the negative store match — a store that must NOT match
       (mismatched endianness, mismatched width, or a disjoint key)
       delivers nothing: the store's data producers stay unconstrained. *)
    pin "INT-34"
      "F: a store whose shape mismatches the read (endian, width) or whose key is disjoint \
       delivers nothing — the data producers stay unconstrained"
      (fun () ->
        let mk ~(store_endian : endian) ~(store_sz : Size.t) ~(load_addr : exp)
            ~(load_endian : endian) ~(seed_wide : Mem.Key.t list)
            ~(seed_data : Ws.t) : AI.t * var * var * AI.t * sub term * tid =
          let mem = memv "pf_m" in
          let rbp = frame_ptr in
          (* The producing chain runs at the store's own width. *)
          let data_w = Size.in_bits store_sz in
          let data_sz = store_sz in
          let ta = Var.create ~is_virtual:true ~fresh:false "pf_a" (Type.Imm data_w) in
          let tb = Var.create ~is_virtual:true ~fresh:false "pf_b" (Type.Imm data_w) in
          let t2 = Var.create ~is_virtual:true ~fresh:false "pf_t" (Type.Imm 32) in
          let ka = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 16))) in
          let kb = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
          let sub, _ =
            sub_of "pf_store_row"
              [ [ Def.create rbp (Bil.Var sp);
                  Def.create ta (Bil.Load (Bil.Var mem, ka, LittleEndian, data_sz));
                  Def.create tb (Bil.Var ta);
                  Def.create mem
                    (Bil.Store (Bil.Var mem, kb, Bil.Var tb, store_endian, store_sz));
                  Def.create t2 (Bil.Load (Bil.Var mem, load_addr, load_endian, `r32)) ],
                [ (1, fun tt ->
                      mk_jmp_to tt
                        (Bil.BinOp (Bil.EQ, Bil.Var t2, Bil.Int (Cbat_word.to_word (w32 6))))) ];
                [], [ (0, mk_ret) ] ]
          in
          let base =
            Core.List.fold (List.rev seed_wide)
              ~init:(Mem.top { Mem.addr_width = 64; Mem.addressable_width = 8 })
              ~f:(fun m k -> Mem.add m ~key:k ~data:(Mem.Val.create seed_data LittleEndian))
          in
          let entry = AI.add_memory (anchored_entry ()) ~key:mem ~data:base in
          let sol =
            static_graph_vsa ~synth:Hike.Synth.empty ~abi:Hike_abi.x86_64_sysv
              sub
              (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv ~entry sub)
          in
          let rctx = mk_rctx ~synth:Hike.Synth.empty ~abi:Hike_abi.x86_64_sysv sub in
          let blk = List.nth (Term.enum blk_t sub |> Seq.to_list) 0 in
          (* The forward state: the block's definitions replayed from the
             block's own IN state — the values the walk starts from. *)
          let forward =
            Vsa.Test_seam.denote_defs ~synth:Hike.Synth.empty blk
              (Graphlib.Std.Solution.get sol (Term.tid blk))
          in
          (* The walk follows the exact SSA definition: the seed is the
             version the block defines, and the state carries its value. *)
          let t2_v =
            match def_version sub (Term.tid blk) t2 with
            | Some v -> v
            | None -> failwith "F: no version of t2"
          in
          let entry = AI.add_word entry ~key:t2_v ~data:(Ws.singleton (w32 6)) in
          let refined =
            Vsa.Test_seam.refine_edge ~sol ~rctx
              ~seeds:(Var.Set.singleton t2_v)
              entry blk
          in
          (refined, ta, tb, forward, sub, Term.tid blk)
        in
        let rbp = frame_ptr in
        let kb = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
        let k24 = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 24))) in
        let key_ofw w =
          match Mem.Key.of_wordset (Ws.stack_word_i64 (Stdlib.Int64.of_int w)) with
          | [ k ] -> k
          | _ -> failwith "key"
        in
        (* No delivery: each producer keeps its forward value at the edge. *)
        let unconstrained refined forward ta tb fsub fblk =
          let at v st =
            let version = version_at fsub fblk v in
            let width = match Var.typ v with Type.Imm w -> w | _ -> 64 in
            AI.find_word width st version in
          Ws.equal (at ta refined) (at ta forward) && Ws.equal (at tb refined) (at tb forward)
        in
        (* Endian: the store writes LittleEndian, the read is BigEndian. *)
        let r_e, ta_e, tb_e, f_e, s_e, blk_e =
          mk ~store_endian:LittleEndian ~store_sz:`r32 ~load_addr:kb
            ~load_endian:BigEndian ~seed_wide:[ key_ofw (-16); key_ofw (-8) ]
            ~seed_data:(Ws.top 32) in
        check "F (endian): a foreign-endian store's data producers stay unconstrained"
          (unconstrained r_e f_e ta_e tb_e s_e blk_e);
        (* Width: the store writes 8 bytes, the read takes 4. *)
        let r_w, ta_w, tb_w, f_w, s_w, blk_w =
          mk ~store_endian:LittleEndian ~store_sz:`r64 ~load_addr:kb
            ~load_endian:LittleEndian ~seed_wide:[ key_ofw (-16); key_ofw (-8) ]
            ~seed_data:(Ws.of_clp (Clp.interval ~width:32 (w32 0) (w32 200))) in
        check "F (width): a wider store's data producers stay unconstrained"
          (unconstrained r_w f_w ta_w tb_w s_w blk_w);
        (* Disjoint key: the read's cell is elsewhere. *)
        let r_d, ta_d, tb_d, f_d, s_d, blk_d =
          mk ~store_endian:LittleEndian ~store_sz:`r32 ~load_addr:k24
            ~load_endian:LittleEndian ~seed_wide:[ key_ofw (-16); key_ofw (-24) ]
            ~seed_data:(Ws.of_clp (Clp.interval ~width:32 (w32 0) (w32 200))) in
        check "F (disjoint): a store outside the read's range leaves the producers unconstrained"
          (unconstrained r_d f_d ta_d tb_d s_d blk_d));

    (* Pin A: the empty cell meet is the identity — the cell keeps its
       stored value; the dead-path bottom is never written. *)
    pin "INT-32"
      "A: a cell meet whose intersection is empty leaves the env unchanged (the stored value        stays, no dead-path bottom)"
      (fun () ->
        let m = memv "pina_m" in
        let rbp = frame_ptr in
        let addr_e = Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8))) in
        let key = key_of (Ws.stack_word_i64 (-8L)) in
        let cell5 =
          Mem.add
            (Mem.top { Mem.addr_width = 64; Mem.addressable_width = 8 })
            ~key ~data:(Mem.Val.create (Ws.singleton (w32 5)) LittleEndian)
        in
        let entry = AI.add_memory (anchored_entry ()) ~key:m ~data:cell5 in
        let refined =
          Vsa.Test_seam.constrain_operands ~synth:Hike.Synth.empty
            ~landmarks:(Cbat_landmarks.create ()) ~env:entry
            (Bil.Load (Bil.Var m, addr_e, LittleEndian, `r32))
            (Ws.singleton (w32 6))
        in
        let cell =
          Mem.Val.data
            (Mem.find (32, LittleEndian)
               (AI.find_memory { Mem.addr_width = 64; Mem.addressable_width = 8 } refined m)
               key)
        in
        check
          "A: the cell keeps its stored {5} — the empty meet writes nothing, not the dead-path            bottom"
          (Ws.equal cell (Ws.singleton (w32 5)));
        check "A: the env is unchanged by the empty meet" (AI.equal refined entry));

    (* T5-4 (head extrapolation): a cell widens strictly by its OWN
       entries — no own entries plain-widen; own entries translate by
       their own steps; a bottom old state stays the plain widen.  One
       pin per logical check. *)
    pin "INT-20" "T5-4 contrast: the plain memory widen drives the cell data infinite"
      (fun () ->
        let mv = memv "t5x_m" in
        let xv = Var.create ~is_virtual:true ~fresh:false "t5x_w" (Type.Imm 32) in
        let key = key_of (Ws.singleton (w32 100)) in
        let midx = { Mem.addr_width = 32; Mem.addressable_width = 8 } in
        let mkstate (d : Ws.t) (wd : Ws.t) : AI.t =
          let m = Mem.add (Mem.top midx) ~key ~data:(Mem.Val.create d LittleEndian) in
          AI.add_word (AI.add_memory AI.top ~key:mv ~data:m) ~key:xv ~data:wd
        in
        let cell_of (st : AI.t) : Ws.t =
          Mem.Val.data (Mem.find (32, LittleEndian) (AI.find_memory midx st mv) key)
        in
        let d_old = Ws.singleton (w32 1) in
        let d_new = Ws.of_clp (Clp.interval ~width:32 (w32 1) (w32 2)) in
        let w_old = Ws.singleton (w32 0) and w_new = Ws.singleton (w32 1) in
        let plain = AI.widen_join (mkstate d_old w_old) (mkstate d_new w_new) in
        check "T5-4 (contrast): the plain memory widen drives the cell data infinite"
          (Ws.is_infinite (cell_of plain)));

    (* F1: the jle-counter head's lower bound is the entry constant. *)
    pin "INT-13" "LM F1: the jle-counter head and taken view lower bounds are the entry constant 0"
      (fun () ->
        let sub, l1_tid, b1_tid, _ = lm_jle_loop ~k1:(w32 100) () in
        let sol = run_anchored sub in
        let i = Var.create ~is_virtual:false ~fresh:false "lm_i" (Type.Imm 32) in
        let head_i = value_at sub sol l1_tid i in
        check_bound "property LM F1: the head's lower bound is the entry constant 0"
          (Ws.min_elem head_i) (fun lo -> Cbat_word.equal lo (w32 0));
        (* The taken view's state is the body's IN-state. *)
        let taken_i = value_at sub sol b1_tid i in
        check_bound "property LM F1: the taken view's lower bound is the entry constant 0"
          (Ws.min_elem taken_i) (fun lo -> Cbat_word.equal lo (w32 0)));

        (* F1-FT: the fallthrough-edge fixture — the head, taken body, and
       fallthrough edge pin the delivered counter values. *)
    pin "INT-15"
      "LM F1-FT: the head, taken body, and fallthrough edge pin the delivered counter values"
      (fun () ->
        let k, sub, sol, l1_tid, b1_tid = lm_jne_run () in
        let i = Var.create ~is_virtual:false ~fresh:false "lm_ne_i" (Type.Imm 32) in
        let head_i = value_at sub sol l1_tid i in
        check_bound "property LM F1-FT: the head's lower bound is the entry constant 0 (vertex side \
                     of the pin)"
          (Ws.min_elem head_i) (fun lo -> Cbat_word.equal lo (w32 0));
        check_bound "property LM F1-FT: the head's upper bound is the landmark K (vertex side of the \
                     pin)"
          (Ws.max_elem head_i) (fun hi -> Cbat_word.equal hi k);
        let body_i = value_at sub sol b1_tid i in
        check_bound "property LM F1-FT: the taken body's lower bound is the entry constant 0"
          (Ws.min_elem body_i) (fun lo -> Cbat_word.equal lo (w32 0));
        check_bound "property LM F1-FT: the taken body's upper bound is K-1 (the guard excluded the \
                     landmark)"
          (Ws.max_elem body_i) (fun hi -> Cbat_word.equal hi (Cbat_word.pred k));
        (* The fallthrough exit receives no counter (it has no phi for
           it), so the edge's own delivery is the observable: the
           production's edge step meets the guard's cond into the
           counter the head holds. *)
        let exits = exit_blocks_of sub in
        let exit_tid =
          match exits with [ b ] -> Term.tid b | _ -> assert false
        in
        let guard_blk = Term.find_exn blk_t sub l1_tid in
        let fall_jmp =
          Term.enum jmp_t guard_blk
          |> Seq.find ~f:(fun j ->
                 match Jmp.kind j with
                 | Goto (Direct t) -> Tid.equal t exit_tid
                 | _ -> false)
          |> Base.Option.value_exn
        in
        let rctx = mk_rctx ~synth:Hike.Synth.empty ~abi:Hike_abi.x86_64_sysv sub in
        let post =
          Vsa.Test_seam.denote_defs ~synth:Hike.Synth.empty guard_blk
            (Graphlib.Std.Solution.get sol l1_tid)
        in
        let refined =
          Vsa.Test_seam.refine_edge_inline ~sol ~rctx ~discarded:false guard_blk post
            (Jmp.cond fall_jmp)
        in
        let i_v =
          match phi_version sub l1_tid i with
          | Some v -> v
          | None -> failwith "F1-FT: the head holds no phi for the counter"
        in
        check
          "property LM F1-FT: the fallthrough edge pins the counter to {K} exactly (edge side of \
           the pin)"
          (Ws.equal (AI.find_word 32 refined i_v) (Ws.singleton k)));

    pin "INT-19" "a constraint follows a copied load back to its stack cell"
      (fun () ->
        let mem = memv "load_constraint_mem" in
        let loaded = Var.create ~is_virtual:true "loaded" (Type.Imm 32) in
        let copied = Var.create ~is_virtual:true "copied" (Type.Imm 32) in
        let addr = Bil.BinOp (Bil.MINUS, Bil.Var frame_ptr,
            Bil.Int (Cbat_word.to_word (w64 8))) in
        let sub, tids = sub_of "copied_load"
            [ [ Def.create loaded (Bil.Load (Bil.Var mem, addr, LittleEndian, `r32));
                Def.create copied (Bil.Var loaded) ], [] ] in
        let key = match Mem.Key.of_wordset (Ws.stack_word_i64 (-8L)) with
          | [ key ] -> key | _ -> Alcotest.fail "expected one stack cell" in
        let wide = Ws.of_clp (Clp.interval ~width:32 (w32 0) (w32 200)) in
        let memory = Mem.add
            (Mem.top { Mem.addr_width = 64; addressable_width = 8 })
            ~key ~data:(Mem.Val.create wide LittleEndian) in
        let entry = AI.add_memory (anchored_entry ()) ~key:mem ~data:memory in
        let abi = Hike.Abi.x86_64_sysv in
        let sol = static_graph_vsa ~synth:Hike.Synth.empty ~abi sub
            (Vsa.init_sol ~abi ~entry sub) in
        let block = Term.find_exn blk_t sub tids.(0) in
        let copied = Base.Option.value_exn (def_version sub tids.(0) copied) in
        let rctx = mk_rctx ~synth:Hike.Synth.empty ~abi sub in
        let expected = Ws.singleton (w32 100) in
        let refined = Vsa.Test_seam.refine_edge ~sol ~rctx
            ~seeds:(Var.Set.singleton copied)
            (AI.add_word entry ~key:copied ~data:expected) block in
        let read env = Mem.Val.data
            (Mem.find (32, LittleEndian) (AI.find_memory (Mem.get_idx memory) env mem) key) in
        check_ws "cell before the constraint" wide (read entry);
        check_ws "cell after the constraint" expected (read refined));

    (* Pin B (re-pinned): the cell's own Zero arm advances and WIDENS.
       The join form this pin once asserted is the corpus-refuted
       candidate — a loop-carried cell never stabilizes under a plain
       join (out_section_sweep/out_rodata_strings ground to the 6000-
       visit backstop), so the widening IS the cell's tuned Zero
       action; the word's Zero joins. *)
    pin "INT-36"
      "B (re-pinned): a cell whose entry is Zero advances its own row and widens — the        loop-stabilizing form"
      (fun () ->
        let mv = memv "pib_m" in
        let key = key_of (Ws.singleton (w32 100)) in
        let midx = { Mem.addr_width = 32; Mem.addressable_width = 8 } in
        let mkstate (d : Ws.t) : AI.t =
          let m = Mem.add (Mem.top midx) ~key ~data:(Mem.Val.create d LittleEndian) in
          AI.add_memory AI.top ~key:mv ~data:m
        in
        let cell_of (st : AI.t) : Ws.t =
          Mem.Val.data (Mem.find (32, LittleEndian) (AI.find_memory midx st mv) key)
        in
        let h = Tid.for_name "pib_head" in
        let lm = Cbat_landmarks.create () in
        let cl = Cbat_landmarks.Cell (Mem.Key.cell_key key) in
        (* One fresh cell reading: its own arm is Zero.  The head's arm
           is Inf, so the cell reads its own row. *)
        Cbat_landmarks.record lm ~head:h ~key:cl ~bound:(w32 8)
          ~is_upper:true ~warmed:false ~dist:2;
        let d_old = Ws.singleton (w32 1) in
        let d_new = Ws.of_clp (Clp.interval ~width:32 (w32 1) (w32 3)) in
        let joined =
          AI.widen_with_landmarks ~head:h ~landmarks:lm
            ~need:(Core.Int.Set.singleton (Cbat_var_id.intern mv))
            (mkstate d_old) (mkstate d_new)
        in
        let c = cell_of joined in
        check "B: the cell's Zero arm widens — the loop-stabilizing form (the join variant                grinds the corpus fixpoint to the visit budget)"
          (Ws.is_infinite c);
        (* The advance rotated the cell's own row. *)
        check "B: the advance committed the cell's own reading"
          (match Cbat_landmarks.entries lm h cl with
           | [ e ] -> (match e.Cbat_landmarks.dist_p, e.Cbat_landmarks.dist with
                       | Some 2, None -> true
                       | _ -> false)
           | _ -> false);
        (* The contrast at the same shape without the entry: plain widen. *)
        let lm2 = Cbat_landmarks.create () in
        let widened =
          AI.widen_with_landmarks ~head:h ~landmarks:lm2
            ~need:(Core.Int.Set.singleton (Cbat_var_id.intern mv))
            (mkstate d_old) (mkstate d_new)
        in
        check "B (contrast): without own entries the cell widens (INT-20's baseline)"
          (Ws.is_infinite (cell_of widened)));

    (* Pin C: per-key consumption — a word-driven arm does not rotate a
       cell's entries, and the clear spends only what was consumed. *)
    pin "INT-37"
      "C: the head's arm spends only the key it consumed — a word advance leaves the cell's        entries, and a word extrapolation clears its own row only"
      (fun () ->
        let h = Tid.for_name "pic_head" in
        let mv = memv "pic_m" in
        let key = key_of (Ws.singleton (w32 100)) in
        let midx = { Mem.addr_width = 32; Mem.addressable_width = 8 } in
        let cl = Cbat_landmarks.Cell (Mem.Key.cell_key key) in
        let mkstate (d : Ws.t) (wd : Ws.t) : AI.t =
          let m = Mem.add (Mem.top midx) ~key ~data:(Mem.Val.create d LittleEndian) in
          AI.add_word (AI.add_memory AI.top ~key:mv ~data:m) ~key:lw_var ~data:wd
        in
        (* The Zero half: the head's word arm advances the word's own
           row; the cell — no own entries, no own Zero — is not
           advanced, and no cell row appears. *)
        let lm = Cbat_landmarks.create () in
        Cbat_landmarks.record lm ~head:h ~key:lw ~bound:(w32 50)
          ~is_upper:true ~warmed:false ~dist:4;
        let j =
          AI.advance_join_landmarks ~head:h ~landmarks:lm
            ~need:(Core.Int.Set.singleton (Cbat_var_id.intern lw_var))
            (mkstate (Ws.singleton (w32 1)) (Ws.singleton (w32 0)))
            (mkstate (Ws.singleton (w32 2)) (Ws.singleton (w32 1)))
        in
        ignore j;
        check "C (Zero): the word-driven advance rotated the word row"
          (match Cbat_landmarks.entries lm h lw with
           | [ e ] -> (match e.Cbat_landmarks.dist_p, e.Cbat_landmarks.dist with
                       | Some 4, None -> true | _ -> false)
           | _ -> false);
        check "C (Zero): the word-driven advance left no cell row behind"
          (Cbat_landmarks.entries lm h cl = []);
        (* The Finite half: a word extrapolation clears its own row; the
           cell row survives. *)
        let lm2 = Cbat_landmarks.create () in
        Cbat_landmarks.record lm2 ~head:h ~key:lw ~bound:(w32 50)
          ~is_upper:true ~warmed:false ~dist:10;
        Cbat_landmarks.advance lm2 h lw;
        Cbat_landmarks.record lm2 ~head:h ~key:lw ~bound:(w32 50)
          ~is_upper:true ~warmed:false ~dist:6;
        Cbat_landmarks.record lm2 ~head:h ~key:cl ~bound:(w32 8)
          ~is_upper:true ~warmed:false ~dist:2;
        let w =
          AI.selective_widen_extrapolate ~head:h ~landmarks:lm2
            ~need:(Core.Int.Set.singleton (Cbat_var_id.intern lw_var))
            ~steps:1
            (mkstate (Ws.singleton (w32 0)) (Ws.singleton (w32 40)))
            (mkstate (Ws.singleton (w32 1)) (Ws.singleton (w32 41)))
        in
        ignore w;
        check "C (Finite): the word extrapolation spent its own row (cleared)"
          (Cbat_landmarks.entries lm2 h lw = []);
        check
          "C (Finite): the cell's row survives the word's clear, and its rotation came from            its OWN Zero arm"
          (match Cbat_landmarks.entries lm2 h cl with
           | [ e ] -> (match e.Cbat_landmarks.dist_p, e.Cbat_landmarks.dist with
                       | Some 2, None -> true | _ -> false)
           | _ -> false));

  ]

let () = run "integration" tests
