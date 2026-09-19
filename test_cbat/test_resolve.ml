(* The indirect-target resolution's pins: the resolution predicate's
   four classes ([Hike.Resolve.resolve_target] — the singleton lifted
   sub resolves, the bounded multi-target set, the foreign singleton,
   and TOP take the pointer call), and the producer's indirect-transfer
   classification through the REAL fixpoint (the [T22-J] family: the
   [Ret] epilogue arm, the in-sub [Resolved] dispatch, the [Foreign]
   identity, the untagged structural transfers). *)

open Test_common
open Test_fixtures
open Bap.Std
open Bap_core_theory

module Sm = Hike.Stack_model
module Pr = Hike.Sections
module Hv = Hike.Vsa

(* 64-bit literal word (native-int [w64] covers 63 bits only). *)
let q64 (v : int64) : Cbat_word.t = Cbat_word.of_int64 ~width:64 v

(* The target-resolution predicate's four classes. *)

let run_t4_resolution () =
  let callee_tid = Tid.for_name "res_callee" in
  let lifted v = if Int64.equal v 0x1000L then Some callee_tid else None in
  let ws_singleton (v : int64) : Cbat_vsa.WordSet.t =
    Cbat_vsa.WordSet.singleton (w64 (Int64.to_int v))
  in
  (* 1. singleton lifted sub: the Resolved Call Site (direct). *)
  check "T4-RES singleton: a singleton naming a lifted sub resolves direct"
    (Hike.Resolve.resolve_target ~lookup:lifted (ws_singleton 0x1000L)
     = Some callee_tid);
  (* 2. bounded multi-target set: the pointer call. *)
  check "T4-RES multi: a bounded two-target set takes the pointer call"
    (Hike.Resolve.resolve_target ~lookup:lifted
       (Cbat_vsa.WordSet.union (ws_singleton 0x1000L)
          (ws_singleton 0x1008L))
     = None);
  (* 3. foreign singleton (no lifted sub at the address): pointer call. *)
  check "T4-RES foreign: a foreign singleton takes the pointer call"
    (Hike.Resolve.resolve_target ~lookup:lifted (ws_singleton 0x9999L) = None);
  (* 4. unresolvable (TOP): pointer call. *)
  check "T4-RES top: an unresolvable target set takes the pointer call"
    (Hike.Resolve.resolve_target ~lookup:lifted (Cbat_vsa.WordSet.top 64) = None);
  ()

(* Lane N8: the completion's rewrite — the indirect-transfer classes
   land in the BIR TERMS (the real [Ret] jmp, the guarded-goto
   dispatch series); the classes are no longer a map. *)

let jmps_of_blk sub i =
  List.nth (Term.enum blk_t sub |> Seq.to_list) i
  |> Term.enum jmp_t |> Seq.to_list

let run_jmp_kinds () =
  (* J1: the lifted return epilogue — [#t := mem[RSP]]; call #t
     noreturn — the target var's reaching def is the retaddr read. *)
  let j1_ra = v64 "t22_j1_ra" in
  let j1_ld =
    Def.create j1_ra (Bil.Load (Bil.Var (memv "t22_j1_m"), Bil.Var sp,
                                LittleEndian, `r64))
  in
  let j1, _ =
    sub_of "t22_ret"
      [ [ j1_ld ],
        [ (1, fun t -> Jmp.create (Call (Call.create ~target:(Indirect (Bil.Var j1_ra)) ()))) ];
        [], [ (0, mk_ret) ] ]
  in
  let _, j1' =
    produce Theory.Target.unknown (Program.create ~subs:[ j1 ] ()) j1
  in
  let j1_retaddr =
    let sol =
      Cbat_vsa.static_graph_vsa
        ~abi:Hike_abi.x86_64_sysv
        ~resolved:Tid.Map.empty []
        (Program.create ~subs:[ j1 ] ()) j1
        (Cbat_vsa.init_sol ~abi:Hike_abi.x86_64_sysv j1)
    in
    Hike.Cfg_complete.retaddr_defs ~abi:Hike.Abi.x86_64_sysv ~sol j1
  in
  check "T22-J1: the epilogue's [RSP] load is the retaddr read"
    (Core.Set.mem j1_retaddr (Term.tid j1_ld));
  check "N8-RET: the epilogue lands in the canonical return shape (a var-free return-less call)"
    (match jmps_of_blk j1' 0 with
     | [ j ] -> (
         match Jmp.kind j with
         | Call c -> (
             match (Call.return c, Call.target c) with
             | None, Indirect (Bil.Unknown _) -> true
             | _ -> false)
         | _ -> false)
     | _ -> false);
  (* J1b: the control — the same target read behind a return=Some call
     is a real indirect call, not the epilogue: no rewrite. *)
  let j1b, _ =
    sub_of "t22_call"
      [ [ j1_ld ],
        [ (1,
           fun t ->
             Jmp.create (Call (Call.create ~return:(Direct t) ~target:(Indirect (Bil.Var j1_ra)) ()))) ];
        [], [ (0, mk_ret) ] ]
  in
  let _, j1b' =
    produce Theory.Target.unknown (Program.create ~subs:[ j1b ] ()) j1b
  in
  check "T22-J1b: a return=Some call with the same target stays a call (no rewrite)"
    (match jmps_of_blk j1b' 0 with
     | [ j ] -> (
         match Jmp.kind j with Call _ -> true | _ -> false)
     | _ -> false);
  (* J2: the jump-table dispatch — the target var's denotation joins
     two in-sub block constants; block_addrs names both blocks' tids,
     so every word of the set resolves in-sub.  The rewrite lands the
     guarded-goto series: [sel=0x1010 ? b2; goto b1] — the lowest
     word's target is the default, so its own guard is redundant. *)
  let j2_sel = v64 "t22_j2_sel" in
  let j2_t1 = Def.create j2_sel (Bil.Int (Cbat_word.to_word (q64 0x1008L))) in
  let j2_t2 = Def.create j2_sel (Bil.Int (Cbat_word.to_word (q64 0x1010L))) in
  let head_flag = v1 "t22_flag" in
  let j2, tids =
    sub_of "t22_dispatch"
      [ [], [ (1, fun t -> mk_jmp_to t (Bil.Var head_flag)); (2, mk_goto) ];
        [ j2_t1 ], [ (3, mk_goto) ];
        [ j2_t2 ], [ (3, mk_goto) ];
        [], [ (4, fun _ -> Jmp.create (Goto (Indirect (Bil.Var j2_sel)))) ];
        [], [ (6, mk_goto) ];
        [], [ (6, mk_goto) ];
        [], [ (0, mk_ret) ] ]
  in
  let b1_tid = tids.(4) in
  let b2_tid = tids.(5) in
  let _, j2' =
    produce Theory.Target.unknown ~block_addrs:[ (0x1008L, b1_tid); (0x1010L, b2_tid) ]
      (Program.create ~subs:[ j2 ] ()) j2
  in
  let eq_word w j =
    match Jmp.cond j with
    | Bil.BinOp (Bil.EQ, Bil.Var v, Bil.Int w') ->
      Var.equal v j2_sel
      && Int64.equal (Word.to_int64_exn w') w
    | _ -> false
  in
  check "N8-DISP: the dispatch becomes a guarded-goto series in the existing block"
    (match jmps_of_blk j2' 3 with
     | [ g2; dflt ] ->
       (match Jmp.kind g2, Jmp.kind dflt with
        | Goto (Direct t2), Goto (Direct td) ->
          Tid.equal t2 b2_tid && Tid.equal td b1_tid
          && eq_word 0x1010L g2
          && (match Jmp.cond dflt with
              | Bil.Int w -> Word.equal w (Word.one 1)
              | _ -> false)
        | _ -> false)
     | _ -> false);
  (* J3: a foreign pointer target (a constant naming no block) — the
     indirect transfer stays. *)
  let j3_t = v64 "t22_j3_t" in
  let j3_ld = Def.create j3_t (Bil.Int (Cbat_word.to_word (q64 0x400000L))) in
  let j3, _ =
    sub_of "t22_foreign"
      [ [ j3_ld ], [ (1, fun _ -> Jmp.create (Goto (Indirect (Bil.Var j3_t)))) ];
        [], [ (0, mk_ret) ] ]
  in
  let _, j3' =
    produce Theory.Target.unknown (Program.create ~subs:[ j3 ] ()) j3
  in
  check "T22-J3: a foreign pointer target is untouched by the rewrite"
    (match jmps_of_blk j3' 0 with
     | [ j ] -> (
         match Jmp.kind j with Goto (Indirect _) -> true | _ -> false)
     | _ -> false);
  (* J3b: the TOP target (an undefined var) stays too. *)
  let j3b_top = v64 "t22_j3b_top" in
  let j3b, _ =
    sub_of "t22_top"
      [ [], [ (1, fun _ -> Jmp.create (Goto (Indirect (Bil.Var j3b_top)))) ];
        [], [ (0, mk_ret) ] ]
  in
  let _, j3b' =
    produce Theory.Target.unknown (Program.create ~subs:[ j3b ] ()) j3b
  in
  check "T22-J3b: a TOP target is untouched by the rewrite"
    (match jmps_of_blk j3b' 0 with
     | [ j ] -> (
         match Jmp.kind j with Goto (Indirect _) -> true | _ -> false)
     | _ -> false)

let run () =
  run_t4_resolution ();
  run_jmp_kinds ()
