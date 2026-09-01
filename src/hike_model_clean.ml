(* Hike_model_clean — the MODEL-TRAFFIC CLEANER, stage 1 of hike-filter
   (the 2026-09-01 optimizability review, Candidate 3, commit 1).

   BAP's x86 call expansion and the -O0 prologue/epilogue idioms emit three
   classes of defs that are DEAD TRAFFIC IN THE LIFTED WORLD:

     - the call push ([RSP := RSP - 8; mem[RSP] := retaddr]): its cell is
       read by nobody — the lifted callee returns via a real LLVM ret and
       the epilogue pop dies with rule 3 below;
     - the prologue's [push rbp] pair + [mov rbp,rsp]: the saved slot is
       read only by the epilogue pop (rule 3);
     - the epilogue's pop/ret cluster ([#t := mem[RSP]]; [RBP := mem[RSP]];
       [RSP := RSP + 8]; [RSP := RBP - k]; the noreturn indirect call).

   Left in, they poison everything downstream: the retaddr push matches
   [is_outgoing_store] (a pushed-7th-arg shape) and BLOCKS its region's
   conversion at stack-to-locals; the epilogue loads pollute the region
   graph; and the emitter materializes them all as inttoptr-of-SP stores
   that defeat SROA and alias the caller's frame (the struct_arr_dynidx
   opt -O2 miscompile class).

   This module runs in HIKE-FILTER — FIRST in the chain, before relevance
   tagging, the VSA fixpoint, the region planner, stack-to-locals and DCE
   — so every later stage sees push-free BIL, and the tags the VSA then
   bakes are CONSISTENT with the cleaned lane.  The rules are POSITIONAL
   (no value-shape checks, no read-guards — the user's "no tricks"
   directive); each is sound by a separate argument:

     Rule 1 (CALL-ADJACENT PUSH): in a block whose jmps contain a Call,
       the LAST {[sp-delta-8], [store-at-sp]} pair.  BAP appends its
       synthesized push after the program's own defs, so the last pair is
       BAP's; the program's own [push arg; call] keeps its pair (its store
       is real callee-read traffic, invisible to intra-sub analysis —
       exactly why only the LAST pair matches).

     Rule 2 (PROLOGUE): in the ENTRY block, from def 0 (skipping leading
       flag defs): [#t := RBP]; [RSP := RSP - 8]; [mem[RSP] := #t]; then
       the [RBP := RSP] mov REWRITTEN IN PLACE to [RBP := RSP - 8] (RSP's
       local is now the pre-push value; the rewrite restores exactly the
       RBP the displacements were baked with — RBP-relative tags are
       IDENTICAL to the pre-clean BIL, and RSP-relative tags are computed
       fresh on the cleaned lane, consistently).  A genuine frame alloc
       ([subq $k, %rsp], k ≠ this cluster — its temp reads RSP, not RBP)
       does NOT match.

     Rule 3 (EPILOGUE TAIL): in a block whose jmp is the noreturn
       indirect call ([is_ret_epilogue_jmp] — the SAME shape
       [Hike_dce.ret_replacement] recognized; that rule MOVES here — the
       deletion of the temp the jmp reads and the jmp rewrite are one
       mechanism and must travel together), delete the contiguous tail
       cluster walking back: [#t := mem[sp-derived]] loads,
       [REG := #t]/[REG := mem[...]] restores of fp/callee-saved,
       [sp := sp ± 8] pops, [sp := fp - k] leaves, interleaved flag defs.
       Stops at the first def that is none of these.

   The compensations, same commit: [create_call_args] threads [sp - 8] as
   hike_stack on the degraded path (the callee's baked [+8] arg tags
   assume the retaddr cell directly below the args — machine-arithmetic:
   the caller's arg pushes end at sp, the would-be post-push is sp - 8,
   and [hike_stack + 8] must land on the first stack arg); the VSA's
   call-abstraction [+8] pop model is NEUTRALIZED in the production
   pipeline ([~retaddr_push_modeled:false] — the raw-library contract the
   L-E1 fixtures pin keeps the default); [restore_sp_after_call] is
   DELETED (the lane is flat across calls — the L-E1e/edge-keyed
   mechanism has no work left); [Hike_dce.ret_replacement] is DELETED
   (the mechanism lives here). *)

open Bap.Std
open Bap_core_theory
module Abi = Hike_abi

(* ------------------------------------------------------------------ *)
(* Shape predicates (positional — no value-shape checks).              *)
(* ------------------------------------------------------------------ *)

(* [is_sp_delta8]: [SP := SP ± 8] — the push decrement / the pop. *)
let is_sp_delta8 (sp : var) (d : def term) : bool =
  not (Convutils.is_mem (Def.lhs d))
  && Var.same (Var.base (Def.lhs d)) sp
  && (match Def.rhs d with
     | Bil.BinOp (Bil.MINUS, a, b) | Bil.BinOp (Bil.PLUS, a, b) ->
         (match a with Bil.Var v -> Var.same v sp | _ -> false)
         && (match b with
            | Bil.Int w -> Int64.equal (Word.to_int64_exn w) 8L
            | _ -> false)
     | _ -> false)

(* [is_store_at_sp]: [mem := mem with [SP, el]:_ <- v] — the pushed cell. *)
let is_store_at_sp (sp : var) (d : def term) : bool =
  Convutils.is_mem (Def.lhs d)
  && (match Def.rhs d with
     | Bil.Store (_, addr, _, _, _) -> (match addr with Bil.Var v -> Var.same v sp | _ -> false)
     | _ -> false)

(* [is_temp_copy]: [#t := <var>] — the push/pop materializations. *)
let is_temp_copy (d : def term) : bool =
  not (Convutils.is_mem (Def.lhs d))
  && (match Def.rhs d with Bil.Var _ -> true | _ -> false)

(* [is_named_temp]: the lhs is a BIL temp ([#t] — the lifter's
   materializations). *)
let is_named_temp (v : var) : bool =
  let name = Var.name v in
  String.length name > 0 && String.equal (String.sub name 0 1) "#"

(* [is_load_from_sp_mem]: [#t := mem[<sp-derived>]] — the pop load. *)
let is_load_from_sp_mem (sp : var) (d : def term) : bool =
  not (Convutils.is_mem (Def.lhs d))
  && (match Def.rhs d with
     | Bil.Load (_, addr, _, _) ->
         Base.Set.exists ~f:(fun v -> Var.same v sp) (Exp.free_vars addr)
     | _ -> false)

(* [is_reg_restore]: [REG := <var>] where REG ∈ fp ∪ callee-saved (the
   [pop rbp]/[pop rbx] shapes — the pop's second half). *)
let is_reg_restore (target : Theory.Target.t) (d : def term) : bool =
  not (Convutils.is_mem (Def.lhs d))
  && (match Def.rhs d with
     | Bil.Var _ ->
         let lhs = Var.base (Def.lhs d) in
         Abi.is_stack_reg (Abi.of_target target) lhs
         || Abi.is_callee_saved (Abi.of_target target) lhs
     | _ -> false)

(* [is_leave]: [SP := FP] / [SP := FP - k] — the [leave] idiom. *)
let is_leave (target : Theory.Target.t) (d : def term) : bool =
  not (Convutils.is_mem (Def.lhs d))
  && Var.same (Var.base (Def.lhs d)) (Abi.sp target)
  && (match Def.rhs d with
     | Bil.Var v -> Var.same v (Abi.fp target)
     | Bil.BinOp (Bil.MINUS, a, _) -> (match a with Bil.Var v -> Var.same v (Abi.fp target) | _ -> false)
     | _ -> false)

(* [is_flag_def]: lhs is a short all-caps flag reg (CF/OF/AF/PF/SF/ZF)
   — the side-effect of a real arithmetic def; never a data carrier. *)
let is_flag_def (d : def term) : bool =
  let name = Var.name (Var.base (Def.lhs d)) in
  String.length name > 0 && String.length name <= 3
  && String.for_all (fun c -> c >= 'A' && c <= 'Z') name
  && String.exists (fun c -> c = 'F') name

(* The epilogue jmp — EXACTLY the old [Hike_dce.ret_replacement]'s
   recognition (an indirect noreturn call reading a Var). *)
let is_ret_epilogue_jmp (j : jmp term) : bool =
  match Jmp.kind j with
  | Call c -> (match (Call.target c, Call.return c) with
               | Indirect (Bil.Var _), None -> true
               | _ -> false)
  | _ -> false

(* The var-free target: a fresh [Unknown] carries no Var dependency, so
   the rewritten jmp is dead to the free-vars-as-args signature. *)
let rewrite_ret_jmp (j : jmp term) : jmp term =
  match Jmp.kind j with
  | Call c when is_ret_epilogue_jmp j ->
      Jmp.create ~tid:(Term.tid j) ~cond:(Jmp.cond j)
        (Call
           (Call.create
              ~target:(Indirect (Bil.Unknown ("hike-model-ret", Type.Imm 64)))
              ()))
  | _ -> j

let is_call_jmp (j : jmp term) : bool =
  match Jmp.kind j with
  | Call c ->
      (* ONLY calls that RETURN: BAP's call expansion pushes the retaddr
         exactly for these ([call @f with return %L]); a noreturn call
         (the lifted ret epilogue) pushes NOTHING — its block's LAST
         store-at-sp pair is the PROLOGUE's [push rbp] in a single-block
         sub, which rule 1 must not eat (the +16-tag bug: rule 1 deleted
         the prologue pair and left [RBP := RSP] reading the PRE-push
         RSP). *)
      Option.is_some (Call.return c)
  | _ -> false

(* ------------------------------------------------------------------ *)
(* Rule 1: the call-adjacent retaddr push.                              *)
(* ------------------------------------------------------------------ *)

(* The LAST [store-at-sp] in the block, with its matching decrement
   scanning back over interleaved flag defs.  Returns the delete range
   [i, j) (decrement .. store inclusive). *)
let find_call_push_range (sp : var) (defs : def term list) :
    (int * int) option =
  let rec back i =
    if i < 0 then None
    else if is_store_at_sp sp (Base.List.nth_exn defs i) then
      let rec dec j =
        if j < 0 then None
        else if is_sp_delta8 sp (Base.List.nth_exn defs j) then Some j
        else if is_flag_def (Base.List.nth_exn defs j) then dec (j - 1)
        else None
      in
      (match dec (i - 1) with
       | Some j -> Some (j, i + 1)
       | None -> None)
    else back (i - 1)
  in
  back (Base.List.length defs - 1)

(* ------------------------------------------------------------------ *)
(* Rule 2: the prologue cluster.                                       *)
(* ------------------------------------------------------------------ *)

(* Match, at index i (skipping leading flag defs), the cluster
     [#t := RBP] (i)  [RSP := RSP - 8] (i+1)  [mem[RSP] := #t] (i+2)
   then (skipping flag defs) [RBP := RSP] (m).  The three cluster defs
   are deleted; the mov is REWRITTEN IN PLACE to [RBP := RSP - 8].  If
   no mov follows (a pushed callee-saved reg whose pop dies with rule
   3), the pair alone is deleted. *)
let clean_prologue (target : Theory.Target.t) (sp : var)
    (defs : def term list) : def term list =
  let fp = Abi.fp target in
  let n = Base.List.length defs in
  let is_rbp_temp (d : def term) =
    is_temp_copy d
    && (match Def.rhs d with Bil.Var v -> Var.same v fp | _ -> false)
  in
  let is_rbp_assign_rsp (d : def term) =
    (not (Convutils.is_mem (Def.lhs d)))
    && Var.same (Var.base (Def.lhs d)) fp
    && (match Def.rhs d with
       | Bil.Var v -> Var.same v sp
       | _ -> false)
  in
  let mov' m =
    Def.with_rhs (Base.List.nth_exn defs m)
      (Bil.BinOp
         (Bil.MINUS, Bil.Var sp, Bil.Int (Word.of_int64 ~width:64 8L)))
  in
  let rec scan i =
    if i + 2 >= n then defs
    else if is_flag_def (Base.List.nth_exn defs i) then scan (i + 1)
    else if is_rbp_temp (Base.List.nth_exn defs i)
         && is_sp_delta8 sp (Base.List.nth_exn defs (i + 1))
         && is_store_at_sp sp (Base.List.nth_exn defs (i + 2))
    then
      (* The [mov rbp,rsp] follows the WHOLE push sequence — the -O0
         prologue pushes r13/r12/rbx AFTER rbp before the mov ([#t:=RBP;
         dec; store; #t:=R13; dec; store; ...; RBP := RSP]) — so the
         scan must skip not just interleaved flag defs but FURTHER PUSH
         PAIRS and the frame-alloc [subq]'s cluster ([#t := RSP; dec-k;
         flags...]).  Positional, no value-shape tricks: it skips flag
         defs, temp-copies, sp-deltas, stores-at-sp, and sp/fp-derived
         loads/stores (the alloc cluster's own members), stopping at the
         first real body def.  The rewrite fires ONLY if the mov is
         found; else the whole cluster is KEPT (sound beats optimal). *)
      let rec mov m =
        if m >= n then None
        else
          let d = Base.List.nth_exn defs m in
          if is_rbp_assign_rsp d then Some m
          else if
            is_flag_def d
            || is_temp_copy d
            || is_sp_delta8 sp d
            || is_store_at_sp sp d
            || (Convutils.is_mem (Def.lhs d)
               && (match Def.rhs d with
                  | Bil.Load (_, a, _, _)
                  | Bil.Store (_, a, _, _, _) ->
                      Base.Set.exists ~f:(fun v ->
                          Abi.is_stack_reg (Abi.of_target target) v)
                          (Exp.free_vars a)
                  | _ -> false))
          then mov (m + 1)
          else None
      in
      (match mov (i + 3) with
       | Some m ->
           (* delete the pair + rewrite the mov IN PLACE: RSP's local is
              now the PRE-push value, so [RBP := RSP - 8] restores the
              machine RBP exactly. *)
           Base.List.filter_mapi defs ~f:(fun idx d ->
               if idx >= i && idx <= i + 2 then None
               else if idx = m then Some (mov' m)
               else Some d)
       | None ->
           (* NO adjacent mov: the cluster is a plain [push rbp] whose
              [RBP := RSP] sits FURTHER down (after the frame-alloc
              subq's flag cluster, the common -O0 shape).  Deleting the
              pair here would leave [RBP := RSP] reading the PRE-push RSP
              — every RBP-relative access shifts by +8 (the +16-tag bug:
              the callee reads its 7th arg at hike_stack+16 instead of
              +8).  Keep the whole cluster: with the pair intact, RSP is
              entry-8 at the mov and [RBP := RSP] = the machine value.
              The pair is merely less-optimal (8 frame bytes, one dead
              store) — SOUND beats optimal. *)
           defs)
    else defs
  in
  scan 0

(* ------------------------------------------------------------------ *)
(* Rule 3: the epilogue tail cluster.                                  *)
(* ------------------------------------------------------------------ *)

let clean_epilogue_tail (target : Theory.Target.t) (sp : var)
    (defs : def term list) : def term list =
  let killable (d : def term) : bool =
    is_sp_delta8 sp d
    || is_flag_def d
    || is_load_from_sp_mem sp d
    || is_reg_restore target d
    || is_leave target d
    || (is_temp_copy d && is_named_temp (Var.base (Def.lhs d)))
  in
  let rec suffix_len = function
    | [] -> 0
    | d :: rest when killable d -> 1 + suffix_len rest
    | _ -> 0
  in
  let k = suffix_len (Base.List.rev defs) in
  let n = Base.List.length defs in
  Base.List.filter_mapi defs ~f:(fun idx d ->
      if idx >= n - k then None else Some d)

(* ------------------------------------------------------------------ *)
(* The block/sub drivers.                                              *)
(* ------------------------------------------------------------------ *)

let clean_blk (target : Theory.Target.t) (sp : var) (is_entry : bool)
    (blk : blk term) : blk term =
  let defs = Term.enum def_t blk |> Seq.to_list in
  let jmps = Term.enum jmp_t blk |> Seq.to_list in
  let has_call = Base.List.exists jmps ~f:is_call_jmp in
  (* RULE 3 (epilogue-tail deletion) is CUT from commit 1 (2026-09-01):
     [is_load_from_sp_mem] matched legitimate spill RELOADS in the ret
     block (the sret_big corruption — build's reloaded sret-pointer lane
     eaten, RAX = -114 where a real pointer belonged).  The epilogue
     cluster is DCE's domain ([Hike_dce.ret_replacement] + the used-set
     sweep) and stays there; only the ret-jmp REWRITE is kept here —
     the same [Unknown] target [ret_replacement] substitutes, unchanged. *)
  let defs = defs in
  let defs =
    if has_call then
      match find_call_push_range sp defs with
      | Some (i, j) ->
          Base.List.filter_mapi defs ~f:(fun idx d ->
              if idx >= i && idx < j then None else Some d)
      | None -> defs
    else defs
  in
  let defs = if is_entry then clean_prologue target sp defs else defs in
  let jmps' = Base.List.map jmps ~f:rewrite_ret_jmp in
  let n_defs = Base.List.length defs in
  let n_orig = Term.enum def_t blk |> Seq.length in
  if n_defs = n_orig && Base.List.length jmps' = Base.List.length jmps then
    blk (* nothing changed — preserve the block term identically *)
  else
    (* rebuild via [Blk.Builder]: copy the (rare) phis, replace the defs
       with the cleaned list, the jmps with the rewritten list — tids and
       attrs ride on the terms; block attrs re-attached (the repo
       idiom, [simplify_jmps]). *)
    let bldr = Blk.Builder.init ~copy_phis:true ~copy_defs:false blk in
    Base.List.iter defs ~f:(fun d -> Blk.Builder.add_def bldr d);
    Base.List.iter jmps' ~f:(fun j -> Blk.Builder.add_jmp bldr j);
    let b = Blk.Builder.result bldr in
    Term.with_attrs b (Term.attrs blk)

let clean_sub (target : Theory.Target.t) (sub : sub term) : sub term =
  if Term.has_attr sub Sub.intrinsic then sub
  else
    let sp = Abi.sp target in
    let entry_tid =
      try Convutils.entry_blk_tid sub with _ -> Term.tid sub
    in
    let mapper =
      object
        inherit Term.mapper
        method! map_blk blk =
          let is_entry = Tid.equal (Term.tid blk) entry_tid in
          clean_blk target sp is_entry blk
      end
    in
    mapper#map_sub sub

(* The stage-1 hook for [filter_subs]: the whole program, every sub. *)
let clean_prog (target : Theory.Target.t) (prog : program term) :
    program term =
  Term.map sub_t prog ~f:(clean_sub target)
