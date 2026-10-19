(* A function's summary: the only fact a caller reads about a callee,
   computed once the callee's own fixpoint is final (ADR 0027).  It
   takes no caller context, so it never changes after it is published.

   [written] is the may-write set over the caller-saved registers'
   interned ids; [None] is any of them.  [returns] is whether control may
   come back to the caller. *)

open Bap.Std

module Vsa = Cbat_vsa
module Model = Hike_stack_model

type t = { written : Core.Int.Set.t option; returns : bool }

(* Nothing proven: any caller-saved register written, control may come
   back. *)
let unknown = { written = None; returns = true }

(* Nothing written, never comes back: where a recursive cycle's
   solve starts (ADR 0027 decision 6). *)
let optimistic = { written = Some Core.Int.Set.empty; returns = false }

let union_written a b =
  match a, b with Some x, Some y -> Some (Core.Set.union x y) | _ -> None

let join a b = { written = union_written a.written b.written; returns = a.returns || b.returns }

let equal a b =
  Base.Option.equal Core.Set.equal a.written b.written && Bool.equal a.returns b.returns

(* One reachable exit's effect: what it adds to the written set and
   whether control may reach the caller through it. *)
type contribution = { adds : Core.Int.Set.t option; back : bool }

let internal = { adds = Some Core.Int.Set.empty; back = false }
let pessimistic = { adds = None; back = true }

let join_contribution a b = { adds = union_written a.adds b.adds; back = a.back || b.back }

(* A transfer into a callee: its writes join; a tail transfer comes back
   iff the callee does.  An unknown callee writes anything. *)
let through ~tail (s : t option) : contribution =
  match s with
  | None -> { adds = None; back = tail }
  | Some s -> { adds = s.written; back = tail && s.returns }

(* [callee] answers a lifted, external or intrinsic target's final
   summary; [slot] the summary of the external a linker slot names;
   [lookup] an entry address's sub.  [envs] and [block_addrs] are the
   sub's own solve results. *)
let of_solved ~(abi : Hike_abi.t) ~(synth : Hike_synth.table)
    ~(callee : Tid.t -> t option)
    ~(slot : int64 -> t option) ~(lookup : int64 -> Tid.t option)
    ~(foreign_slots : Core.Int64.Set.t) ~(block_addrs : Tid.t Addr.Map.t)
    ~(envs : (Vsa.AI.t * Vsa.AI.t) Tid.Map.t) (sub : sub term) : t =
  let own_blocks =
    Term.enum blk_t sub |> Seq.map ~f:Term.tid |> Seq.to_list
    |> Core.Set.of_list (module Tid)
  in
  let index = Hike_transfer.index_of_sub sub in
  let reachable blk =
    match Core.Map.find envs (Term.tid blk) with
    | Some (pre, _) -> not (Vsa.AI.equal pre Vsa.AI.bottom)
    | None -> false
  in
  (* Only reachable blocks denote, so their states exist. *)
  let denote ~blk ?def e =
    let pre, post = Core.Map.find_exn envs (Term.tid blk) in
    Vsa.denote_exp_at ~synth ~post ~pre ~blk ?def e
  in
  let foreign e =
    match Hike_transfer.slot_of_target ~synth ~index e with
    | Some a when Core.Set.mem foreign_slots a -> Some a
    | _ -> None
  in
  (* A return leaves RSP at entry + word unless the body moved it some
     other way; the ABI restore is assumed either way (decision 8). *)
  let check_restore blk =
    let restored =
      match denote ~blk (Bil.Var (Model.version_at_end blk abi.Hike_abi.sp)) with
      | Ok ws ->
        Base.Option.equal Int64.equal (Model.singleton_stack_position ws)
          (Some (Int64.add Model.segment_base (Int64.of_int abi.Hike_abi.word)))
      | Error _ -> false
    in
    if not restored then
      Hike_diag.warn
        "summary: sub %s: RSP at a return is not entry + word; the ABI \
         restore is assumed"
        (Sub.name sub)
  in
  (* An indirect jump: each case word is a block of this sub or a known
     entry (a tail call); any other target is unknown. *)
  let indirect_goto blk e =
    match foreign e with
    | Some a -> through ~tail:true (slot a)
    | None -> (
      match
        Hike_cfg_complete.case_words ~denote ~block_addrs
          ~last_defs:(Vsa.last_defs blk) ~blk e
      with
      | None -> pessimistic
      | Some words ->
        Base.List.fold words ~init:internal ~f:(fun acc w ->
            join_contribution acc
              (match Cbat_word.to_int64 w with
               | Error _ -> pessimistic
               | Ok a -> (
                 match Core.Map.find block_addrs (Addr.of_int64 a) with
                 | Some t when Core.Set.mem own_blocks t -> internal
                 | _ -> (
                   match lookup a with
                   | Some t -> through ~tail:true (callee t)
                   | None -> pessimistic)))))
  in
  let indirect_call blk ~tail e =
    match foreign e with
    | Some a -> through ~tail (slot a)
    | None -> (
      match denote ~blk e with
      | Ok ws -> (
        match Hike_resolve.resolve_target ~lookup ws with
        | Some t -> through ~tail (callee t)
        | None -> through ~tail None)
      | Error _ -> through ~tail None)
  in
  let effect_of blk (j : jmp term) : contribution =
    if Hike_return.is_jmp j then begin
      check_restore blk;
      { adds = Some Core.Int.Set.empty; back = true }
    end
    else
      match Jmp.kind j with
      | Int _ -> { adds = None; back = false }
      | Ret _ -> pessimistic
      | Goto (Direct t) ->
        if Core.Set.mem own_blocks t then internal else pessimistic
      | Goto (Indirect e) -> indirect_goto blk e
      | Call c -> (
        let tail = Base.Option.is_none (Call.return c) in
        match Call.target c with
        | Direct t -> through ~tail (callee t)
        | Indirect e -> indirect_call blk ~tail e)
  in
  Term.enum blk_t sub
  |> Seq.filter ~f:reachable
  |> Seq.fold
       ~init:{ adds = Some (Cbat_var_id.intern_set (Hike_vsa.written_regs_of_sub ~synth sub));
               back = false }
       ~f:(fun acc blk ->
           Term.enum jmp_t blk |> Seq.fold ~init:acc ~f:(fun acc j -> join_contribution acc (effect_of blk j)))
  |> fun e -> { written = e.adds; returns = e.back }
