(* The noreturn fact: the set of subs whose control never returns to
   their caller.  Classified in layers, each from a fact:

   1. The ABI runtime contract: a sub the loader names (a body-less
      extern, or the PLT stub BAP names after it) whose symbol is a
      never-returning function.  This is the base fact, like the entry
      symbol.
   2. Lifted subs: a conservative fixpoint — every exit is a call to a
      noreturn callee, a transfer to a noreturn sub, or a trap; no
      return, no unresolved exit.  Unknown callees return.

   The CONSUMER is the completion's edge set: a call whose resolved
   target is in this set carries no return continuation, so the decode's
   fallthrough after it is not an edge and its glue prunes.  The drive
   loop computes the set on the SOLVED program (denotations and the
   canonical returns are final) and threads it into the next round's
   solve, so the temporary edge never reaches the VSA. *)

open Bap.Std

module Abi = Hike_abi

(* The loader-level symbol a sub carries: strip the '@' decoration and
   the ':external'/kind suffix so the runtime contract can match. *)
let name_base (n : string) : string =
  let n =
    match Base.String.chop_prefix n ~prefix:"@" with Some x -> x | None -> n
  in
  match Base.String.index n ':' with
  | Some i -> Base.String.prefix n i
  | None -> n

let has_noreturn_name (abi : Abi.t) (sub : sub term) : bool =
  Base.List.mem abi.Abi.noreturn_symbols (name_base (Sub.name sub))
    ~equal:String.equal

let is_entry (sub : sub term) : bool = Term.has_attr sub Sub.entry_point

(* The base layer: loader-named never-returning subs. *)
let base_noreturn (abi : Abi.t) (sub : sub term) : bool =
  has_noreturn_name abi sub && not (is_entry sub)

(* The conservative lifted-sub rule: every exit of every block is a
   known-noreturn transfer and at least one exit exists; a return, an
   unresolved transfer, or a call to a callee not yet classified makes
   the sub returning. *)
let sub_exits_are_noreturn (noreturn : Tid.Set.t) (sub : sub term) : bool =
  let jmps =
    Term.enum blk_t sub |> Seq.concat_map ~f:(Term.enum jmp_t) |> Seq.to_list
  in
  (not (Base.List.is_empty jmps))
  && Base.List.for_all jmps ~f:(fun j ->
         match Jmp.kind j with
         | Int _ -> true
         | Call c -> (
             match Call.target c with
             | Direct t -> Core.Set.mem noreturn t
             | Indirect _ -> false)
         | Goto (Direct t) -> Core.Set.mem noreturn t
         | Goto (Indirect _) -> false
         | Ret _ -> false)

let classify ~(target : Bap_core_theory.Theory.Target.t) (prog : program term) :
    Tid.Set.t =
  let abi = Abi.of_target target in
  let subs = Term.enum sub_t prog |> Seq.to_list in
  let noreturn = ref Tid.Set.empty in
  Base.List.iter subs ~f:(fun s ->
      if base_noreturn abi s then
        noreturn := Core.Set.add !noreturn (Term.tid s));
  (* The call graph may resolve in waves: each round adopts the subs
     whose every exit now transfers to the classified set. *)
  let changed = ref true in
  while !changed do
    changed := false;
    Base.List.iter subs ~f:(fun s ->
        if
          (not (Core.Set.mem !noreturn (Term.tid s)))
          && sub_exits_are_noreturn !noreturn s
        then begin
          noreturn := Core.Set.add !noreturn (Term.tid s);
          changed := true
        end)
  done;
  !noreturn
