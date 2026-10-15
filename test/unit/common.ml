(* Shared test infrastructure: check harness, BIR fixture builders, stderr capture, emitter runner, domain aliases. *)
open Bap.Std
open Bap_core_theory
module W = Word
module Clp = Cbat_clp
module Ex = Clp.Exact

module Wo = Cbat_word
module Ws = Cbat_clp_set_composite

(* Wrapped BIR-fixpoint library; siblings re-exported by cbat_vsa.mli. *)
module AI = Cbat_vsa.AI
module Mem = Cbat_vsa.Mem
module Vsa = Cbat_vsa

(* Memmap fusion pipeline under test. *)
module MK = Cbat_vsa.Mem.Key
module MV = Cbat_vsa.Mem.Val

(* Explicit anchored entry state (RSP = the symbolic segment base,
   offset 0 — the production universe); fixtures pass it to the
   fixpoint so unit pins exercise the same representation the default
   entry seeds. *)
let anchored_entry () : AI.t =
  let rsp = Var.create ~is_virtual:false ~fresh:false "RSP" (Type.Imm 64) in
  let rbp = Var.create ~is_virtual:false ~fresh:false "RBP" (Type.Imm 64) in
  let e = AI.add_word AI.top ~key:rsp ~data:(Ws.stack_word_i64 0L) in
  AI.add_word e ~key:rbp ~data:(Ws.stack_word_i64 0L)

let w32 = Cbat_word.of_int ~width:32
let w33 = Cbat_word.of_int ~width:33
let w64 = Cbat_word.of_int ~width:64

(* create n (defaults) = singleton {n} *)
module IntLattice : Cbat_lattice_intf.S_val with type t = int = struct
  (* Local open: supplies bin_io helpers without shadowing (=) file-wide. *)
  open! Core

  type t = int [@@deriving bin_io, sexp, compare]

  let pp = Int.pp
  let meet = min
  let join = max
  let bottom = Int.min_value
  let top = Int.max_value
  let widen_join a b = if a = b then a else top
  let equal = ( = )
  let precedes = ( <= )
end

module Make_val (K : Cbat_map_lattice.Key_val) (L : Cbat_lattice_intf.S_val) =
struct
  module IL = Cbat_lattice_intf.Free_index_val (L)
  include Cbat_map_lattice.Make_indexed_val (K) (IL)
end

module Map = Make_val (IntLattice) (IntLattice)

(* Every def is denoted (spec §2.1); all-tracked is the only mode. *)

let v64 (n : string) : var = Var.create ~is_virtual:false ~fresh:false n (Type.Imm 64)
let v1 (n : string) : var = Var.create ~is_virtual:false ~fresh:false n (Type.Imm 1)
let memv (n : string) : var = Var.create ~is_virtual:false ~fresh:false n (Type.Mem (`r64, `r8))

(* Fixture stack pointer. *)
let sp = v64 "RSP"

module Kb = Hike.Kb
module Sm = Hike.Stack_model
module Ds = Hike.Def_slots

let static_graph_vsa ~abi ?callee ?resolved ?sub_lookup sub init =
  Vsa.static_graph_vsa ~abi
    ~def_reads:Sm.def_reads ~def_writes:Sm.def_writes
    ~phi_reads:Sm.phi_reads ~phi_writes:Sm.phi_writes
    ~jmp_reads:(Sm.jmp_reads ~abi)
    ?callee ?resolved ?sub_lookup sub init

let mk_rctx ~abi ?sub_lookup sub =
  Vsa.Test_seam.mk_rctx ~abi
    ~def_reads:Sm.def_reads ~def_writes:Sm.def_writes
    ~phi_reads:Sm.phi_reads ~phi_writes:Sm.phi_writes
    ~jmp_reads:(Sm.jmp_reads ~abi)
    ?sub_lookup sub
(* The record vocabulary: test_fixtures resolves [Cu] through this open. *)
module Cu = Hike.Stack_model

let q64 (v : int64) : Cbat_word.t = Cbat_word.of_int64 ~width:64 v

let i2w (x : int64) : Cbat_word.t =
  Cbat_word.of_word (Word.of_int64 ~width:64 x)

(* The list-form facts builder (the producer-internal promotion
   product the rewrite pins stamp). *)
let mk_facts ?(prom_arity = 0) ?(prom_resolved = Tid.Map.empty) () :
    Hike.Promote.facts =
  { Hike.Promote.prom_arity; prom_resolved }

(* The absolute segment-line position of a frame offset (T15): the
   entry RSP is the segment base, so a frame offset o sits at
   [base + o].  Fixture kinds carry absolute positions, exactly like
   the producer's tags.  A plain in-band extent (a real band address,
   e.g. the B5 absurd hull) is NOT a frame offset and stays raw. *)
let pos (o : int64) : int64 = Int64.add Hike.Stack_model.segment_base o
module B2l = Hike.Bil2llvm
module Hv = Hike.Vsa

(* The analysis facts over no envs and no addresses: the pre-solver
   world every top-identity consumer reads. *)
let top_facts : Hike.Kb.facts =
  Hike.Kb.build ~lookup:(fun _ -> None) ~block_envs:Tid.Map.empty
    ~block_addrs:(Core.Map.empty (module Addr))
    ~target:Theory.Target.unknown

(* The fixtures' callees: a sub of [prog] writes the registers its
   own defs write; any other target writes anything. *)
let callee_of (prog : program term) (tid : Tid.t) : Vsa.Call_effects.callee =
  match Term.find sub_t prog tid with
  | Some s -> Summary (Some (Cbat_var_id.intern_set (Hv.written_regs_of_sub s)))
  | None -> Summary None

(* The production solve with every callee summarized, so it never
   pauses: the block environments, the rewritten sub and the grown
   block-address map. *)
let solve ?(images = []) ?(block_addrs = Addr.Map.empty) ~callee target (sub : sub term) :
    (Cbat_vsa.AI.t * Cbat_vsa.AI.t) Tid.Map.t * sub term * Tid.t Addr.Map.t =
  match
    Hv.start target ~lookup:(fun _ -> None) ~images ~callee ~block_addrs
      ~foreign_slots:Core.Int64.Set.empty sub
  with
  | Hv.Done (envs, sub', block_addrs') -> (envs, sub', block_addrs')
  | Hv.Paused _ -> Alcotest.fail "solve: a fixture callee is blocked"

(* The producer, composed: the solve's products for [sub] with [prog]'s
   subs as its callees — the tests' one-line driver. *)
let produce ?(block_addrs = []) ?(images = []) target (prog : program term)
    (sub : sub term) :
    (Cbat_vsa.AI.t * Cbat_vsa.AI.t) Tid.Map.t * sub term * Tid.t Addr.Map.t =
  solve ~images ~callee:(callee_of prog) target
    ~block_addrs:
      (Core.Map.of_alist_exn (module Addr)
         (Base.List.map block_addrs ~f:(fun (a, t) -> (Addr.of_int64 a, t))))
    sub

(* Runs the production attribution protocol over fixture analysis facts. *)
let run_chain_attrib ?(spans = []) (subs : sub term list) : program term =
  let target = Theory.Target.unknown in
  let prog = Program.create ~subs () in
  let acc =
    Seq.fold (Term.enum sub_t prog) ~init:Tid.Map.empty ~f:(fun acc sub ->
        let envs, sub', _ = produce target prog sub in
        Core.Map.set acc ~key:(Term.tid sub) ~data:(envs, sub'))
  in
  let all_envs =
    Core.Map.fold acc ~init:Tid.Map.empty ~f:(fun ~key:_ ~data:(e, _) m ->
        Core.Map.fold e ~init:m ~f:(fun ~key ~data m' -> Core.Map.set m' ~key ~data))
  in
  let facts =
    Hike.Kb.build ~lookup:(fun _ -> None) ~block_envs:all_envs
      ~block_addrs:(Core.Map.empty (module Addr)) ~target
  in
  let prog =
    Term.map sub_t prog ~f:(fun sub ->
        Core.Map.find acc (Term.tid sub)
        |> Base.Option.value_map ~default:sub ~f:snd)
  in
  let prog =
    Hike.Variadic.stamp ~abi:facts.abi ~entry:Hike.Stack_model.segment_base
      ~denote:facts.denote prog
  in
  let result =
    Hike.Attribution.run ~facts ~word:8 ~entry:Hike.Stack_model.segment_base
      ~spans ~meta:[] ~tls:None ~relative:[] ~externals:[] prog
  in
  result.program

(* The fixtures' analysis facts: the subs' converged environments, plus
   the stamped subs the seam reads (the fixpoint's sweep tags every def
   with its before-env).  The bool reports a nonempty env set. *)
let fixture_facts (subs : sub term list) :
    Hike.Kb.facts * sub term list * bool =
  let all_envs, stamped, ok =
    Base.List.fold subs ~init:(Tid.Map.empty, [], true)
      ~f:(fun (m, stamped, ok) sub ->
        let envs, sub', _ =
          solve ~callee:(callee_of (Program.create ~subs:[ sub ] ()))
            Theory.Target.unknown sub
        in
        (Core.Map.merge m envs
           ~f:(fun ~key:_ el ->
             match el with
               | `Left v | `Right v | `Both (_, v) -> Some v),
         sub' :: stamped,
         ok && not (Core.Map.is_empty envs)))
  in
  (Hike.Kb.build ~lookup:(fun _ -> None) ~block_envs:all_envs
     ~block_addrs:(Core.Map.empty (module Addr)) ~target:Theory.Target.unknown,
   Base.List.rev stamped,
   ok && not (Core.Map.is_empty all_envs))

let install_fixture_envs (subs : sub term list) : Hike.Kb.facts =
  let facts, _, _ = fixture_facts subs in
  facts

(* The facts plus the one stamped sub (the unstamped term when the
   solve did not converge). *)
let fixture_facts_sub (sub : sub term) : Hike.Kb.facts * sub term =
  let facts, stamped, _ = fixture_facts [ sub ] in
  (facts, match stamped with [ s ] -> s | _ -> sub)

(* The attribution ctx over fixtures with freshly solved, stamped
   envs. *)
let fixture_ctx ?(spans = []) (subs : sub term list) : Hike.Sections.ctx =
  let facts, subs, _ = fixture_facts subs in
  Hike.Sections.attribute ~facts ~word:8 ~entry:Hike.Stack_model.segment_base
    ~spans (Program.create ~subs ())

(* The single-sub rewrite: the chain replica's rewritten sub. *)
let rewrite_one (sub : sub term) : sub term =
  let prog = run_chain_attrib [ sub ] in
  Term.first sub_t prog |> Base.Option.value_exn



(* Full-range 64-bit word; [w64] takes a native int. *)
