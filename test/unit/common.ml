(* Shared test infrastructure: check harness, BIR fixture builders, stderr capture, emitter runner, domain aliases. *)
open Bap.Std
open Bap_core_theory
module W = Word
(* The x86-64 target BAP declares with its registers and roles (the one a
   loaded project carries); [of_string "x86_64-gnu-elf"] names only the
   register-less family. *)
let x86_target () : Theory.Target.t = Theory.Target.of_string "bap:x86_64-gnu-elf"
(* The word-set view of [Cbat_clp]: a value is the canonical piece union,
   built from progressions and acted on by the [Pieces] operations.  The
   single-progression layer is [Cbat_clp] itself. *)
module Clp = struct
  module P = Cbat_clp.Pieces
  module Exact = Cbat_clp.Exact
  module Pieces = P

  type t = P.t

  let of_progression = P.of_progression
  let create ?width ?step ?cardn base =
    P.of_arcs (Cbat_clp.arcs ?width ?step ?cardn base)
  let create_ascending ~width ~base ~step =
    P.of_progression (Cbat_clp.create_ascending ~width ~base ~step)
  let create_descending ~width ~base ~step =
    P.of_progression (Cbat_clp.create_descending ~width ~base ~step)
  let infinite bs = P.of_progression (Cbat_clp.infinite bs)
  let interval = Cbat_clp.interval
  let singleton = P.singleton
  let bottom = P.bottom
  let top = P.top
  (* The circular hull of an ascending, deduplicated word list. *)
  let of_list = P.hull_of_list

  let bitwidth = P.bitwidth
  let cardinality = P.cardinality
  let min_elem = P.min_elem
  let max_elem = P.max_elem
  let min_elem_signed = P.min_elem_signed
  let max_elem_signed = P.max_elem_signed
  let elem = P.elem
  let iter = P.elements
  let equal = P.equal
  let overlap = P.overlap
  let splits_by = P.splits_by
  let is_bottom = P.is_bottom
  let is_top = P.is_top
  let is_ascending = P.is_ascending
  let is_descending = P.is_descending
  let is_circular = P.is_circular
  let is_infinite (t : t) = List.exists Cbat_clp.is_infinite (P.to_list t)
  let subset = P.precedes
  let precedes = P.precedes

  let union = P.union
  let join = P.join
  let meet = P.meet
  let intersection = P.intersection
  let diff = P.diff
  let widen_join = P.widen_join
  let extrapolate_steps = P.extrapolate_steps
  let translate = P.translate

  let add = P.add
  let sub = P.sub
  let mul = P.mul
  let div = P.div
  let sdiv = P.sdiv
  let modulo = P.modulo
  let smodulo = P.smodulo
  let arshift = P.arshift
  let rshift = P.rshift
  let lshift = P.lshift
  let logand = P.logand
  let logor = P.logor
  let logxor = P.logxor
  let lnot = P.lnot
  let neg = P.neg
  let extract = P.extract
  let cast = P.cast
  let concat = P.concat
end
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
  let abi = Hike.Abi.x86_64_sysv in
  let e = AI.add_word AI.top ~key:abi.Hike.Abi.sp ~data:(Ws.stack_word_i64 0L) in
  AI.add_word e ~key:abi.Hike.Abi.frame_pointer ~data:(Ws.stack_word_i64 0L)

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

(* The fixtures' registers come from the SysV ABI module, never from
   their names: the stack pointer, the integer parameter registers in
   order, and the return registers in order. *)
let sysv = Hike.Abi.x86_64_sysv
let sp = sysv.Hike.Abi.sp
let int_param n = Base.List.nth_exn sysv.Hike.Abi.int_param_regs n
let int_ret n = Base.List.nth_exn sysv.Hike.Abi.return_regs n
let callee_saved n = Base.List.nth_exn sysv.Hike.Abi.callee_saved n
let thread_pointer = sysv.Hike.Abi.thread_pointer
let frame_ptr = sysv.Hike.Abi.frame_pointer


let abi_cf = sysv.Hike.Abi.carry_flag
let abi_pf = sysv.Hike.Abi.parity_flag
let abi_zf = sysv.Hike.Abi.zero_flag
let abi_sf = sysv.Hike.Abi.sign_flag
let abi_of = sysv.Hike.Abi.overflow_flag

module Kb = Hike.Kb
module Sm = Hike.Stack_model
module Ds = Hike.Def_slots

(* The VSA's input form: an SSA sub.  Every sub the analysis sees is
   SSA-constructed; there is no other form.  The form is memoised: the
   construction is deterministic and the pins read it repeatedly. *)
let ssa_forms : (string, sub term) Hashtbl.t = Hashtbl.create 16

let ssa_form (sub : sub term) : sub term =
  let key = Tid.to_string (Term.tid sub) in
  match Hashtbl.find_opt ssa_forms key with
  | Some s -> s
  | None ->
    let prog = Program.create ~subs:[ sub ] () in
    let prog = Hike.Ssa.ssa_program ~synth:Hike.Synth.empty ~target:(x86_target ()) prog in
    let s =
      Term.enum sub_t prog
      |> Seq.find ~f:(fun s -> String.equal (Sub.name s) (Sub.name sub))
      |> Base.Option.value_exn in
    Hashtbl.replace ssa_forms key s;
    s

(* The version of the base variable [v] that block [tid] holds: the
   definition's own version, or the block's incoming phi. *)
let version_at (ssa : sub term) (tid : tid) (v : var) : var =
  let blk = Term.find_exn blk_t ssa tid in
  Sm.version_at_end blk v

(* The version the block receives: its incoming phi's left-hand side. *)
let phi_version (ssa : sub term) (tid : tid) (v : var) : var option =
  let blk = Term.find_exn blk_t ssa tid in
  Term.enum phi_t blk
  |> Seq.find_map ~f:(fun p ->
      if Var.same (Var.base (Phi.lhs p)) v then Some (Phi.lhs p) else None)

(* The version the block defines: its definition's left-hand side. *)
let def_version (ssa : sub term) (tid : tid) (v : var) : var option =
  let blk = Term.find_exn blk_t ssa tid in
  Term.enum def_t blk
  |> Seq.filter_map ~f:(fun d ->
      if Var.same (Var.base (Def.lhs d)) v then Some (Def.lhs d) else None)
  |> Seq.to_list
  |> fun l -> match List.rev l with [] -> None | v :: _ -> Some v

(* The value the block receives for the base variable [v].  A block's
   state holds the versions it receives; a block with no phi for [v]
   holds only the seeded base variables. *)
let value_at (ssa : sub term) (sol : Vsa.vsa_sol) (tid : tid) (v : var) : Ws.t =
  let width = match Var.typ v with Type.Imm w -> w | _ -> 64 in
  let key = match phi_version ssa tid v with Some version -> version | None -> v in
  AI.find_word width (Graphlib.Std.Solution.get sol tid) key

(* The value the base variable [v] has after the block's definitions:
   the definition's own value, or the received one when the block does
   not define it. *)
let value_after (ssa : sub term) (sol : Vsa.vsa_sol) (tid : tid) (v : var) : Ws.t =
  let width = match Var.typ v with Type.Imm w -> w | _ -> 64 in
  let blk = Term.find_exn blk_t ssa tid in
  let post =
    Vsa.Test_seam.denote_defs ~synth:Hike.Synth.empty blk
      (Graphlib.Std.Solution.get sol tid) in
  match def_version ssa tid v with
  | Some version -> AI.find_word width post version
  | None -> value_at ssa sol tid v

let static_graph_vsa ~abi ~synth ?callee ?resolved ?sub_lookup sub init =
  Vsa.static_graph_vsa ~abi
    ~synth:(ref synth)
    ~def_reads:(fun d -> Sm.reads (`Def d)) ~def_writes:(fun d -> Sm.writes (`Def d))
    ~phi_reads:(fun p -> Sm.reads (`Phi p)) ~phi_writes:(fun p -> Sm.writes (`Phi p))
    ~jmp_reads:(fun j -> Core.Set.union (Sm.reads (`Jmp j)) (Sm.writes (`Jmp j)))
    ?callee ?resolved ?sub_lookup sub init

let mk_rctx ~abi ~synth ?sub_lookup sub =
  Vsa.Test_seam.mk_rctx ~abi
    ~synth:(ref synth)
    ~def_reads:(fun d -> Sm.reads (`Def d)) ~def_writes:(fun d -> Sm.writes (`Def d))
    ~phi_writes:(fun p -> Sm.writes (`Phi p))
    ~jmp_reads:(fun j -> Core.Set.union (Sm.reads (`Jmp j)) (Sm.writes (`Jmp j)))
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
let top_facts () : Hike.Kb.facts =
  Hike.Kb.build ~lookup:(fun _ -> None) ~block_envs:Tid.Map.empty
    ~block_addrs:(Core.Map.empty (module Addr))
    ~target:(x86_target ())

(* The fixtures' callees: a sub of [prog] writes the registers its
   own defs write; any other target writes anything. *)
let callee_of ~synth (prog : program term) (tid : Tid.t) : Vsa.Call_effects.callee =
  match Term.find sub_t prog tid with
  | Some s -> Summary (Some (Cbat_var_id.intern_set (Hv.written_regs_of_sub ~synth s)))
  | None -> Summary None

(* The production solve with every callee summarized, so it never
   pauses: the block environments, the rewritten sub and the grown
   block-address map. *)
let solve_with_synth ~synth ?(images = [])
    ?(block_addrs = Addr.Map.empty) ~callee target (sub : sub term) =
  match
    Hv.start target ~lookup:(fun _ -> None) ~images ~callee ~block_addrs
      ~synth
      ~foreign_slots:Core.Int64.Set.empty sub
  with
  | Hv.Done (envs, sub', block_addrs', synth, _) -> (envs, sub', block_addrs', synth)
  | Hv.Paused _ -> Alcotest.fail "solve: a fixture callee is blocked"

let solve ~synth ?images ?block_addrs ~callee target sub =
  let envs, sub, addrs, _ =
    solve_with_synth ~synth ?images ?block_addrs ~callee target sub
  in
  (envs, sub, addrs)

(* The producer, composed: the solve's products for [sub] with [prog]'s
   subs as its callees — the tests' one-line driver. *)
let produce ~synth ?(block_addrs = []) ?(images = []) target (prog : program term)
    (sub : sub term) :
    (Cbat_vsa.AI.t * Cbat_vsa.AI.t) Tid.Map.t * sub term * Tid.t Addr.Map.t =
  solve ~synth ~images ~callee:(callee_of ~synth prog) target
    ~block_addrs:
      (Core.Map.of_alist_exn (module Addr)
         (Base.List.map block_addrs ~f:(fun (a, t) -> (Addr.of_int64 a, t))))
    sub

(* Runs the production attribution protocol over fixture analysis facts. *)
let run_chain_attrib_result ~synth ?(spans = []) (subs : sub term list) :
    Hike.Attribution.result =
  let target = (x86_target ()) in
  let prog = Program.create ~subs () in
  let acc, synth =
    Seq.fold (Term.enum sub_t prog) ~init:(Tid.Map.empty, synth)
      ~f:(fun (acc, synth) sub ->
        let envs, sub', _, synth =
          solve_with_synth ~synth ~callee:(callee_of ~synth prog) target sub
        in
        (Core.Map.set acc ~key:(Term.tid sub) ~data:(envs, sub'), synth))
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
  let facts = Hike.Kb.with_synth facts (Hike.Synth.union facts.synth synth) in
  let prog =
    Hike.Variadic.stamp ~abi:facts.abi ~entry:Hike.Stack_model.segment_base
      ~denote:facts.denote prog
  in
  Hike.Attribution.run ~facts ~word:8 ~entry:Hike.Stack_model.segment_base
    ~spans ~meta:[] ~tls:None ~relative:[] ~externals:[] prog

let run_chain_attrib ~synth ?spans (subs : sub term list) : program term =
  (run_chain_attrib_result ~synth ?spans subs).program

(* The fixtures' analysis facts: the subs' converged environments, plus
   the stamped subs the seam reads (the fixpoint's sweep tags every def
   with its before-env).  The bool reports a nonempty env set. *)
let fixture_facts ~synth (subs : sub term list) :
    Hike.Kb.facts * sub term list * bool =
  let all_envs, stamped, ok, synth =
    Base.List.fold subs ~init:(Tid.Map.empty, [], true, synth)
      ~f:(fun (m, stamped, ok, synth) sub ->
        let envs, sub', _, synth =
          solve_with_synth ~synth ~callee:(callee_of ~synth (Program.create ~subs:[ sub ] ()))
            (x86_target ()) sub
        in
        (Core.Map.merge m envs
           ~f:(fun ~key:_ el ->
             match el with
               | `Left v | `Right v | `Both (_, v) -> Some v),
         sub' :: stamped,
         ok && not (Core.Map.is_empty envs), synth))
  in
  let facts = Hike.Kb.build ~lookup:(fun _ -> None) ~block_envs:all_envs
      ~block_addrs:(Core.Map.empty (module Addr)) ~target:(x86_target ()) in
  (Hike.Kb.with_synth facts (Hike.Synth.union facts.synth synth),
   Base.List.rev stamped,
   ok && not (Core.Map.is_empty all_envs))

let install_fixture_envs ~synth (subs : sub term list) : Hike.Kb.facts =
  let facts, _, _ = fixture_facts ~synth subs in
  facts

(* The facts plus the one stamped sub (the unstamped term when the
   solve did not converge). *)
let fixture_facts_sub ~synth (sub : sub term) : Hike.Kb.facts * sub term =
  let facts, stamped, _ = fixture_facts ~synth [ sub ] in
  (facts, match stamped with [ s ] -> s | _ -> sub)

(* The attribution ctx over fixtures with freshly solved, stamped
   envs. *)
let fixture_ctx ~synth ?(spans = []) (subs : sub term list) : Hike.Sections.ctx =
  let facts, subs, _ = fixture_facts ~synth subs in
  Hike.Sections.attribute ~facts ~word:8 ~entry:Hike.Stack_model.segment_base
    ~spans (Program.create ~subs ())

(* The single-sub rewrite: the chain replica's rewritten sub. *)
let rewrite_one ~synth (sub : sub term) : sub term =
  let prog = run_chain_attrib ~synth [ sub ] in
  Term.first sub_t prog |> Base.Option.value_exn

(* The rewritten sub with the synthetic vars its attribution recorded. *)
let rewrite_one_synth ~synth (sub : sub term) : Hike.Synth.table * sub term =
  let result = run_chain_attrib_result ~synth [ sub ] in
  (result.facts.Hike.Kb.synth,
   Term.first sub_t result.program |> Base.Option.value_exn)



(* Full-range 64-bit word; [w64] takes a native int. *)
