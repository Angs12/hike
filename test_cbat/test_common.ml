(* Shared test infrastructure: check harness, BIR fixture builders, stderr capture, emitter runner, domain aliases. *)
open Bap.Std
open Bap_core_theory
module W = Word
module Clp = Cbat_clp
module Fs = Cbat_fin_set

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

(* AI word environment from (var, word-set) binds over top. *)
let failures = ref 0

let check (name : string) (b : bool) : unit =
  if b then Printf.printf "ok: %s\n" name
  else (
    Printf.printf "FAIL: %s\n" name;
    incr failures)

(* A check over an optional bound: a missing lookup fails the check. *)
let check_bound name o f = check name (match o with Some v -> f v | None -> false)

let contains_substring (hay : string) (needle : string) : bool =
  let n = String.length hay and m = String.length needle in
  let rec go i = i + m <= n && (String.sub hay i m = needle || go (i + 1)) in
  m = 0 || go 0

(* Capture stderr emitted by [f] as a string. *)
let capture_stderr (f : unit -> unit) : string =
  let path = Filename.temp_file "cbat_cap" ".err" in
  let fd = Unix.openfile path [ Unix.O_WRONLY; Unix.O_TRUNC; Unix.O_CREAT ] 0o600 in
  let saved = Unix.dup Unix.stderr in
  Unix.dup2 fd Unix.stderr;
  Unix.close fd;
  (try f ()
   with e ->
     Unix.dup2 saved Unix.stderr;
     Unix.close saved;
     Sys.remove path;
     raise e);
  flush stderr;
  Unix.dup2 saved Unix.stderr;
  Unix.close saved;
  let ic = open_in path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  Sys.remove path;
  s

(* Did the not_implemented hit for [comp] log its stderr line while [f] ran? *)
let fired (comp : string) (f : unit -> unit) : bool = contains_substring (capture_stderr f) comp
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

module Map = Cbat_map_lattice.Make_val (IntLattice) (IntLattice)

(* Every def is denoted (spec §2.1); all-tracked is the only mode. *)

let v64 (n : string) : var = Var.create ~is_virtual:false ~fresh:false n (Type.Imm 64)
let v1 (n : string) : var = Var.create ~is_virtual:false ~fresh:false n (Type.Imm 1)
let memv (n : string) : var = Var.create ~is_virtual:false ~fresh:false n (Type.Mem (`r64, `r8))

(* Fixture stack pointer. *)
let sp = v64 "RSP"

module Kb = Hike.Kb
module Sm = Hike.Stack_model
(* The record vocabulary: test_fixtures resolves [Cu] through this open. *)
module Cu = Hike.Stack_model

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

(* The producer, composed: the fixpoint's two products (the block
   environments and the REWRITTEN SUB) — the tests' one-line driver.
   [install_run] happens at the caller, exactly like the pass. *)
let produce ?(block_addrs = []) ?(images = [])
    target (prog : program term) (sub : sub term) :
    (Cbat_vsa.AI.t * Cbat_vsa.AI.t) Tid.Map.t * sub term =
  Hike.Kb.install_block_addrs
    (Core.Map.of_alist_exn (module Addr)
       (Base.List.map block_addrs ~f:(fun (a, t) -> (Addr.of_int64 a, t))));
  Hv.fixpoint target ~prog ~symtab:None ~images sub
  |> Base.Option.value ~default:(Tid.Map.empty, sub)

(* The T2 chain replica over fixtures: the composed production entries
   (fixpoint, facts, the one install, the jmp/dyn stamps, the
   attribution, and the rewrite) — the tests' one-line driver.
   Returns the rewritten program. *)
let run_chain_attrib ?(spans = []) (subs : sub term list) : program term =
  let target = Theory.Target.unknown in
  let prog = Program.create ~subs () in
  let abi = Hike.Abi.x86_64_sysv in
  let acc =
    Seq.fold (Term.enum sub_t prog) ~init:Tid.Map.empty ~f:(fun acc sub ->
        let envs, sub' = produce target prog sub in
        Core.Map.set acc ~key:(Term.tid sub) ~data:(envs, sub'))
  in
  let all_envs =
    Core.Map.fold acc ~init:Tid.Map.empty ~f:(fun ~key:_ ~data:(e, _) m ->
        Core.Map.fold e ~init:m ~f:(fun ~key ~data m' -> Core.Map.set m' ~key ~data))
  in
  Kb.install_run ~block_envs:all_envs;
  let prog =
    Term.map sub_t prog ~f:(fun sub ->
        let _, sub' =
          Core.Map.find acc (Term.tid sub)
          |> Option.value ~default:(Tid.Map.empty, sub)
        in
        Sm.stamp_dyn_allocs
          ~dynamic_alloc_tids:(Hike.Promote.dynamic_alloc_tids_of ~sp ~denote:Hike.Vsa.denote_exp_at sub') sub')
  in
  let ctx =
    Hike.Sections.attribute ~word:8 ~entry:Hike.Stack_model.segment_base ~abi ~spans
      ~denote:Hv.denote_exp_at prog
  in
  let prog = Term.map sub_t prog ~f:(Hike.Sections.stamp_tags ctx) in
  Hike.Promote.rewrite_program ~word:8 ~entry:Hike.Stack_model.segment_base ~abi ~sp
    ~symtab:None ~spans ~denote:Hv.denote_exp_at ~ctx prog

(* Installs the fixtures' block environments through the sanctioned KB
   lifecycle (the attribution's seam reads them). *)
let install_fixture_envs (subs : sub term list) : bool =
  let all_envs, ok =
    Base.List.fold subs ~init:(Tid.Map.empty, true) ~f:(fun (m, ok) sub ->
        match
          Hv.fixpoint Theory.Target.unknown
            ~prog:(Program.create ~subs:[ sub ] ())
            ~symtab:None ~images:[] sub
        with
        | None -> (m, false)
        | Some (envs, _) ->
            (Core.Map.merge m envs
               ~f:(fun ~key:_ el ->
                 match el with
                   | `Left v | `Right v | `Both (_, v) -> Some v),
             ok))
  in
  Kb.install_run ~block_envs:all_envs;
  ok && not (Core.Map.is_empty all_envs)

(* The attribution ctx over fixtures with freshly installed envs. *)
let fixture_ctx ?(spans = []) (subs : sub term list) : Hike.Sections.ctx =
  ignore (install_fixture_envs subs);
  Hike.Sections.attribute ~word:8 ~entry:Hike.Stack_model.segment_base
    ~abi:Hike.Abi.x86_64_sysv ~spans ~denote:Hv.denote_exp_at
    (Program.create ~subs ())

(* The single-sub rewrite: the chain replica's rewritten sub. *)
let rewrite_one (sub : sub term) : sub term =
  let prog = run_chain_attrib [ sub ] in
  Term.first sub_t prog |> Base.Option.value_exn



(* Full-range 64-bit word; [w64] takes a native int. *)
