(* The analysis closure: the run's facts as ONE value, built by
   [build] at the discover boundary and threaded through every
   consumer as a parameter.  The KB value slots (sec-tag, dyn-alloc,
   window) stay the term-carried half; the module has no read API for
   the closure — [install]/[facts] move the record across the pass
   boundary, one fetch per pass entry. *)

open Bap.Std

(* One KB computation, evaluated through a fresh toplevel var. *)
let eval (x : 'a Bap_core_theory.KB.t) : 'a =
  let v = Toplevel.var "hike-kb-eval" in
  Toplevel.put v x;
  Toplevel.get v

(* The denotation seam: [exp] in the before-env of [def], or the
   block's postcondition with no [def]. *)
type denote =
  blk:blk term -> ?def:def term -> exp ->
  (Cbat_vsa.WordSet.t, Type.error) Result.t

type facts = {
  (* One (pre, post) pair per block tid; [post] answers no-def queries
     and [pre] feeds the VSA_DEBUG differential's replay.  Absence
     means the sub's analysis did not converge; [denote] answers
     [AI.top]. *)
  envs : (Cbat_vsa.AI.t * Cbat_vsa.AI.t) Tid.Map.t;
  (* An address to the tid of the block whose extent contains it.
     An empty map keeps every dispatch foreign. *)
  block_addrs : Tid.t Addr.Map.t;
  sub_addrs : Tid.t Addr.Map.t;
  images : Cbat_vsa.section_image list;
  foreign_slots : Core.Int64.Set.t;
  target : Bap_core_theory.Theory.Target.t;
  abi : Hike_abi.t;
  (* [e] denotes in the before-env of [def] — the def's Env Tag — or,
     with no [def], in the block's postcondition (the state a jmp
     reads).  A def with no tag (minted after the boundary) answers
     [AI.top]. *)
  denote : denote;
  (* The run's resolution lookup: one name table for the program,
     built at the discover boundary beside the other facts. *)
  lookup : int64 -> Tid.t option;
  (* Each VLA allocation's frame fact (its frame-relative offset band and
     the base's entry-line range), keyed by the def computing its base —
     the seed's confirmed allocations, drained here so nothing crosses a
     program run.  [vla_parents] names the frame a nested allocation
     descends from. *)
  vla_extents : Hike_origin.vla_extent Tid.Map.t;
  vla_parents : Tid.t Tid.Map.t;
  (* The emitter's section spec, installed by the attribution pass in
     the same run that built [envs]; [None] = no attribution ran and
     the sections emit with no components. *)
  spec : Hike_spec.section_spec option;
  (* The DCE's per-sub escape roots: the storage mem vars whose bytes
     escape the sub.  The attribution computes them from its trees; the
     sweep reads them off the record. *)
  escape_roots : Var.Set.t Tid.Map.t;
  (* All synthetic kinds, recorded once at attribution's facts boundary
     after storage and dispatch materialization. *)
  synth : Hike_synth.table;
}

let build ~(block_envs : (Cbat_vsa.AI.t * Cbat_vsa.AI.t) Tid.Map.t)
    ~(lookup : int64 -> Tid.t option)
    ~(block_addrs : Tid.t Addr.Map.t)
    ~(target : Bap_core_theory.Theory.Target.t) : facts =
  let blk_envs blk =
    match Core.Map.find block_envs (Term.tid blk) with
    | Some pair -> pair
    | None -> (Cbat_vsa.AI.top, Cbat_vsa.AI.top)
  in
  let vla_extents, vla_parents, candidates = Hike_origin.Vla_seed.take () in
  (* A frame SP never entered is no allocation: its value reads as the
     stack positions it stands for — the base range plus its offsets —
     and an unknown base as the stack top. *)
  let on_stack_line ws =
    match Cbat_vsa.WordSet.origin ws with
    | Some (Hike_origin.Vla t) when not (Core.Map.mem vla_extents t) -> (
        let module Ws = Cbat_vsa.WordSet in
        let k_int w = Base.Result.ok (Cbat_word.to_int64 w) in
        let range =
          match Core.Map.find candidates t, Ws.vla_offsets ws with
          | Some { Hike_origin.base_lo = Some blo; base_hi = Some bhi; _ }, Some offs
            when not (Ws.is_top ws || Ws.is_infinite ws) -> (
              match Base.Option.bind (Ws.Clp.min_elem_signed offs) ~f:k_int,
                    Base.Option.bind (Ws.Clp.max_elem_signed offs) ~f:k_int with
              | Some klo, Some khi -> Some (Int64.add blo klo, Int64.add bhi khi)
              | _ -> None)
          | _ -> None
        in
        let width = 8 * (Hike_abi.of_target target).Hike_abi.word in
        let word v = Cbat_word.of_int64 ~width v in
        match range with
        | Some (lo, hi) -> Ws.stack_word (Ws.Clp.interval ~width (word lo) (word hi))
        | None -> Ws.sub (Ws.stack_word_i64 0L) (Ws.top width))
    | _ -> ws
  in
  { envs = block_envs;
    block_addrs;
    sub_addrs = Addr.Map.empty;
    images = [];
    foreign_slots = Core.Int64.Set.empty;
    target;
    abi = Hike_abi.of_target target;
    lookup;
    vla_extents;
    vla_parents;
    denote =
      (fun ~blk ?def e ->
        let pre, post = blk_envs blk in
        Base.Result.map ~f:on_stack_line
          (Cbat_vsa.denote_exp_at ~pre ~post ~blk ?def e));
    spec = None;
    escape_roots = Tid.Map.empty;
    synth = Hike_synth.empty }

(* The run's record, installed once at the discover boundary. *)
let run : facts option ref = ref None

let install (f : facts) = run := Some f

let facts () =
  match !run with
  | Some f -> f
  | None -> failwith "hike: no analysis facts installed (discover did not run)"

(* The optional read for passes that also run on fixtures (no analysis). *)
let facts_opt () : facts option = !run

(* The attribution pass adds the emitter spec and the sweep's escape
   roots to the installed record. *)
let with_attribution (f : facts) ~(spec : Hike_spec.section_spec)
    ~(escape_roots : Var.Set.t Tid.Map.t) : facts =
  { f with spec = Some spec; escape_roots }
