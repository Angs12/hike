(* The analysis closure: the run's facts as ONE value, built by
   [build] at the pass_vsa boundary and threaded through every
   consumer as a parameter.  The KB value slots (sec-tag, dyn-alloc,
   window) stay the term-carried half; the module has no read API for
   the closure — [install]/[facts] move the record across the pass
   boundary, one fetch per pass entry. *)

open Bap.Std

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
  target : Bap_core_theory.Theory.Target.t;
  abi : Hike_abi.t;
  (* [e] denotes in the before-env of [def] — the def's Env Tag — or,
     with no [def], in the block's postcondition (the state a jmp
     reads).  A def with no tag (minted after the boundary) answers
     [AI.top]. *)
  denote : denote;
  (* The run's resolution lookup: one name table for the program,
     built at the pass_vsa boundary beside the other facts. *)
  lookup : int64 -> Tid.t option;
  (* The emitter's section spec, installed by the attribution pass in
     the same run that built [envs]; [None] = no attribution ran and
     the sections emit with no components. *)
  spec : Bil2llvm_env.section_spec option;
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
  { envs = block_envs;
    block_addrs;
    target;
    abi = Hike_abi.of_target target;
    lookup;
    denote =
      (fun ~blk ?def e ->
        let pre, post = blk_envs blk in
        Cbat_vsa.denote_exp_at ~pre ~post ~blk ?def e);
    spec = None }

(* The run's record, installed once at the pass_vsa boundary. *)
let run : facts option ref = ref None

let install (f : facts) = run := Some f

let facts () =
  match !run with
  | Some f -> f
  | None -> failwith "hike: no analysis facts installed (pass_vsa did not run)"

(* The optional read for passes that also run on fixtures (no analysis). *)
let facts_opt () : facts option = !run

(* The attribution pass adds the emitter spec to the installed record. *)
let with_spec (f : facts) (spec : Bil2llvm_env.section_spec) : facts =
  { f with spec = Some spec }
