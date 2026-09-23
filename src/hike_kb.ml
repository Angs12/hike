(* The analysis closure: the run's facts as ONE value, built by
   [build] at the pass_vsa boundary and threaded through every
   consumer as a parameter.  The KB value slots (sec-tag, dyn-alloc,
   window) stay the term-carried half; the module has no read API for
   the closure — [install]/[facts] move the record across the pass
   boundary, one fetch per pass entry. *)

open Bap.Std
module Hike_abi = Hike_abi

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
  addr_bits : int;
  target : Bap_core_theory.Theory.Target.t;
  abi : Hike_abi.t;
  (* [e] denotes in the before-env of [def] — the def's Env Tag — or,
     with no [def], in the block's postcondition (the state a jmp
     reads).  A def with no tag (minted after the boundary) answers
     [AI.top]. *)
  denote : denote;
  (* The emitter's section spec, installed by the attribution pass in
     the same run that built [envs]; [None] = no attribution ran and
     the sections emit with no components. *)
  spec : Bil2llvm_env.section_spec option;
}

let build ~(block_envs : (Cbat_vsa.AI.t * Cbat_vsa.AI.t) Tid.Map.t)
    ~(block_addrs : Tid.t Addr.Map.t)
    ~(target : Bap_core_theory.Theory.Target.t) : facts =
  let blk_envs blk =
    match Core.Map.find block_envs (Term.tid blk) with
    | Some pair -> pair
    | None -> (Cbat_vsa.AI.top, Cbat_vsa.AI.top)
  in
  { envs = block_envs;
    block_addrs;
    addr_bits = Hike_abi.addr_size_bits target;
    target;
    abi = Hike_abi.of_target target;
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

(* The attribution pass adds the emitter spec to the installed record. *)
let with_spec (f : facts) (spec : Bil2llvm_env.section_spec) : facts =
  { f with spec = Some spec }

(* A mid-block case entry becomes its own block, on the map. *)
let add_block_addr (f : facts) ~addr ~(tid : Tid.t) : facts =
  { f with block_addrs = Core.Map.set f.block_addrs ~key:addr ~data:tid }
