(* The pipeline's analysis crossing: the run's block-boundary
   environments, installed atomically once per analysis run — a reader
   never sees one table from this run and the other from the previous
   one.  The environments are the analysis's ONLY cross-pass product;
   every other fact re-derives through the seam. *)

open Bap.Std

(* The block-boundary environments: one (pre, post) pair per block tid.
   The producer stamps them at the sticky loop's stabilization from the
   final converged solution; a phi reads [pre], a jmp reads [post]. *)
let env_stamps : (Cbat_vsa.AI.t * Cbat_vsa.AI.t) Tid.Map.t ref =
  ref Tid.Map.empty

(* The block's stamped pair; absence means the sub's analysis did not
   converge, so every reader takes [Cbat_vsa.AI.top] — the
   no-constraint identity. *)
let block_env (btid : Tid.t) : (Cbat_vsa.AI.t * Cbat_vsa.AI.t) option =
  Core.Map.find !env_stamps btid

(* The run's install: the block-env stamps of ONE analysis run replace
   the table in one write, after the producer's fold completes. *)
let install_run ~(block_envs : (Cbat_vsa.AI.t * Cbat_vsa.AI.t) Tid.Map.t) :
    unit =
  env_stamps := block_envs
