(* The pipeline's analysis crossing: the run's block-boundary
   environments and the run's block-address map, each installed
   atomically once per analysis run — a reader never sees one table
   from this run and the other from the previous one.  Every other
   fact re-derives through the seam. *)

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

(* The run's block-address map: an address to the tid of the block
   whose extent contains it — the dispatch resolution's word home.  An
   un-built map (empty) keeps every dispatch foreign. *)
let block_addrs_table = ref (Core.Map.empty (module Addr))

(* The map's run-boundary install, where the producer's facts live. *)
let install_block_addrs m = block_addrs_table := m

(* A case entry carved out of a block's middle becomes a block of its
   own, on the map. *)
let add_block_addr ~addr ~(tid : Tid.t) =
  block_addrs_table := Core.Map.set !block_addrs_table ~key:addr ~data:tid

(* The run's map, read-only. *)
let block_addrs () = !block_addrs_table

(* The block an address names on the run's map. *)
let block_addr (a : Addr.t) : Tid.t option = Core.Map.find !block_addrs_table a

(* The run's install: the block-env stamps of ONE analysis run replace
   the table in one write, after the producer's fold completes. *)
let install_run ~(block_envs : (Cbat_vsa.AI.t * Cbat_vsa.AI.t) Tid.Map.t) :
    unit =
  env_stamps := block_envs
