(* The analysis run's tables: block environments and the block-address
   map, each installed atomically once per run. *)

open Bap.Std
module Hike_abi = Hike_abi

(* One (pre, post) pair per block tid; a phi reads [pre], a jmp reads
   [post]. *)
let env_stamps : (Cbat_vsa.AI.t * Cbat_vsa.AI.t) Tid.Map.t ref =
  ref Tid.Map.empty

(* Absence means the sub's analysis did not converge; every reader
   takes [Cbat_vsa.AI.top]. *)
let block_env (btid : Tid.t) : (Cbat_vsa.AI.t * Cbat_vsa.AI.t) option =
  Core.Map.find !env_stamps btid

(* An address to the tid of the block whose extent contains it.  An
   empty map keeps every dispatch foreign. *)
let block_addrs_table = ref (Core.Map.empty (module Addr))

let install_block_addrs m = block_addrs_table := m

(* A mid-block case entry becomes its own block, on the map. *)
let add_block_addr ~addr ~(tid : Tid.t) =
  block_addrs_table := Core.Map.set !block_addrs_table ~key:addr ~data:tid

let block_addrs () = !block_addrs_table

let block_addr (a : Addr.t) : Tid.t option = Core.Map.find !block_addrs_table a

let install_run ~(block_envs : (Cbat_vsa.AI.t * Cbat_vsa.AI.t) Tid.Map.t) :
    unit =
  env_stamps := block_envs

(* One computation per program, keyed on the program's physical
   identity. *)
let summaries_memo :
    ((Bap.Std.program term * Hike_abi.t) * Var.Set.t option Tid.Map.t) option ref
  = ref None
