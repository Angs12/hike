(* Production no-op adapter. *)

let enabled = false

let denote_calls = ref 0
let join_calls = ref 0
let equal_calls = ref 0
let widen_calls = ref 0
let walk_calls = ref 0

(* Unused metric refs; parity with the debug adapter. *)
let walk_pops = ref 0
let walk_blocks = ref 0
let walk_truncs = ref 0
let walk_max_pops = ref 0
let budget_hits = ref 0
let pops_saved = ref 0

let t_scaffold = ref 0.
let scaffold_calls = ref 0

let t_glue = ref 0.
let glue_calls = ref 0

(* Unused time refs; parity with the debug adapter. *)
let t_denote = ref 0.
let t_walk = ref 0.
let t_join = ref 0.
let t_widen = ref 0.
let t_equal = ref 0.

let reset () = ()

let time (_which : [ `Denote | `Equal | `Glue | `Join | `Scaffold | `Walk | `Widen ])
    (f : unit -> 'a) : 'a = f ()

let bump_walk_pops ~pops:_ ~blocks:_ ~truncated:_ ~budget_cap:_ () = ()

let report (_label : string) : unit = ()

let stats () :
    float * int * float * int * float * int * int * int * int * int * float =
  (0., 0, 0., 0, 0., 0, 0, 0, 0, 0, 0.)

let memo_stats () : int * int * int * int * int = (0, 0, 0, 0, 0)

