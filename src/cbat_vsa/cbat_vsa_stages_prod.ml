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

let t_scaffold = ref 0.
let scaffold_calls = ref 0

let t_glue = ref 0.
let glue_calls = ref 0

let reset () = ()

let time (_which : [ `Denote | `Equal | `Glue | `Join | `Scaffold | `Walk | `Widen ])
    (f : unit -> 'a) : 'a = f ()

let bump_walk_pops ~pops:_ ~blocks:_ ~truncated:_ () = ()

let report (_label : string) : unit = ()
