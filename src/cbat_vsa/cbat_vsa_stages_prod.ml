(* Production no-op adapter. *)

let denote_calls = ref 0
let join_calls = ref 0
let equal_calls = ref 0
let widen_calls = ref 0
let walk_calls = ref 0

let incr_walk () = ()

let t_scaffold = ref 0.
let scaffold_calls = ref 0

(* Unused cell-landmark census refs; parity with the debug adapter. *)
let cell_lm_recorded = ref 0
let cell_lm_consumed = ref 0

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

let report (_label : string) : unit = ()

