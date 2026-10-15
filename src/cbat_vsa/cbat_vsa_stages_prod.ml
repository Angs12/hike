(* Production no-op adapter. *)

let incr_walk () = ()

let reset () = ()

let time (_which : [ `Denote | `Equal | `Glue | `Join | `Scaffold | `Walk | `Widen ])
    (f : unit -> 'a) : 'a = f ()

let report (_label : string) : unit = ()
