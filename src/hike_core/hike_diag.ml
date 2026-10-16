(* The sole production output channel; the [hike:] prefix is
   load-bearing. *)
(* A debug trace line, compiled out of production; the message is a thunk
   so production never formats it. *)
let debug ~(tag : string) (msg : unit -> string) =
#ifdef VSA_DEBUG
  Printf.eprintf "%s: %s\n%!" tag (msg ())
#else
  ignore msg
#endif

let warn fmt =
  Printf.ksprintf
    (fun s -> Printf.eprintf "hike: %s\n%!" s)
    fmt

