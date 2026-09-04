(* The sole production output channel. *)

(* Emit a [hike: ...] warning. The prefix is load-bearing. *)
let warn fmt =
  Printf.ksprintf
    (fun s -> Printf.eprintf "hike: %s\n" s)
    fmt

