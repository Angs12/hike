(* The sole production output channel; the [hike:] prefix is
   load-bearing. *)
let warn fmt =
  Printf.ksprintf
    (fun s -> Printf.eprintf "hike: %s\n" s)
    fmt

