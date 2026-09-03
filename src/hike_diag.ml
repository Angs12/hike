(* The sole production output channel. *)

(* Emit a [hike: ...] warning. The prefix is load-bearing. *)
let warn fmt =
  Printf.ksprintf
    (fun s -> Printf.eprintf "hike: %s\n" s)
    fmt

(* Warn once per [key]. *)
let warn_once ~(tbl : unit -> bool ref) ~(set : unit -> unit) key fmt =
  Printf.ksprintf
    (fun s ->
      let seen = tbl () in
      if not !seen then begin
        Printf.eprintf "hike: %s\n" s;
        set ();
        seen := true
      end)
    fmt
