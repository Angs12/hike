(* Census counters: one count per counter key, dumped at exit under a
   per-instance prefix.  The counters exist only under VSA_DEBUG — a
   non-debug build compiles the module empty and every call site to
   nothing. *)

#ifdef VSA_DEBUG
open Core

module Make (P : sig val prefix : string end) = struct
  let counts : int String.Map.t ref = ref String.Map.empty

  let bump (key : string) : unit =
    counts := Map.update !counts key ~f:(function Some n -> n + 1 | None -> 1)

  let dump () =
    Map.iteri !counts ~f:(fun ~key ~data:n ->
        Printf.eprintf "%s: %s=%d\n%!" P.prefix key n)

  let () = at_exit dump

  (* Print the first [limit] lines carrying [key]; the rest only count.
     The per-visit witness a counting key cannot show. *)
  let noted : (string, int) Hashtbl.t = Hashtbl.create (module String)

  let note (key : string) ~(limit : int) (msg : string) : unit =
    let n = Hashtbl.find noted key |> Option.value ~default:0 in
    Hashtbl.set noted ~key ~data:(n + 1);
    if n < limit then Printf.eprintf "%s: %s\n%!" P.prefix msg
end
#endif
