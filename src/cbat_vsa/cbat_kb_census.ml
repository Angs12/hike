(* KB operation census: one count per counter key, dumped at exit.  The
   counters exist only under VSA_DEBUG — a non-debug build compiles the
   module empty and every call site to nothing. *)

#ifdef VSA_DEBUG
open Core

(* [<slot>.<get|put>] for every hike KB slot, [seam.query.def] /
   [seam.query.nodef] for the denotation seam, and [domain.*] for the
   domain callbacks the KB invokes on a put. *)
let counts : int String.Map.t ref = ref String.Map.empty

let bump (key : string) : unit =
  counts := Map.update !counts key ~f:(function Some n -> n + 1 | None -> 1)

let dump () =
  Map.iteri !counts ~f:(fun ~key ~data:n ->
         Printf.eprintf "hike-kb-census: %s=%d\n%!" key n)

let () = at_exit dump
#endif
