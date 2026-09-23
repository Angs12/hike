(* KB operation census: one count per counter key, dumped at exit.  The
   counters exist only under VSA_DEBUG — a non-debug build compiles the
   module empty and every call site to nothing. *)

#ifdef VSA_DEBUG
open Core

(* [<slot>.<get|put>] for every hike KB slot, [seam.query.def] /
   [seam.query.nodef] for the denotation seam, and [domain.*] for the
   domain callbacks the KB invokes on a put. *)
let counts : (string, int) Hashtbl.t = Hashtbl.create (module String)

let bump (key : string) : unit =
  let n = Hashtbl.find counts key |> Option.value ~default:0 in
  Hashtbl.set counts ~key ~data:(n + 1)

let dump () =
  Hashtbl.to_alist counts
  |> List.sort ~compare:(fun (a, _) (b, _) -> String.compare a b)
  |> List.iter ~f:(fun (key, n) ->
         Printf.eprintf "hike-kb-census: %s=%d\n%!" key n)

let () = at_exit dump
#endif
