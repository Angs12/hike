(* Attribution census: one count per counter key, dumped at exit.  The
   counters exist only under VSA_DEBUG — a non-debug build compiles the
   module empty and every call site to nothing. *)

#ifdef VSA_DEBUG
open Core

(* Keys name the mechanism: [unbounded.stack.*] / [ld.top.*] for the
   top-address roots, [blind.*] for the bit-reading op, [b65p.shape.*]
   for the band shapes, [call.frame.*] for the call-clamp arms,
   [band.*] for the backward rows, [bottomskip.*] for the dead-edge
   visits. *)
let counts : (string, int) Hashtbl.t = Hashtbl.create (module String)

let bump (key : string) : unit =
  let n = Hashtbl.find counts key |> Option.value ~default:0 in
  Hashtbl.set counts ~key ~data:(n + 1)

let dump () =
  Hashtbl.to_alist counts
  |> List.sort ~compare:(fun (a, _) (b, _) -> String.compare a b)
  |> List.iter ~f:(fun (key, n) ->
         Printf.eprintf "hike-attr-census: %s=%d\n%!" key n)

let () = at_exit dump
#endif
