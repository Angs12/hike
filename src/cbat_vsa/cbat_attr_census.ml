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
let counts : int String.Map.t ref = ref String.Map.empty

let bump (key : string) : unit =
  counts := Map.update !counts key ~f:(function Some n -> n + 1 | None -> 1)

let dump () =
  Map.iteri !counts ~f:(fun ~key ~data:n ->
         Printf.eprintf "hike-attr-census: %s=%d\n%!" key n)

let () = at_exit dump

(* Print the first [limit] lines carrying [key]; the rest only count.
   The per-visit witness a counting key cannot show. *)
let noted : (string, int) Hashtbl.t = Hashtbl.create (module String)

let note (key : string) ~(limit : int) (msg : string) : unit =
  let n = Hashtbl.find noted key |> Option.value ~default:0 in
  Hashtbl.set noted ~key ~data:(n + 1);
  if n < limit then Printf.eprintf "hike-attr-census: %s\n%!" msg
#endif
