(* Microbenchmark: the per-op cost of the domain's numeric substrate.

   Word.t = Z.t (GMP). Values >62 bits are always boxed; the domain's
   words are 64/65-bit, so every op allocates. This measures:
     - ns/op and minor-words/op for Word.t at the domain's widths
     - the same for int64 (the proposed fast path)
     - the ratio, and therefore how many ops the measured 653M minor
       words per heavy sub actually represents.

   Decides: is the domain's cost op-COUNT or op-COST? *)

let n = 2_000_000

let time f =
  let t0 = Unix.gettimeofday () in
  let r = f () in
  let t1 = Unix.gettimeofday () in
  (t1 -. t0, r)

let minor_words () =
  let s = Gc.quick_stat () in
  s.Gc.minor_words

let () =
  Printf.printf "OCaml %s\n" Sys.ocaml_version;
  let open Bap.Std in

  (* --- Word.t: the domain's mix (add / mul / compare / shift) --- *)
  let w64 = Word.of_int ~width:64 0x1234567890ABCDEF in
  let w65 = Word.of_int ~width:65 7 in
  let w64b = Word.of_int ~width:64 0x0FEDCBA987654321 in

  let m0 = minor_words () in
  let t, _ = time (fun () ->
      let acc = ref w64 in
      for _ = 1 to n do acc := Word.add !acc w64b done;
      !acc) in
  let mw = minor_words () -. m0 in
  Printf.printf "Word.add   w64 : %7.1f ns/op   %.2f words/op\n"
    (t *. 1e9 /. float n) (mw /. float n);

  let m0 = minor_words () in
  let t, _ = time (fun () ->
      let acc = ref w64 in
      for _ = 1 to n do acc := Word.mul !acc w64b done;
      !acc) in
  let mw = minor_words () -. m0 in
  Printf.printf "Word.mul   w64 : %7.1f ns/op   %.2f words/op\n"
    (t *. 1e9 /. float n) (mw /. float n);

  let m0 = minor_words () in
  let t, _ = time (fun () ->
      let acc = ref 0 in
      for _ = 1 to n do if Word.compare w64 w64b > 0 then incr acc done;
      !acc) in
  let mw = minor_words () -. m0 in
  Printf.printf "Word.compare   : %7.1f ns/op   %.2f words/op\n"
    (t *. 1e9 /. float n) (mw /. float n);

  let m0 = minor_words () in
  let t, _ = time (fun () ->
      let acc = ref w65 in
      for _ = 1 to n do acc := Word.lshift !acc w65 done;
      !acc) in
  let mw = minor_words () -. m0 in
  Printf.printf "Word.lshift w65: %7.1f ns/op   %.2f words/op\n"
    (t *. 1e9 /. float n) (mw /. float n);

  (* --- int64: the proposed fast path --- *)
  let i0 = 0x1234567890ABCDEFL and i1 = 0x0FEDCBA987654321L in
  let m0 = minor_words () in
  let t, _ = time (fun () ->
      let acc = ref i0 in
      for _ = 1 to n do acc := Int64.add !acc i1 done;
      !acc) in
  let mw = minor_words () -. m0 in
  Printf.printf "Int64.add      : %7.1f ns/op   %.2f words/op\n"
    (t *. 1e9 /. float n) (mw /. float n);

  let t, _ = time (fun () ->
      let acc = ref i0 in
      for _ = 1 to n do acc := Int64.mul !acc i1 done;
      !acc) in
  Printf.printf "Int64.mul      : %7.1f ns/op\n" (t *. 1e9 /. float n);

  (* --- what the measured churn implies --- *)
  let measured_minor = 653_000_000.0 in     (* du/ls __strftime_internal *)
  let measured_secs = 2.8 in
  Printf.printf "\nImplied by the measurement (% .0f minor words / %.1fs):\n"
    measured_minor measured_secs;
  Printf.printf "  if ~6 words/op  -> %.0f M ops  (%.0f M ops/s)\n"
    (measured_minor /. 6.0 /. 1e6) (measured_minor /. 6.0 /. measured_secs /. 1e6);
  Printf.printf "  if ~2 words/op  -> %.0f M ops  (%.0f M ops/s)\n"
    (measured_minor /. 2.0 /. 1e6) (measured_minor /. 2.0 /. measured_secs /. 1e6);
  Printf.printf "  if ~20 words/op -> %.0f M ops  (%.0f M ops/s)\n"
    (measured_minor /. 20.0 /. 1e6) (measured_minor /. 20.0 /. measured_secs /. 1e6);
  Printf.printf "\n(reference: a 3 GHz core does ~%.0f M trivial int ops/s)\n" 1000.0
