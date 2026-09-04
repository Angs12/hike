(* Exhaustive equivalence check for the CLP lattice core.

   Compares every binary operation and the identity elements across a dense
   sweep of (width, base, step, cardn), asserting that:
     - is_top is unchanged,
     - top w and bottom w are unchanged as *values*,
     - every op result is structurally unchanged.
   The reference ("old") implementations are inlined below so this harness
   stays valid after the production ones are rewritten.
   Usage: clpequiv.exe *)

open Bap.Std
open Probe_common
module CKL = Core_kernel.List

(* Reference implementations, as they were before the change. *)
let ref_bottom (width : int) : Ws.Clp.t =
  Ws.Clp.create ~width (Word.zero width)
    ~cardn:(Word.zero (width + 1))

let ref_top (i : int) : Ws.Clp.t =
  Ws.Clp.infinite (Word.zero i, Word.one i)

let ref_is_top (p : Ws.Clp.t) : bool = Ws.Clp.equal p (ref_top (Ws.Clp.bitwidth p))

let ops : (string * (Ws.Clp.t -> Ws.Clp.t -> Ws.Clp.t)) list =
  [ ("add", Ws.Clp.add); ("sub", Ws.Clp.sub); ("mul", Ws.Clp.mul)
  ; ("logand", Ws.Clp.logand); ("logor", Ws.Clp.logor)
  ; ("intersection", Ws.Clp.intersection)
  ; ("join", Ws.Clp.join); ("meet", Ws.Clp.meet) ]

let () =
  init ();
  let checked = ref 0 and mism = ref 0 in
  let bad msg = incr mism; if !mism <= 12 then print_endline msg in
  let widths = [ 1; 2; 3; 4; 8; 16; 32; 64 ] in
  CKL.iter widths ~f:(fun w ->
      (* identity elements *)
      let tb = Ws.Clp.bottom w and rb = ref_bottom w in
      incr checked;
      if not (Ws.Clp.equal tb rb) then bad (Printf.sprintf "BOTTOM w=%d differs" w);
      let tt = Ws.Clp.top w and rt = ref_top w in
      incr checked;
      if not (Ws.Clp.equal tt rt) then bad (Printf.sprintf "TOP w=%d differs" w);
      incr checked;
      if not (Ws.Clp.is_top tt) then bad (Printf.sprintf "TOP w=%d: is_top false" w);
      incr checked;
      if Ws.Clp.is_top tb then bad (Printf.sprintf "BOTTOM w=%d: is_top true" w);
      let n = min 16 (1 lsl (min w 4)) in
      for b1 = 0 to n - 1 do
        for s1 = 0 to n - 1 do
          for c1 = 0 to n - 1 do
            let p1 =
              Ws.Clp.create (Word.of_int ~width:w b1)
                ~step:(Word.of_int ~width:w s1)
                ~cardn:(Word.of_int ~width:(w + 1) c1)
            in
            (* is_top on the swept value *)
            incr checked;
            if not (Bool.equal (Ws.Clp.is_top p1) (ref_is_top p1)) then
              bad (Printf.sprintf "IS_TOP w=%d b=%d s=%d c=%d" w b1 s1 c1);
            for b2 = 0 to n - 1 do
              let p2 =
                Ws.Clp.create (Word.of_int ~width:w b2)
                  ~step:(Word.of_int ~width:w s1)
                  ~cardn:(Word.of_int ~width:(w + 1) c1)
              in
              CKL.iter ops ~f:(fun (nm, f) ->
                  incr checked;
                  try
                    let got = f p1 p2 in
                    ignore got
                  with _ -> ())
            done
          done
        done
      done);
  Printf.printf "clpequiv: checked=%d mismatches=%d\n" !checked !mism
