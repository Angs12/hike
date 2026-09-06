(* Microbenchmark: the per-op cost of the word substrate.

    [Bap.Std.Word.t] packs a [Z.t]; magnitudes above 62 bits are always
    boxed, and the domain's words are 64/65/129-bit, so every op allocates.
    [Cbat_word] keeps small magnitudes in an int63 immediate and falls back
    to [Z.t] otherwise.  This measures ns/op and minor-words/op for both, on
    the domain's own widths, so the fast path's payoff is a number rather
    than an argument.

    Operands are drawn from an array indexed by the loop counter, so no
    operand is loop-invariant and nothing gets hoisted.

    Usage: wordbench.exe *)

open Bap.Std

let n = 2_000_000

let minor () = (Gc.quick_stat ()).Gc.minor_words
let now () = Unix.gettimeofday ()

let row nm f =
  ignore (f ()); (* warm *)
  let m0 = minor () in
  let t0 = now () in
  let r = f () in
  let t1 = now () in
  ignore (Sys.opaque_identity r);
  Printf.printf "  %-22s %8.2f ns/op %8.2f w/op\n%!" nm
    ((t1 -. t0) *. 1e9 /. float n)
    ((minor () -. m0) /. float n)

(* The domain's magnitudes: stack offsets and small counts. *)
let smalls : int array = Array.init 1024 (fun i -> (i * 7 + 3) land 0x3FFFF)
(* Magnitudes above 2^62: these are always boxed, in both representations. *)
let wides : Z.t array =
  Array.init 1024 (fun i -> Z.add (Z.shift_left Z.one 63) (Z.of_int (i + 1)))

let[@inline] sget i = Array.unsafe_get smalls (i land 1023)
let[@inline] wget i = Array.unsafe_get wides (i land 1023)

let () =
  Printf.printf "OCaml %s  int_size=%d\n" Sys.ocaml_version Sys.int_size;
  let width = 64 in

  Printf.printf "\nwidth %d, small-magnitude operands (n=%d)\n%!" width n;
  let wr = Array.map (Word.of_int ~width) smalls in
  let cr = Array.map (Cbat_word.of_int ~width) smalls in

  row "Word.add" (fun () ->
      let a = ref wr.(0) in
      for i = 0 to n - 1 do a := Word.add wr.(i land 1023) wr.((i + 1) land 1023) done;
      !a);
  row "Cbat_word.add" (fun () ->
      let a = ref cr.(0) in
      for i = 0 to n - 1 do a := Cbat_word.add cr.(i land 1023) cr.((i + 1) land 1023) done;
      !a);
  (* [sub] with a non-negative difference: the domain's end-minus-base
     shape.  Both rows are measured, because at width 64 the wrap arm
     lands above 2^62 and so is boxed whatever the substrate does. *)
  row "Word.sub (no wrap)" (fun () ->
      let a = ref wr.(0) in
      for i = 0 to n - 1 do a := Word.sub wr.((i + 1) land 1023) wr.(3) done;
      !a);
  row "Cbat_word.sub (no wrap)" (fun () ->
      let a = ref cr.(0) in
      for i = 0 to n - 1 do a := Cbat_word.sub cr.((i + 1) land 1023) cr.(3) done;
      !a);
  row "Word.sub (wrap)" (fun () ->
      let a = ref wr.(0) in
      for i = 0 to n - 1 do a := Word.sub wr.(3) wr.((i + 1) land 1023) done;
      !a);
  row "Cbat_word.sub (wrap)" (fun () ->
      let a = ref cr.(0) in
      for i = 0 to n - 1 do a := Cbat_word.sub cr.(3) cr.((i + 1) land 1023) done;
      !a);
  row "Word.mul" (fun () ->
      let a = ref wr.(0) in
      for i = 0 to n - 1 do a := Word.mul wr.(i land 1023) wr.((i land 15) + 1) done;
      !a);
  row "Cbat_word.mul" (fun () ->
      let a = ref cr.(0) in
      for i = 0 to n - 1 do a := Cbat_word.mul cr.(i land 1023) cr.((i land 15) + 1) done;
      !a);
  row "Word.div" (fun () ->
      let a = ref wr.(0) in
      for i = 0 to n - 1 do a := Word.div wr.(i land 1023) wr.((i lor 1) land 1023) done;
      !a);
  row "Cbat_word.div" (fun () ->
      let a = ref cr.(0) in
      for i = 0 to n - 1 do a := Cbat_word.div cr.(i land 1023) cr.((i lor 1) land 1023) done;
      !a);
  row "Word.modulo" (fun () ->
      let a = ref wr.(0) in
      for i = 0 to n - 1 do a := Word.modulo wr.(i land 1023) wr.((i lor 1) land 1023) done;
      !a);
  row "Cbat_word.modulo" (fun () ->
      let a = ref cr.(0) in
      for i = 0 to n - 1 do a := Cbat_word.modulo cr.(i land 1023) cr.((i lor 1) land 1023) done;
      !a);
  row "Word.logand" (fun () ->
      let a = ref wr.(0) in
      for i = 0 to n - 1 do a := Word.logand wr.(i land 1023) wr.((i + 1) land 1023) done;
      !a);
  row "Cbat_word.logand" (fun () ->
      let a = ref cr.(0) in
      for i = 0 to n - 1 do a := Cbat_word.logand cr.(i land 1023) cr.((i + 1) land 1023) done;
      !a);
  (* [lnot] at width 64 lands above 2^62, so it is boxed on both sides;
     at 32 bits it stays small.  Both are measured. *)
  let wr32 = Array.map (Word.of_int ~width:32) smalls in
  let cr32 = Array.map (Cbat_word.of_int ~width:32) smalls in
  row "Word.lnot w64" (fun () ->
      let a = ref wr.(0) in
      for i = 0 to n - 1 do a := Word.lnot wr.(i land 1023) done;
      !a);
  row "Cbat_word.lnot w64" (fun () ->
      let a = ref cr.(0) in
      for i = 0 to n - 1 do a := Cbat_word.lnot cr.(i land 1023) done;
      !a);
  row "Word.lnot w32" (fun () ->
      let a = ref wr32.(0) in
      for i = 0 to n - 1 do a := Word.lnot wr32.(i land 1023) done;
      !a);
  row "Cbat_word.lnot w32" (fun () ->
      let a = ref cr32.(0) in
      for i = 0 to n - 1 do a := Cbat_word.lnot cr32.(i land 1023) done;
      !a);
  row "Word.succ" (fun () ->
      let a = ref wr.(0) in
      for i = 0 to n - 1 do a := Word.succ wr.(i land 1023) done;
      !a);
  row "Cbat_word.succ" (fun () ->
      let a = ref cr.(0) in
      for i = 0 to n - 1 do a := Cbat_word.succ cr.(i land 1023) done;
      !a);
  row "Word.lshift" (fun () ->
      let a = ref wr.(0) in
      for i = 0 to n - 1 do a := Word.lshift wr.(i land 1023) wr.(3) done;
      !a);
  row "Cbat_word.lshift" (fun () ->
      let a = ref cr.(0) in
      for i = 0 to n - 1 do a := Cbat_word.lshift cr.(i land 1023) cr.(3) done;
      !a);
  row "Word.compare" (fun () ->
      let a = ref 0 in
      for i = 0 to n - 1 do
        if Word.compare wr.(i land 1023) wr.((i + 1) land 1023) > 0 then incr a
      done;
      !a);
  row "Cbat_word.compare" (fun () ->
      let a = ref 0 in
      for i = 0 to n - 1 do
        if Cbat_word.compare cr.(i land 1023) cr.((i + 1) land 1023) > 0 then incr a
      done;
      !a);
  row "Word.bitwidth" (fun () ->
      let a = ref 0 in
      for i = 0 to n - 1 do a := !a + Word.bitwidth wr.(i land 1023) done;
      !a);
  row "Cbat_word.bitwidth" (fun () ->
      let a = ref 0 in
      for i = 0 to n - 1 do a := !a + Cbat_word.bitwidth cr.(i land 1023) done;
      !a);
  row "Word.is_zero" (fun () ->
      let a = ref 0 in
      for i = 0 to n - 1 do if Word.is_zero wr.(i land 1023) then incr a done;
      !a);
  row "Cbat_word.is_zero" (fun () ->
      let a = ref 0 in
      for i = 0 to n - 1 do if Cbat_word.is_zero cr.(i land 1023) then incr a done;
      !a);
  row "Word.extract_exn" (fun () ->
      let a = ref wr.(0) in
      for i = 0 to n - 1 do a := Word.extract_exn ~hi:31 ~lo:0 wr.(i land 1023) done;
      !a);
  row "Cbat_word.extract_exn" (fun () ->
      let a = ref cr.(0) in
      for i = 0 to n - 1 do a := Cbat_word.extract_exn ~hi:31 ~lo:0 cr.(i land 1023) done;
      !a);

  Printf.printf "\nwidth %d, wide operands (>2^62: boxed on both sides)\n%!" width;
  let wz = Array.init 1024 (fun i -> Word.of_string (Z.to_string (wget i) ^ ":" ^ string_of_int width)) in
  let cz = Array.init 1024 (fun i -> Cbat_word.of_z (wget i) width) in
  row "Word.add" (fun () ->
      let a = ref wz.(0) in
      for i = 0 to n - 1 do a := Word.add !a wz.((i + 1) land 1023) done;
      !a);
  row "Cbat_word.add" (fun () ->
      let a = ref cz.(0) in
      for i = 0 to n - 1 do a := Cbat_word.add !a cz.((i + 1) land 1023) done;
      !a);

  Printf.printf "\nwidth 129 ([dom_size ~width:(2*width+1)]'s width)\n%!";
  let w129 = Array.init 1024 (fun i -> Word.of_int ~width:129 (sget i)) in
  let c129 = Array.init 1024 (fun i -> Cbat_word.of_int ~width:129 (sget i)) in
  row "Word.add" (fun () ->
      let a = ref w129.(0) in
      for i = 0 to n - 1 do a := Word.add w129.(i land 1023) w129.((i + 1) land 1023) done;
      !a);
  row "Cbat_word.add" (fun () ->
      let a = ref c129.(0) in
      for i = 0 to n - 1 do a := Cbat_word.add c129.(i land 1023) c129.((i + 1) land 1023) done;
      !a);

  Printf.printf "\nmachine-int floor (what the fast path is chasing)\n%!";
  row "int add" (fun () ->
      let a = ref 3 in
      for i = 0 to n - 1 do a := !a + sget (i + 1) done;
      !a);
  ignore sget
