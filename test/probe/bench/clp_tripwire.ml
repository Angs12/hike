(* Allocation tripwire: per-op minor-word ceilings over clp_bench's 50
   rows. Counts are machine-independent (Gc.minor_words; the two loops
   must agree); a ceiling is 2x the post-fix count + 16 — generous, so
   only a real allocation regression trips. No wall-time assertions. *)
open Probe_common
open Clp_bench_rows

let ceilings : (string * int) list =
  [
    ("word.logand(mask,addr)", 24);
    ("word.logand(big,big)", 30);
    ("word.logand(128,128)", 34);
    ("word.logor(addr,mask)", 24);
    ("word.logxor(small,small)", 24);
    ("word.logxor(signed,big)", 30);
    ("word.lnot(mask)", 30);
    ("word.lnot(big)", 30);
    ("word.extract_exn(hi=31,addr)", 24);
    ("word.extract_exn(hi=7,big)", 24);
    ("word.extract_exn(hi=63,128)", 40);
    ("word.factor_2s(big)", 30);
    ("word.factor_2s(mask)", 30);
    ("word.factor_2s(128)", 42);
    ("word.lead_1_bit(mask)", 20);
    ("word.lead_1_bit(big)", 20);
    ("word.lead_1_bit(zero)", 24);
    ("word.mkzw(via of_word 64)", 50);
    ("word.mkzw(via of_word 128)", 46);
    ("word.mkzw(via of_int64 -1)", 30);
    ("word.mkzw(via of_int 64 -1)", 30);
    ("clp.logand(asc8,asc8b)", 724);
    ("clp.logand(interval,interval)", 1480);
    ("clp.logand(interval,singleton)", 228);
    ("clp.logand(128,128)", 1482);
    ("clp.logor(asc8,asc8b)", 1134);
    ("clp.logor(interval,singleton)", 774);
    ("clp.logxor(singleton,singleton)", 2466);
    ("clp.logxor(asc8,asc8b)", 5304);
    ("clp.logxor(interval,interval)", 6750);
    ("clp.logxor(128,128)", 8124);
    ("clp.create(singleton)", 82);
    ("clp.create(two,step8)", 74);
    ("clp.create(finite,step8,2^20)", 74);
    ("clp.create(wrap,step8,2^63)", 116);
    ("clp.create(128,singleton)", 90);
    ("composite.logand(clp,clp)", 1372);
    ("composite.logand(fin,fin)", 5254);
    ("composite.logand(clp,fin)", 3716);
    ("composite.logand(stack,nib)", 944);
    ("composite.logand(stack,mask)", 342);
    ("composite.logand(stack,stack)", 82);
    ("composite.logor(clp,clp)", 2006);
    ("composite.logor(fin,fin)", 644);
    ("composite.logxor(clp,clp)", 6302);
    ("composite.logxor(fin,fin)", 644);
    ("composite.logxor(stack,fin)", 82);
    ("composite.lnot(clp)", 330);
    ("composite.lnot(fin)", 1986);
    ("composite.lnot(stack)", 82);
  ]

let () =
  init ();
  let rows = rows () in
  let ceiling_of n = List.assoc_opt n ceilings in
  let over =
    List.filter
      (fun r ->
        match ceiling_of r.name with
        | Some c -> r.w_a > float_of_int c || r.w_b > float_of_int c
        | None -> false)
      rows
  in
  let no_ceiling = List.filter (fun r -> ceiling_of r.name = None) rows in
  let stale =
    List.filter (fun (n, _) -> not (List.exists (fun r -> r.name = n) rows))
      ceilings
  in
  List.iter
    (fun r ->
      Printf.eprintf "TRIPWIRE OVER: %s words=(%.0f, %.0f) ceiling=%s\n"
        r.name r.w_a r.w_b
        (match ceiling_of r.name with
        | Some c -> string_of_int c
        | None -> "?"))
    over;
  List.iter
    (fun r -> Printf.eprintf "TRIPWIRE NO-CEILING: %s\n" r.name)
    no_ceiling;
  List.iter
    (fun (n, _) -> Printf.eprintf "TRIPWIRE STALE-CEILING: %s\n" n)
    stale;
  if over = [] && no_ceiling = [] && stale = [] then
    Printf.printf "TRIPWIRE OK: %d rows within ceilings\n" (List.length rows)
  else begin
    Printf.eprintf
      "TRIPWIRE FAIL: %d over, %d no-ceiling, %d stale, rows=%d ceilings=%d\n"
      (List.length over) (List.length no_ceiling) (List.length stale)
      (List.length rows) (List.length ceilings);
    exit 1
  end
