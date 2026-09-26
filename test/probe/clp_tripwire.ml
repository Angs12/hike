(* Allocation tripwire: per-op minor-word ceilings over clp_bench's 50
   rows. Counts are machine-independent (Gc.minor_words; the two loops
   must agree); a ceiling is 2x the post-fix count + 16 — generous, so
   only a real allocation regression trips. No wall-time assertions. *)
open Probe_common
open Clp_bench_rows

let ceilings : (string * int) list =
  [
    ("word.logand(mask,addr)", 24);
    ("word.logand(big,big)", 32);
    ("word.logand(128,128)", 34);
    ("word.logor(addr,mask)", 24);
    ("word.logxor(small,small)", 24);
    ("word.logxor(signed,big)", 32);
    ("word.lnot(mask)", 54);
    ("word.lnot(big)", 64);
    ("word.extract_exn(hi=31,addr)", 24);
    ("word.extract_exn(hi=7,big)", 24);
    ("word.extract_exn(hi=63,128)", 34);
    ("word.factor_2s(big)", 40);
    ("word.factor_2s(mask)", 30);
    ("word.factor_2s(128)", 42);
    ("word.lead_1_bit(mask)", 20);
    ("word.lead_1_bit(big)", 20);
    ("word.lead_1_bit(zero)", 24);
    ("word.mkzw(via of_word 64)", 44);
    ("word.mkzw(via of_word 128)", 46);
    ("word.mkzw(via of_int64 -1)", 54);
    ("word.mkzw(via of_int 64 -1)", 46);
    ("clp.logand(asc8,asc8b)", 926);
    ("clp.logand(interval,interval)", 1760);
    ("clp.logand(interval,singleton)", 1582);
    ("clp.logand(128,128)", 1406);
    ("clp.logor(asc8,asc8b)", 2766);
    ("clp.logor(interval,singleton)", 2216);
    ("clp.logxor(singleton,singleton)", 1924);
    ("clp.logxor(asc8,asc8b)", 7472);
    ("clp.logxor(interval,interval)", 6484);
    ("clp.logxor(128,128)", 7736);
    ("clp.create(singleton)", 66);
    ("clp.create(two,step8)", 50);
    ("clp.create(finite,step8,2^20)", 50);
    ("clp.create(wrap,step8,2^63)", 92);
    ("clp.create(128,singleton)", 74);
    ("composite.logand(clp,clp)", 1312);
    ("composite.logand(fin,fin)", 2902);
    ("composite.logand(clp,fin)", 3634);
    ("composite.logand(stack,nib)", 254);
    ("composite.logand(stack,mask)", 224);
    ("composite.logand(stack,stack)", 32);
    ("composite.logor(clp,clp)", 2668);
    ("composite.logor(fin,fin)", 86);
    ("composite.logxor(clp,clp)", 7004);
    ("composite.logxor(fin,fin)", 86);
    ("composite.logxor(stack,fin)", 32);
    ("composite.lnot(clp)", 230);
    ("composite.lnot(fin)", 980);
    ("composite.lnot(stack)", 32);
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
