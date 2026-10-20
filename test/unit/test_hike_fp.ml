(* The FP temp width pins: one intrinsic temp name serves several
   widths, so the pass puts the width into the identity (the name) and
   names each mapped FP call's operand width. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

let the_sub (p : program term) : sub term = Term.enum sub_t p |> Seq.hd_exn

let subs_of (p : program term) : sub term list =
  Term.enum sub_t p |> Seq.to_list

let def_lhs_names (sub : sub term) : string list =
  Term.enum blk_t sub
  |> Seq.concat_map ~f:(fun b ->
         Term.enum def_t b |> Seq.map ~f:(fun d -> Var.name (Def.lhs d)))
  |> Seq.to_list

let var_names (sub : sub term) : string list =
  Term.enum blk_t sub
  |> Seq.concat_map ~f:(fun b ->
         Term.enum def_t b
         |> Seq.concat_map ~f:(fun d ->
                Core.Set.to_sequence (Exp.free_vars (Def.rhs d)))
         |> Seq.map ~f:Var.name)
  |> Seq.to_list

let targets_of (sub : sub term) : string list =
  Term.enum blk_t sub
  |> Seq.concat_map ~f:(fun b ->
         Term.enum jmp_t b
         |> Seq.filter_map ~f:(fun j ->
                match Jmp.kind j with
                | Call c -> (
                    match Call.target c with
                    | Direct t -> Some (Tid.name t)
                    | Indirect _ -> None)
                | _ -> None))
  |> Seq.to_list

(* One temp def at [w] bits, read back, plus an FP call to [intr].
   The FP pass is a pre-SSA stage (the pipeline qualifies the temps
   before the SSA construction), so the fixture is the pre-SSA sub. *)
let fp_fixture (intr : string) (w : int) : sub term =
  let temp =
    Var.create ~is_virtual:false ~fresh:false "intrinsic:x0" (Type.Imm w)
  in
  let rd = Var.create ~is_virtual:false ~fresh:false "fp_rd" (Type.Imm w) in
  let callee = Tid.for_name intr in
  fst
    (raw_sub_of "fp_w"
       [ ( [ Def.create temp (Bil.Int (Cbat_word.to_word (w64 1))) ],
           [ (1,
              fun t ->
                Jmp.create
                  (Call
                     (Call.create ~return:(Direct t) ~target:(Direct callee) ()))) ]
         );
         ([ Def.create rd (Bil.Var temp) ], [ (2, mk_goto) ]);
         ([], [ (0, fun _ -> Jmp.create (Ret (Direct (Tid.create ())))) ]) ])

let fp_run (subs : sub term list) : Hike.Synth.table * program term =
  Hike.Fp.run_program ~synth:Hike.Synth.empty (Program.create ~subs ())

let fp_prog (subs : sub term list) : program term = snd (fp_run subs)

let tests : unit Alcotest.test list =
  [
    (* HFP-02: the same source name at two widths stays two identities. *)
    pin "HFP-02" "a 32-bit and a 64-bit temp def stay distinct"
      (fun () ->
        let names =
          Base.List.concat_map
            (subs_of (fp_prog [ fp_fixture "intrinsic:not_mapped" 32;
                                fp_fixture "intrinsic:not_mapped" 64 ]))
            ~f:def_lhs_names
        in
        check "HFP-02: both widths are distinct identities, never the bare name"
          (Base.List.mem names "intrinsic:x0:32" ~equal:String.equal
          && Base.List.mem names "intrinsic:x0:64" ~equal:String.equal
          && not (Base.List.mem names "intrinsic:x0" ~equal:String.equal)));

    (* HFP-03: an untagged mapped target takes the table's sized spelling
       for the nearest preceding temp def's width. *)
    pin "HFP-03" "an untagged mapped target is rewritten to its sized spelling"
      (fun () ->
        let sub =
          the_sub (fp_prog [ fp_fixture "intrinsic:fadd_rne_ieee754_binary" 64 ])
        in
        check "HFP-03: the target names the operand width"
          (Base.List.mem (targets_of sub)
             "@intrinsic:fadd_rne_ieee754_binary_64"
             ~equal:String.equal));

    (* HFP-04: an already sized target is left alone, and a non-mapped one
       is never rewritten. *)
    pin "HFP-04" "a sized target and a non-mapped target are untouched"
      (fun () ->
        let targets =
          Base.List.concat_map
            (subs_of
               (fp_prog
                  [ fp_fixture "intrinsic:fadd_rne_ieee754_binary_32" 32;
                    fp_fixture "intrinsic:not_a_real_intrinsic" 32 ]))
            ~f:targets_of
        in
        check "HFP-04: sized and non-mapped targets keep their names"
          (Base.List.mem targets "@intrinsic:fadd_rne_ieee754_binary_32"
             ~equal:String.equal
          && Base.List.mem targets "@intrinsic:not_a_real_intrinsic"
               ~equal:String.equal));

    (* HFP-05: an unqualified target whose temp width has no sized row
       stays unqualified AND says so — the residue is loud, and every
       consumer's word-width fallback is the recorded answer. *)
    pin "HFP-05" "an unsizable width leaves the target unqualified and warns"
      (fun () ->
        let out = ref "" in
        let synth, prog = fp_run [ fp_fixture "intrinsic:forder_ieee754_binary" 80 ] in
        let sub = the_sub prog in
        out := capture_stderr (fun () ->
            ignore (Hike.Fp.run_program ~synth (Program.create ~subs:[ sub ] ())));
        let targets =
          Base.List.concat_map (subs_of (fp_prog
              [ fp_fixture "intrinsic:forder_ieee754_binary" 80 ]))
            ~f:targets_of
        in
        check "HFP-05: the warn fires and the target stays unqualified"
          (contains_substring !out "has no sized spelling at width 80"
          && Base.List.mem targets "@intrinsic:forder_ieee754_binary"
               ~equal:String.equal));
  ]

let () = run "hike_fp" tests
