(* The narrow DCE rule: only target flags and virtual temporaries are
   candidates; every named non-flag value and memory access stays. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

let target = x86_target ()
let synth = Hike.Synth.empty

let ssa_of sub =
  Program.create ~subs:[ sub ] ()
  |> Hike.Ssa.ssa_program ~synth ~target
  |> Term.enum sub_t |> Seq.hd_exn

let removed sub dce v =
  let in_sub s =
    Term.enum blk_t s
    |> Seq.exists ~f:(fun b ->
           Term.enum def_t b |> Seq.exists ~f:(fun d -> Var.same (Def.lhs d) v))
  in
  in_sub sub && not (in_sub dce)

let kept sub v =
  Term.enum blk_t sub
  |> Seq.exists ~f:(fun b ->
         Term.enum def_t b |> Seq.exists ~f:(fun d -> Var.same (Def.lhs d) v))

let tests : unit Alcotest.test list =
  [
    pin "DCE-01"
      "unread flags and virtuals go; named and memory defs stay"
      (fun () ->
        let abi = Hike.Abi.of_target target in
        let virt = Var.create ~is_virtual:true "dce_virt" (Type.Imm 64) in
        let named = v64 "dce_named" in
        let mem = memv "dce_mem" in
        let zf = abi.Hike.Abi.zero_flag in
        let sub =
          let b = Blk.Builder.create () in
          Blk.Builder.add_def b
            (Def.create virt
               (Bil.BinOp (Bil.XOR, Bil.Var (int_param 0), Bil.Var (int_param 1))));
          Blk.Builder.add_def b
            (Def.create zf
               (Bil.BinOp (Bil.EQ, Bil.Var virt, Bil.Var (int_param 2))));
          Blk.Builder.add_def b
            (Def.create named
               (Bil.BinOp (Bil.XOR, Bil.Var (int_param 0), Bil.Var (int_param 3))));
          Blk.Builder.add_def b
            (Def.create mem
               (Bil.Store
                  (Bil.Var mem, Bil.Var (int_param 0), Bil.Var (int_param 1),
                   LittleEndian, `r64)));
          ignore (Blk.Builder.add_jmp b (Hike_return.create ()));
          Blk.Builder.result b
        in
        let sub =
          let sb = Sub.Builder.create ~name:"dce1" () in
          Sub.Builder.add_blk sb sub;
          Sub.Builder.result sb
        in
        let ssa = ssa_of sub in
        let dce = Hike.Dce.dce_sub ~synth ~target ssa in
        Hike_test.Verify_ssa.sub ~synth ~target ~what:"DCE-01" dce;
        check "DCE-01"
          (removed ssa dce virt && removed ssa dce zf
          && not (removed ssa dce named) && kept dce named
          && not (removed ssa dce mem) && kept dce mem));

    pin "DCE-02" "a flag read by a jump condition stays"
      (fun () ->
        let abi = Hike.Abi.of_target target in
        let zf = abi.Hike.Abi.zero_flag in
        let sub, _ = raw_sub_of "dce2"
            [ [ Def.create zf
                  (Bil.BinOp (Bil.EQ, Bil.Var (int_param 0), Bil.Var (int_param 1))) ],
              [ (1, fun t -> mk_jmp_to t (Bil.Var zf)); (2, mk_goto) ];
              [], [ (0, mk_ret) ];
              [], [ (0, mk_ret) ] ]
        in
        let ssa = ssa_of sub in
        let dce = Hike.Dce.dce_sub ~synth ~target ssa in
        Hike_test.Verify_ssa.sub ~synth ~target ~what:"DCE-02" dce;
        check "DCE-02" (not (removed ssa dce zf) && kept dce zf));
  ]

let () = run "dce" tests
