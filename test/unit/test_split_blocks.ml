(* The split pass's pins: a direct-goto jmp series becomes one block
   per jmp, each piece carrying an explicit Goto to the next; piece 1
   keeps the tid, defs, phis, and attrs; every other multi-jmp shape
   stays whole with one warning. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

let guard v k =
  Bil.BinOp (Bil.EQ, Bil.Var v, Bil.Int (Cbat_word.to_word (w64 k)))

let blocks_of (sub : sub term) : blk term list =
  Term.enum blk_t sub |> Seq.to_list

let tids_of (sub : sub term) : Tid.t list =
  blocks_of sub |> Base.List.map ~f:Term.tid

let goto_target (j : jmp term) : Tid.t =
  match Jmp.kind j with
  | Goto (Direct t) -> t
  | _ -> failwith "goto_target"

let tests : unit Alcotest.test list =
  [




    pin "SBLK-03" "single-jmp and jmp-free blocks pass through untouched"
      (fun () ->
        let flag = v64 "sb3_flag" in
        let sub, _ =
          sub_of "sb3"
            [ [ Def.create flag (Bil.Int (Cbat_word.to_word (w64 0))) ],
              [ (1, fun t -> mk_jmp_to t (guard flag 1)) ];
              [], [ (0, mk_ret) ];
              [], [] ]
        in
        let split = Hike.Split_blocks.split_sub sub in
        check "SBLK-03"
          (tids_of sub = tids_of split
          && Base.List.length (blocks_of split) = 3));

    pin "SBLK-04"
      "an indirect jmp in a 3+-jmp series leaves the block whole, with one warning"
      (fun () ->
        let flag = v64 "sb4_flag" in
        let sub, tids =
          sub_of "sb4"
            [ [ Def.create flag (Bil.Int (Cbat_word.to_word (w64 0))) ],
              [ (1, fun t -> mk_jmp_to t (guard flag 1));
                (1, fun t -> mk_jmp_to t (guard flag 2));
                (2,
                 fun _ ->
                   Jmp.create (Goto (Indirect (Bil.Var (v64 "sb4_tgt"))))) ];
              [], [ (0, mk_ret) ];
              [], [] ]
        in
        let split_holder = ref sub in
        let err =
          capture_stderr (fun () ->
              split_holder := Hike.Split_blocks.split_sub sub)
        in
        check "SBLK-04"
          (contains_substring err "hike: split-blocks:"
          && contains_substring err "sb4"
          && contains_substring err (Tid.name tids.(0))
          && tids_of sub = tids_of !split_holder));
    pin "SBLK-05"
      "a guard var defined in the series block stays out of free_regs after the split"
      (fun () ->
        let x = v64 "sb5_x" in
        let sub, _ =
          sub_of "sb5"
            [ [ Def.create x (Bil.Int (Cbat_word.to_word (w64 7))) ],
              [ (1, fun t -> mk_jmp_to t (guard x 1));
                (2, mk_goto) ];
              [ Def.create (v64 "sb5_y1")
                  (Bil.BinOp
                     (Bil.PLUS, Bil.Var x,
                      Bil.Int (Cbat_word.to_word (w64 1)))) ],
              [ (0, mk_ret) ];
              [ Def.create (v64 "sb5_y2")
                  (Bil.BinOp
                     (Bil.PLUS, Bil.Var x,
                      Bil.Int (Cbat_word.to_word (w64 2)))) ],
              [ (0, mk_ret) ] ]
        in
        let split = Hike.Split_blocks.split_sub sub in
        check "SBLK-05"
          (Base.List.map
             (Hike.Split_blocks.free_regs ~abi:Hike.Abi.x86_64_sysv split)
             ~f:Var.name
           = []));
  ]

let () = run "split_blocks" tests
