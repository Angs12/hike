(* The split pass's pins: a direct-goto jmp series becomes one block
   per jmp, the pieces consecutive in term order; piece 1 keeps the
   tid, defs, phis, and attrs; every other multi-jmp shape stays whole
   with one warning. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

let guard v k =
  Bil.BinOp (Bil.EQ, Bil.Var v, Bil.Int (Cbat_word.to_word (w64 k)))

let blocks_of (sub : sub term) : blk term list =
  Term.enum blk_t sub |> Seq.to_list

let jmps_of (b : blk term) : jmp term list =
  Term.enum jmp_t b |> Seq.to_list

let tids_of (sub : sub term) : Tid.t list =
  blocks_of sub |> Base.List.map ~f:Term.tid

let goto_target (j : jmp term) : Tid.t =
  match Jmp.kind j with
  | Goto (Direct t) -> t
  | _ -> failwith "goto_target"

let sb_of (name : string) (blks : blk term list) : sub term =
  let b = Sub.Builder.create ~name () in
  Base.List.iter blks ~f:(Sub.Builder.add_blk b);
  Sub.Builder.result b

(* A def+phi+jmps block with the address attr, built by hand so the
   phi rides it. *)
let series_blk ~(defs : def term list) ~(phis : phi term list)
    (jmps : jmp term list) : blk term =
  let b = Blk.Builder.create () in
  Base.List.iter defs ~f:(Blk.Builder.add_def b);
  Base.List.iter phis ~f:(Blk.Builder.add_phi b);
  Base.List.iter jmps ~f:(Blk.Builder.add_jmp b);
  let blk = Blk.Builder.result b in
  Term.set_attr blk address (Cbat_word.to_word (w64 0x1234))

let tests : unit Alcotest.test list =
  [
    pin "SBLK-01"
      "a 3-jmp direct-goto series becomes 3 one-jmp pieces, consecutive in term order"
      (fun () ->
        let flag = v64 "sb_flag" in
        let sub, tids =
          sub_of "sb_series"
            [ [ Def.create flag (Bil.Int (Cbat_word.to_word (w64 0))) ],
              [ (1, fun t -> mk_jmp_to t (guard flag 1));
                (2, fun t -> mk_jmp_to t (guard flag 2));
                (3, mk_goto) ];
              [], [ (0, mk_ret) ];
              [], [];
              [], [];
              [], [] ]
        in
        let split = Hike.Split_blocks.split_sub sub in
        let blks = blocks_of split in
        let p1 = Base.List.nth_exn blks 0
        and p2 = Base.List.nth_exn blks 1
        and p3 = Base.List.nth_exn blks 2 in
        check "SBLK-01"
          (Base.List.length blks = 7
          && Base.List.for_all blks ~f:(fun b ->
                 Base.List.length (jmps_of b) <= 1)
          && Tid.equal (Term.tid p1) tids.(0)
          && Tid.equal (goto_target (Base.List.nth_exn (jmps_of p1) 0)) tids.(1)
          && Tid.equal (goto_target (Base.List.nth_exn (jmps_of p2) 0)) tids.(2)
          && Tid.equal (goto_target (Base.List.nth_exn (jmps_of p3) 0)) tids.(3));
        check "SBLK-01"
          (Base.Option.equal Tid.equal
             (Hike.Split_blocks.fallthrough split p1)
             (Some (Term.tid p2))
          && Base.Option.equal Tid.equal
               (Hike.Split_blocks.fallthrough split p2)
               (Some (Term.tid p3))
          && Base.Option.equal Tid.equal
               (Hike.Split_blocks.fallthrough split p3)
               (Some tids.(1))));

    pin "SBLK-02"
      "piece 1 keeps the original tid, defs, phis, and address attr; later pieces are bare"
      (fun () ->
        let flag = v64 "sb2_flag" in
        let t1 = blk_of_defs [] and t2 = blk_of_defs [] in
        let next = blk_of_defs [] in
        let series =
          series_blk
            ~defs:[ Def.create (v64 "sb2_x") (Bil.Int (Cbat_word.to_word (w64 7))) ]
            ~phis:
              [ Phi.of_list (v64 "sb2_p")
                  [ (Term.tid next, Bil.Int (Cbat_word.to_word (w64 0))) ] ]
            [ mk_jmp_to (Term.tid t1) (guard flag 1);
              mk_goto (Term.tid t2) ]
        in
        let sub = sb_of "sb2" [ series; next; t1; t2 ] in
        let split = Hike.Split_blocks.split_sub sub in
        let blks = blocks_of split in
        let p1 = Base.List.nth_exn blks 0 and p2 = Base.List.nth_exn blks 1 in
        check "SBLK-02"
          (Tid.equal (Term.tid p1) (Term.tid series)
          && Base.List.length (jmps_of p1) = 1
          && Base.List.length (Term.enum def_t p1 |> Seq.to_list) = 1
          && Base.List.length (Term.enum phi_t p1 |> Seq.to_list) = 1
          && Base.Option.is_some (Term.get_attr p1 address)
          && Base.List.length (jmps_of p2) = 1
          && Base.List.is_empty (Term.enum def_t p2 |> Seq.to_list)
          && Base.List.is_empty (Term.enum phi_t p2 |> Seq.to_list)
          && Base.Option.is_none (Term.get_attr p2 address)));

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
      "an indirect jmp in the series leaves the block whole, with one warning"
      (fun () ->
        let flag = v64 "sb4_flag" in
        let sub, tids =
          sub_of "sb4"
            [ [ Def.create flag (Bil.Int (Cbat_word.to_word (w64 0))) ],
              [ (1, fun t -> mk_jmp_to t (guard flag 1));
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
          (Base.List.map (Hike.Split_blocks.free_regs split) ~f:Var.name
           = []));
  ]

let () = run "split_blocks" tests
