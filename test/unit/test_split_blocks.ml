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

(* A tiny facts fixture for the post-solve materializer.  The denotation is
   deliberately independent of the expression so the pin exercises the
   bounded-target seam rather than the VSA transfer rules. *)
let materialize_facts ~(program : program term) ~(words : Cbat_vsa.WordSet.t)
    ~(subs : (int64 * tid) list) : Hike.Kb.facts =
  let block_addrs =
    Term.enum sub_t program
    |> Seq.concat_map ~f:(Term.enum blk_t)
    |> Seq.filter_map ~f:(fun blk ->
           Base.Option.map (Term.get_attr blk address) ~f:(fun a ->
               (a, Term.tid blk)))
    |> Seq.to_list
    |> Core.Map.of_alist_exn (module Addr)
  in
  let sub_addrs =
    Base.List.map subs ~f:(fun (a, t) -> (Addr.of_int64 a, t))
    |> Core.Map.of_alist_exn (module Addr)
  in
  let facts =
    Hike.Kb.build ~lookup:(fun a ->
        Base.List.find_map subs ~f:(fun (v, t) ->
            Base.Option.some_if (Int64.equal a v) t))
      ~block_envs:Tid.Map.empty ~block_addrs
      ~target:Theory.Target.unknown
  in
  { facts with
    Hike.Kb.sub_addrs;
    denote = (fun ~blk:_ ?def:_ _ -> Ok words) }

let stamp_sub (sub : sub term) (addresses : (int64 * tid) list) : sub term =
  Term.map blk_t sub ~f:(fun blk ->
      match
        Base.List.find_map addresses ~f:(fun (a, t) ->
            Base.Option.some_if (Tid.equal t (Term.tid blk)) a)
      with
      | Some a -> Term.set_attr blk address (Addr.of_int64 a)
      | None -> blk)

let direct_call_target (j : jmp term) : tid option =
  match Jmp.kind j with
  | Call c -> (match Call.target c with Direct t -> Some t | _ -> None)
  | _ -> None

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

    pin "SBLK-06"
      "a bounded indirect call becomes one direct arm per named sub start"
      (fun () ->
        let target = v64 "sb6_target" in
        let callee_a, callee_a_tids =
          sub_of "sb6_a" [ [], [ (0, mk_ret) ] ]
        in
        let callee_b, callee_b_tids =
          sub_of "sb6_b" [ [], [ (0, mk_ret) ] ]
        in
        let caller, caller_tids =
          sub_of "sb6_caller"
            [ [], [ (1, fun t ->
                        Jmp.create
                          (Call
                             (Call.create ~target:(Indirect (Bil.Var target))
                                ~return:(Direct t) ()))) ];
              [], [ (0, mk_ret) ] ]
        in
        let caller =
          stamp_sub caller [ (0x1000L, caller_tids.(0)); (0x1008L, caller_tids.(1)) ]
        in
        let callee_a = stamp_sub callee_a [ (0x2000L, callee_a_tids.(0)) ] in
        let callee_b = stamp_sub callee_b [ (0x3000L, callee_b_tids.(0)) ] in
        let program = Program.create ~subs:[ caller; callee_a; callee_b ] () in
        let words =
          Cbat_vsa.WordSet.of_list ~width:64 [ w64 0x2000; w64 0x3000 ]
        in
        let facts =
          materialize_facts ~program ~words
            ~subs:[ (0x2000L, Term.tid callee_a); (0x3000L, Term.tid callee_b) ]
        in
        let result = Hike.Split_blocks.materialize ~facts program in
        let caller' =
          Term.find sub_t result (Term.tid caller)
          |> Base.Option.value_exn
        in
        let js = Term.enum blk_t caller' |> Seq.hd_exn |> Term.enum jmp_t
                   |> Seq.to_list
        in
        let targets =
          Base.List.filter_map js ~f:direct_call_target
          |> Base.List.map ~f:Tid.name
          |> Base.List.sort ~compare:String.compare
        in
        check "SBLK-06"
          (targets =
           (Base.List.map [ Term.tid callee_a; Term.tid callee_b ] ~f:Tid.name
            |> Base.List.sort ~compare:String.compare)));

    pin "SBLK-07"
      "a bounded target with no naming-map entry fails loudly"
      (fun () ->
        let target = v64 "sb7_target" in
        let caller, tids =
          sub_of "sb7_caller"
            [ [], [ (1, fun t ->
                        Jmp.create
                          (Call
                             (Call.create ~target:(Indirect (Bil.Var target))
                                ~return:(Direct t) ()))) ];
              [], [ (0, mk_ret) ] ]
        in
        let caller = stamp_sub caller [ (0x1000L, tids.(0)); (0x1008L, tids.(1)) ] in
        let program = Program.create ~subs:[ caller ] () in
        let facts = materialize_facts ~program
            ~words:(Cbat_vsa.WordSet.singleton (w64 0x4000)) ~subs:[] in
        let raised =
          try
            ignore (Hike.Split_blocks.materialize ~facts program);
            false
          with Failure _ -> true
        in
        check "SBLK-07" raised);
  ]

let () = run "split_blocks" tests
