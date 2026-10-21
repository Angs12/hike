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
      ~target:(x86_target ())
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
        let split = Hike.Split_blocks.split_sub ~synth:Hike.Synth.empty ~target:(x86_target ()) sub in
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
              split_holder := Hike.Split_blocks.split_sub ~synth:Hike.Synth.empty ~target:(x86_target ()) sub)
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
        let split = Hike.Split_blocks.split_sub ~synth:Hike.Synth.empty ~target:(x86_target ()) sub in
        let free =
          Hike.Split_blocks.free_regs ~synth:Hike.Synth.empty
            ~abi:Hike.Abi.x86_64_sysv split
          |> Base.List.map ~f:Var.name
        in
        (* The SSA form signs the sub with the ABI's return lanes; the
           ret reads them, so they are the free set.  The guard var the
           series block defines is not among them. *)
        let ret_regs =
          Hike.Abi.x86_64_sysv.Hike.Abi.return_regs |> Base.List.map ~f:Var.name
        in
        check "SBLK-05"
          (not (Base.List.mem free "sb5_x" ~equal:String.equal)
          && Base.List.sort ~compare:String.compare free
             = Base.List.sort ~compare:String.compare ret_regs));

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
        let _, result = Hike.Split_blocks.materialize ~facts program in
        let caller' =
          Term.find sub_t result (Term.tid caller)
          |> Base.Option.value_exn
        in
        let calls =
          Term.enum blk_t caller'
          |> Seq.concat_map ~f:(Term.enum jmp_t)
          |> Seq.filter_map ~f:(fun j ->
                 if Hike.Ssa.is_call_jmp j then direct_call_target j else None)
          |> Seq.to_list
        in
        let targets =
          Base.List.map calls ~f:Tid.name
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

    pin "SBLK-08"
      "an in-sub word the arming phase did not arm is armed as a case, not a failure"
      (fun () ->
        let target = v64 "sb8_target" in
        let sub, tids =
          sub_of "sb8"
            [ [], [ (1, fun _ -> Jmp.create (Goto (Indirect (Bil.Var target)))) ];
              [], [ (0, mk_ret) ] ]
        in
        let sub = stamp_sub sub [ (0x1000L, tids.(0)); (0x1008L, tids.(1)) ] in
        let program = Program.create ~subs:[ sub ] () in
        let facts =
          materialize_facts ~program
            ~words:(Cbat_vsa.WordSet.singleton (w64 0x1008)) ~subs:[]
        in
        let _, result = Hike.Split_blocks.materialize ~facts program in
        let sub' = Term.find sub_t result (Term.tid sub) |> Base.Option.value_exn in
        let gotos =
          Term.enum blk_t sub' |> Seq.concat_map ~f:(Term.enum jmp_t)
          |> Seq.filter_map ~f:(fun j ->
                 match Jmp.kind j with
                 | Goto (Direct t) -> Some (Tid.name t)
                 | _ -> None)
          |> Seq.to_list
        in
        check "SBLK-08"
          (Base.List.mem gotos (Tid.name tids.(1)) ~equal:String.equal));
    pin "SBLK-09"
      "splitting an SSA call-and-goto block keeps boundary versions and emission valid"
      (fun () ->
        let x = v64 "sb9_x" and g = v64 "sb9_g" in
        let input = int_param 1 in
        let ret = int_ret 0 and arg = int_param 0 in
        let callee, _ = raw_sub_of "@sb9_callee" [ [], [ (0, mk_ret) ] ] in
        let callee =
          Term.append arg_t callee (Arg.create ~intent:Out ret (Var ret))
          |> fun s -> Term.append arg_t s
               (Arg.create ~intent:In arg (Var arg))
        in
        let word k = Bil.Int (Cbat_word.to_word (w64 k)) in
        let caller, _ =
          raw_sub_of "sb9"
            [ [ Def.create x (word 0); Def.create g (word 0);
                Def.create arg (Bil.Var input) ],
              [ (2, fun t -> mk_jmp_to t (guard g 1));
                (2, fun t ->
                    Jmp.create ~cond:(guard g 2)
                      (Call
                         (Call.create ~return:(Direct t)
                            ~target:(Direct (Term.tid callee)) ())));
                (1, mk_goto) ];
              [ Def.create x (word 1) ], [ (2, mk_goto) ];
              [ Def.create (v64 "sb9_y")
                  (Bil.BinOp (Bil.PLUS, Bil.Var x, word 1)) ],
              [ (0, mk_ret) ] ]
        in
        let prog = Program.create ~subs:[ callee; caller ] () in
        let prog =
          Hike.Ssa.ssa_program ~synth:Hike.Synth.empty ~target:(x86_target ()) prog
          |> Hike.Types.sign_program ~synth:Hike.Synth.empty ~target:(x86_target ())
        in
        let find p = Term.enum sub_t p
                     |> Seq.find ~f:(fun s -> String.equal (Sub.name s) "sb9")
                     |> Base.Option.value_exn in
        let before = find prog in
        let after = Hike.Split_blocks.split_sub ~synth:Hike.Synth.empty ~target:(x86_target ()) before in
        let graph = Sub.to_graph after in
        let preds tid =
          Graphs.Tid.Node.preds tid graph |> Seq.to_list
          |> Base.List.filter ~f:(fun t -> Option.is_some (Term.find blk_t after t))
          |> Base.List.sort ~compare:Tid.compare
        in
        let phis_ok =
          Seq.for_all (Term.enum blk_t after) ~f:(fun b ->
              Seq.for_all (Term.enum phi_t b) ~f:(fun phi ->
                  let srcs =
                    Phi.values phi |> Seq.map ~f:fst |> Seq.to_list
                    |> Base.List.sort ~compare:Tid.compare
                  in
                  srcs = preds (Term.tid b)))
        in
        let lhs =
          Term.enum blk_t after
          |> Seq.concat_map ~f:(fun b ->
                 Seq.append (Term.enum phi_t b |> Seq.map ~f:Phi.lhs)
                   (Term.enum def_t b |> Seq.map ~f:Def.lhs))
          |> Seq.filter ~f:(fun v -> Var.index v > 0)
          |> Seq.to_list
        in
        let call_blks =
          Term.enum blk_t after
          |> Seq.filter ~f:(fun b ->
                 Seq.exists (Term.enum jmp_t b) ~f:(fun j ->
                     match Jmp.kind j with
                     | Call c -> Call.return c <> None
                     | _ -> false))
          |> Seq.to_list
        in
        let versions_on_call =
          match call_blks with
          | [ b ] ->
            let j = Term.first jmp_t b |> Base.Option.value_exn in
            let effects = Hike.Stack_model.effects j in
            Term.has_attr b Hike.Stack_model.ssa_tag
            && not (Base.List.is_empty effects.writes)
            && Base.List.for_all effects.reads ~f:(fun v ->
                 Option.equal Var.equal
                   (Hike.Stack_model.boundary_read b v) (Some v))
            && Base.List.for_all effects.writes ~f:(fun v ->
                 Option.equal Var.equal
                   (Hike.Stack_model.boundary_write b v) (Some v))
          | _ -> false
        in
        check "SBLK-09 split"
          (Base.List.length (blocks_of after) > Base.List.length (blocks_of before));
        check "SBLK-09 one incoming per predecessor" phis_ok;
        check "SBLK-09 single definitions"
          (Base.List.length lhs
           = Base.List.length (Base.List.dedup_and_sort lhs ~compare:Var.compare));
        check "SBLK-09 versions travel with the call" versions_on_call;
        (* The emitter's pipeline constructs the SSA form itself, so the
           emission runs over the pre-SSA program: the pipeline's own
           split, the one the terms above describe. *)
        let ir =
          emit_ir_spec ~synth:Hike.Synth.empty
            empty_spec [ callee; caller ]
        in
        (* The IR's blocks: a label line opens one. *)
        let lines = Core.String.split_lines ir in
        let blocks =
          List.fold_left
            (fun acc l ->
              if String.length l > 1 && l.[0] = '"' then [ l ] :: acc
              else
                match acc with
                | [] -> []
                | b :: rest -> (b @ [ l ]) :: rest)
            [] lines
          |> List.rev
        in
        let call_block =
          Base.List.find blocks ~f:(fun b ->
              Base.List.exists b ~f:(fun l -> contains_substring l " = call "))
          |> Base.Option.value_exn
        in
        (* The phis the call's own block defines: the versions the split
           carried to it. *)
        let phi_names =
          Base.List.filter_map call_block ~f:(fun l ->
            match String.split_on_char ' ' (String.trim l) with
            | name :: "=" :: "phi" :: _ -> Some name
            | _ -> None)
        in
        (* A rendered local: %<digits>.  The call's arguments are the
           block's phi values and the values the block's own defs
           produced (the register names). *)
        let is_local (s : string) =
          let n = String.length s in
          n > 1 && s.[0] = '%'
          && (let ok = ref true in
              for i = 1 to n - 1 do
                if not (s.[i] >= '0' && s.[i] <= '9') then ok := false
              done;
              !ok)
        in
        let call_line =
          Base.List.find call_block ~f:(fun l -> contains_substring l " = call ")
          |> Base.Option.value_exn
        in
        let args_text =
          let n = String.length call_line in
          let rec from i =
            if i < 0 then ""
            else if call_line.[i] = '(' then String.sub call_line i (n - i)
            else from (i - 1)
          in
          let t = from (n - 1) in
          let m = String.length t in
          if m > 0 && t.[m - 1] = ')' then String.sub t 0 (m - 1) else t
        in
        let call_args =
          String.split_on_char ',' args_text
          |> Base.List.filter_map ~f:(fun a ->
                 match String.split_on_char ' ' (String.trim a) with
                 | _ :: v :: _ when is_local v -> Some v
                 | _ -> None)
        in
        check "SBLK-09 emitted call reads the call piece's versions"
          ((Base.List.length call_args > 0
           && Base.List.for_all call_args ~f:(fun v ->
                  Base.List.mem phi_names v ~equal:String.equal))
          && not (contains_substring ir "undef"));
        (* The input lane's value is the one the call piece holds before
           the call: the copy the fixture moves it into. *)
        check "SBLK-09 emitted call reads the input lane's pre-call value"
          (contains_substring call_line ("i64 %" ^ Var.name input)));
  ]

let () = run "split_blocks" tests
