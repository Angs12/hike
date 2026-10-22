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
                (2,
                 fun _ ->
                   Jmp.create (Goto (Indirect (Bil.Var (v64 "sb4_tgt")))));
                (1, fun t -> mk_jmp_to t (guard flag 2)) ];
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
