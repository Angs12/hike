(* Decode pins: one function's body from BAP's decoded state.  Each pin
   builds its own binary fixture (code at 0x400078). *)

open Bap.Std
open Hike_test.Harness

module D = Hike.Decode

let addr = Addr.of_int64
let file_of project = D.file_of (Project.program project)

(* The decoded state and one function's candidate graph and entry block. *)
let candidate ?is_entry project entry =
  let state = (D.initial project).grown in
  let is_entry =
    Base.Option.value is_entry ~default:(Disasm.Driver.is_subroutine state) in
  let cfg = D.function_cfg ~file:(file_of project) state ~entry ~is_entry in
  let entry_blk =
    Graphs.Cfg.nodes cfg
    |> Seq.find ~f:(fun b -> Addr.equal (Block.addr b) entry)
    |> Base.Option.value_exn in
  (state, cfg, entry_blk)

let starts cfg =
  Graphs.Cfg.nodes cfg |> Seq.map ~f:(fun b -> Word.to_int64_exn (Block.addr b))
  |> Seq.to_list |> List.sort compare

let calls_of sub =
  Term.enum blk_t sub |> Seq.concat_map ~f:(Term.enum jmp_t)
  |> Seq.filter_map ~f:(fun j -> match Jmp.kind j with Call c -> Some c | _ -> None)
  |> Seq.to_list

(* call g; ret; g: ret *)
let call_ret = "\xe8\x01\x00\x00\x00\xc3\xc3"

let tests = [
  pin "DEC-01" "a function's candidate graph stops at another entry and names its calls"
    (fun () ->
      with_binary call_ret (fun project ->
          let state, cfg, _ = candidate project (addr 0x400078L) in
          check "DEC-01.blocks" (starts cfg = [ 0x400078L; 0x40007dL ]);
          check "DEC-01.calls"
            (match D.calls state cfg with
             | [ (b, [ g ]) ] ->
               Word.to_int64_exn (Block.addr b) = 0x400078L
               && Word.to_int64_exn g = 0x40007eL
             | _ -> false)));

  pin "DEC-02" "a call's fallthrough stays only when the callee may return"
    (fun () ->
      with_binary call_ret (fun project ->
          let state, cfg, entry = candidate project (addr 0x400078L) in
          let lift keep =
            D.trim state cfg ~entry ~keep_fall:(fun _ -> keep)
            |> D.lift ~file:(file_of project) ~tid:(Tid.create ()) ~name:"f" entry in
          let returning = lift true and noreturn = lift false in
          check "DEC-02.returning.blocks" (Term.length blk_t returning = 2);
          check "DEC-02.returning.call"
            (List.for_all (fun c -> Call.return c <> None) (calls_of returning));
          check "DEC-02.noreturn.blocks" (Term.length blk_t noreturn = 1);
          check "DEC-02.noreturn.call"
            (match calls_of noreturn with
             | [ c ] -> Call.return c = None
             | _ -> false);
          check "DEC-02.named" (Sub.name noreturn = "f"
                                && Term.get_attr noreturn address = Some (addr 0x400078L))));

  pin "DEC-03" "a jump into another entry leaves the body"
    (fun () ->
      (* jmp g; g: ret *)
      with_binary "\xe9\x00\x00\x00\x00\xc3" (fun project ->
          let g = addr 0x40007dL in
          let _, cfg, _ =
            candidate ~is_entry:(Addr.equal g) project (addr 0x400078L) in
          check "DEC-03" (starts cfg = [ 0x400078L ])));
]

let () = run "decode" tests
