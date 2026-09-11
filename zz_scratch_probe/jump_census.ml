(* T13 lane census: how many jcc flag idioms the jump compiler compiles,
   per family, and what stays residual (each residual idiom cond printed
   with its binary + sub for cross-reference against bir_dump).
   Usage:
     jump_census.exe <binary> [<binary> ...] *)

open Bap.Std
open Probe_common

let () =
  init ();
  if Array.length Sys.argv < 2 then (
    print_endline "usage: jump_census.exe <binary>...";
    exit 0);
  let compiled = Base.Hashtbl.create (module Base.String) in
  let residual = Base.Hashtbl.create (module Base.String) in
  let non_flag = ref 0 in
  let uncond = ref 0 in
  let label ~bin ~sub ~was_compiled cond =
    let pp_cond = Format.asprintf "%a" Exp.pp cond in
    match Hike.Jump.family_of_cond cond with
    | Some f ->
        let n = Base.Hashtbl.find compiled f |> Option.value ~default:0 in
        Base.Hashtbl.set compiled ~key:f ~data:(n + 1);
        if not was_compiled then begin
          let r = Base.Hashtbl.find residual f |> Option.value ~default:0 in
          Base.Hashtbl.set residual ~key:f ~data:(r + 1);
          Printf.printf "  residual %s: %s :: %s :: %s\n" f bin sub pp_cond
        end
    | None ->
        if Exp.equal cond (Bil.Int (Word.one 1)) then incr uncond
        else begin
          incr non_flag;
          Printf.printf "  non-idiom: %s :: %s :: %s\n" bin sub pp_cond
        end
  in
  for i = 1 to Array.length Sys.argv - 1 do
    let path = Sys.argv.(i) in
    let bin = Filename.basename path in
    let proj = load_project path in
    let prog = Project.program proj in
    Term.enum sub_t prog |> Seq.iter ~f:(fun s ->
        let sub = Sub.name s in
        let s' = Hike.Jump.compile_sub s in
        let conds s =
          Term.enum blk_t s
          |> Seq.concat_map ~f:(fun b -> Term.enum jmp_t b |> Seq.map ~f:Jmp.cond)
          |> Seq.to_list
        in
        let before = conds s in
        let after = conds s' in
        if Base.List.length before = Base.List.length after then
          ( match Base.List.iter2 before after ~f:(fun b a ->
                label ~bin ~sub ~was_compiled:(not (Exp.equal b a)) b) with
          | Ok () -> ()
          | Unequal_lengths -> () ))
  done;
  Printf.printf "== census: per family (compiled / residual)\n";
  Base.Hashtbl.iteri compiled ~f:(fun ~key ~data ->
      let r = Base.Hashtbl.find residual key |> Option.value ~default:0 in
      Printf.printf "  %s: %d compiled / %d residual\n" key (data - r) r);
  Printf.printf "== residual: non-idiom conds (already value comparisons etc.): %d\n"
    !non_flag;
  Printf.printf "== unconditional (cond = 1): %d\n" !uncond
