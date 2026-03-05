open Bap.Std
module SubSet = Set.Make (Sub)

let text_section proj =
  Project.memory proj |> Memmap.to_sequence
  |> Seq.filter ~f:(fun (_, v) ->
      match Value.get Image.section v with
      | Some name -> String.equal name ".text"
      | None -> false)

(*  Given a function, return a set of functions that are reachable from it. *)
let reachable_funcs prog sub =
  let rec reachable_funcs_aux funcs func_list =
    match func_list with
    | [] -> funcs
    | func :: rest ->
        let funcs = SubSet.add func funcs in
        let func_list =
          Term.enum blk_t func
          |> Seq.fold ~init:rest ~f:(fun unchecked blk ->
              Term.enum jmp_t blk
              |> Seq.fold ~init:unchecked ~f:(fun unchecked jmp ->
                  match Jmp.kind jmp with
                  | Call c -> (
                      match Call.target c with
                      | Indirect _ -> unchecked
                      | Direct tid ->
                          let sub =
                            Base.Option.value_exn (Term.find sub_t prog tid)
                              ~message:"Reachable_funcs: no sub found"
                          in
                          if not (SubSet.mem sub funcs) then sub :: unchecked
                          else unchecked)
                  | _ -> unchecked))
        in
        reachable_funcs_aux funcs func_list
  in
  reachable_funcs_aux SubSet.empty [ sub ]

let text_funcs proj =
  let prog = Project.program proj in
  let sub =
    Term.enum sub_t prog |> Seq.find_exn ~f:(fun sub -> Sub.name sub = "main")
  in
  let reachable = reachable_funcs prog sub in
  let text_mem = text_section proj |> Seq.to_list |> Base.List.hd_exn |> fst in
  let symbols = Project.symbols proj in
  SubSet.fold
    (fun sub acc ->
      let _, first_block, _ =
        Symtab.find_by_name symbols (Sub.name sub)
        |> Base.Option.value_exn ~message:"Reachable_funcs: no symbol found"
      in
      let fn_addr = Block.addr first_block in
      if Memory.contains text_mem fn_addr then sub :: acc else acc)
    reachable []
