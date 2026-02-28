open Bap.Std
module SubSet = Set.Make (Sub)

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
