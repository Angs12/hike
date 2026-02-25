open Core_kernel
open Poly
open Bap.Std
include Self ()

(* let jumps (blk : blk term) = *)
(*   Term.enum jmp_t blk *)
(*   |> Seq.find_map ~f:(fun j -> *)
(*          Option.some_if *)
(*            (match Jmp.kind j with *)
(*            | Call c -> not (Call.return c = None) *)
(*            | _ -> false) *)
(*            j) *)

(* let func_calls (func : sub term) = *)
(*   Term.enum blk_t func *)
(*   |> Seq.find_map ~f:(fun b -> *)
(*          Option.some_if (match jumps b with None -> false | Some _ -> true) b) *)

(* let is_leaf func = *)
(*   let calls = func_calls func in *)
(*   match calls with None -> Ok func | Some _ -> Error "Function is not leaf" *)

let find_sub prog ~func =
  Term.enum sub_t prog
  |> Seq.find ~f:(fun s -> Sub.name s = func)
  |> Result.of_option ~error:"Could not find function"

let find_leaf proj ~func = find_sub (Project.program proj) ~func
