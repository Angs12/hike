open Convlir.Decl_parser
module LibcMap = Map.Make (String)

let libc_functions : funcdef LibcMap.t =
  parse_header_file "../../../tests/stdio_headers.ll"

let rec string_of_functype (ft : functype) =
  match ft with
  | Void -> " void "
  | Int n -> Printf.sprintf " int%d " n
  | Float -> Printf.sprintf " float "
  | Double -> Printf.sprintf " double "
  | Half -> Printf.sprintf " half "
  | Bfloat -> Printf.sprintf " bfloat "
  | X86fp80 -> Printf.sprintf " x86_fp80 "
  | FP128 -> Printf.sprintf " fp128 "
  | PPCfp128 -> Printf.sprintf " ppc_fp128 "
  | Pointer -> " ptr "
  | X86amx -> Printf.sprintf " x86_amx "
  | Struct ts ->
      Printf.sprintf " {%s} "
        (Base.List.map ts ~f:string_of_functype |> Base.String.concat ~sep:",")

let () =
  LibcMap.iter
    (fun name def ->
      let arg_list = Base.List.map ~f:string_of_functype def.args in
      Stdio.printf "%s : %s -> %s \n" name
        (Base.List.fold_right arg_list ~init:"" ~f:( ^ ))
        (string_of_functype def.return))
    libc_functions
