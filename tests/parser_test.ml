open Base
open Convlir.Decl_parser

let libc_functions : funcdef LibcMap.t =
  parse_file "../../../tests/stdio_headers.ll"

let string_of_functype (ft : functype) : string =
  match ft with
  | Void -> " void "
  | Int n -> Printf.sprintf " int%d " n
  | Float n -> Printf.sprintf " float%d " n
  | Pointer -> " ptr "
  | Struct n -> Printf.sprintf " struct%d " n

let () =
  LibcMap.iteri libc_functions ~f:(fun ~key:name ~data:def ->
      let arg_list = List.map ~f:string_of_functype def.args in
      Stdio.printf "%s : %s -> %s \n" name
        (List.fold_right arg_list ~init:"" ~f:( ^ ))
        (string_of_functype def.return))
