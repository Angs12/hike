open Convlir.Decl_parser
open Convlir
open Bap.Std
open Format
module Libcmap = Map.Make (String)

let libc_functions : funcdef Libcmap.t =
  parse_header_file "../../../tests/stdio_headers.ll"

let print_libc libc =
  let module Abi = Cdecl_gnu_abi in
  Libcmap.iter
    (fun key (data : Decl_parser.funcdef) ->
      let ret = Abi.return data.return in
      let args = Abi.args data.args data.return in
      fprintf std_formatter "fn %s " key;
      List.iter (fun (a, _) -> fprintf std_formatter " %a " Exp.pp a) args;
      fprintf std_formatter " -> ";
      List.iter (fun r -> fprintf std_formatter " %a " Var.pp r) ret;
      fprintf std_formatter "\n")
    libc

let () =
  print_endline "Testing cdecl abi for unix systems";
  libc_functions |> print_libc
