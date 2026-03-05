open Convlir.Decl_parser
open Convlir
open Bap.Std
module Libcmap = Map.Make (String)

let libc_functions : funcdef Libcmap.t =
  parse_header_file "../../../tests/stdio_headers.ll"

let print_libc libc =
  Libcmap.iter
    (fun key (data : Decl_parser.funcdef) ->
      let ret = Gnu64_abi.return_regs data.return in
      let args = Gnu64_abi.arg_regs data.args in
      Stdio.printf "fn %s " key;
      List.iter (fun r -> Stdio.printf " %s " (Var.name r)) args;
      Stdio.printf " -> ";
      List.iter (fun r -> Stdio.printf " %s " (Var.name r)) ret;
      Stdio.printf "\n")
    libc

let () = libc_functions |> print_libc
