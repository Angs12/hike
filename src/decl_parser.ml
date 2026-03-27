module LibcMap = Map.Make (String)

type functype =
  | Void
  | Pointer
  | Int of int
  | Half
  | Bfloat
  | Float
  | Double
  | FP128
  | X86fp80
  | PPCfp128
  | X86amx
  | Struct of functype list

type funcdef = { return : functype; args : functype list }
type libcmap = funcdef Map.Make(String).t

let rec functype_to_lltype llvm_ctx functype =
  match functype with
  | Void -> Llvm.void_type llvm_ctx
  | Pointer -> Llvm.pointer_type llvm_ctx
  | Int n -> Llvm.integer_type llvm_ctx n
  | Half -> Llvm.float_type llvm_ctx (*TODO: half type *)
  | Bfloat -> Llvm.float_type llvm_ctx (*TODO: bfloat type *)
  | Float -> Llvm.float_type llvm_ctx
  | Double -> Llvm.double_type llvm_ctx
  | FP128 -> Llvm.fp128_type llvm_ctx
  | X86fp80 -> Llvm.x86fp80_type llvm_ctx
  | PPCfp128 -> Llvm.ppc_fp128_type llvm_ctx
  | X86amx -> Llvm.x86_mmx_type llvm_ctx
  | Struct types ->
      let lltys = Base.List.map types ~f:(functype_to_lltype llvm_ctx) in
      Llvm.struct_type llvm_ctx (Base.List.to_array lltys)

open Core

let rec ll_type_to_functype (s : string) : functype =
  match s with
  | "void" -> Void
  | "ptr" -> Pointer
  | t ->
      if String.length t >= 4 && String.is_prefix ~prefix:"ptr " t then Pointer
      else if String.length t > 0 && Char.equal (String.get t 0) 'i' then
        Int (int_of_string (String.sub t ~pos:1 ~len:(String.length t - 1)))
      else if String.length t > 0 && Char.equal (String.get t 0) '{' then
        let inner = String.sub t ~pos:1 ~len:(String.length t - 2) in
        let types = String.split inner ~on:',' |> List.map ~f:String.strip in
        Struct (List.map types ~f:ll_type_to_functype)
      else Void

let extract_arg_type (s : string) : string =
  match
    String.split s ~on:' ' |> List.filter ~f:(fun x -> not (String.is_empty x))
  with
  | x :: _ -> x
  | [] -> "ptr"

let parse_decl (line : string) : (string * funcdef) option =
  if not (String.is_prefix ~prefix:"declare" line) then None
  else
    match (String.index line '@', String.rindex line ')') with
    | Some name_start, Some paren_end -> (
        try
          let name_start = name_start + 1 in
          let name_end =
            Option.value_exn (String.index_from line name_start '(')
          in
          let paren_start =
            Option.value_exn (String.index_from line name_end '(')
          in
          let name =
            String.sub line ~pos:name_start ~len:(name_end - name_start)
          in
          let ret_end = name_start - 1 in
          let ret_type =
            String.sub line ~pos:7 ~len:(ret_end - 7) |> String.strip
          in
          let args_str =
            String.sub line ~pos:(paren_start + 1)
              ~len:(paren_end - paren_start - 1)
          in
          let args =
            if String.is_empty args_str then []
            else
              String.split args_str ~on:','
              |> List.map ~f:String.strip
              |> List.map ~f:extract_arg_type
          in
          Some
            ( name,
              {
                return = ll_type_to_functype ret_type;
                args = List.map args ~f:ll_type_to_functype;
              } )
        with _ -> None)
    | _ -> None

let parse_header_file (filename : string) : libcmap =
  let lines = In_channel.read_lines filename in
  let decls = List.filter_map lines ~f:parse_decl in
  List.fold decls ~init:LibcMap.empty ~f:(fun map (name, def) ->
      LibcMap.add name def map)
