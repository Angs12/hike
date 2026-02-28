open Core
module LibcMap = Map.Make (String)

type functype = Void | Int of int | Float of int | Pointer | Struct of int
type funcdef = { return : functype; args : functype list }

let type_size (s : string) : int =
  match s with
  | "void" -> 0
  | "ptr" -> 64
  | "float" -> 32
  | "double" -> 64
  | "half" -> 16
  | "bfloat" -> 16
  | t ->
      if String.length t > 0 && Char.equal (String.get t 0) 'i' then
        int_of_string (String.sub t ~pos:1 ~len:(String.length t - 1))
      else 0

let ll_type_to_functype (s : string) : functype =
  match s with
  | "void" -> Void
  | "ptr" -> Pointer
  | "float" -> Float 32
  | "double" -> Float 64
  | "half" -> Float 16
  | "bfloat" -> Float 16
  | t ->
      if String.length t > 0 && Char.equal (String.get t 0) 'i' then
        Int (int_of_string (String.sub t ~pos:1 ~len:(String.length t - 1)))
      else if String.length t > 0 && Char.equal (String.get t 0) '{' then
        let inner = String.sub t ~pos:1 ~len:(String.length t - 2) in
        let types = String.split inner ~on:',' |> List.map ~f:String.strip in
        let total_size =
          List.fold types ~init:0 ~f:(fun acc x -> acc + type_size x)
        in
        Struct total_size
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
    match
      (String.index line '@', String.index line '(', String.rindex line ')')
    with
    | Some name_start, Some paren_start, Some paren_end -> (
        try
          let name_start = name_start + 1 in
          let name_end =
            Option.value_exn (String.index_from line name_start '(')
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

let parse_file (filename : string) : funcdef LibcMap.t =
  let lines = In_channel.read_lines filename in
  let decls = List.filter_map lines ~f:parse_decl in
  let map_ref = ref LibcMap.empty in
  List.iter decls ~f:(fun (name, def) ->
      map_ref := Map.set !map_ref ~key:name ~data:def);
  !map_ref
