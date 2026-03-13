open Str

type ctype =
  | Void | Char | Short | Int | Long | LongLong | Float | Double | LongDouble
  | Pointer of ctype
  | Struct of string option * ctype list
  | Union of string option * ctype list
  | Enum of string option
  | Typedef of string

let typedef_env : (string, ctype) Hashtbl.t = Hashtbl.create 256

let resolve_typedef t =
  let rec resolve = function
    | Typedef name -> (try resolve (Hashtbl.find typedef_env name) with Not_found -> Typedef name)
    | Pointer inner -> Pointer (resolve inner)
    | t -> t
  in resolve t

let rec parse_type s =
  let s = String.trim s in
  let len = String.length s in
  match s with
  | "" -> Typedef s
  | "void" -> Void | "char" -> Char | "short" -> Short | "int" -> Int
  | "long" -> Long | "float" -> Float | "double" -> Double
  | "const" -> Int
  | _ when len > 0 && s.[len-1] = '*' -> Pointer (parse_type (String.sub s 0 (len - 1)))
  | _ when string_match (regexp "^const ") s 0 -> parse_type (String.sub s 6 (len - 6))
  | _ when string_match (regexp "^struct ") s 0 ->
      let rest = String.sub s 7 (len - 7) in
      let name = if rest = "" then None else Some rest in
      Struct (name, [])
  | _ when string_match (regexp "^union ") s 0 ->
      let rest = String.sub s 6 (len - 6) in
      let name = if rest = "" then None else Some rest in
      Union (name, [])
  | _ when string_match (regexp "^enum ") s 0 ->
      let rest = String.sub s 5 (len - 5) in
      let name = if rest = "" then None else Some rest in
      Enum name
  | _ when string_match (regexp "^unsigned ") s 0 ->
      (match String.trim (String.sub s 8 (len - 8)) with
       | "char" -> Char | "short" -> Short | "int" -> Int | "long" -> Long | "longlong" -> LongLong
       | x -> Typedef ("unsigned " ^ x))
  | _ when string_match (regexp "^signed ") s 0 ->
      (match String.trim (String.sub s 7 (len - 7)) with
       | "char" -> Char | "short" -> Short | "int" -> Int | "long" -> Long | "longlong" -> LongLong
       | x -> Typedef ("signed " ^ x))
  | _ -> Typedef s

let ctype_to_string = function
  | Void -> "void" | Char -> "char" | Short -> "short" | Int -> "int"
  | Long -> "long" | LongLong -> "longlong" | Float -> "float" | Double -> "double"
  | LongDouble -> "longdouble" | Pointer _ -> "ptr"
  | Struct (Some n, _) -> "struct<<" ^ n ^ ">>" | Struct (None, _) -> "struct<<anonymous>>"
  | Union (Some n, _) -> "union<<" ^ n ^ ">>" | Union (None, _) -> "union<<anonymous>>"
  | Enum (Some n) -> "enum<<" ^ n ^ ">>" | Enum None -> "enum<<anonymous>>"
  | Typedef n -> n

let json_escape s =
  let b = Buffer.create (String.length s) in
  String.iter (fun c ->
    match c with
    | '"' -> Buffer.add_string b "\\\""
    | '\\' -> Buffer.add_string b "\\\\"
    | '\n' -> Buffer.add_string b "\\n"
    | '\r' -> Buffer.add_string b "\\r"
    | '\t' -> Buffer.add_string b "\\t"
    | _ -> Buffer.add_char b c
  ) s;
  Buffer.contents b

let rindex s c =
  let rec f i = if i < 0 then None else if s.[i] = c then Some i else f (i - 1) in
  f (String.length s - 1)

let read_file f =
  let ic = open_in f in
  let rec aux acc = try aux (input_line ic :: acc) with End_of_file -> close_in ic; List.rev acc in
  aux []

let is_header_file f = String.length f > 2 && String.sub f (String.length f - 2) 2 = ".h"

let get_all_headers d =
  Array.to_list (Sys.readdir d)
  |> List.filter is_header_file
  |> List.map (Filename.concat d)

let re_typedef = regexp "^typedef[ \t]+.+[ \t]+([a-zA-Z_][a-zA-Z0-9_]*)[ \t]*;$"
let re_typedef_unsigned = regexp "^typedef[ \t]+unsigned[ \t]+[a-zA-Z_][a-zA-Z0-9_]*[ \t]+([a-zA-Z_][a-zA-Z0-9_]*)[ \t]*;$"
let re_function = regexp ".*([^)]*);$"
let re_typedef_struct = regexp "^typedef?[ \t]+struct[ \t]+([a-zA-Z_][a-zA-Z0-9_]*)[ \t]*;$"
let re_typedef_struct_body = regexp "^typedef[ \t]+struct.*{"
let re_struct_fwd = regexp "^struct[ \t]+[a-zA-Z_][a-zA-Z0-9_]*[ \t]*;$"
let re_enum_fwd = regexp "^enum[ \t]+[a-zA-Z_][a-zA-Z0-9_]*[ \t]*;$"
let re_union_fwd = regexp "^union[ \t]+[a-zA-Z_][a-zA-Z0-9_]*[ \t]*;$"
let re_struct_body = regexp "struct"
let re_identifier = regexp "[a-zA-Z_][a-zA-Z0-9_]*$"

let parse_typedef line =
  let line = String.trim line in
  if string_match re_typedef line 0 then
    try Some (matched_group 1 line, parse_type (matched_group 1 line)) with _ -> None
  else if string_match re_typedef_unsigned line 0 then
    try Some (matched_group 1 line, Typedef ("unsigned " ^ matched_group 1 line)) with _ -> None
  else None

let collect_typedefs_from_file f =
  try
    read_file f
    |> List.fold_left (fun acc line ->
        try
          match parse_typedef (String.trim line) with
          | Some (name, ctype) -> (name, ctype) :: acc
          | None -> acc
        with _ -> acc) []
  with _ -> []

let add_standard_typedefs () =
  List.iter (fun (n, t) -> Hashtbl.add typedef_env n t)
    [("uintptr_t", Pointer Void); ("size_t", Long); ("ssize_t", Long);
     ("intptr_t", Pointer Void); ("ptrdiff_t", Long)]

let collect_all_typedefs dir =
  get_all_headers dir
  |> List.iter (fun f ->
      List.iter (fun (n, t) -> Hashtbl.add typedef_env n t)
        (collect_typedefs_from_file f))

let setup_typedefs () =
  add_standard_typedefs ();
  collect_all_typedefs "/usr/include"

type func_decl = Func of string * ctype * ctype list

type declaration =
  | Function of string * ctype * ctype list
  | Variable of string * ctype
  | StructDef of string * (string * ctype) list
  | UnionDef of string * (string * ctype) list
  | EnumDef of string * (string * int) list
  | Typedef of string * ctype

let re_arg_type = regexp "^[ \t]*[^ \t*]+[ \t]*\\*[ \t]*"

let parse_function_decl line =
  if not (string_match re_function line 0) then None
  else
    let decl = matched_string line in
    match rindex decl '(', rindex decl ')' with
    | Some i, Some j ->
        let ret_and_name = String.sub decl 0 i |> String.trim in
        let args_str = String.sub decl (i + 1) (j - i - 1) |> String.trim in
        let args = if args_str = "" || args_str = "void" then []
          else split (regexp "[ \t]*,[ \t]*") args_str
               |> List.map (fun s ->
                    let arg = String.trim s in
                    let arg_type = 
                      if string_match re_arg_type arg 0 then
                        String.trim (matched_string arg)
                      else
                        arg
                    in
                    resolve_typedef (parse_type arg_type)) in
        (match rindex ret_and_name ' ' with
         | Some k ->
             let name = String.sub ret_and_name (k + 1) (String.length ret_and_name - k - 1) |> String.trim in
             let ret = String.sub ret_and_name 0 k |> String.trim |> parse_type |> resolve_typedef in
             Some (Func (name, ret, args))
         | None -> None)
    | _ -> None

let get_struct_name line prefix =
  let name = String.sub line (String.length prefix) (String.length line - String.length prefix - 1) |> String.trim in
  if name = "" then None else Some name

let parse_struct_def line =
  let line = String.trim line in
  if string_match re_typedef_struct line 0 then
    Some (StructDef (matched_group 1 line, []))
  else if string_match re_typedef_struct_body line 0 then
    (match rindex line '}' with
     | Some i ->
         let after = String.sub line (i + 1) (String.length line - i - 1) |> String.trim in
         let name = try
           let idx = String.index after ';' in
           String.sub after 0 idx |> String.trim
         with _ -> after
         in
         if name <> "" then Some (StructDef (name, [])) else None
     | None -> None)
  else if string_match re_struct_fwd line 0 then
    (match get_struct_name line "struct" with Some n -> Some (StructDef (n, [])) | None -> None)
  else if string_match re_enum_fwd line 0 then
    (match get_struct_name line "enum" with Some n -> Some (EnumDef (n, [])) | None -> None)
  else if string_match re_union_fwd line 0 then
    (match get_struct_name line "union" with Some n -> Some (UnionDef (n, [])) | None -> None)
  else if string_match re_struct_body line 0 then
    (try
      let name_before = match rindex line '{' with
        | Some i ->
            let b = String.sub line 0 i |> String.trim in
            (try ignore (search_forward re_identifier b 0);
             let n = matched_string b in
             if n = "struct" || n = "typedef" then None else Some n
            with _ -> None)
        | None -> None in
      let name_after = match rindex line '}' with
        | Some i ->
            let r = String.sub line (i + 1) (String.length line - i - 1) |> String.trim in
            let r = if r <> "" && r.[0] = ';' then String.sub r 1 (String.length r - 1) |> String.trim else r in
            (try ignore (search_forward re_identifier r 0); Some (matched_string r) with _ -> None)
        | None -> None in
      match name_before with
      | Some n -> Some (StructDef (n, []))
      | None -> (match name_after with Some n -> Some (StructDef (n, [])) | None -> None)
    with _ -> None)
  else None

let parse_line l =
  let l = String.trim l in
  if l = "" then []
  else match parse_struct_def l with
    | Some d -> [d]
    | None -> (match parse_function_decl l with
      | Some (Func (n, r, a)) -> [Function (n, r, a)]
      | None -> [])

let decl_to_json = function
  | Function (n, r, a) -> Printf.sprintf "{\"type\":\"function\",\"name\":\"%s\",\"return\":\"%s\",\"args\":[%s]}" (json_escape n) (json_escape (ctype_to_string r)) (String.concat ", " (List.map (fun x -> "\"" ^ json_escape (ctype_to_string x) ^ "\"") a))
  | Variable (n, t) -> Printf.sprintf "{\"type\":\"variable\",\"name\":\"%s\",\"ctype\":\"%s\"}" (json_escape n) (json_escape (ctype_to_string t))
  | StructDef (n, _) -> Printf.sprintf "{\"type\":\"struct\",\"name\":\"%s\"}" (json_escape n)
  | UnionDef (n, _) -> Printf.sprintf "{\"type\":\"union\",\"name\":\"%s\"}" (json_escape n)
  | EnumDef (n, _) -> Printf.sprintf "{\"type\":\"enum\",\"name\":\"%s\"}" (json_escape n)
  | Typedef (n, t) -> Printf.sprintf "{\"type\":\"typedef\",\"name\":\"%s\",\"ctype\":\"%s\"}" (json_escape n) (json_escape (ctype_to_string t))

let process_headers dir =
  add_standard_typedefs ();
  collect_all_typedefs dir;
  get_all_headers dir
  |> List.map (fun f -> List.map parse_line (read_file f) |> List.concat)
  |> List.concat
  |> List.map decl_to_json
  |> String.concat ",\n"
  |> (fun j -> "[" ^ j ^ "]")
  |> fun json -> let oc = open_out "headers_output.json" in output_string oc json; close_out oc;
  print_endline "Parsed headers and wrote to headers_output.json"
