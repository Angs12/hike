open Convlir.Header_parser

let test_eq name f input expected =
  let result = f input in
  if result = expected then Printf.printf "PASS: %s\n" name
  else
    Printf.printf "FAIL: %s got %s, expected %s\n" name (ctype_to_string result)
      (ctype_to_string expected)

let test_match name f input check =
  match f input with
  | Some x when check x -> Printf.printf "PASS: %s\n" name
  | _ -> Printf.printf "FAIL: %s\n" name

let test_some name f input =
  match f input with
  | Some _ -> Printf.printf "PASS: %s\n" name
  | None -> Printf.printf "FAIL: %s\n" name

let () =
  setup_typedefs ();
  Printf.printf "=== Tests ===\n";

  (* parse_type tests *)
  List.iter
    (fun (s, t) -> test_eq s parse_type s t)
    [
      ("void", Void);
      ("char", Char);
      ("int", Int);
      ("long", Long);
      ("float", Float);
      ("double", Double);
      ("int*", Pointer Int);
      ("char*", Pointer Char);
      ("int**", Pointer (Pointer Int));
      ("const int", Int);
      ("unsigned int", Int);
      ("unsigned long", Long);
      ("signed int", Int);
      ("struct foo", Struct (Some "foo", []));
      ("union baz", Union (Some "baz", []));
      ("enum color", Enum (Some "color"));
    ];

  (* ctype_to_string tests *)
  List.iter
    (fun (t, s) ->
      if ctype_to_string t = s then Printf.printf "PASS\n"
      else Printf.printf "FAIL got %s\n" (ctype_to_string t))
    [
      (Void, "void");
      (Char, "char");
      (Int, "int");
      (Pointer Int, "ptr");
      (Struct (Some "foo", []), "struct<<foo>>");
      (Enum (Some "c"), "enum<<c>>");
    ];

  (* function parsing - name only *)
  List.iter
    (fun s ->
      test_match s parse_function_decl s (function Func (n, _, _) -> n <> ""))
    [
      "int foo();";
      "void bar(int x);";
      "int add(int a, int b);";
      "char* get_name(void);";
      "struct foo* create(void);";
    ];

  (* struct/union/enum parsing *)
  List.iter
    (fun s -> test_some s parse_struct_def s)
    [
      "struct foo;";
      "struct bar { int x; };";
      "typedef struct { int x; } foo_t;";
      "enum color;";
      "union data;";
    ];

  (* typedef resolution *)
  List.iter
    (fun (s, t) -> test_eq s (fun x -> resolve_typedef (parse_type x)) s t)
    [ ("uintptr_t", Pointer Void); ("size_t", Long) ];

  (* function with typedef args *)
  test_match "typedef args" parse_function_decl "void foo(uintptr_t* ptr);"
    (function
    | Func ("foo", Void, [ x ]) when ctype_to_string x = "ptr" -> true
    | _ -> false);

  (* struct ptr args *)
  List.iter
    (fun s -> test_some s parse_function_decl s)
    [
      "void process(struct node* n);";
      "int compare(const struct item* a, const struct item* b);";
    ];

  (* function variations *)
  List.iter
    (fun s ->
      test_match s parse_function_decl s (function Func (_, _, args) ->
          List.length args > 0))
    [
      "int main(int argc, char** argv);";
      "void* memset(void* s, int c, size_t n);";
    ];

  (* function pointers (as typedefs) *)
  List.iter
    (fun s -> test_eq s parse_type s (Typedef s))
    [ "int (*func)(int);"; "void (*callback)(void*);" ];

  (* recursive/nested structs *)
  List.iter
    (fun s -> test_some s parse_struct_def s)
    [
      "struct node { int data; struct node* next; };";
      "struct tree { int value; struct tree* left; struct tree* right; };";
    ];

  Printf.printf "\n=== All done ===\n"
