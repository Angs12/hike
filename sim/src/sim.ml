open Core_kernel
open Poly
open Bap.Std.Project
open Bap.Std
open Bap_main
open Bap_main.Extension
open Bap_main.Extension.Command
open Format
open Normalize
open Leafs
include Self ()

let features_used =
  [
    "semantics";
    "function-starts";
    "disassembler";
    "lifter";
    "symbolizer";
    "rooter";
    "reconstructor";
    "brancher";
    "loader";
    "abi";
  ]

let rec inst_n_grams stmts ~window =
  match stmts with
  | [] -> []
  | _ -> List.take stmts window :: inst_n_grams (List.drop stmts 1) ~window

let exists_func proj ~func =
  let symtab = Project.symbols proj in
  let f = Symtab.find_by_name symtab func in
  Option.map ~f:(fun (n, _, _) -> n) f

let print_n_gram n_gram =
  print_endline
  @@ List.fold_right n_gram ~init:"\n\n/--/" ~f:(fun acc stmt ->
         stmt ^ acc ^ "/--/")

let print_norm_insts insts file =
  Stdlib.output_string file
  @@ List.fold_right insts ~init:"" ~f:(fun acc stmt -> stmt ^ "\n" ^ acc)

let in_n_gram inst n_gram = List.exists ~f:(fun n -> n = inst) n_gram

let compare_n_grams n_gram1 n_gram2 =
  n_gram1 |> List.count ~f:(fun inst -> in_n_gram inst n_gram2) |> fun count ->
  Float.of_int count /. Float.of_int (List.length n_gram1)

let similarity func1 func2 =
  let n_grams1 = normalizer#visit_term sub_t func1 [] in
  let n_grams2 = normalizer#visit_term sub_t func2 [] in
  let file1 = Stdlib.open_out "bin1_norm" in
  let file2 = Stdlib.open_out "bin2_norm" in
  print_norm_insts n_grams1 file1;
  print_norm_insts n_grams2 file2;
  compare_n_grams n_grams1 n_grams2

let prepare_sub arch proj sub =
  sub |> Sub.ssa |> Deadcode.clean_sub arch |> Sub.flatten

(* let prepare_sub arch proj sub = *)
(*   sub |> Sub.ssa |> Deadcode.clean_sub arch |> Smt.remove_opaque proj *)
(*   |> Smt.merge_cfg |> Deadcode.clean_sub arch |> Sub.flatten *)

let get_pass (name : string) =
  Bil.passes () |> List.find ~f:(fun p -> Bil.Pass.name p = name)

let main bin1 bin2 func _ =
  let loader = "llvm" in
  let normalization = Option.value_exn @@ get_pass "bnf1" in
  let optimizations =
    List.map
      ~f:(fun pass -> Option.value_exn @@ get_pass pass)
      [ "constant-propagation"; "prune-dead-virtuals"; "constant-folding" ]
  in
  Bil.select_passes @@ (normalization :: optimizations);
  let proj1 =
    Project.create ~package:bin1 @@ Input.load bin1 ~loader |> Or_error.ok_exn
  in
  let proj2 =
    Project.create ~package:bin2 @@ Input.load bin2 ~loader |> Or_error.ok_exn
  in
  print_endline @@ "Programs loaded";
  let proj1_arch = Project.arch proj1 in
  let proj2_arch = Project.arch proj2 in
  let open Result in
  let func1 = find_leaf proj1 ~func >>| prepare_sub proj1_arch proj1 in
  let func2 = find_leaf proj2 ~func >>| prepare_sub proj2_arch proj2 in
  print_endline @@ "Functions found in both binaries: ";
  Result.combine func1 func2 ~ok:similarity ~err:(fun err1 err2 ->
      err1 ^ " " ^ err2)
  |> fun pattern ->
  match pattern with
  | Ok score ->
      print_float score;
      Ok ()
  | Error msg -> failwith msg

let bin1 =
  Command.argument
    Extension.Type.("BIN1" %: string =? "a.out")
    ~doc:"First binary"

let bin2 =
  Command.argument
    Extension.Type.("BIN2" %: string =? "a.out")
    ~doc:"Second binary"

let func =
  Command.argument Extension.Type.("FUNC" %: string) ~doc:"Function name"

let () =
  Command.declare "sim"
    (args $ bin1 $ bin2 $ func)
    main ~doc:"Similarity of two binaries" ~requires:features_used

let () = Extension.declare ~provides:[ "command" ] (fun _ -> Ok ())
