(* Fixture runner (d4 counter loop) plus binary live-map tracer; vsa-debug only.
   Usage: vsa_debug.exe d4 | vsa_debug.exe <binary> [subname] *)

open Bap.Std
open Probe_common

(* d4 counter-loop fixture: i:=0, then i:=i+1 around a two-jump header. *)
let w32 n = Word.of_int ~width:32 n

let fixture_d4 () : sub term =
  let i = Var.create ~is_virtual:false ~fresh:false "i" (Type.Imm 32) in
  let iv = Bil.Var i in
  let lt5 = Bil.BinOp (Bil.LT, iv, Bil.Int (w32 5)) in
  let nlt5 = Bil.UnOp (Bil.NOT, lt5) in
  let entry_b = Blk.Builder.create () in
  let body_b = Blk.Builder.create () in
  let header_b = Blk.Builder.create () in
  let exit_b = Blk.Builder.create () in
  Blk.Builder.add_def entry_b (Def.create i (Bil.Int (w32 0)));
  Blk.Builder.add_def body_b (Def.create i (Bil.BinOp (Bil.PLUS, iv, Bil.Int (w32 1))));
  let entry0 = Blk.Builder.result entry_b in
  let body0 = Blk.Builder.result body_b in
  let header0 = Blk.Builder.result header_b in
  let exit0 = Blk.Builder.result exit_b in
  let body_tid = Term.tid body0 in
  let header_tid = Term.tid header0 in
  let exit_tid = Term.tid exit0 in
  let entry_b = Blk.Builder.init ~copy_defs:true entry0 in
  Blk.Builder.add_jmp entry_b (Jmp.create (Goto (Direct body_tid)));
  let body_b = Blk.Builder.init ~copy_defs:true body0 in
  Blk.Builder.add_jmp body_b (Jmp.create (Goto (Direct header_tid)));
  let header_b = Blk.Builder.init ~copy_defs:true header0 in
  Blk.Builder.add_jmp header_b (Jmp.create ~cond:nlt5 (Goto (Direct exit_tid)));
  Blk.Builder.add_jmp header_b (Jmp.create ~cond:lt5 (Goto (Direct body_tid)));
  let sub_b = Sub.Builder.create ~name:"vsa_debug_d4" () in
  Sub.Builder.add_blk sub_b (Blk.Builder.result entry_b);
  Sub.Builder.add_blk sub_b (Blk.Builder.result body_b);
  Sub.Builder.add_blk sub_b (Blk.Builder.result header_b);
  Sub.Builder.add_blk sub_b (Blk.Builder.result exit_b);
  Sub.Builder.result sub_b

let i_of (sub : sub term) : var =
  Term.enum blk_t sub
  |> Seq.concat_map ~f:(Term.enum def_t)
  |> Seq.find_map ~f:(fun d ->
      if String.equal (Var.name (Var.base (Def.lhs d))) "i" then
        Some (Var.base (Def.lhs d))
      else None)
  |> Option.value ~default:(Var.create "i" (Type.Imm 32))

let run_one_fixture (name : string) (sub : sub term) : unit =
  Printf.printf "=== fixture %s ===\n" name;
  let sp = Hike.Abi.x86_64_sysv.sp in
  let prog' = Program.create ~subs:[ sub ] () in
  let sol =
    Vsa.static_graph_vsa [] prog' sub (Vsa.init_sol sub)
  in
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun b ->
      let st0 = Graphlib.Std.Solution.get sol (Term.tid b) in
      let st1 = ref st0 in
      Printf.printf "-- blk %s\n" (Tid.name (Term.tid b));
      Term.enum def_t b
      |> Seq.iter ~f:(fun d ->
          let pre = !st1 in
          let post = Vsa.Test_seam.denote_def d pre in
          Printf.printf "    %s\n      pre : %s\n      post: %s\n"
            (def_to_string d)
            (state_summary [ sp; i_of sub ] pre)
            (state_summary [ sp; i_of sub ] post);
          st1 := post))

let run_binary (path : string) (name : string) : unit =
  let proj = load_project path in
  let prog = Project.program proj in
  let sp = sp_of proj in
  let sub =
    match find_sub prog name with
    | Some s -> s
    | None -> usage Sys.argv.(0) (Printf.sprintf "<binary> [subname] - %s not found" name)
  in
  Printf.printf "=== binary %s (%s) ===\n" (Filename.basename path) (Sub.name sub);
  let sub', sol = analyze_and_fixpoint sp prog sub in
  Printf.printf "(fused single-pass: no views — the per-block IN-states are the solution)\n";
  let vars = lhs_vars_of sub' in
  Term.enum blk_t sub'
  |> Seq.iter ~f:(fun b ->
      let st = Graphlib.Std.Solution.get sol (Term.tid b) in
      Printf.printf "%s :: %s\n" (Tid.name (Term.tid b))
        (state_summary (sp :: vars) st))

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  init ();
  match args with
  | [] -> usage Sys.argv.(0) "(d4 | <binary> [subname])"
  | "d4" :: _ -> run_one_fixture "d4" (fixture_d4 ())
  | path :: rest ->
    let name = match rest with n :: _ -> n | [] -> "main" in
    run_binary path name
