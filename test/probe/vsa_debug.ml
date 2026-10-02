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
  let sol = run_sub_fixpoint sub in
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
  let prog = production_input proj in
  let sp = sp_of proj in
  let sub =
    match find_sub prog name with
    | Some s -> s
    | None -> usage Sys.argv.(0) (Printf.sprintf "<binary> [subname] - %s not found" name)
  in
  Printf.printf "=== binary %s (%s) ===\n" (Filename.basename path) (Sub.name sub);
  (* The fused solve returns the rewritten (normalized) sub and the
     per-block (pre, post) envs: the walks read the forms production
     analyses. *)
  let envs, sub', _grown =
    Hike.Vsa.fixpoint (Project.target proj)
      ~lookup:(fun _ -> None)
      ~sub_addrs:(Core.Map.empty (module Addr)) ~images:[]
      ~written:(Hike.Vsa.kill_summaries ~abi:Hike.Abi.x86_64_sysv
                  (Program.create ~subs:[ sub ] ()))
      ~lift_at:(fun _ ~block_addrs:_ -> None)
      ~block_addrs:(Core.Map.empty (module Addr)) sub
  in
  let pre_of tid = match Core.Map.find envs tid with
    | Some (pre, _) -> pre
    | None -> Cbat_vsa.AI.top
  in
  let vars = lhs_vars_of sub' in
  (* The sub's model memory var (any store's lhs). *)
  let sub_mem_var =
    Seq.filter_map (Term.enum blk_t sub')
      ~f:(fun b ->
        Seq.filter_map (Term.enum def_t b)
          ~f:(fun d ->
            match Var.typ (Def.lhs d) with
            | Type.Mem _ -> Some (Def.lhs d)
            | _ -> None)
        |> Seq.hd)
    |> Seq.hd
  in
  let dump_mem = try Sys.getenv "VSA_DUMP_MEM" <> "" with _ -> false in
  (* One line per word def: the def, then the lhs's raw composite (the
     origin and its offset pieces, not the materialized view). *)
  let dump_defs = try Sys.getenv "VSA_DUMP_DEFS" <> "" with _ -> false in
  let mem_idx : Cbat_vsa.Mem.idx = { addr_width = 64; addressable_width = 8 } in
  let mem_of (st : Cbat_vsa.AI.t) (v : var) : Cbat_vsa.Mem.t option =
    Core.Option.try_with (fun () ->
        Cbat_vsa.AI.find_memory mem_idx st v)
  in
  let cellstat (st : Cbat_vsa.AI.t) (v : var) : string =
    match mem_of st v with
    | None -> "no-mem"
    | Some m ->
        let txt = Format.asprintf "%a" Cbat_vsa.Mem.pp m in
        let cells =
          String.split_on_char '[' txt
          |> Base.List.length |> fun k -> k - 1
        in
        let txt =
          Base.String.filter txt ~f:(fun c -> c != '\n' && c != '\t' && c != ' ')
        in
        Printf.sprintf "%d cells: %s" cells
          (if cells > 0 then String.sub txt 0 (min 400 (String.length txt))
           else "")
  in
  if dump_defs then
    Term.enum blk_t sub'
    |> Seq.iter ~f:(fun b ->
        let st = ref (pre_of (Term.tid b)) in
        (* The block's IN memory: the cells the walk's deliveries and the
           joins produced. *)
        (match sub_mem_var with
         | Some mv ->
           Printf.printf "  [%s] PRE-MEM %s\n%!" (Tid.name (Term.tid b))
             (cellstat !st mv)
         | None -> ());
        Term.enum def_t b
        |> Seq.iter ~f:(fun d ->
            let lv = Def.lhs d in
            let post = Vsa.Test_seam.denote_def d !st in
            (match Var.typ lv with
             | Type.Imm n when n <= 64 ->
               Printf.printf "  [%s] %s\n%!" (Tid.name (Term.tid b))
                 (Format.asprintf "%a = %a" Def.pp d Vsa.WordSet.pp
                    (Cbat_vsa.AI.find_word n post lv))
             | Type.Mem _ ->
               (* The access's address denotation and the resulting
                  cells: the round trip's two ends. *)
               let node = Hike.Stack_model.mem_node_of (Def.rhs d) in
               let addr_exp =
                 match node with
                 | Some (`Load (_, a, _)) -> Some a
                 | Some (`Store (_, a, _, _)) -> Some a
                 | None -> None
               in
               let addr_s =
                 match addr_exp with
                 | None -> "?"
                 | Some a ->
                   (match
                      Vsa.denote_exp_at ~pre:!st ~blk:b ~def:d a
                    with
                    | Ok ws -> Format.asprintf "%a" Vsa.WordSet.pp ws
                    | Error _e -> "err")
               in
               Printf.printf "  [%s] %s | addr=%s | %s\n%!"
                 (Tid.name (Term.tid b))
                 (Format.asprintf "%a" Def.pp d) addr_s (cellstat post lv)
             | _ -> ());
            st := post));
  Term.enum blk_t sub'
  |> Seq.iter ~f:(fun b ->
      let st0 = pre_of (Term.tid b) in
      Printf.printf "%s :: %s\n" (Tid.name (Term.tid b))
        (state_summary (sp :: vars) st0);
      if dump_mem then begin
        let st = ref st0 in
        Term.enum def_t b
        |> Seq.iter ~f:(fun d ->
              let lv = Def.lhs d in
              let is_mem =
                match Var.typ lv with
                | Bap.Std.Type.Mem _ -> true
                | _ -> false
              in
              (if is_mem then
               Printf.printf "  def %-8s | pre %s | post %s\n%!"
                 (Var.name lv)
                 (cellstat !st lv)
                 (let post = Vsa.Test_seam.denote_def d !st in
                  let r = cellstat post lv in
                  st := post;
                  r)))
      end)

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  init ();
  match args with
  | [] -> usage Sys.argv.(0) "(d4 | <binary> [subname])"
  | "d4" :: _ -> run_one_fixture "d4" (fixture_d4 ())
  | path :: rest ->
    let name = match rest with n :: _ -> n | [] -> "main" in
    run_binary path name
