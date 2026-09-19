(* Window probe: per sub it prints the finalized tree's residue/Args
   verdict (the window geometry the layout consumes) and the promoted
   slots/arity, at the production chain and at a replica of the
   production fixpoint.  Per sub it prints:
   - the verdict: the tree's window extent, the promoted slots/arity,
   - the seam-kind tags (the test-seam channel),
   - [sp_extents] (the stored-value channel),
   - the escape channels replicated on the same solution: each store's
     data denotation at the BLOCK-ENTRY state (where caller_side reads
     it) and at the def's own pre-state, and each parameter register's
     denotation at the block's end state — with the defining defs
     (RBP/RSP arithmetic) and their products.
   Usage: wc_diag.exe <binary> <sub> [<sub>...]
   [<binary> --all] prints one SWEEP line per sub: the production
   verdict, the promoted arity, and the escape-extent count. *)

open Bap.Std
open Probe_common

module Model = Hike__Hike_stack_model
module Promote = Hike__Hike_sections
module Vsa = Cbat_vsa

let i64_of_word w =
  match Cbat_word.to_int64 w with Ok v -> Some v | Error _ -> None

(* The absolute segment positions of a stack-offset set's hull. *)
let hull (offs : Vsa.WordSet.Clp.t) : (int64 * int64) option =
  match Vsa.WordSet.Clp.min_elem offs, Vsa.WordSet.Clp.max_elem offs with
  | Some mn, Some mx -> (
      match i64_of_word mn, i64_of_word mx with
      | Some lo, Some hi -> (
          match
            ( Vsa.Cbat_extraction.position_of_offset lo,
              Vsa.Cbat_extraction.position_of_offset hi )
          with
          | Some lo, Some hi -> Some (lo, hi)
          | _ -> None)
      | _ -> None)
  | _ -> None

let rel (pos : int64) : int64 = Int64.sub pos Model.segment_base

(* The finalized-tree verdict: attribute the single-sub program (the
   envs installed first) and read the storage decisions — the window
   is the widest Frame/Window member, the arity is the Arg_slot count. *)
let tree_verdict (abi : Hike_abi.t)
    (envs : (Vsa.AI.t * Vsa.AI.t) Tid.Map.t) (sub : sub term) :
    int64 option * int =
  Hike.Kb.install_run ~block_envs:envs;
  let prog = Program.create ~subs:[ sub ] () in
  let ctx =
    Hike.Sections.attribute ~word:8 ~entry:Model.segment_base ~abi ~spans:[]
      ~denote:Hike.Vsa.denote_exp_at prog
  in
  let tree =
    match Core.Map.find ctx.Hike.Sections.sub_trees (Term.tid sub) with
    | Some t -> t
    | None -> failwith "tree_verdict: no sub tree"
  in
  let word = 8L in
  let wacc = ref None and smax = ref (-1) in
  Base.List.iter (Hike.Sections.Tree.to_sequence tree |> Seq.to_list)
    ~f:(fun (_r, rs) ->
        (match rs.Hike.Sections.storage with
         | Hike.Sections.Stack_residue | Hike.Sections.Stack_residue ->
           Base.List.iter rs.Hike.Sections.members ~f:(fun m ->
               if m.Hike.Sections.m_width > 0 then
                 let w = Int64.sub m.Hike.Sections.m_hi Model.segment_base in
                 if Int64.compare w word >= 0 then
                   wacc :=
                     Some
                       (Int64.max w (Base.Option.value !wacc ~default:word)))
         | Hike.Sections.Arg_slot i -> smax := Int.max !smax i
         | _ -> ()));
  (!wacc, if !smax < 0 then 0 else !smax + 1)

(* One evaluation of an exp: stack-derived (with hull, relative to the
   entry line) or not. *)
let eval_data (e : exp) (st : AI.t) : string =
  match Vsa.Test_seam.denote_imm_exp e st with
  | Error _ -> "DENOTE-ERR"
  | Ok ws -> (
      match Vsa.WordSet.stack_offsets ws with
      | None -> Printf.sprintf "plain(%s)" (ws_to_string ws)
      | Some offs -> (
          match hull offs with
          | Some (lo, hi) ->
            Printf.sprintf "STACK[rel %Ld..%Ld]" (rel lo) (rel hi)
          | None -> "STACK(no-hull)"))

let stack_hull (e : exp) (st : AI.t) : (int64 * int64) option =
  match Vsa.Test_seam.denote_imm_exp e st with
  | Error _ -> None
  | Ok ws -> (
      match Vsa.WordSet.stack_offsets ws with
      | None -> None
      | Some offs -> hull offs)

let print_info (abi : Hike_abi.t) (sub : sub term)
    (offsets : Vsa.Cbat_extraction.kind Tid.Map.t)
    (envs : (Vsa.AI.t * Vsa.AI.t) Tid.Map.t) : unit =
  let name = Sub.name sub in
  let tree_wc, tree_arity = tree_verdict abi envs sub in
  Printf.printf "VERDICT %s: window_extent=%s\n%!" name
    (match tree_wc with
     | None -> "None"
     | Some w -> Printf.sprintf "Some(%Ld)" w);
  ignore abi;
  let names = Base.Hashtbl.create (module Tid) in
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun b ->
      let bn = Tid.to_string (Term.tid b) in
      Term.enum def_t b
      |> Seq.iteri ~f:(fun i d -> Base.Hashtbl.set names ~key:(Term.tid d)
                                      ~data:(Printf.sprintf "%s#%d" bn i)));
  Core.Map.iteri offsets
    ~f:(fun ~key:dtid ~data:(kind : Vsa.Cbat_extraction.kind) ->
        match kind with
        | Caller (lo, hi) ->
          Printf.printf "  TAG %s Caller(abs %Ld..%Ld rel %Ld..%Ld)\n%!"
            (Base.Option.value (Base.Hashtbl.find names dtid) ~default:"?")
            lo hi (rel lo) (rel hi)
        | Mixed (lo, hi) ->
          Printf.printf "  TAG %s Mixed(abs %Ld..%Ld)\n%!"
            (Base.Option.value (Base.Hashtbl.find names dtid) ~default:"?") lo hi
        | _ -> ())

(* The escape-channel replica at the production-shaped fixpoint. *)
let dig_stores (abi : Hike_abi.t)
    (sp : var) (prog : program term) (sub : sub term) : unit =
  let prog1 = Program.create ~subs:[ sub ] () in
  let sol =
    try
      Some
        (Vsa.static_graph_vsa ~abi:Hike_abi.x86_64_sysv
           [] prog1 sub (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv sub))
    with _ -> None
  in
  match sol with
  | None -> Printf.printf "DIGEST %s: fixpoint failed\n%!" (Sub.name sub)
  | Some sol ->
    Printf.printf "DIGEST %s (sp=%s)\n%!" (Sub.name sub) (Var.name sp);
    let params = Hike_abi.param_regs abi in
    let word = Int64.of_int abi.Hike_abi.word in
    (* The window-class arms over a candidate extent list: the same
       see/wrap the predicate applies. *)
    let would_be (exts : (int64 * int64) list) : string =
      let acc = ref None in
      let see w =
        if Int64.compare w word >= 0 then
          acc := Some (Int64.max w (Base.Option.value !acc ~default:word))
      in
      let wrap () = acc := Some (Base.Option.value !acc ~default:word) in
      Base.List.iter exts ~f:(fun (l, h) ->
          if Int64.compare l h > 0 then wrap ()
          else see (Int64.sub h Model.segment_base));
      match !acc with
      | None -> "None"
      | Some w -> Printf.sprintf "Some(%Ld)" w
    in
    let pre_exts = ref [] in
    let mention_sp (e : exp) =
      let vs = Exp.free_vars e in
      Core.Set.exists vs ~f:(fun v ->
          Var.same v sp || Base.String.equal (Var.name v) "RBP")
    in
    Term.enum blk_t sub
    |> Seq.iter ~f:(fun b ->
        let bn = Tid.to_string (Term.tid b) in
        let st0 = Graphlib.Std.Solution.get sol (Term.tid b) in
        let _, st_end =
          Vsa.Test_seam.fold_block_states ~sol b ~init:()
            ~f:(fun st_before _st d () ->
                let idx_name rhs =
                  Format.asprintf "%a" Exp.pp rhs in
                (* A defining def of SP/RBP arithmetic: show its
                   product. *)
                if mention_sp (Def.rhs d) then
                  Printf.printf "  DEF %s  %s := %s\n    prod=%s\n%!"
                    bn (Var.name (Def.lhs d)) (idx_name (Def.rhs d))
                    (eval_data (Def.rhs d) st_before);
                match Model.store_data_of_rhs (Def.rhs d) with
                | None -> ()
                | Some (data, _) ->
                  (match stack_hull data st0 with
                   | Some (lo, hi) ->
                     Printf.printf "  ESC-STORE-AT-ENTRY %s data=%s rel(%Ld..%Ld)\n%!"
                       bn (idx_name data) (rel lo) (rel hi)
                   | None -> ());
                  (match stack_hull data st_before with
                   | Some ext ->
                     pre_exts := ext :: !pre_exts;
                     Printf.printf "  ESC-STORE-AT-DEF %s data=%s rel(%Ld..%Ld)\n%!"
                       bn (idx_name data) (rel (fst ext)) (rel (snd ext))
                   | None -> ());
                  Printf.printf "  STORE %s data=%s\n    entry=%s\n    pre  =%s\n%!"
                    bn (idx_name data)
                    (eval_data data st0) (eval_data data st_before))
        in
        Base.List.iter params ~f:(fun v ->
            match stack_hull (Bil.Var v) st_end with
            | Some (lo, hi) ->
              pre_exts := (lo, hi) :: !pre_exts;
              Printf.printf "  ESC-PARAM-AT-END %s %s rel(%Ld..%Ld)\n%!"
                bn (Var.name v) (rel lo) (rel hi)
            | None -> ()));
    let denote ~(blk : blk term) ?(def : def term option) (e : exp) =
      match def with
      | Some d ->
        Vsa.denote_exp_at
          ~pre:(Graphlib.Std.Solution.get sol (Term.tid blk))
          ~blk ~def:d e
      | None ->
        Vsa.denote_exp_at
          ~pre:(Graphlib.Std.Solution.get sol (Term.tid blk))
          ~blk e
    in
    Printf.printf "  WOULD-BE-AT-DEF window_extent=%s\n%!" (would_be !pre_exts)

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  init ();
  match args with
  | path :: subs when subs <> [] ->
    let proj = load_project path in
    let target = Project.target proj in
    let abi = Hike_abi.of_target target in
    let sp = sp_of proj in
    let symtab = Some (Project.symbols proj) in
    let prog =
      Hike.Split_mem.normalize
        (Term.map sub_t (Project.program proj) ~f:(Hike.Jump.compile_sub target))
    in
      let bin = Filename.basename path in
    let one sub =
      try
        let envs, _sub' =
          Hike.Vsa.fixpoint target sp ~prog
            ~images:[] sub
          |> Base.Option.value ~default:(Tid.Map.empty, sub)
        in
        let wc, arity = tree_verdict abi envs sub in
        Printf.printf "SWEEP %s %s wc=%s arity=%d\n%!" bin
          (Sub.name sub)
          (match wc with
           | None -> "None"
           | Some w -> Printf.sprintf "Some(%Ld)" w)
          arity
      with e ->
        Printf.printf "SWEEP-ERR %s %s %s\n%!" bin (Sub.name sub)
          (Printexc.to_string e)
    in
    if Base.String.equal (List.hd subs) "--all" then
      Base.List.iter (all_subs prog) ~f:one
    else
      Base.List.iter subs ~f:(fun want ->
          match find_sub prog want with
          | None -> Printf.printf "MISS: no sub %s\n%!" want
          | Some sub ->
            let envs, _sub' =
              Hike.Vsa.fixpoint target sp ~prog:(Project.program proj)
                ~images:[] sub
              |> Base.Option.value ~default:(Tid.Map.empty, sub)
            in
            let sol =
              Vsa.static_graph_vsa ~abi:Hike_abi.x86_64_sysv
                ~resolved:Tid.Map.empty []
                (Program.create ~subs:[ sub ] ()) sub
                (Vsa.init_sol ~abi:Hike_abi.x86_64_sysv sub)
            in
            print_info abi sub (seam_kinds_of sol sub) envs;
            dig_stores abi sp prog sub)
  | _ -> usage Sys.argv.(0) "<binary> <sub>|--all [<sub>...]"
