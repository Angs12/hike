(* Reports fixpoint verdict, widening-point set, head BIR, and head states.
   Usage: conv_diag.exe <binary> [subname] (default "main"). *)

open Bap.Std
open Probe_common

(* Direct-jump CFG successors of a block. *)
let succs (blk : blk term) : tid list =
  Term.enum jmp_t blk
  |> Seq.filter_map ~f:(fun j ->
      match Jmp.kind j with
      | Goto (Direct t) | Ret (Direct t) -> Some t
      | Call c -> (
          match Call.target c with
          | Direct t -> Some t
          | _ -> None)
      | _ -> None)
  |> Seq.to_list

let cfg_of (sub : sub term) : (tid * tid list) list =
  Term.enum blk_t sub
  |> Seq.map ~f:(fun b -> (Term.tid b, succs b))
  |> Seq.to_list

let succs_of (cfg : (tid * tid list) list) (t : tid) : tid list =
  match Base.List.Assoc.find cfg t ~equal:Tid.equal with
  | Some ts -> ts
  | None -> []

(* Reachability in the CFG. *)
let reachable (cfg : (tid * tid list) list) (start : tid) (target : tid) :
    bool =
  let rec go seen = function
    | [] -> false
    | t :: rest ->
      if Tid.equal t target then true
      else if Base.List.mem seen t ~equal:Tid.equal then go seen rest
      else go (t :: seen) (succs_of cfg t @ rest)
  in
  go [] [ start ]

let on_cycle (cfg : (tid * tid list) list) (t : tid) : bool =
  Base.List.exists (succs_of cfg t) ~f:(fun s -> reachable cfg s t)

(* One (head, members) per cyclic SCC; head is the smallest Tid name. *)
let cyclic_heads (cfg : (tid * tid list) list) : (tid * tid list) list =
  let cyc =
    Base.List.filter_map cfg ~f:(fun (t, _) ->
        if on_cycle cfg t then Some t else None)
  in
  let rec group = function
    | [] -> []
    | t :: rest ->
      let same_cycle x y = reachable cfg x y && reachable cfg y x in
      let comp, rest' =
        Base.List.partition_tf rest ~f:(fun x -> same_cycle t x)
      in
      let members = t :: comp in
      let head =
        Base.List.fold_left members ~init:t ~f:(fun acc x ->
            if String.compare (Tid.name x) (Tid.name acc) < 0 then x else acc)
      in
      (head, members) :: group rest'
  in
  group cyc

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  init ();
  match args with
  | [] -> usage Sys.argv.(0) "<binary> [subname]"
  | path :: rest ->
    let proj = load_project path in
    let prog = Project.program proj in
    let sp = sp_of proj in
    let name = match rest with n :: _ -> n | [] -> "main" in
    let sub =
      match find_sub prog name with
      | Some s -> s
      | None ->
        usage Sys.argv.(0)
          (Printf.sprintf "<binary> [subname] - %s not found" name)
    in
    Printf.printf "=== conv_diag %s (%s) ===\n" (Filename.basename path)
      (Sub.name sub);
    let sub' = Hike.Relevance.analyze sp sub in
    let prog' = Program.create ~subs:[ sub' ] () in
    let sol =
      try Vsa.static_graph_vsa [] prog' sub' (Vsa.init_sol sub')
      with
      | Vsa.Fixpoint_not_converged (n, _sol, gap) ->
        Printf.printf "FIXPOINT NOT CONVERGED after %d rounds\n" n;
        (match gap with
         | Some (b, s) ->
           Printf.printf "  first still-growing (block, successor): (%s -> %s)\n"
             (Tid.name b) (Tid.name s)
         | None -> Printf.printf "  (no gap pair captured)\n");
        exit 0
    in
    Printf.printf "FIXPOINT CONVERGED\n";
    let cfg = cfg_of sub' in
    let heads = cyclic_heads cfg in
    Printf.printf "WIDENING-POINT set (%d cyclic SCCs):\n" (List.length heads);
    List.iter
      (fun (head, members) ->
        Printf.printf "  head %s  (cycle members: %s)\n" (Tid.name head)
          (Base.String.concat ~sep:", "
             (Base.List.map members ~f:(fun t -> Tid.name t))))
      heads;
    List.iter
      (fun (head, _members) ->
        match
          Term.enum blk_t sub'
          |> Seq.find ~f:(fun b -> Tid.equal (Term.tid b) head)
        with
        | Some b -> Printf.printf "%s\n" (blk_bil_to_string b)
        | None -> ())
      heads;
    List.iter
      (fun (head, members) ->
        let st = Graphlib.Std.Solution.get sol head in
        let vars =
          members
          |> Base.List.concat_map ~f:(fun t ->
              Term.enum blk_t sub'
              |> Seq.find ~f:(fun b -> Tid.equal (Term.tid b) t)
              |> Option.to_list)
          |> Base.List.concat_map ~f:(fun b ->
              Term.enum def_t b
              |> Seq.map ~f:(fun d -> Var.base (Def.lhs d))
              |> Seq.to_list)
          |> Base.List.dedup_and_sort ~compare:(fun a b -> String.compare (Var.name a) (Var.name b))
        in
        Printf.printf "  head %s gap-successor state: %s\n" (Tid.name head)
          (state_summary vars st))
      heads
