(* The jump compiler: each jump's cond becomes the simplest equivalent
   expression over values.  A backward pass substitutes the defs it
   passes into the cond — a def replaces its var, so every var left
   reads the value at the walked position — and simplifies after each
   step; the walk continues into a unique goto predecessor.  The
   smallest flag-free form wins: inlined at the jump when its vars still
   hold those values there, else bound to a fresh comparison def at its
   own position.  No flag-free form keeps the cond. *)

open Bap.Std
open Bap_core_theory
open Core
module B = Hike_backsubst

(* The status flags, identified by the target's register roles. *)
let flag_vars (target : Theory.Target.t) : var list =
  let role r = Option.map ~f:Var.reify (Theory.Target.reg target r) in
  let open Theory.Role.Register in
  List.filter_opt
    [ role zero_flag; role carry_flag; role sign_flag; role overflow_flag;
      role parity_flag ]

let is_flag (flags : var list) (v : var) : bool = List.exists flags ~f:(Var.same v)

(* An indirect transfer's destination blocks: the [Insn.Slot.dests]
   facts on its instruction, the ones the discovery provides as it
   resolves them.  The BIR carries no edge for them; a transfer with no
   fact has none. *)
let targets_of ?(file : string option) (sub : sub term) : jmp term -> tid list =
  let by_addr =
    Term.enum blk_t sub
    |> Seq.filter_map ~f:(fun b ->
        Option.map (Term.get_attr b address) ~f:(fun a -> (Bitvec.to_int64 (Word.to_bitvec a), Term.tid b)))
    |> Seq.to_list |> Int64.Map.of_alist_reduce ~f:(fun a _ -> a) in
  let dests ~file (a : addr) : int64 list =
    let v : int64 list Toplevel.var = Toplevel.var "hike-jump-dests" in
    Toplevel.put v
      (let open KB.Syntax in
       Theory.Label.for_addr ~package:file (Word.to_bitvec a) >>= fun label ->
       KB.collect Theory.Semantics.slot label >>= fun sema ->
       match KB.Value.get Insn.Slot.dests sema with
       | None -> KB.return []
       | Some ds ->
         KB.List.filter_map (Core.Set.to_list ds) ~f:(fun d ->
             KB.collect Theory.Label.addr d >>| Option.map ~f:Bitvec.to_int64));
    Toplevel.get v in
  match file with
  | None -> fun _ -> []
  | Some file ->
    fun j ->
      let indirect =
        match Jmp.kind j with
        | Goto (Indirect _) -> true
        | Call c -> (match Call.target c with Indirect _ -> true | Direct _ -> false)
        | _ -> false in
      match Term.get_attr j address with
      | Some a when indirect -> List.filter_map (dests ~file a) ~f:(Core.Map.find by_addr)
      | _ -> []

let acceptable (flags : var list) (e : exp) : bool =
  (not (B.has_unknown e))
  && not (Core.Set.exists (Exp.free_vars e) ~f:(is_flag flags))

let order (f : B.form) =
  (B.size f.exp, (if B.holds f f.exp then 0 else 1), f.hops, - f.pos)

(* The best flag-free form of [j]'s cond, if any improves on it. *)
let compile_jmp ~(flags : var list) (g : B.graph) (b0 : blk term) (j : jmp term) :
    B.form option =
  let orig = Jmp.cond j in
  B.forms g b0 orig
  |> List.filter ~f:(fun (f : B.form) -> acceptable flags f.exp)
  |> List.min_elt ~compare:(fun x y -> Poly.compare (order x) (order y))
  |> Option.filter ~f:(fun (f : B.form) -> not (Exp.equal f.exp orig))

let uses_of ~(abi : Hike_abi.t) (s : sub term) : Var.Set.t =
  Hike_stack_model.sub_reads ~abi s

(* Compiles every jump's cond, then drops every def of a consumed flag var
   no read survives.  A compiled cond that reads memory, or whose vars are
   rewritten before the jump, is bound to a fresh 1-bit def at its own
   position — the VSA tags the def, and the tag licenses the emitter's
   frame addressing. *)
let compile_sub ?(file : string option) (target : Theory.Target.t) (sub : sub term) :
    sub term =
  let abi = Hike_abi.of_target target in
  let flags = flag_vars target in
  let g = B.graph_of_sub ~targets:(targets_of ?file sub) sub in
  let plans =
    Term.enum blk_t sub
    |> Seq.concat_map ~f:(fun b ->
        Term.enum jmp_t b
        |> Seq.filter_map ~f:(fun j ->
            Option.map (compile_jmp ~flags g b j) ~f:(fun f -> (Term.tid j, f))))
    |> Seq.to_list in
  if List.is_empty plans then sub
  else
    let conds, binds =
      List.fold plans ~init:(Tid.Map.empty, []) ~f:(fun (conds, binds) (jt, (f : B.form)) ->
          if B.holds f f.exp && not (Hike_stack_model.reads_mem f.exp) then
            (Core.Map.set conds ~key:jt ~data:f.exp, binds)
          else
            let v = Hike_synth.fresh ~bits:1 Hike_synth.Comparison in
            (Core.Map.set conds ~key:jt ~data:(Bil.Var v), (f, v) :: binds)) in
    let consumed =
      List.fold plans ~init:Var.Set.empty ~f:(fun acc (_, (f : B.form)) ->
          Core.Set.union acc (Core.Set.filter f.substituted ~f:(is_flag flags))) in
    let sub1 =
      B.bind sub binds
      |> Term.map blk_t ~f:(fun blk ->
          Term.map jmp_t blk ~f:(fun j ->
              match Core.Map.find conds (Term.tid j) with
              | Some c -> Jmp.with_cond j c
              | None -> j)) in
    let dead = Core.Set.diff consumed (uses_of ~abi sub1) in
    if Core.Set.is_empty dead then sub1
    else
      Term.map blk_t sub1 ~f:(fun blk ->
          Term.filter def_t blk ~f:(fun d -> not (Core.Set.mem dead (Def.lhs d))))
