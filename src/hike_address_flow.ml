(* Allocation provenance for address rewriting.  Logical stack positions
   and the SSA definition index come from VSA; allocation roots stay
   logical [Stack] ranges until the ownership constraints are closed. *)
open Bap.Std

type anchor =
  | Binding of int64 * int64
  | Window

type owners = { roots : anchor list; unknown : bool }

type target = { base : var; offset : int64 }

let pending = { roots = []; unknown = false }
let unknown = { pending with unknown = true }
let one root = { pending with roots = [ root ] }
let roots t = t.roots

let same a b =
  match a, b with
  | Binding (a_lo, a_hi), Binding (b_lo, b_hi) ->
      Int64.equal a_lo b_lo && Int64.equal a_hi b_hi
  | Window, Window -> true
  | _ -> false

let join a b =
  { roots =
      Base.List.dedup_and_sort (a.roots @ b.roots) ~compare:(fun a b ->
          match a, b with
          | Window, Window -> 0
          | Window, _ -> -1
          | _, Window -> 1
          | Binding (a_lo, a_hi), Binding (b_lo, b_hi) ->
              let c = Int64.compare a_lo b_lo in
              if c <> 0 then c else Int64.compare a_hi b_hi);
    unknown = a.unknown || b.unknown }

let equal a b =
  Bool.equal a.unknown b.unknown && Base.List.equal same a.roots b.roots

(* The SSA definition index is VSA's own: [defs] names every version once,
   with its defining term.  Jump effects add the lanes a call defines. *)
let solve ~sub ~abi ~entry ~targets ~nonstack ~leaves ~phi_leaves ~defs =
  let definitions, reads =
    Core.Map.fold defs ~init:(Var.Set.empty, Var.Set.empty)
      ~f:(fun ~key:_ ~data:term (writes, reads) ->
        let lhs =
          match term with `Def d -> Def.lhs d | `Phi p -> Phi.lhs p in
        (Core.Set.add writes lhs,
         Core.Set.union reads (Hike_stack_model.reads term)))
  in
  let writes, reads =
    Term.enum blk_t sub
    |> Seq.fold ~init:(definitions, reads) ~f:(fun (writes, reads) blk ->
        Term.enum jmp_t blk
        |> Seq.fold ~init:(writes, reads) ~f:(fun (writes, reads) j ->
            (Core.Set.union writes (Hike_stack_model.writes (`Jmp j)),
             Core.Set.union reads (Hike_stack_model.reads (`Jmp j)))))
  in
  let get state v = Base.Option.value (Core.Map.find state v) ~default:pending in
  let initial =
    Core.Set.fold (Core.Set.diff reads writes) ~init:Var.Map.empty
      ~f:(fun acc v ->
        let value =
          if Hike_abi.is_sp abi (Var.base v) then
            Base.Option.value_map entry ~default:unknown ~f:one
          else unknown in
        Core.Map.set acc ~key:v ~data:value)
  in
  let rec inherit_from state leaves = function
    | Bil.Var v -> get state v
    | Bil.BinOp ((Bil.PLUS | Bil.MINUS), a, b) ->
        let address e =
          Core.Set.exists (Exp.free_vars e) ~f:(fun v ->
              match Core.Map.find leaves v with
              | Some (`Static _ | `Addr) -> true
              | Some `Int -> false
              | None -> false) in
        (match address a, address b with
         | true, false -> inherit_from state leaves a
         | false, true -> inherit_from state leaves b
         | _ -> join (inherit_from state leaves a) (inherit_from state leaves b))
    | Bil.Cast (_, _, a) -> inherit_from state leaves a
    | Bil.Ite (_, a, b) -> join (inherit_from state leaves a) (inherit_from state leaves b)
    | Bil.Load _ | Bil.Store _ | Bil.Unknown _ -> unknown
    | e ->
        let roots =
          Core.Set.fold (Exp.free_vars e) ~init:pending ~f:(fun roots v ->
              match Core.Map.find leaves v with
              | Some `Int -> roots
              | Some (`Static _ | `Addr) | None -> join roots (get state v)) in
        roots
  in
  let def state d =
    let value =
      match Core.Map.find targets (Term.tid d) with
      | Some target -> one target
      | None when Core.Set.mem nonstack (Term.tid d) -> pending
      | None ->
        inherit_from state
          (Base.Option.value (Core.Map.find leaves (Term.tid d))
             ~default:Var.Map.empty)
          (Def.rhs d) in
    Core.Map.set state ~key:(Def.lhs d) ~data:value
  in
  let phi state p =
    let value =
      Phi.values p
      |> Seq.fold ~init:pending ~f:(fun acc (pred, e) ->
          join acc (inherit_from state (phi_leaves p pred) e)) in
    Core.Map.set state ~key:(Phi.lhs p) ~data:value
  in
  let jmp state j =
    let effects = Hike_stack_model.effects j in
    let sp =
      Base.List.find effects.reads ~f:(fun v -> Hike_abi.is_sp abi (Var.base v)) in
    Base.List.fold effects.writes ~init:state ~f:(fun state v ->
        let value =
          if Hike_abi.is_sp abi (Var.base v) then
            Base.Option.value_map sp ~default:unknown ~f:(get state)
          else unknown in
        Core.Map.set state ~key:v ~data:value)
  in
  (* Each SSA version has one definition, so one state for the whole sub
     holds every version's owners; the terms re-apply until it is stable. *)
  let elts =
    Term.enum blk_t sub
    |> Seq.concat_map ~f:Blk.elts
    |> Seq.to_list in
  let step state =
    Base.List.fold elts ~init:state ~f:(fun state -> function
        | `Def d -> def state d
        | `Phi p -> phi state p
        | `Jmp j -> jmp state j) in
  let rec close state =
    let next = step state in
    if Core.Map.equal equal state next then state else close next in
  get (close initial)

let word ~bits k = Bil.Int (Word.of_int64 ~width:bits k)
let integer ~bits e = Bil.Cast (Bil.UNSIGNED, bits, e)
let add a b = Bil.BinOp (Bil.PLUS, a, b)
let sub a b = Bil.BinOp (Bil.MINUS, a, b)

let target_equal a b =
  Var.equal a.base b.base && Int64.equal a.offset b.offset

(* The value's one resolved allocation.  Several logical roots are fine
   once the ownership closure made them share storage; distinct targets
   are not convertible (the consumer keeps its native pointers). *)
let resolved_opt ~resolve owners v =
  match owners v with
  | { roots = []; unknown = false } -> None
  | { roots = root :: rest; unknown = false } -> (
      match resolve root with
      | None -> None
      | Some target ->
          if
            Base.List.for_all rest ~f:(fun root ->
                match resolve root with
                | Some other -> target_equal target other
                | None -> false)
          then Some target
          else None)
  | _ -> None

(* The resolved allocation a value belongs to; a non-convertible value
   is an internal ownership error, never a silent partial rewrite. *)
let resolved ~resolve owners v =
  match resolved_opt ~resolve owners v with
  | Some target -> target
  | None ->
      let value = owners v in
      failwith
        (Printf.sprintf
           "hike-flow: unresolved allocation of %s (roots=%d, unknown=%b)"
           (Format.asprintf "%a" Var.pp v) (Base.List.length value.roots)
           value.unknown)

let position ~bits ~owners ~resolve v =
  let target = resolved ~resolve owners v in
  add (sub (integer ~bits (Bil.Var v)) (integer ~bits (Bil.Var target.base)))
    (word ~bits target.offset)

(* Only pointer leaves change.  Original operators and integer indices
   survive, even when an anchor's constant adjustment could cancel. *)
let substitute ~bits ~leaves ~owners ~resolve ~logical target exp =
  let anchor offset =
    Hike_synth_addr.base_plus ~addr_bits:bits target.base
      ~rel:target.offset (word ~bits offset) in
  let mapper = object
    inherit Exp.mapper as super
    method! map_exp e =
      match logical e with Some e -> e | None -> super#map_exp e
    method! map_var v =
      match Core.Map.find leaves v with
      | Some (`Static offset) -> anchor offset
      | Some `Addr -> (
          match resolved ~resolve owners v with
          | { base; offset } when Var.equal base target.base
                                && Int64.equal offset target.offset ->
              Bil.Var v
          | _ ->
              Hike_synth_addr.base_plus ~addr_bits:bits target.base
                ~rel:target.offset
                (position ~bits ~owners ~resolve v))
      | Some `Int | None -> Bil.Var v
  end in
  mapper#map_exp exp

(* The logical coordinate of an expression on the stack line.  A loaded
   value is already a native pointer; it cannot be rewritten to an offset
   without changing its type, so [None] keeps real-pointer arithmetic. *)
let rec logical ~bits ~leaves ~owners ~resolve exp =
  match exp with
  | Bil.Int _ -> Some exp
  | Bil.Var v -> (
      match Core.Map.find leaves v with
      | Some (`Static offset) -> Some (word ~bits offset)
      | Some `Addr ->
          Base.Option.map (resolved_opt ~resolve owners v) ~f:(fun _ ->
              position ~bits ~owners ~resolve v)
      | Some `Int | None -> Some exp)
  | Bil.BinOp ((Bil.PLUS | Bil.MINUS) as op, a, b) -> (
      match (logical ~bits ~leaves ~owners ~resolve a,
             logical ~bits ~leaves ~owners ~resolve b)
      with
      | Some a, Some b -> Some (Bil.BinOp (op, a, b))
      | _ -> None)
  | Bil.Cast (cast, width, a) ->
      Base.Option.map (logical ~bits ~leaves ~owners ~resolve a)
        ~f:(fun a -> Bil.Cast (cast, width, a))
  | Bil.Ite (cond, a, b) -> (
      match (logical ~bits ~leaves ~owners ~resolve a,
             logical ~bits ~leaves ~owners ~resolve b)
      with
      | Some a, Some b -> Some (Bil.Ite (cond, a, b))
      | _ -> None)
  | _ -> None
