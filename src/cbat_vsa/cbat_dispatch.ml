(* Guard construction for an in-VSA dispatch: bind the target expression
   once, then build one guarded arm per enumerated target word.  Word
   enumeration and base recovery belong to the caller; this module only
   reads the materialized view and never changes the sub. *)

open Bap.Std

type base = {
  summand : exp;
  values : int64 list;
}

type materialized = {
  base : base option;
  targets : (Cbat_word.t * Tid.t) list;
  sub : Sub.t;
  module_addr : int64 -> exp;
}

type arm_kind = Jump | Call

type arm = {
  guard : exp;
  target : Tid.t;
  kind : arm_kind;
}

(* The transfer's unconditional condition is the constant true; it adds
   nothing to the case test. *)
let is_true_cond (e : exp) : bool =
  match e with Bil.Int w -> Word.equal w (Word.one 1) | _ -> false

(* A variable names an SSA value (a def's lhs or a phi's lhs), so every
   arm may read it directly.  A load or any other expression would be
   re-evaluated per arm, so it gets one binding. *)
let bind_target (e : exp) : exp * (var * def term) option =
  match e with
  | Bil.Var _ -> (e, None)
  | _ ->
    let bits =
      match Type.infer e with
      | Ok (Type.Imm n) -> n
      | Ok _ | Error _ ->
        failwith "Cbat_dispatch: the target expression is not a word"
    in
    let t =
      Var.create ~is_virtual:true ~fresh:true "dispatch_target"
        (Type.Imm bits)
    in
    (Bil.Var t, Some (t, Def.create t e))

let int_exp ~bits (v : int64) : exp =
  Bil.Int (Word.of_int64 ~width:bits v)

(* One word's case test: the target's value is that word, expressed in the
   same value domain as the target.  A module-relative base makes the test
   the offset [target - summand == word - base]. *)
let case_test ~(target : exp) ~(base : base option)
    ~(module_addr : int64 -> exp) (w : Cbat_word.t) : exp =
  let bits = Cbat_word.bitwidth w in
  let a = Cbat_word.to_int64_exn w in
  match base with
  | Some { summand; values = b :: bs } ->
    let delta b =
      Bil.BinOp
        ( Bil.EQ
        , Bil.BinOp (Bil.MINUS, target, summand)
        , int_exp ~bits (Int64.sub a b) )
    in
    (match bs with
     | [] -> delta b
     | bs ->
       let guarded b =
         Bil.BinOp
           ( Bil.AND
           , Bil.BinOp (Bil.EQ, summand, module_addr b)
           , delta b )
       in
       List.fold_left
         (fun acc b -> Bil.BinOp (Bil.OR, acc, guarded b))
         (guarded b) bs)
  | Some { values = []; _ } | None ->
    Bil.BinOp (Bil.EQ, target, module_addr a)

let arms ~(kind : arm_kind) ~(cond : exp option) ~(target : exp)
    ~(base : base option) ~(module_addr : int64 -> exp)
    ~(targets : (Cbat_word.t * Tid.t) list) : arm list =
  let cond =
    match cond with Some c when not (is_true_cond c) -> Some c | _ -> None
  in
  List.map
    (fun (w, target_tid) ->
      let test = case_test ~target ~base ~module_addr w in
      let guard =
        match cond with
        | None -> test
        | Some c -> Bil.BinOp (Bil.AND, c, test)
      in
      { guard; target = target_tid; kind })
    targets

let materialize (m : materialized) ~(kind : arm_kind) ~(cond : exp option)
    ~(target : exp) : (var * def term) option * arm list =
  let bound, binding = bind_target target in
  (binding,
   arms ~kind ~cond ~target:bound ~base:m.base ~module_addr:m.module_addr
     ~targets:m.targets)

(* One arm's transfer.  The wrapper chooses [Call] when the original
   transfer has a return; [Jump] otherwise.  The arm layout is identical. *)
let arm_jmp ~(kind : arm_kind) ~(return : label option)
    ~(is_intra : Tid.t -> bool) (a : arm) : jmp term =
  match kind with
  | Call ->
    Jmp.create ~cond:a.guard
      (Call
         (Call.create ~target:(Direct a.target)
            ~return:(Core.Option.value_exn return) ()))
  | Jump ->
    if is_intra a.target then
      Jmp.create_goto ~cond:a.guard (Direct a.target)
    else
      Jmp.create ~cond:a.guard
        (Call (Call.create ~target:(Direct a.target) ()))

(* The transfer's indirect target expression. *)
let indirect_target (j : jmp term) : exp option =
  match Jmp.kind j with
  | Goto (Indirect e) -> Some e
  | Call c -> (
    match Call.target c with Indirect e -> Some e | Direct _ -> None)
  | _ -> None

(* The whole BIR rewrite of a dispatch site: one target binding (when the
   expression is not stable), the ordered arm chain, the no-match trap of
   a complete call set, and the explicit false edge of a conditional
   transfer.  [is_intra] names a target that is a block of the current
   sub; every other jump target is a function entry (a tail call).  The
   input sub/block is read only. *)
let rewrite_source (m : materialized) ~(kind : arm_kind)
    ~(blk : blk term) ~(jmp : jmp term) ~(is_intra : Tid.t -> bool)
    ~(false_target : Tid.t option) : blk term * blk term option =
  let target =
    match indirect_target jmp with
    | Some e -> e
    | None -> failwith "Cbat_dispatch: the transfer is not indirect"
  in
  let cond = Jmp.cond jmp in
  let original =
    match Jmp.kind jmp with
    | Call c when Option.is_some (Call.return c) -> Some c
    | _ -> None
  in
  let binding, arms =
    materialize m ~kind ~cond:(Some cond) ~target
  in
  let kind = match original with Some _ -> Call | None -> Jump in
  let return = match original with Some c -> Call.return c | None -> None in
  let jmps =
    List.map (arm_jmp ~kind ~return ~is_intra) arms @ [ jmp ]
  in
  begin
    let blk =
      Term.concat_map jmp_t blk ~f:(fun j ->
          if Tid.equal (Term.tid j) (Term.tid jmp) then jmps else [ j ])
    in
    (* Only a conditional transfer has a false continuation; an
       unconditional indirect jump's set is exhaustive.  Keep the false
       edge after the arm/trap chain. *)
    let blk =
      if is_true_cond cond then blk
      else
        match false_target with
        | None -> blk
        | Some t -> Term.append jmp_t blk (Jmp.create (Goto (Direct t)))
    in
    let blk =
      match binding with
      | None -> blk
      | Some (_, d) -> Term.append def_t blk d
    in
    (blk, None)
  end
