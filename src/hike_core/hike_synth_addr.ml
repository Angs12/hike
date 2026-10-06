(* The synthetic address layer: the leaf census and the base/displacement
   arithmetic of an address value.  The vocabulary (kinds, spans) lives
   in Hike_synth below the VSA; this layer needs the domain's word sets
   and the model's offset line, so it lives with the model. *)

open Bap.Std
module Model = Hike_stack_model

(* A leaf's kind: [`Static k] an address whose offset is provably k,
   [`Addr] an address whose offset is not static, [`Int] a visible
   non-address (a runtime piece).  A var the denotation cannot see is
   absent — unknown may be a pointer at emission, so it never enters a
   displacement. *)
type leaf = [ `Static of int64 | `Addr | `Int ]

let w64 (k : int64) : exp =
  Bil.Int (Cbat_word.to_word (Cbat_word.of_int64 ~width:64 k))

(* The entry-line arithmetic of an address exp: each [`Static] leaf
   folds to its constant, each [`Int] leaf (a value outside the stack
   segment) stays a runtime piece.  [None] when an address part is a
   pointer or invisible — the value then composes over its operands'
   own pointers. *)
let offset_of ~(leaves : leaf Var.Map.t) (e : exp) : exp option =
  Hike_exp_fold.fold
    (fun e child ->
      match e with
      | Bil.Int _ -> Some e
      | Bil.Var v -> (
          match Core.Map.find leaves v with
          | Some (`Static k) -> Some (w64 k)
          | Some `Int -> Some e
          | Some `Addr | None -> None)
      | Bil.BinOp ((Bil.PLUS | Bil.MINUS) as op, a, b) -> (
          match (child a, child b) with
          | Some a', Some b' -> (
              match (a', b') with
              | Bil.Int x, Bil.Int y -> (
                  match
                    (Cbat_word.to_int64 (Cbat_word.of_word x),
                     Cbat_word.to_int64 (Cbat_word.of_word y))
                  with
                  | Ok x', Ok y' ->
                      Some
                        (w64
                           ((if op = Bil.PLUS then Stdlib.Int64.add
                             else Stdlib.Int64.sub)
                              x' y'))
                  | _ -> Some (Bil.BinOp (op, a', b')))
              | _ -> Some (Bil.BinOp (op, a', b')))
          | _ -> None)
      | Bil.Cast (cast, width, a) ->
          Base.Option.map (child a) ~f:(fun a' -> Bil.Cast (cast, width, a'))
      | Bil.Ite (c, a, b) -> (
          match (child a, child b) with
          | Some a', Some b' -> Some (Bil.Ite (c, a', b'))
          | _ -> None)
      | _ ->
          if
            Core.Set.exists (Exp.free_vars e) ~f:(fun v ->
                match Core.Map.find leaves v with
                | Some `Int -> false
                | _ -> true)
          then None
          else Some e)
    e

(* [base + (disp − rel)] with the displacement folded: a static
   displacement folds to a constant (the base itself at zero). *)
let base_plus (base : var) ~(rel : int64) (disp : exp) : exp =
  match disp with
  | Bil.Int w -> (
      match Cbat_word.to_int64 (Cbat_word.of_word w) with
      | Ok k ->
          let k = Stdlib.Int64.sub k rel in
          if Stdlib.Int64.equal k 0L then Bil.Var base
          else Bil.BinOp (Bil.PLUS, Bil.Var base, w64 k)
      | Error _ -> Bil.BinOp (Bil.PLUS, Bil.Var base, disp))
  | _ ->
      Bil.BinOp
        (Bil.PLUS, Bil.Var base, Bil.BinOp (Bil.MINUS, disp, w64 rel))

(* Every var leaf's kind: a synthetic leaf's class is its kind's (a
   module address is an integer value, a stack storage's base is its
   allocated offset); a var with no synthetic identity asks the
   denotation. *)
let address_leaves ~(denote : blk:blk term -> ?def:def term -> exp ->
                     (Cbat_clp_set_composite.t, Type.error) Result.t)
    ~(storages : Hike_synth.storage_span list)
    ~(blk : blk term) ~(def : def term) (e : exp) : leaf Var.Map.t =
  (object
     inherit [ leaf Var.Map.t ] Exp.visitor
     method! visit_var v acc =
       let by_denotation () =
         match denote ~blk ~def (Bil.Var v) with
         | Ok ws
           when (not
                   (Cbat_clp_set_composite.is_top ws
                   || Cbat_clp_set_composite.is_bottom ws))
                && Cbat_clp_set_composite.in_stack_segment ws ->
           (* A Vla-origin value's offsets are frame-relative —
              read them off the value, never the entry-line hull. *)
           let off =
             match Cbat_clp_set_composite.origin ws with
             | Some (Cbat_clp_set_composite.Origin.Vla _) -> (
                 match Cbat_clp_set_composite.vla_offsets ws with
                 | Some offs -> Model.singleton_offset offs
                 | None -> None)
             | _ -> (
                 match Cbat_clp_set_composite.stack_offsets ws with
                 | Some offs -> Model.singleton_offset offs
                 | None -> None)
           in
           Core.Map.set acc ~key:v
             ~data:(match off with Some k -> `Static k | None -> `Addr)
         | Ok ws
           when not
                  (Cbat_clp_set_composite.is_top ws
                  || Cbat_clp_set_composite.is_bottom ws) ->
           Core.Map.set acc ~key:v ~data:`Int
         | Ok _ | Error _ -> acc
       in
       match Hike_synth.classify Hike_synth.empty v with
       | Some (Hike_synth.Module_addr _) ->
         Core.Map.set acc ~key:v ~data:`Int
       | Some (Hike_synth.Storage (Hike_synth.Stack id)) -> (
         match Hike_synth.span_of_storage storages (Hike_synth.Stack id) with
         | Some s ->
           Core.Map.set acc ~key:v
             ~data:
               (`Static
                  (Stdlib.Int64.sub s.Hike_synth.ss_lo Model.segment_base))
         | None -> by_denotation ())
       | _ -> by_denotation ()
   end)#visit_exp e Var.Map.empty
