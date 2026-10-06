(* The FP temp widths are the lifter's, never a table's: one intrinsic
   temp name serves several widths and a var's identity is type-blind,
   so the width must be in the name.  Every temp occurrence is qualified
   by its own width and each mapped FP call's target names its operand
   width; no later pass resolves one. *)

open Bap.Std
open Bap.Std.Bil.Types

(* The FP model's operand and result temps: [intrinsic:xN] /
   [intrinsic:yN], any number of them. *)
let temp_lane v =
  match Hike_synth.classify Hike_synth.empty v with
  | Some (Hike_synth.Fp_lane (lane, i)) -> Some (lane, i)
  | _ -> None

(* A temp's identity carries its width. *)
let qualify v =
  match Var.typ v, temp_lane v with
  | Type.Imm w, Some (lane, i) ->
    Var.with_index (Hike_synth.fp_lane ~addr_bits:w lane i) (Var.index v)
  | _ -> v

(* A mapped FP call's target names its operand width: the nearest
   preceding temp def in term order.  The sized spelling is the table's
   own, so no consumer resolves a width. *)
let tag_targets (sub : sub term) : sub term =
  Term.map blk_t sub ~f:(fun blk ->
      let widths = ref Tid.Map.empty in
      let cur = ref 64 in
      Blk.elts blk
      |> Seq.iter ~f:(fun elt ->
             match elt with
             | `Def d -> (
                 let l = Def.lhs d in
                 match Var.typ l with
                 | Type.Imm w when Option.is_some (temp_lane l) -> cur := w
                 | _ -> ())
             | `Jmp j ->
                 widths := Core.Map.set !widths ~key:(Term.tid j) ~data:!cur
             | `Phi _ -> ());
      Term.map jmp_t blk ~f:(fun j ->
          match Jmp.kind j with
          | Call c -> (
              match Call.target c with
              | Direct t -> (
                  let name = Tid.name t in
                  match Hike_native_fp.native_fp_op name with
                  | Some _ -> (
                      (* [widths] is total over the block's jmps — every
                         jmp elt records the width in effect there. *)
                      let w = Core.Map.find_exn !widths (Term.tid j) in
                      match Hike_native_fp.sized_name name w with
                      | Some sized ->
                          Jmp.with_kind j
                            (Call
                               (Call.with_target c
                                  (Direct (Tid.for_name sized))))
                      | None ->
                          (* No sized row at the temp's width: the
                             unqualified target stays.  An op with sized
                             rows at other widths says so — the residue
                             is the recorded word-width fallback; an op
                             with none (the runtime boundary) keeps the
                             unqualified spelling as its identity. *)
                          if Hike_native_fp.has_sized_rows name then
                            Hike_diag.warn
                              "fp: sub %s: intrinsic %s has no sized spelling at width %d - the unqualified target stays"
                              (Sub.name sub) name w;
                          j)
                  | _ -> j)
              | _ -> j)
          | _ -> j))

(* Every occurrence of a temp, defs and reads alike. *)
let qualify_sub (sub : sub term) : sub term =
  let m =
    object
      inherit Exp.mapper
      method! map_sym v = qualify v
    end
  in
  Term.map blk_t sub ~f:(fun blk ->
      Blk.map_elts
        ~def:(fun d ->
            Def.with_lhs
              (Def.with_rhs d (m#map_exp (Def.rhs d)))
              (qualify (Def.lhs d)))
        ~jmp:(Jmp.map_exp ~f:m#map_exp)
        ~phi:(fun p ->
            Phi.with_lhs (Phi.map_exp p ~f:m#map_exp) (qualify (Phi.lhs p)))
        blk)

let run_program (prog : program term) : program term =
  Term.map sub_t prog ~f:(fun sub -> qualify_sub (tag_targets sub))
