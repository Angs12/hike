(* The FP temp widths are the lifter's, never a table's: one intrinsic
   temp name serves several widths and a var's identity is type-blind,
   so the width must be in the name.  Every temp occurrence is qualified
   by its own width and each mapped FP call's target names its operand
   width; no later pass resolves one. *)

open Bap.Std
open Bap.Std.Bil.Types

(* The FP model's operand and result temps: [intrinsic:xN] /
   [intrinsic:yN], any number of them. *)
let is_temp (n : string) : bool =
  let rest p =
    let lp = String.length p in
    if Core.String.is_prefix n ~prefix:p && String.length n > lp then
      Some (String.sub n lp (String.length n - lp))
    else None
  in
  let digits s = Core.String.for_all s ~f:Core.Char.is_digit in
  match rest "intrinsic:x" with
  | Some d -> digits d
  | None -> ( match rest "intrinsic:y" with Some d -> digits d | None -> false)

(* A temp's identity carries its width. *)
let qualify (v : var) : var =
  match Var.typ v with
  | Type.Imm w when is_temp (Var.name v) ->
      let nv =
        Var.create ~is_virtual:false ~fresh:false
          (Bil2llvm_fp.temp_name (Var.name v) w)
          (Type.Imm w)
      in
      Var.with_index nv (Var.index v)
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
                 | Type.Imm w when is_temp (Var.name l) -> cur := w
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
                  match Bil2llvm_fp.native_fp_op name with
                  | Some _
                    when Base.Option.is_none
                           (Bil2llvm_fp.fp_width_of_name name) -> (
                      let w =
                        Base.Option.value
                          (Core.Map.find !widths (Term.tid j))
                          ~default:64
                      in
                      match Bil2llvm_fp.sized_name name w with
                      | Some sized ->
                          Jmp.with_kind j
                            (Call
                               (Call.with_target c
                                  (Direct (Tid.for_name sized))))
                      | None -> j)
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
      Term.map def_t blk ~f:(fun d ->
          Def.with_lhs
            (Def.with_rhs d (m#map_exp (Def.rhs d)))
            (qualify (Def.lhs d)))
      |> Term.map phi_t ~f:(fun p ->
             Phi.with_lhs (Phi.map_exp p ~f:m#map_exp) (qualify (Phi.lhs p)))
      |> Term.map jmp_t ~f:(Jmp.map_exp ~f:m#map_exp))

let run_program (prog : program term) : program term =
  Term.map sub_t prog ~f:(fun sub -> qualify_sub (tag_targets sub))
