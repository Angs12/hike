(* The variadic pass: a sub whose lifted body holds the va_list
   construction is stamped variadic, so the emitter defines it as a real
   LLVM variadic and attribution keeps only the stack argument reach its
   accesses require. *)

open Bap.Std
open Bap.Std.Bil.Types
module Abi = Hike_abi
module Model = Hike_stack_model


(* The lifted va_list construction: the incoming parameter registers
   stored into the sub's own frame (the reg_save_area) beside a pointer
   at/above the entry args base stored into the frame (the
   overflow_arg_area).  The construction is the proof — a sub that
   merely carries the same registers is not variadic.  The [al] guard
   around the vector spills corroborates and is not required.  Frame
   positions and the register set come from the denotation and [Abi]. *)
let is_construction ~(abi : Abi.t) ~(entry : int64)
    ~(denote : blk:blk term -> ?def:def term -> exp ->
               (Cbat_clp_set_composite.t, Type.error) Result.t)
    (sub : sub term) : bool =
  let word = abi.Abi.word in
  let a_base = Model.args_base ~entry ~word in
  let params = abi.Abi.int_param_regs @ abi.Abi.vector_param_regs in
  (* A failed denotation cannot prove the construction, so the sub stays
     unstamped.  That is an ABI under-approximation, not a false variadic:
     a false positive would change the emitted convention. *)
  let positions ~blk ~def (e : exp) : (int64 * int64) option =
    match denote ~blk ~def e with
    | Error err ->
      Hike_diag.debug ~tag:"hike-dbg-variadic" (fun () ->
          Printf.sprintf "denotation failed: %s" (Type.Error.to_string err));
      None
    | Ok ws -> Model.positions_of_offsets ws
  in
  let in_frame ~blk ~def (e : exp) : bool =
    match positions ~blk ~def e with
    | Some (lo, hi) ->
        Int64.compare lo hi <= 0 && Int64.compare hi (Int64.pred entry) <= 0
    | None -> false
  in
  let stores_overflow ~blk ~def (d : def term) : bool =
    match Model.addr_of_rhs (Def.rhs d) with
    | Some (addr, _) when in_frame ~blk ~def addr -> (
        match Model.store_data_of_rhs (Def.rhs d) with
        | Some data -> (
            match positions ~blk ~def data with
            | Some (dlo, dhi) ->
                Int64.compare dlo a_base >= 0 && Int64.compare dlo dhi <= 0
            | None -> false)
        | None -> false)
    | _ -> false
  in
  let stored_params ~blk ~def (d : def term) : Var.Set.t =
    match Model.addr_of_rhs (Def.rhs d) with
    | Some (addr, _) when in_frame ~blk ~def addr -> (
        match Model.store_data_of_rhs (Def.rhs d) with
        | None -> Var.Set.empty
        | Some data ->
            let free = Exp.free_vars data in
            Base.List.fold params ~init:Var.Set.empty ~f:(fun acc r ->
                if Core.Set.exists free ~f:(fun v -> Var.same v r) then
                  Core.Set.add acc (Var.base r)
                else acc))
    | _ -> Var.Set.empty
  in
  let overflow, regs =
    Term.enum blk_t sub
    |> Seq.fold ~init:(false, Var.Set.empty) ~f:(fun (ov, regs) blk ->
           Term.enum def_t blk
           |> Seq.fold ~init:(ov, regs) ~f:(fun (ov, regs) d ->
                  ( ov || stores_overflow ~blk ~def:d d,
                    Core.Set.union regs (stored_params ~blk ~def:d d) )))
  in
  (* The register-save bound: the reg_save_area saves more parameter
     registers (integer and vector together) than half the integer
     count, regardless of their individual use, where an ordinary sub
     stores only the args it reads.  A sub whose named args consume
     every integer register saves only its vector registers. *)
  overflow
  && Core.Set.length regs > Base.List.length abi.Abi.int_param_regs / 2

let tag : unit Value.Tag.t =
  Value.Tag.register ~package:"hike" ~name:"hike-variadic"
    ~uuid:"7b2d4c9e-1a35-4f80-9c62-5e8d0f3a1b47"
    (module Core.Unit)

let is_variadic (sub : sub term) : bool = Term.has_attr sub tag

(* A fixed-signature sub (@main, an emittable intrinsic) carries a
   convention of its own, never the ABI's, so it is not a variadic
   definition however its body is built. *)
let stamp ~(abi : Abi.t) ~(entry : int64)
    ~(denote : blk:blk term -> ?def:def term -> exp ->
               (Cbat_clp_set_composite.t, Type.error) Result.t)
    (prog : program term) : program term =
  Term.map sub_t prog ~f:(fun sub ->
      if (not (Model.fixed_signature sub))
         && is_construction ~abi ~entry ~denote sub
      then Term.set_attr sub tag ()
      else sub)
