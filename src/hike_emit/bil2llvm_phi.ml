(* BIR phis: every phi of a sub is created, empty, before any body is
   emitted, so a use in a block emitted ahead of its dominator (a rep
   loop's body before its head) still finds the sub-wide binding. *)

open Bap.Std
module Abi = Hike_abi
open Bil2llvm_env
open Bil2llvm_exp
open Bil2llvm_access

(* A BIR phi renders as the LLVM phi of its own lhs.  The type is the
   lhs's: the type pass makes a phi with a pointer incoming a pointer. *)
let create ctx scope blks =
  Seq.iter blks ~f:(fun blk ->
      let tid = Term.tid blk in
      let llvm_builder =
        Llvm.builder_at_end ctx.llvm_ctx (get_bb scope tid)
      in
      Term.enum phi_t blk
      |> Seq.iter ~f:(fun phi ->
          let var = Phi.lhs phi in
          let res =
            if var_is_ptr ctx var then
              Bil2llvm_value.Ptr (Llvm.build_empty_phi ctx.ptr_ty "" llvm_builder)
            else
              Bil2llvm_value.Int
                (Llvm.build_empty_phi (typ_lltype ctx (Var.typ var)) ""
                   llvm_builder)
          in
          insert_bir_phi scope tid var (Bil2llvm_value.ll res);
          insert_local scope tid var res;
          Base.Option.iter (Ssa_name.of_var var)
            ~f:(fun name -> bind_definition scope name res)))

(* One incoming per (source block, exp): the exp evaluates in the
   source block's context, before its terminator. *)
let fill ctx scope blks =
  let empty = ref [] in
  Seq.iter blks ~f:(fun blk ->
      let tid = Term.tid blk in
      Term.enum phi_t blk
      |> Seq.iter ~f:(fun phi ->
          let phi_ll =
            Base.Option.value_exn
              (get_bir_phi scope tid (Phi.lhs phi))
          in
          Phi.values phi
          |> Seq.iter ~f:(fun (src, exp) ->
              let src_bb =
                match get_bb_opt scope src with
                | Some bb -> bb
                | None ->
                  failwith
                    (Printf.sprintf
                       "hike: phi incoming from block %s, which is not a \
                        block of sub %s"
                       (Tid.name src)
                       (Tid.name (Term.tid (Seq.hd_exn blks))))
              in
              let copies =
                match Llvm.block_terminator src_bb with
                | None -> 0
                | Some term ->
                  Array.fold_left (fun n bb ->
                      if Stdlib.(bb = get_bb scope tid) then n + 1 else n)
                    0 (Llvm.successors term)
              in
              if copies > 0 then begin
              let src_b =
                match Llvm.block_terminator src_bb with
                | Some t -> Llvm.builder_before ctx.llvm_ctx t
                | None -> Llvm.builder_at_end ctx.llvm_ctx src_bb
              in
              let value =
                match exp with
                | Bil.Var v -> (
                    match resolve_ssa scope src v with
                    | Some value -> value
                    | None -> create_exp ctx scope src_b src exp)
                | _ -> create_exp ctx scope src_b src exp
              in
              (* The incoming takes the phi's type. *)
              let phi_is_ptr =
                match resolve_ssa scope tid (Phi.lhs phi) with
                | Some (Bil2llvm_value.Ptr _) -> true
                | _ -> false
              in
              let value =
                Bil2llvm_value.ll
                  (Bil2llvm_value.coerce ~addr_bits:ctx.addr_bits src_b
                     ~ptr:phi_is_ptr value)
              in
              (* An environment register's phi also stores each
                 incoming to the process-global cell at its own source
                 block — whichever edge runs leaves its value there. *)
              if Abi.is_env_reg ctx.abi (Phi.lhs phi) then
                ignore (Llvm.build_store value (env_global ctx (Phi.lhs phi)) src_b);
              for _ = 1 to copies do Llvm.add_incoming (value, src_bb) phi_ll done
              end);
          if Base.List.is_empty (Llvm.incoming phi_ll) then empty := phi_ll :: !empty));
  (* Constant branches can leave a BIR block without emitted predecessors.
     Replace its empty phis after every incoming has been wired. *)
  Base.List.iter !empty ~f:(fun phi ->
      Llvm.replace_all_uses_with phi (Llvm.poison (Llvm.type_of phi));
      Llvm.delete_instruction phi)
