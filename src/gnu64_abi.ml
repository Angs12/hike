open Base
open Decl_parser
open Bap.Std

type typeclass =
  | INT
  | SSE
  | SSEUP
  | X87
  | X87UP
  | COMPLEX_X87
  | NOCLASS
  | MEMORY

let rec arg_type_size (t : functype) : int =
  match t with
  | Void -> 0
  | Pointer -> 8
  | Int n -> n / 8
  | Half -> 4
  | Bfloat -> 8
  | Float -> 4
  | Double -> 8
  | FP128 -> 16
  | X86fp80 -> 10
  | PPCfp128 -> 16
  | X86amx -> 16
  | Struct ts -> List.fold ts ~init:0 ~f:(fun acc t -> acc + arg_type_size t)

(* let arg_aggregate_classification (ts : typeclass list) : typeclass = *)
(*   let classify cl1 cl2 = *)
(*     match (cl1, cl2) with *)
(*     | INT, INT -> INT *)
(*     | SSE, SSE -> SSE *)
(*     | SSEUP, SSEUP -> SSEUP *)
(*     | X87, X87 -> X87 *)
(*     | X87UP, X87UP -> X87UP *)
(*     | COMPLEX_X87, COMPLEX_X87 -> COMPLEX_X87 *)
(*     | NOCLASS, NOCLASS -> NOCLASS *)
(*     | MEMORY, MEMORY -> MEMORY *)
(*     | NOCLASS, _ -> cl2 *)
(*     | _, NOCLASS -> cl1 *)
(*     | MEMORY, _ -> MEMORY *)
(*     | _, MEMORY -> MEMORY *)
(*     | INT, _ -> INT *)
(*     | _, INT -> INT *)
(*     | X87UP, _ | X87, _ | COMPLEX_X87, _ -> MEMORY *)
(*     | _, X87UP | _, X87 | _, COMPLEX_X87 -> MEMORY *)
(*     | _ -> SSE *)
(*   in *)
(*   INT *)

let arg_type_classification (ts : functype list) : typeclass list =
  let classify t accum =
    match t with
    | Void -> accum
    | Pointer -> INT :: accum
    | Int n -> if n <= 64 then INT :: accum else SSE :: accum
    | Half -> SSE :: accum
    | Bfloat -> SSE :: accum
    | Float -> SSE :: accum
    | Double -> SSE :: accum
    | FP128 -> SSE :: SSEUP :: accum
    | X86fp80 -> X87 :: X87UP :: accum
    | PPCfp128 -> SSE :: SSEUP :: accum
    | X86amx -> INT :: accum (* TODO *)
    | Struct _ -> MEMORY :: accum (* TODO *)
  in
  List.fold_right ts ~init:[] ~f:classify

type regs_state = {
  avl_int_reg : var;
  avl_xmm_reg : var;
  avl_xmm_reg_offset : int;
}

let arg_regs (ts : functype list) : var list =
  let rdi = Var.create "RDI" (Imm 64) in
  let rsi = Var.create "RSI" (Imm 64) in
  let rdx = Var.create "RDX" (Imm 64) in
  let rcx = Var.create "RCX" (Imm 64) in
  let r8 = Var.create "R8" (Imm 64) in
  let r9 = Var.create "R9" (Imm 64) in
  let int_regs = ref [ rdi; rsi; rdx; rcx; r8; r9 ] in
  let xmm0 = Var.create "XMM0" (Imm 128) in
  let xmm1 = Var.create "XMM1" (Imm 128) in
  let vec_regs = ref [ xmm0; xmm1 ] in
  let regs_state =
    ref { avl_int_reg = rdi; avl_xmm_reg = xmm0; avl_xmm_reg_offset = 0 }
  in
  let cls = arg_type_classification ts in
  let is_sse = ref false in
  List.fold cls ~init:[] ~f:(fun acc t ->
      match t with
      | INT ->
          if !is_sse then (
            let new_reg = List.hd_exn !vec_regs in
            regs_state := { !regs_state with avl_xmm_reg = new_reg };
            regs_state := { !regs_state with avl_xmm_reg_offset = 0 });
          let new_reg = List.hd_exn !int_regs in
          regs_state := { !regs_state with avl_int_reg = new_reg };
          int_regs := List.tl_exn !int_regs;
          new_reg :: acc
      | MEMORY ->
          if !is_sse then (
            let new_reg = List.hd_exn !vec_regs in
            regs_state := { !regs_state with avl_xmm_reg = new_reg };
            regs_state := { !regs_state with avl_xmm_reg_offset = 0 });
          failwith "TODO add stack arguments"
      | SSE ->
          let new_reg = List.hd_exn !vec_regs in
          regs_state := { !regs_state with avl_xmm_reg = new_reg };
          regs_state := { !regs_state with avl_xmm_reg_offset = 64 };
          vec_regs := List.tl_exn !vec_regs;
          new_reg :: acc
      | SSEUP ->
          let reg = !regs_state.avl_xmm_reg in
          if !regs_state.avl_xmm_reg_offset = 64 then (
            regs_state := { !regs_state with avl_xmm_reg_offset = 128 };
            acc)
          else (*arg does not fit in xmm register *)
            (
            regs_state := { !regs_state with avl_xmm_reg_offset = 0 };
            vec_regs := reg :: !vec_regs;
            failwith "TODO add sseup arguments")
      | X87 | X87UP | COMPLEX_X87 ->
          if !is_sse then (
            let new_reg = List.hd_exn !vec_regs in
            regs_state := { !regs_state with avl_xmm_reg = new_reg };
            regs_state := { !regs_state with avl_xmm_reg_offset = 0 });
          failwith "TODO add x87 arguments"
      | NOCLASS -> acc)
  |> List.rev

let return_regs (t : functype) : var list =
  let cls = arg_type_classification [ t ] in
  let rax = Var.create "RAX" (Imm 64) in
  let rdx = Var.create "RDX" (Imm 64) in
  let xmm0 = Var.create "XMM0" (Imm 128) in
  (* let xmm1 = Var.create "XMM1" (Imm 128) in *)
  let st0 = Var.create "ST0" (Imm 80) in
  let st1 = Var.create "ST1" (Imm 80) in
  let regs_state =
    ref { avl_int_reg = rax; avl_xmm_reg = xmm0; avl_xmm_reg_offset = 0 }
  in
  List.fold cls ~init:[] ~f:(fun acc cl ->
      match cl with
      | INT ->
          let new_reg = !regs_state.avl_int_reg in
          regs_state := { !regs_state with avl_int_reg = rdx };
          new_reg :: acc
      | SSE ->
          let new_reg = !regs_state.avl_xmm_reg in
          regs_state := { !regs_state with avl_xmm_reg = new_reg };
          new_reg :: acc
      | SSEUP -> acc
      | X87 -> st0 :: acc
      | X87UP -> acc
      | COMPLEX_X87 -> st0 :: st1 :: acc
      | NOCLASS -> acc
      | MEMORY -> rax :: acc)
(* TODO *)
