(* Emitter FP lane: the native render arms.  The op vocabulary, its
   sized spellings and the lane signatures live in [Hike_native_fp]
   (the lower core library); this module only lowers them to LLVM. *)

open Bap.Std
module Abi = Hike_abi
open Bil2llvm_env
open Bil2llvm_exp
open Bil2llvm_access

include Hike_native_fp

(* The float type of a lane width and its integer lane: single, double
   or x87 extended. *)
let fp_ty_of (llvm_ctx : Llvm.llcontext) (w : int) :
    Llvm.lltype * Llvm.lltype =
  if w <= 32 then (Llvm.float_type llvm_ctx, Llvm.i32_type llvm_ctx)
  else if w <= 64 then (Llvm.double_type llvm_ctx, Llvm.i64_type llvm_ctx)
  else (Llvm.x86fp80_type llvm_ctx, Llvm.integer_type llvm_ctx 80)

(* An FP operand is an integer lane holding the value's bits. *)
let bitcast_to_fp llvm_builder v fp_ty =
  Llvm.build_bitcast v fp_ty "" llvm_builder

(* A one-operand LLVM math intrinsic ([llvm.<name>.fN]) at width [w]. *)
let fp_intrinsic ctx llvm_builder name ~(w : int) (xf : Llvm.llvalue) =
  let fp_ty, _ = fp_ty_of ctx.llvm_ctx w in
  let suffix = if w <= 32 then "f32" else if w <= 64 then "f64" else "f80" in
  let fty = Llvm.function_type fp_ty [| fp_ty |] in
  let f =
    Llvm.declare_function (Printf.sprintf "llvm.%s.%s" name suffix) fty
      ctx.llvm_module
  in
  Llvm.build_call fty f [| xf |] "" llvm_builder

(* x86's float-to-integer conversion: [rne] rounds to nearest-even
   first, [rtz] truncates; an unordered or out-of-range source answers
   the integer indefinite (the most negative value), where LLVM's
   [fptosi] would be poison. *)
let build_fp_to_int ctx llvm_builder (rnd : rounding) (xf : Llvm.llvalue)
    ~(src_w : int) ~(res_w : int) : Llvm.llvalue =
  let llvm_ctx = ctx.llvm_ctx in
  let fp_ty, _ = fp_ty_of llvm_ctx src_w in
  let xf =
    match rnd with
    | Rtz -> xf
    | Rne -> fp_intrinsic ctx llvm_builder "roundeven" ~w:src_w xf
  in
  let int_ty = Llvm.integer_type llvm_ctx res_w in
  let bound = Float.ldexp 1.0 (res_w - 1) in
  let lo = Llvm.const_float fp_ty (-. bound) in
  let hi = Llvm.const_float fp_ty bound in
  let in_range =
    Llvm.build_and
      (Llvm.build_fcmp Llvm.Fcmp.Oge xf lo "" llvm_builder)
      (Llvm.build_fcmp Llvm.Fcmp.Olt xf hi "" llvm_builder)
      "" llvm_builder
  in
  let i = Llvm.build_fptosi xf int_ty "" llvm_builder in
  let indefinite =
    Llvm.const_of_int64 int_ty (Int64.shift_left 1L (res_w - 1)) true in
  Llvm.build_select in_range i indefinite "" llvm_builder

let build_fp_binop ctx llvm_builder op a b ~(w : int) =
  let fp_ty, ret_ty = fp_ty_of ctx.llvm_ctx w in
  let da = bitcast_to_fp llvm_builder a fp_ty in
  let db = bitcast_to_fp llvm_builder b fp_ty in
  let d =
    match op with
    | FMUL -> Llvm.build_fmul da db "" llvm_builder
    | FADD -> Llvm.build_fadd da db "" llvm_builder
    | FSUB -> Llvm.build_fsub da db "" llvm_builder
    | FDIV -> Llvm.build_fdiv da db "" llvm_builder
    | FREM -> Llvm.build_frem da db "" llvm_builder
    | _ -> assert false
  in
  Llvm.build_bitcast d ret_ty "" llvm_builder

(* Operand defs of a block indexed by base var, last def wins. *)
let temp_defs_of_blk (blk : blk term) : def term Var.Map.t =
  Term.enum def_t blk
  |> Seq.fold ~init:Var.Map.empty ~f:(fun m d ->
         Core.Map.set m ~key:(Var.base (Def.lhs d)) ~data:d)

(* The x87 register stack in the thread's state cell: ST(i) is physical
   register (top + i) mod 8; a push decrements the top, a pop increments
   it, and the valid bits follow them. *)
module X87 = struct
  let i8 ctx = Llvm.i8_type ctx.llvm_ctx
  let i32 ctx = Llvm.i32_type ctx.llvm_ctx
  let lane_w = 80

  let cell ctx =
    Core.Map.find_exn !(ctx.synth_vals)
      (Hike_synth.x87_state ~addr_bits:ctx.addr_bits)

  let field ctx b i =
    Llvm.build_struct_gep (x87_state_type ctx) (cell ctx) i "" b

  let load_byte ctx b i = Llvm.build_load (i8 ctx) (field ctx b i) "" b
  let store_byte ctx b i v = ignore (Llvm.build_store v (field ctx b i) b)
  let top ctx b = load_byte ctx b 1
  let byte ctx n = Llvm.const_int (i8 ctx) n
  let mod8 ctx b v = Llvm.build_and v (byte ctx 7) "" b

  let register ctx b phys =
    Llvm.build_in_bounds_gep (x87_state_type ctx) (cell ctx)
      [| Llvm.const_int (i32 ctx) 0; Llvm.const_int (i32 ctx) 0;
         Llvm.build_zext phys (i32 ctx) "" b |] "" b

  let lane_ty ctx = snd (fp_ty_of ctx.llvm_ctx lane_w)

  (* ST(i) for an index lane of any width. *)
  let st_ptr ctx b i =
    let i = Llvm.build_trunc_or_bitcast i (i8 ctx) "" b in
    register ctx b (mod8 ctx b (Llvm.build_add (top ctx b) i "" b))

  let st ctx b i = Llvm.build_load (lane_ty ctx) (st_ptr ctx b i) "" b
  let set_st ctx b i v = ignore (Llvm.build_store v (st_ptr ctx b i) b)
  let st0 ctx = byte ctx 0

  let bit ctx b phys = Llvm.build_shl (byte ctx 1) phys "" b

  let push ctx b v =
    let t = mod8 ctx b (Llvm.build_sub (top ctx b) (byte ctx 1) "" b) in
    store_byte ctx b 1 t;
    ignore (Llvm.build_store v (register ctx b t) b);
    store_byte ctx b 2 (Llvm.build_or (load_byte ctx b 2) (bit ctx b t) "" b)

  let pop ctx b =
    let t = top ctx b in
    let v = Llvm.build_load (lane_ty ctx) (register ctx b t) "" b in
    store_byte ctx b 2
      (Llvm.build_and (load_byte ctx b 2)
         (Llvm.build_not (bit ctx b t) "" b) "" b);
    store_byte ctx b 1 (mod8 ctx b (Llvm.build_add t (byte ctx 1) "" b));
    v

  let fp ctx b v = bitcast_to_fp b v (fst (fp_ty_of ctx.llvm_ctx lane_w))
  let lane ctx b f = Llvm.build_bitcast f (lane_ty ctx) "" b

  (* A memory operand as an extended value, exactly. *)
  let extend ctx b (format : x87_format) x =
    let x = coerce_int_width ctx.llvm_ctx b ~bits:(Bil2llvm_int.width x) x
        (x87_format_bits format) in
    let ext_ty = fst (fp_ty_of ctx.llvm_ctx lane_w) in
    match format with
    | F 80 -> x
    | F w ->
      lane ctx b
        (Llvm.build_fpext (bitcast_to_fp b x (fst (fp_ty_of ctx.llvm_ctx w)))
           ext_ty "" b)
    | I _ -> lane ctx b (Llvm.build_sitofp x ext_ty "" b)

  (* The control word's rounding (bits 10-11): nearest-even, down, up,
     toward zero. *)
  let round ctx b control xf =
    let rc =
      Llvm.build_and
        (Llvm.build_lshr control (Llvm.const_int (Llvm.type_of control) 10) "" b)
        (Llvm.const_int (Llvm.type_of control) 3) "" b in
    let is n = Llvm.build_icmp Llvm.Icmp.Eq rc
        (Llvm.const_int (Llvm.type_of control) n) "" b in
    let by name = fp_intrinsic ctx b name ~w:lane_w xf in
    Llvm.build_select (is 0) (by "roundeven")
      (Llvm.build_select (is 1) (by "floor")
         (Llvm.build_select (is 2) (by "ceil") (by "trunc") "" b) "" b) "" b

  (* An extended value in a memory operand's format. *)
  let narrow ctx b (format : x87_format) ~(control : Llvm.llvalue option) v =
    match format with
    | F 80 -> v
    | F w ->
      let fp_ty, lane_ty = fp_ty_of ctx.llvm_ctx w in
      Llvm.build_bitcast (Llvm.build_fptrunc (fp ctx b v) fp_ty "" b) lane_ty "" b
    | I w ->
      let xf = fp ctx b v in
      let xf = match control with Some c -> round ctx b c xf | None -> xf in
      build_fp_to_int ctx b Rtz xf ~src_w:lane_w ~res_w:w

  (* The tag word: two bits per physical register, empty (3), zero (1),
     special (2: NaN, infinity, denormal, unsupported) or valid (0). *)
  let tag_word ctx b =
    let i16 = Llvm.i16_type ctx.llvm_ctx in
    let i80 = lane_ty ctx in
    let k n = Llvm.const_of_int64 i80 n false in
    let valid = load_byte ctx b 2 in
    Base.List.fold (Base.List.init 8 ~f:Fun.id) ~init:(Llvm.const_int i16 0)
      ~f:(fun acc p ->
          let r = Llvm.build_load i80 (register ctx b (byte ctx p)) "" b in
          let exp = Llvm.build_and (Llvm.build_lshr r (k 64L) "" b) (k 0x7fffL) "" b in
          let mant = Llvm.build_and r (k (-1L)) "" b in
          let eq a n = Llvm.build_icmp Llvm.Icmp.Eq a (k n) "" b in
          let integer_bit = Llvm.build_lshr r (k 63L) "" b in
          let zero = Llvm.build_and (eq exp 0L) (eq mant 0L) "" b in
          let special =
            Llvm.build_or (Llvm.build_or (eq exp 0L) (eq exp 0x7fffL) "" b)
              (eq (Llvm.build_and integer_bit (k 1L) "" b) 0L) "" b in
          let held =
            Llvm.build_icmp Llvm.Icmp.Ne
              (Llvm.build_and valid (bit ctx b (byte ctx p)) "" b) (byte ctx 0) "" b in
          let tag =
            Llvm.build_select held
              (Llvm.build_select zero (Llvm.const_int i16 1)
                 (Llvm.build_select special (Llvm.const_int i16 2)
                    (Llvm.const_int i16 0) "" b) "" b)
              (Llvm.const_int i16 3) "" b in
          Llvm.build_or acc (Llvm.build_shl tag (Llvm.const_int i16 (2 * p)) "" b) "" b)

  (* The 28-byte environment image: control word, status word with the
     top index, tag word; the pointer fields are zero. *)
  let store_env ctx b control =
    let i224 = Llvm.integer_type ctx.llvm_ctx 224 in
    let at v sh =
      Llvm.build_shl (Llvm.build_zext v i224 "" b) (Llvm.const_int i224 sh) "" b in
    let status =
      Llvm.build_shl
        (Llvm.build_zext (top ctx b) (Llvm.i16_type ctx.llvm_ctx) "" b)
        (Llvm.const_int (Llvm.i16_type ctx.llvm_ctx) 11) "" b in
    let image =
      Llvm.build_or (at control 0)
        (Llvm.build_or (at status 32) (at (tag_word ctx b) 64) "" b) "" b in
    let masked = Llvm.build_or control (Llvm.const_int (Llvm.type_of control) 0x3f) "" b in
    [ masked; image ]

  let load_env ctx b image =
    let field sh w =
      Llvm.build_trunc
        (Llvm.build_lshr image (Llvm.const_int (Llvm.type_of image) sh) "" b)
        (Llvm.integer_type ctx.llvm_ctx w) "" b in
    let status = field 32 16 and tags = field 64 16 in
    store_byte ctx b 1
      (mod8 ctx b
         (Llvm.build_trunc
            (Llvm.build_lshr status (Llvm.const_int (Llvm.type_of status) 11) "" b)
            (i8 ctx) "" b));
    let valid =
      Base.List.fold (Base.List.init 8 ~f:Fun.id) ~init:(byte ctx 0) ~f:(fun acc p ->
          let tag =
            Llvm.build_and
              (Llvm.build_lshr tags (Llvm.const_int (Llvm.type_of tags) (2 * p)) "" b)
              (Llvm.const_int (Llvm.type_of tags) 3) "" b in
          let held =
            Llvm.build_icmp Llvm.Icmp.Ne tag (Llvm.const_int (Llvm.type_of tags) 3) "" b in
          Llvm.build_or acc
            (Llvm.build_select held (bit ctx b (byte ctx p)) (byte ctx 0) "" b) "" b) in
    store_byte ctx b 2 valid;
    [ field 0 16 ]

  (* The op's effect on the state and its result lanes, in [fp_rets]
     order. *)
  let lower ctx b (op : x87) ~(arg : int -> Llvm.llvalue) : Llvm.llvalue list =
    let unary f = set_st ctx b (st0 ctx) (lane ctx b (f (fp ctx b (st ctx b (st0 ctx))))) in
    let constant c = lane ctx b (Llvm.const_float (fst (fp_ty_of ctx.llvm_ctx lane_w)) c) in
    match op with
    | Push format -> push ctx b (extend ctx b format (arg 0)); []
    | Push_zero -> push ctx b (constant 0.0); []
    | Push_one -> push ctx b (constant 1.0); []
    | Push_st -> push ctx b (st ctx b (arg 0)); []
    | Store { pop = popped; format; truncate } ->
      let control = match format, truncate with
        | I _, false -> Some (arg 0)
        | _ -> None in
      let v = if popped then pop ctx b else st ctx b (st0 ctx) in
      [ narrow ctx b format ~control v ]
    | Store_st { pop = popped } ->
      set_st ctx b (arg 0) (st ctx b (st0 ctx));
      if popped then ignore (pop ctx b : Llvm.llvalue);
      []
    | Arith { op; reversed; operand; pop = popped } ->
      let dst, src = match operand with
        | St0_sti -> (st0 ctx, st ctx b (arg 0))
        | Sti_st0 -> (arg 0, st ctx b (st0 ctx))
        | Memory format -> (st0 ctx, extend ctx b format (arg 0)) in
      let d = st ctx b dst in
      let x, y = if reversed then (src, d) else (d, src) in
      set_st ctx b dst (build_fp_binop ctx b (x87_arith_op op) x y ~w:lane_w);
      if popped then ignore (pop ctx b : Llvm.llvalue);
      []
    | Chs -> unary (fun x -> Llvm.build_fneg x "" b); []
    | Abs -> unary (fp_intrinsic ctx b "fabs" ~w:lane_w); []
    | Sqrt -> unary (fp_intrinsic ctx b "sqrt" ~w:lane_w); []
    | Rndint -> unary (round ctx b (arg 0)); []
    | Xch ->
      let a = st ctx b (st0 ctx) and c = st ctx b (arg 0) in
      set_st ctx b (st0 ctx) c;
      set_st ctx b (arg 0) a;
      []
    | Compare { ordered = _; pop = popped } ->
      let a = fp ctx b (st ctx b (st0 ctx)) and c = fp ctx b (st ctx b (arg 0)) in
      let cmp p = Llvm.build_fcmp p a c "" b in
      let unordered = cmp Llvm.Fcmp.Uno in
      let flags =
        [ Llvm.build_or unordered (cmp Llvm.Fcmp.Oeq) "" b;
          unordered;
          Llvm.build_or unordered (cmp Llvm.Fcmp.Olt) "" b ] in
      if popped then ignore (pop ctx b : Llvm.llvalue);
      flags
    | Store_env -> store_env ctx b (arg 0)
    | Load_env -> load_env ctx b (arg 0)
end

let create_native_fp_call ctx scope llvm_builder blk_tid blk call op =
  match op with
  | FHLT ->
      (* Halt traps without binding results or emitting fallthrough. *)
      create_interrupt ctx llvm_builder
  | FMUL | FADD | FSUB | FDIV | FREM | SFLOAT _ | SINT _ | FCONVERT _ | FORDER
   | ISNAN | FSQRT | X87 _ ->
  let llvm_ctx = ctx.llvm_ctx in
  let fallthrough = Option.map label_tid (Call.return call) in
  let target = Call.target call |> label_tid in
  let word_bits = Hike_abi.word_bits ctx.abi in
  let temp_defs = temp_defs_of_blk blk in
  let sig_ =
    fp_sig_of op
      ~w:(lane_width_of_name ~word_bits (Tid.name target))
  in
  let arg_value (i : int) : Llvm.llvalue =
    (* The [intrinsic:xN] temp the block defined IS the operand; it
       routes through the memory dispatch, so a converted operand
       materializes in its own world. *)
    let av = Base.List.nth_exn sig_.fp_args i in
    as_int ctx llvm_builder
      (match Core.Map.find temp_defs av with
       | Some d ->
           mem_access ctx scope llvm_builder blk_tid
             (Hike_def_slots.sec_tag d) d (Def.rhs d)
       | None ->
           (* A versioned operand may be defined outside this block; the
              SSA binding is the authority.  An unbound temp freezes
              undef. *)
           create_exp ctx scope llvm_builder blk_tid (Bil.Var av))
  in
  let w_of = Bil2llvm_int.width in
  let results =
    match op with
    | X87 x -> X87.lower ctx llvm_builder x ~arg:arg_value
    | _ -> [ match op with
    | FMUL | FADD | FSUB | FDIV | FREM ->
        let a = arg_value 0 in
        let b = arg_value 1 in
        let w = min (w_of a) (w_of b) in
        build_fp_binop ctx llvm_builder op a b ~w
    | SFLOAT res_w ->
        (* [sitofp] converts at the operand's own LLVM type (the
           lifter's extract/cast chain built it). *)
        let x = arg_value 0 in
        let tgt_fp_ty, tgt_lane_ty = fp_ty_of llvm_ctx res_w in
        let d = Llvm.build_sitofp x tgt_fp_ty "" llvm_builder in
        Llvm.build_bitcast d tgt_lane_ty "" llvm_builder
    | SINT (rnd, res_w) ->
        let x = arg_value 0 in
        let src_w = Bil2llvm_int.width x in
        let src_fp_ty, _ = fp_ty_of llvm_ctx src_w in
        let d = Llvm.build_bitcast x src_fp_ty "" llvm_builder in
        build_fp_to_int ctx llvm_builder rnd d ~src_w ~res_w
    | FCONVERT res_w ->
        let x = arg_value 0 in
        let in_w = conv_in_w op in
        let x =
          coerce_int_width llvm_ctx llvm_builder
            ~bits:(Bil2llvm_int.width x) x in_w
        in
        let src_fp_ty, _ = fp_ty_of llvm_ctx in_w in
        let tgt_fp_ty, tgt_lane_ty = fp_ty_of llvm_ctx res_w in
        let xf = bitcast_to_fp llvm_builder x src_fp_ty in
        let d =
          if res_w > in_w
          then Llvm.build_fpext xf tgt_fp_ty "" llvm_builder
          else Llvm.build_fptrunc xf tgt_fp_ty "" llvm_builder
        in
        Llvm.build_bitcast d tgt_lane_ty "" llvm_builder
    | FORDER ->
        let a = arg_value 0 in
        let b = arg_value 1 in
        let w = min (w_of a) (w_of b) in
        let src_fp_ty, _ = fp_ty_of llvm_ctx w in
        Llvm.build_fcmp Llvm.Fcmp.Olt
          (bitcast_to_fp llvm_builder a src_fp_ty)
          (bitcast_to_fp llvm_builder b src_fp_ty)
          "" llvm_builder
    | ISNAN ->
        let x = arg_value 0 in
        let w = Bil2llvm_int.width x in
        let src_fp_ty, _ = fp_ty_of llvm_ctx w in
        let xf = bitcast_to_fp llvm_builder x src_fp_ty in
        Llvm.build_fcmp Llvm.Fcmp.Uno xf xf "" llvm_builder
    | FSQRT ->
        let x = arg_value 0 in
        let w = Bil2llvm_int.width x in
        let fp_ty, lane_ty = fp_ty_of llvm_ctx w in
        let d =
          fp_intrinsic ctx llvm_builder "sqrt" ~w
            (bitcast_to_fp llvm_builder x fp_ty)
        in
        Llvm.build_bitcast d lane_ty "" llvm_builder
    | FHLT | X87 _ ->
        (* Unreachable: the outer matches handle halt and x87. *)
        assert false ]
  in
  (* Ret temps bind the call's written version: the SSA
     pass minted one per call, so every read downstream resolves. *)
  Base.List.iter2_exn sig_.fp_rets results ~f:(fun ret result ->
      let rw =
        match Var.typ ret with
        | Type.Imm w -> w
        | _ ->
            failwith
              (Printf.sprintf
                 "hike-emit: FP return temp %s is not an immediate lane"
                 (Var.name ret))
      in
      let r_lane =
        coerce_int_width llvm_ctx llvm_builder
          ~bits:(Bil2llvm_int.width result) result rw in
      let arg = Arg.create ret (Bil.Var ret) in
      bind_call_ret ctx scope blk_tid arg (Bil2llvm_value.Int r_lane));
  finish_call scope llvm_builder fallthrough
