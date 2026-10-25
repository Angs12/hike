(* The native-FP intrinsic vocabulary: the mapped ops, the width each
   spelling names, and each op's lane signature.  Pure identities and
   lane facts — the LLVM rendering stays in the emitter. *)

open Bap.Std

(* A float-to-integer conversion's rounding, as the lifter names it:
   [rne] for the rounding conversions, [rtz] for the truncating ones. *)
type rounding = Rne | Rtz

(* An x87 memory operand's format: a binary float or a signed integer
   of the given width; [F 80] is the extended format itself. *)
type x87_format = F of int | I of int

(* The second operand of an x87 arithmetic op: [St0_sti] writes ST0,
   [Sti_st0] writes ST(i), a memory operand writes ST0. *)
type x87_operand = St0_sti | Sti_st0 | Memory of x87_format

type x87_arith = Add | Sub | Mul | Div

type native_fp = FMUL | FADD | FSUB | FDIV | FREM
               | SFLOAT of int | SINT of rounding * int
               | FCONVERT of int | FORDER | FHLT | ISNAN | FSQRT
               | X87 of x87

(* The x87 ops: each acts on the thread's x87 register stack, ST(i)
   counted from the top.  [Store] of an integer rounds by the control
   word unless it truncates; [reversed] arithmetic swaps the operands. *)
and x87 =
  | Push of x87_format
  | Push_zero
  | Push_one
  | Push_st
  | Store of { pop : bool; format : x87_format; truncate : bool }
  | Store_st of { pop : bool }
  | Arith of { op : x87_arith; reversed : bool; operand : x87_operand; pop : bool }
  | Chs
  | Abs
  | Sqrt
  | Rndint
  | Xch
  | Compare of { ordered : bool; pop : bool }
  | Store_env
  | Load_env

let fp_intrinsic_name = Hike_abi.strip_at

(* The FP temps' identity carries their width: the lifter uses one name
   ([intrinsic:x0]) for a single- AND a double-precision operand, and
   BAP's var identity is type-blind, so the width must be in the name.
   [hike-fp] qualifies every occurrence. *)

(* The integer conversions: the lifter's suffix is the RESULT width (the
   constructor's argument); [hike-fp] appends the operand width, which
   is independent of the result's. *)
let conversion_rows : (string * native_fp * int option) list =
  Base.List.concat_map
    [ ("cast_sfloat_rne", fun r -> SFLOAT r);
      ("cast_sint_rne", fun r -> SINT (Rne, r));
      ("cast_sint_rtz", fun r -> SINT (Rtz, r)) ]
    ~f:(fun (stem, op) ->
        Base.List.concat_map [ 64; 32 ] ~f:(fun res ->
            let name = Printf.sprintf "intrinsic:%s_ieee754_binary_%d" stem res in
            (name, op res, None)
            :: Base.List.map [ 64; 32 ] ~f:(fun w ->
                (Printf.sprintf "%s_%d" name w, op res, Some w))))

let x87_format_bits = function F w | I w -> w

(* The native op an x87 arithmetic op computes. *)
let x87_arith_op = function Add -> FADD | Sub -> FSUB | Mul -> FMUL | Div -> FDIV

let x87_format_name = function
  | F w -> Printf.sprintf "f%d" w
  | I w -> Printf.sprintf "i%d" w

(* The lifter's spelling of an x87 op. *)
let x87_name (op : x87) : string =
  let fmt = x87_format_name in
  let pop_word pop = if pop then "pop" else "store" in
  "intrinsic:x87_"
  ^
  match op with
  | Push f -> "push_" ^ fmt f
  | Push_zero -> "push_zero"
  | Push_one -> "push_one"
  | Push_st -> "push_st"
  | Store { pop; format; truncate } ->
    Printf.sprintf "%s%s_%s" (pop_word pop) (if truncate then "_trunc" else "")
      (fmt format)
  | Store_st { pop } -> pop_word pop ^ "_st"
  | Arith { op; reversed; operand; pop } ->
    let name = match op with
      | Add -> "fadd" | Sub -> "fsub" | Mul -> "fmul" | Div -> "fdiv" in
    Printf.sprintf "%s%s%s_%s" name (if reversed then "r" else "")
      (if pop then "p" else "")
      (match operand with
       | St0_sti -> "st0_sti"
       | Sti_st0 -> "sti_st0"
       | Memory f -> fmt f)
  | Chs -> "fchs"
  | Abs -> "fabs"
  | Sqrt -> "fsqrt"
  | Rndint -> "frndint"
  | Xch -> "fxch"
  | Compare { ordered; pop } ->
    Printf.sprintf "f%scomi%s" (if ordered then "" else "u") (if pop then "p" else "")
  | Store_env -> "fnstenv"
  | Load_env -> "fldenv"

(* Every x87 op the lifter emits. *)
let x87_ops : x87 list =
  let floats = [ F 32; F 64; F 80 ] and ints = [ I 16; I 32; I 64 ] in
  let arith =
    Base.List.concat_map [ Add; Sub; Mul; Div ] ~f:(fun op ->
        Base.List.concat_map
          (match op with Sub | Div -> [ false; true ] | Add | Mul -> [ false ])
          ~f:(fun reversed ->
              Base.List.map
                ([ (St0_sti, false); (Sti_st0, false); (Sti_st0, true) ]
                 @ Base.List.map [ F 32; F 64; I 16; I 32 ] ~f:(fun f -> (Memory f, false)))
                ~f:(fun (operand, pop) -> Arith { op; reversed; operand; pop }))) in
  Base.List.map (floats @ ints) ~f:(fun f -> Push f)
  @ [ Push_zero; Push_one; Push_st ]
  @ Base.List.map (floats @ ints) ~f:(fun format ->
      Store { pop = true; format; truncate = false })
  @ Base.List.map [ F 32; F 64; I 16; I 32 ] ~f:(fun format ->
      Store { pop = false; format; truncate = false })
  @ Base.List.map ints ~f:(fun format -> Store { pop = true; format; truncate = true })
  @ [ Store_st { pop = true }; Store_st { pop = false } ]
  @ arith
  @ [ Chs; Abs; Sqrt; Rndint; Xch ]
  @ Base.List.concat_map [ true; false ] ~f:(fun ordered ->
      Base.List.map [ false; true ] ~f:(fun pop -> Compare { ordered; pop }))
  @ [ Store_env; Load_env ]

let x87_rows : (string * native_fp * int option) list =
  Base.List.map x87_ops ~f:(fun op -> (x87_name op, X87 op, None))

(* One row per mapped intrinsic name, with the operand width it names.
   The unsized spellings ([_binary]) carry none: the lifter picks the
   width per instruction, and [hike-fp] rewrites the target to the sized
   spelling before any consumer reads it.  The table intentionally keeps
   both [forder_rne] and bare [forder] spellings plus the runtime-boundary
   rows; the duplicates are compatibility, not dead data. *)
let native_fp_table : (string * native_fp * int option) list =
  [ ("intrinsic:fmul_rne_ieee754_binary_64", FMUL, Some 64);
    ("intrinsic:fmul_rne_ieee754_binary_32", FMUL, Some 32);
    ("intrinsic:fadd_rne_ieee754_binary_64", FADD, Some 64);
    ("intrinsic:fadd_rne_ieee754_binary_32", FADD, Some 32);
    ("intrinsic:fsub_rne_ieee754_binary_64", FSUB, Some 64);
    ("intrinsic:fsub_rne_ieee754_binary_32", FSUB, Some 32);
    ("intrinsic:fdiv_rne_ieee754_binary_64", FDIV, Some 64);
    ("intrinsic:fdiv_rne_ieee754_binary_32", FDIV, Some 32);
    ("intrinsic:frem_rne_ieee754_binary_64", FREM, Some 64);
    ("intrinsic:frem_rne_ieee754_binary_32", FREM, Some 32);
    ("intrinsic:forder_rne_ieee754_binary_64", FORDER, Some 64);
    ("intrinsic:forder_rne_ieee754_binary_32", FORDER, Some 32);
    ("intrinsic:forder_ieee754_binary_64", FORDER, Some 64);
    ("intrinsic:forder_ieee754_binary_32", FORDER, Some 32);
    ("intrinsic:is_nan_rne_ieee754_binary_64", ISNAN, Some 64);
    ("intrinsic:is_nan_rne_ieee754_binary_32", ISNAN, Some 32);
    ("intrinsic:is_nan_ieee754_binary_64", ISNAN, Some 64);
    ("intrinsic:is_nan_ieee754_binary_32", ISNAN, Some 32);
    (* Exact width conversions: the suffix is the result width. *)
    ("intrinsic:fconvert_rne_ieee754_binary_64", FCONVERT 64, Some 64);
    ("intrinsic:fconvert_rne_ieee754_binary_32", FCONVERT 32, Some 32);
    (* The untagged spellings the lifter emits: [hike-fp] rewrites them
       to one of the sized rows above. *)
    ("intrinsic:fmul_rne_ieee754_binary", FMUL, None);
    ("intrinsic:fadd_rne_ieee754_binary", FADD, None);
    ("intrinsic:fsub_rne_ieee754_binary", FSUB, None);
    ("intrinsic:fdiv_rne_ieee754_binary", FDIV, None);
    ("intrinsic:frem_rne_ieee754_binary", FREM, None);
    ("intrinsic:forder_rne_ieee754_binary", FORDER, None);
    ("intrinsic:fsqrt_rne_ieee754_binary_64", FSQRT, Some 64);
    ("intrinsic:fsqrt_rne_ieee754_binary_32", FSQRT, Some 32);
    ("intrinsic:fsqrt_rne_ieee754_binary", FSQRT, None);
    ("intrinsic:is_nan_rne_ieee754_binary", ISNAN, None);
    ("intrinsic:is_nan_ieee754_binary", ISNAN, None);
    ("intrinsic:forder_ieee754_binary", FORDER, None);
    ("intrinsic:hlt", FHLT, None) ]
  @ conversion_rows
  @ x87_rows

(* The table as a hash map, built once: call dispatch consults it
   per call site per sub. *)
let native_fp_map =
  let t = Core.String.Table.create () in
  Base.List.iter native_fp_table ~f:(fun (k, v, w) ->
      Core.Hashtbl.set t ~key:k ~data:(v, w));
  t

let row_of_name (name : string) : (native_fp * int option) option =
  Core.Hashtbl.find native_fp_map (fp_intrinsic_name name)

let native_fp_op (name : string) : native_fp option =
  Core.Option.map (row_of_name name) ~f:fst

(* The ONE lane-width policy for a mapped call: the width the target
   names, the target word when the spelling stayed unqualified.  Only
   rows with no sized spelling (the runtime boundary) reach the word
   fallback; a sized-row miss is refused by Hike_fp, including the
   80-bit class.  Every consumer of a mapped call's widths reads this. *)
let lane_width_of_name ~(word_bits : int) (name : string) : int =
  let named = Core.Option.bind (row_of_name name) ~f:snd in
  Base.Option.value named ~default:word_bits

(* The bare sized spelling of an untagged FP target, when the table
   knows it: the name [hike-fp] rewrites the target to. *)
let sized_name (name : string) (w : int) : string option =
  let sized = Printf.sprintf "%s_%d" (fp_intrinsic_name name) w in
  if Core.Hashtbl.mem native_fp_map sized then Some sized else None

(* Whether the table carries sized spellings for the op at all.  The
   width-less rows without one (the runtime boundary) keep the
   unqualified spelling as their identity; a miss at the temp's width is
   then structural, not a residue. *)
let has_sized_rows (name : string) : bool =
  let bare = fp_intrinsic_name name in
  Base.List.exists native_fp_table ~f:(fun (n, _, _) ->
      let n = fp_intrinsic_name n in
      Base.String.is_prefix n ~prefix:bare
      && String.length n > String.length bare
      && n.[String.length bare] = '_')

(* The lifter's own lane temps, before [hike-fp] gives them a width: the
   vars its intrinsic semantics write before and read after a call.  They
   are born outside Hike, so the lifter's vocabulary is declared here:
   operands [intrinsic:x0..x3], results [intrinsic:y0..y2]. *)
let lifter_lanes : (Hike_synth.lane * int) Var.Map.t =
  let lane kind c i =
    Var.create ~is_virtual:false ~fresh:false (Printf.sprintf "intrinsic:%c%d" c i)
      (Type.Imm 64), (kind, i)
  in
  Core.Map.of_alist_exn (module Var)
    (Base.List.init 4 ~f:(lane Hike_synth.Input 'x')
     @ Base.List.init 3 ~f:(lane Hike_synth.Output 'y'))

let lifter_lane (v : Var.t) : (Hike_synth.lane * int) option =
  Core.Map.find lifter_lanes (Var.base v)

(* The static model interface of each mapped op: the input temps the
   call block defines (fp_args) and the result temps consumers read
   (fp_rets); FCONVERT w reads x0 at the complementary width.  An x87
   op's ST(i) index is a word ([w]); the control word is 16 bits; a
   compare answers ZF, PF and CF; the environment image is 28 bytes. *)
type fp_sig = { fp_args : Var.t list; fp_rets : Var.t list }

(* The complementary FP input width of a conversion (fpext widens,
   fptrunc narrows); the identity for the non-conversion ops. *)
let conv_in_w = function
  | FCONVERT res_w -> if res_w = 64 then 32 else 64
  | _ -> 64

let fp_sig_of (op : native_fp) ~(w : int) : fp_sig =
  let x0 k = Hike_synth.fp_lane ~addr_bits:k Hike_synth.Input 0 in
  let y0 k = Hike_synth.fp_lane ~addr_bits:k Hike_synth.Output 0 in
  match op with
  | FMUL | FADD | FSUB | FDIV | FREM ->
    { fp_args = [ x0 w; Hike_synth.fp_lane ~addr_bits:w Hike_synth.Input 1 ];
      fp_rets = [ y0 w ] }
  (* The predicates answer one bit. *)
  | FORDER ->
    { fp_args = [ x0 w; Hike_synth.fp_lane ~addr_bits:w Hike_synth.Input 1 ];
      fp_rets = [ y0 1 ] }
  | ISNAN -> { fp_args = [ x0 w ]; fp_rets = [ y0 1 ] }
  | FSQRT -> { fp_args = [ x0 w ]; fp_rets = [ y0 w ] }
  | SFLOAT res_w | SINT (_, res_w) ->
    { fp_args = [ x0 w ]; fp_rets = [ y0 res_w ] }
  | FCONVERT res_w ->
    { fp_args = [ x0 (conv_in_w op) ];
      fp_rets = [ y0 res_w ] }
  | FHLT -> { fp_args = []; fp_rets = [] }
  | X87 op ->
    let x k i = Hike_synth.fp_lane ~addr_bits:k Hike_synth.Input i in
    let y k i = Hike_synth.fp_lane ~addr_bits:k Hike_synth.Output i in
    let index = [ x w 0 ] and control = [ x 16 0 ] in
    let fp_args, fp_rets = match op with
      | Push f -> ([ x (x87_format_bits f) 0 ], [])
      | Push_zero | Push_one | Chs | Abs | Sqrt -> ([], [])
      | Push_st | Store_st _ | Xch -> (index, [])
      | Store { format = I _ as f; truncate = false; _ } ->
        (control, [ y (x87_format_bits f) 0 ])
      | Store { format; _ } -> ([], [ y (x87_format_bits format) 0 ])
      | Arith { operand = St0_sti | Sti_st0; _ } -> (index, [])
      | Arith { operand = Memory f; _ } -> ([ x (x87_format_bits f) 0 ], [])
      | Rndint -> (control, [])
      | Compare _ -> (index, [ y 1 0; y 1 1; y 1 2 ])
      | Store_env -> (control, [ y 16 0; y 224 1 ])
      | Load_env -> ([ x 224 0 ], [ y 16 0 ]) in
    { fp_args; fp_rets }
