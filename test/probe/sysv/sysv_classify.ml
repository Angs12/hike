(* The System V placement of signatures read from stdin, as tokens.

   Input: S-expressions (case ((return TYPE)? (params (TYPE ...)))).
   Output, one line per case:  <return tokens> | <argument tokens>
   with  I = integer register eightbyte, S = vector register (an SSE
   eightbyte and its SSEUPs), X = x87, M = memory, V = no value.  A
   scalar passed on the stack keeps its class tokens; an aggregate or
   complex value on the stack is M.  The compiler oracle
   (test/gate/sysv_oracle.py) compares this with clang's lowering. *)

open Core

let tokens_of_class = function
  | Hike_sysv.Integer -> "I"
  | Sse -> "S"
  | Sse_up | No_class -> ""
  | X87 -> "X"
  | X87_up -> ""

let class_tokens ty =
  match Hike_sysv.classify ty with
  | Hike_sysv.Eightbytes ebs -> String.concat (List.map ebs ~f:tokens_of_class)
  | Complex_x87 -> "X"
  | Memory | Invisible_reference -> "M"

(* clang writes an aggregate of at most one eightbyte, passed on the stack
   once the integer registers are gone, as a plain integer: the same
   8-byte slot, a different spelling.  [integers_used] is the count of
   integer registers taken before the argument. *)
let argument_tokens ~integers_used (ty : Hike_sysv.ctype)
    (a : Hike_sysv.argument) =
  match a.location, ty with
  | Registers parts, _ ->
      String.concat
        (List.map parts ~f:(function
             | Hike_sysv.Integer_register _ -> "I"
             | Vector_register _ -> "S"))
  | Stack _, Scalar M64 -> "M"  (* clang spells it byval: an 8-byte slot *)
  | Stack _, Scalar _ -> class_tokens ty
  | Stack _, Aggregate agg
    when integers_used >= 6 && agg.size <= 8 && agg.align <= 8 -> "I"
  | Stack _, (Complex _ | Aggregate _) -> "M"
  | Nowhere, _ -> ""

let integer_parts (a : Hike_sysv.argument) =
  match a.location with
  | Registers parts ->
      List.count parts ~f:(function
          | Hike_sysv.Integer_register _ -> true
          | Vector_register _ -> false)
  | Stack _ | Nowhere -> 0

let return_tokens = function
  | Hike_sysv.Void -> "V"
  | Returned_in_memory -> "M"
  | Returned_in parts ->
      String.concat
        (List.map parts ~f:(function
             | Hike_sysv.Integer_return _ -> "I"
             | Vector_return _ -> "S"
             | X87_return -> "X"
             | X87_complex_return -> "XX"))

let case_of_sexp = function
  | Sexp.List fields ->
      let find key =
        List.find_map fields ~f:(function
            | Sexp.List [ Sexp.Atom k; v ] when String.equal k key -> Some v
            | _ -> None) in
      let return = Option.map (find "return") ~f:Hike_sysv.ctype_of_sexp in
      let params =
        match find "params" with
        | Some (Sexp.List items) -> List.map items ~f:Hike_sysv.ctype_of_sexp
        | _ -> [] in
      (return, params)
  | Sexp.Atom _ -> failwith "case: expected a record"

let () =
  let input = In_channel.input_all In_channel.stdin in
  List.iter (Sexp.of_string_many input) ~f:(fun sexp ->
      let return, params = case_of_sexp sexp in
      let call = Hike_sysv.place_call ~return params in
      let hidden =
        match call.return with Hike_sysv.Returned_in_memory -> 1 | _ -> 0 in
      let _, tokens =
        List.fold2_exn params call.arguments ~init:(hidden, [])
          ~f:(fun (used, acc) ty a ->
              ( used + integer_parts a,
                argument_tokens ~integers_used:used ty a :: acc )) in
      let args = String.concat (List.rev tokens) in
      Out_channel.output_string Out_channel.stdout
        (sprintf "%s | %s\n" (return_tokens call.return) args))
