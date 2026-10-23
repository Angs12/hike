open Core

type real = Float16 | Float | Double | Long_double

type scalar =
  | Bool | Char | Short | Int | Long | Long_long | Pointer
  | Real of real
  | Float128
  | Decimal32 | Decimal64 | Decimal128
  | Int128
  | M64 | M128 | M256 | M512

type ctype =
  | Scalar of scalar
  | Complex of real
  | Aggregate of aggregate

and aggregate = {
  size : int;
  align : int;
  fields : field list;
  trivial : bool;
}

and field = { offset : int; ty : ctype }

(* ---- sizes ---- *)

let real_size = function
  | Float16 -> 2 | Float -> 4 | Double -> 8 | Long_double -> 16

let scalar_size = function
  | Bool | Char -> 1
  | Short -> 2
  | Int -> 4
  | Long | Long_long | Pointer -> 8
  | Real r -> real_size r
  | Float128 | Decimal128 | Int128 | M128 -> 16
  | Decimal32 -> 4
  | Decimal64 | M64 -> 8
  | M256 -> 32
  | M512 -> 64

let rec size_of = function
  | Scalar s -> scalar_size s
  | Complex r -> 2 * real_size r
  | Aggregate a -> a.size

and align_of = function
  | Scalar s -> scalar_size s
  | Complex r -> real_size r
  | Aggregate a -> a.align

let array elem ~count =
  let size = size_of elem in
  Aggregate
    { size = count * size;
      align = align_of elem;
      fields = List.init count ~f:(fun i -> { offset = i * size; ty = elem });
      trivial = true }

(* ---- S-expressions ---- *)

let reals =
  [ ("Float16", Float16); ("Float", Float); ("Double", Double);
    ("Long_double", Long_double) ]

let scalars =
  [ ("Bool", Bool); ("Char", Char); ("Short", Short); ("Int", Int);
    ("Long", Long); ("Long_long", Long_long); ("Pointer", Pointer);
    ("Float128", Float128); ("Decimal32", Decimal32);
    ("Decimal64", Decimal64); ("Decimal128", Decimal128);
    ("Int128", Int128); ("M64", M64); ("M128", M128); ("M256", M256);
    ("M512", M512) ]
  @ List.map reals ~f:(fun (name, r) -> (name, Real r))

let name_of table v =
  fst (List.find_exn table ~f:(fun (_, x) -> Poly.equal x v))

let record_fields sexp =
  match sexp with
  | Sexp.List items ->
    List.map items ~f:(function
        | Sexp.List [ Sexp.Atom key; value ] -> (key, value)
        | _ -> Sexplib0.Sexp_conv.of_sexp_error "expected (key value)" sexp)
  | Sexp.Atom _ -> Sexplib0.Sexp_conv.of_sexp_error "expected a record" sexp

let int_of_sexp = Sexplib0.Sexp_conv.int_of_sexp
let bool_of_sexp = Sexplib0.Sexp_conv.bool_of_sexp

let rec ctype_of_sexp sexp =
  match sexp with
  | Sexp.Atom name ->
    (match List.Assoc.find scalars name ~equal:String.equal with
     | Some s -> Scalar s
     | None ->
       Sexplib0.Sexp_conv.of_sexp_error ("unknown type " ^ name) sexp)
  | Sexp.List [ Sexp.Atom "Complex"; Sexp.Atom name ] ->
    (match List.Assoc.find reals name ~equal:String.equal with
     | Some r -> Complex r
     | None ->
       Sexplib0.Sexp_conv.of_sexp_error ("unknown complex base " ^ name) sexp)
  | Sexp.List [ Sexp.Atom "Aggregate"; record ] -> Aggregate (aggregate_of_sexp record)
  | _ -> Sexplib0.Sexp_conv.of_sexp_error "unknown type" sexp

and aggregate_of_sexp sexp =
  let fields = record_fields sexp in
  let get key =
    match List.Assoc.find fields key ~equal:String.equal with
    | Some v -> v
    | None -> Sexplib0.Sexp_conv.of_sexp_error ("missing " ^ key) sexp in
  let size = int_of_sexp (get "size") in
  let align = int_of_sexp (get "align") in
  let members =
    match get "fields" with
    | Sexp.List items -> List.map items ~f:field_of_sexp
    | atom -> Sexplib0.Sexp_conv.of_sexp_error "expected a field list" atom in
  let trivial =
    match List.Assoc.find fields "trivial" ~equal:String.equal with
    | Some v -> bool_of_sexp v
    | None -> true in
  { size; align; fields = members; trivial }

and field_of_sexp sexp =
  let fields = record_fields sexp in
  let get key =
    match List.Assoc.find fields key ~equal:String.equal with
    | Some v -> v
    | None -> Sexplib0.Sexp_conv.of_sexp_error ("missing " ^ key) sexp in
  { offset = int_of_sexp (get "offset"); ty = ctype_of_sexp (get "ty") }

let rec sexp_of_ctype = function
  | Scalar s -> Sexp.Atom (name_of scalars s)
  | Complex r -> Sexp.(List [ Atom "Complex"; Atom (name_of reals r) ])
  | Aggregate a ->
    let open Sexp in
    List [ Atom "Aggregate";
           List [ List [ Atom "size"; Atom (Int.to_string a.size) ];
                  List [ Atom "align"; Atom (Int.to_string a.align) ];
                  List [ Atom "fields";
                         List (List.map a.fields ~f:(fun f ->
                             List [ List [ Atom "offset"; Atom (Int.to_string f.offset) ];
                                    List [ Atom "ty"; sexp_of_ctype f.ty ] ])) ];
                  List [ Atom "trivial"; Atom (Bool.to_string a.trivial) ] ] ]

(* ---- classification ---- *)

type eightbyte = Integer | Sse | Sse_up | X87 | X87_up | No_class

type classification =
  | Memory
  | Invisible_reference
  | Complex_x87
  | Eightbytes of eightbyte list

(* The eightbyte classes of a basic type. *)
let scalar_classes = function
  | Bool | Char | Short | Int | Long | Long_long | Pointer -> [ Integer ]
  | Int128 -> [ Integer; Integer ]
  | Real (Float16 | Float | Double) | Decimal32 | Decimal64 | M64 -> [ Sse ]
  | Float128 | Decimal128 | M128 -> [ Sse; Sse_up ]
  | M256 -> Sse :: List.init 3 ~f:(fun _ -> Sse_up)
  | M512 -> Sse :: List.init 7 ~f:(fun _ -> Sse_up)
  | Real Long_double -> [ X87; X87_up ]

(* The scalar and complex leaves of a type with their offsets from
   [base]; a complex type other than long double is two reals. *)
let rec leaves base = function
  | Scalar _ as t -> [ (base, t) ]
  | Complex Long_double as t -> [ (base, t) ]
  | Complex r ->
    [ (base, Scalar (Real r)); (base + real_size r, Scalar (Real r)) ]
  | Aggregate a ->
    List.concat_map a.fields ~f:(fun f -> leaves (base + f.offset) f.ty)

(* What an eightbyte holds while the fields sharing it are merged. *)
type slot = Empty | In_memory | Class of eightbyte

(* The merge of two classes sharing an eightbyte (psABI 3.2.3, 4). *)
let merge a b =
  match a, b with
  | _ when Poly.equal a b -> a
  | Empty, x | x, Empty -> x
  | In_memory, _ | _, In_memory -> In_memory
  | Class Integer, _ | _, Class Integer -> Class Integer
  | Class (X87 | X87_up), _ | _, Class (X87 | X87_up) -> In_memory
  | _ -> Class Sse

let complex_as_aggregate r =
  { size = 2 * real_size r; align = real_size r; trivial = true;
    fields = [ { offset = 0; ty = Scalar (Real r) };
               { offset = real_size r; ty = Scalar (Real r) } ] }

(* The post-merger cleanup (psABI 3.2.3, 5) of an aggregate of [size]
   bytes whose eightbytes merged to [slots]; [None] is MEMORY. *)
let post_merge ~size (slots : slot list) : eightbyte list option =
  let classes =
    List.map slots ~f:(function Class c -> c | Empty | In_memory -> No_class) in
  let preceded p i = i > 0 && p (List.nth_exn classes (i - 1)) in
  let memory = List.exists slots ~f:(Poly.equal In_memory) in
  let x87_up_orphan =
    List.existsi classes ~f:(fun i c ->
        Poly.equal c X87_up && not (preceded (Poly.equal X87) i)) in
  let bad_vector =
    size > 16
    && (not (Poly.equal (List.hd_exn classes) Sse)
        || List.exists (List.tl_exn classes) ~f:(fun c -> not (Poly.equal c Sse_up))) in
  if memory || x87_up_orphan || bad_vector then None
  else
    Some
      (List.mapi classes ~f:(fun i c ->
           if Poly.equal c Sse_up
           && not (preceded (fun p -> Poly.equal p Sse || Poly.equal p Sse_up) i)
           then Sse else c))

(* The eightbyte classes a type places at absolute eightbyte indices when
   it starts [base] bytes into the object being classified; [None] when
   the type is MEMORY.  An aggregate classifies each field recursively,
   merges what the fields place in each eightbyte, and cleans up its own
   eightbytes. *)
let rec placed ~base = function
  | Scalar s ->
    Some (List.mapi (scalar_classes s) ~f:(fun i c -> ((base / 8) + i, c)))
  | Complex Long_double -> None
  | Complex r -> placed ~base (Aggregate (complex_as_aggregate r))
  | Aggregate a ->
    if not a.trivial then None
    else
      let fields =
        List.map a.fields ~f:(fun f -> placed ~base:(base + f.offset) f.ty) in
      if List.exists fields ~f:Option.is_none then None
      else
        let first = base / 8 in
        let count = if a.size = 0 then 0 else ((base + a.size - 1) / 8) - first + 1 in
        let slots = Array.create ~len:count Empty in
        let outside = ref false in
        List.iter (List.concat (List.filter_opt fields)) ~f:(fun (index, c) ->
            let i = index - first in
            if i < 0 || i >= count then outside := true
            else slots.(i) <- merge slots.(i) (Class c));
        if !outside then None
        else
          Option.map (post_merge ~size:a.size (Array.to_list slots))
            ~f:(List.mapi ~f:(fun i c -> (first + i, c)))

(* A complex or aggregate type: MEMORY when over eight eightbytes or
   holding an unaligned field (psABI 3.2.3, 1), else its merged classes. *)
let classify_top t =
  let size = size_of t in
  let unaligned =
    List.exists (leaves 0 t) ~f:(fun (offset, ty) ->
        offset % align_of ty <> 0 || offset + size_of ty > size) in
  if size > 64 || unaligned then Memory
  else
    match placed ~base:0 t with
    | None -> Memory
    | Some classes -> Eightbytes (List.map classes ~f:snd)

let classify = function
  | Scalar s -> Eightbytes (scalar_classes s)
  | Complex Long_double -> Complex_x87
  | Complex _ as t -> classify_top t
  | Aggregate a as t -> if a.trivial then classify_top t else Invisible_reference

(* ---- placement ---- *)

type register_part =
  | Integer_register of int
  | Vector_register of { index : int; eightbytes : int }

type location =
  | Registers of register_part list
  | Stack of { offset : int; size : int }
  | Nowhere

type argument = { location : location; indirect : bool }

type return_part =
  | Integer_return of int
  | Vector_return of { index : int; eightbytes : int }
  | X87_return
  | X87_complex_return

type return_location =
  | Void
  | Returned_in of return_part list
  | Returned_in_memory

type call = {
  return : return_location;
  arguments : argument list;
  vector_registers_used : int;
  integer_registers_used : int;
  stack_size : int;
}

let integer_registers = 6
let vector_registers = 8

let round_up value ~to_ = (value + to_ - 1) / to_ * to_

(* A register an eightbyte lands in. *)
type assigned =
  | Integer_slot of int
  | Vector_slot of { index : int; eightbytes : int }

(* Assigns eightbytes to registers, given the counts already taken: an
   INTEGER eightbyte takes the next integer register, an SSE eightbyte a
   fresh vector register that the SSEUP eightbytes after it extend. *)
let assign eightbytes ~ints ~vectors =
  let parts, ints, vectors =
    List.fold eightbytes ~init:([], ints, vectors)
      ~f:(fun (parts, ints, vectors) c ->
          match c, parts with
          | Integer, _ -> (Integer_slot ints :: parts, ints + 1, vectors)
          | Sse, _ ->
            (Vector_slot { index = vectors; eightbytes = 1 } :: parts, ints,
             vectors + 1)
          | Sse_up, Vector_slot { index; eightbytes } :: rest ->
            (Vector_slot { index; eightbytes = eightbytes + 1 } :: rest, ints,
             vectors)
          | (Sse_up | X87 | X87_up | No_class), _ -> (parts, ints, vectors)) in
  (List.rev parts, ints, vectors)

let has_x87 eightbytes = List.exists eightbytes ~f:(Poly.equal X87)

let place_return = function
  | None -> Void
  | Some ty ->
    (match classify ty with
     | Memory | Invisible_reference -> Returned_in_memory
     | Complex_x87 -> Returned_in [ X87_complex_return ]
     | Eightbytes ebs when has_x87 ebs -> Returned_in [ X87_return ]
     | Eightbytes ebs ->
       (match assign ebs ~ints:0 ~vectors:0 with
        | [], _, _ -> Void
        | parts, _, _ ->
          Returned_in
            (List.map parts ~f:(function
                 | Integer_slot i -> Integer_return i
                 | Vector_slot { index; eightbytes } ->
                   Vector_return { index; eightbytes }))))

let place_call ~return arguments =
  let return_location = place_return return in
  let first_integer =
    match return_location with Returned_in_memory -> 1 | _ -> 0 in
  let on_stack (ints, vectors, stack) ~size ~align ~indirect =
    let offset = round_up stack ~to_:(Int.max 8 align) in
    let size = round_up size ~to_:8 in
    ((ints, vectors, offset + size),
     { location = Stack { offset; size }; indirect }) in
  let (ints, vectors, stack), placed =
    List.fold_map arguments ~init:(first_integer, 0, 0)
      ~f:(fun ((ints, vectors, stack) as state) ty ->
          let in_memory () =
            on_stack state ~size:(size_of ty) ~align:(align_of ty) ~indirect:false in
          match classify ty with
          | Invisible_reference ->
            if ints < integer_registers then
              ((ints + 1, vectors, stack),
               { location = Registers [ Integer_register ints ]; indirect = true })
            else on_stack state ~size:8 ~align:8 ~indirect:true
          | Memory | Complex_x87 -> in_memory ()
          | Eightbytes ebs when has_x87 ebs -> in_memory ()
          | Eightbytes ebs ->
            let wanted_ints = List.count ebs ~f:(Poly.equal Integer) in
            let wanted_vectors = List.count ebs ~f:(Poly.equal Sse) in
            if List.for_all ebs ~f:(Poly.equal No_class) then
              (state, { location = Nowhere; indirect = false })
            else if ints + wanted_ints > integer_registers
                 || vectors + wanted_vectors > vector_registers
            then in_memory ()
            else
              let parts, ints, vectors = assign ebs ~ints ~vectors in
              ((ints, vectors, stack),
               { location =
                   Registers
                     (List.map parts ~f:(function
                          | Integer_slot i -> Integer_register i
                          | Vector_slot { index; eightbytes } ->
                            Vector_register { index; eightbytes }));
                 indirect = false })) in
  { return = return_location; arguments = placed;
    vector_registers_used = vectors; integer_registers_used = ints;
    stack_size = stack }
