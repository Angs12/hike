(* System V x86-64 classification and placement pins (psABI 3.2.3), each
   from a rule or a worked example of the specification. *)

open Hike_test.Harness
open Hike_sysv

let sc s = Scalar s
let real r = Scalar (Real r)
let int_ = sc Int and long = sc Long and ptr = sc Pointer
let double = real Double and float_ = real Float

let strukt ?(trivial = true) ~size ~align fields =
  Aggregate
    { size; align; trivial;
      fields = List.map (fun (offset, ty) -> { offset; ty }) fields }

let classes ty = classify ty

let eb l = Eightbytes l

let tests : unit Alcotest.test list =
  [
    pin "SV-01" "basic types take their natural classes" (fun () ->
        List.iter (fun s ->
            check "INTEGER" (classes (sc s) = eb [ Integer ]))
          [ Bool; Char; Short; Int; Long; Long_long; Pointer ];
        List.iter (fun ty ->
            check "SSE" (classes ty = eb [ Sse ]))
          [ real Float16; float_; double; sc Decimal32; sc Decimal64; sc M64 ];
        List.iter (fun s ->
            check "SSE, SSEUP" (classes (sc s) = eb [ Sse; Sse_up ]))
          [ Float128; Decimal128; M128 ];
        check "__m256 is SSE and three SSEUP"
          (classes (sc M256) = eb [ Sse; Sse_up; Sse_up; Sse_up ]);
        check "__m512 is SSE and seven SSEUP"
          (classes (sc M512) = eb (Sse :: List.init 7 (fun _ -> Sse_up)));
        check "long double is X87, X87UP"
          (classes (real Long_double) = eb [ X87; X87_up ]);
        check "__int128 is two INTEGER eightbytes"
          (classes (sc Int128) = eb [ Integer; Integer ]));

    pin "SV-02" "complex types are a pair of their base type" (fun () ->
        check "float complex fits one eightbyte"
          (classes (Complex Float) = eb [ Sse ]);
        check "_Float16 complex fits one eightbyte"
          (classes (Complex Float16) = eb [ Sse ]);
        check "double complex" (classes (Complex Double) = eb [ Sse; Sse ]);
        check "long double complex" (classes (Complex Long_double) = Complex_x87));

    pin "SV-03" "an aggregate's eightbytes merge their fields' classes" (fun () ->
        let s_int_double =
          strukt ~size:16 ~align:8 [ (0, int_); (4, int_); (8, double) ] in
        check "{int a, b; double d}" (classes s_int_double = eb [ Integer; Sse ]);
        check "INTEGER wins over SSE in one eightbyte"
          (classes (strukt ~size:8 ~align:4 [ (0, int_); (4, float_) ])
           = eb [ Integer ]);
        check "two floats stay SSE"
          (classes (strukt ~size:8 ~align:4 [ (0, float_); (4, float_) ])
           = eb [ Sse ]);
        check "{double, double}"
          (classes (strukt ~size:16 ~align:8 [ (0, double); (8, double) ])
           = eb [ Sse; Sse ]);
        check "{float x, y, z} is two SSE eightbytes"
          (classes (strukt ~size:12 ~align:4
                      [ (0, float_); (4, float_); (8, float_) ])
           = eb [ Sse; Sse ]);
        check "{long, double}"
          (classes (strukt ~size:16 ~align:8 [ (0, long); (8, double) ])
           = eb [ Integer; Sse ]);
        check "a nested aggregate contributes its leaves"
          (classes (strukt ~size:16 ~align:8
                      [ (0, strukt ~size:8 ~align:4 [ (0, int_); (4, int_) ]);
                        (8, double) ])
           = eb [ Integer; Sse ]);
        check "an array is its elements"
          (classes (array int_ ~count:4) = eb [ Integer; Integer ]));

    pin "SV-04" "an object larger than eight eightbytes, or unaligned, is MEMORY"
      (fun () ->
        check "72 bytes" (classes (array long ~count:9) = Memory);
        check "an unaligned (packed) field"
          (classes (strukt ~size:5 ~align:1 [ (0, sc Char); (1, int_) ]) = Memory);
        check "more than two eightbytes without a vector shape"
          (classes (array int_ ~count:5) = Memory);
        check "eight eightbytes of integers"
          (classes (array long ~count:8) = Memory));

    pin "SV-05" "a vector aggregate of SSE then SSEUPs is not MEMORY" (fun () ->
        check "{__m256}"
          (classes (strukt ~size:32 ~align:32 [ (0, sc M256) ])
           = eb [ Sse; Sse_up; Sse_up; Sse_up ]);
        check "{__m512}"
          (classes (strukt ~size:64 ~align:64 [ (0, sc M512) ])
           = eb (Sse :: List.init 7 (fun _ -> Sse_up)));
        check "two __m128 are MEMORY (the third eightbyte is not SSEUP)"
          (classes (strukt ~size:32 ~align:16 [ (0, sc M128); (16, sc M128) ])
           = Memory));

    pin "SV-06" "a union merges its members, X87 with anything else is MEMORY"
      (fun () ->
        check "union {int; float}"
          (classes (strukt ~size:4 ~align:4 [ (0, int_); (0, float_) ])
           = eb [ Integer ]);
        check "union {double; long}"
          (classes (strukt ~size:8 ~align:8 [ (0, double); (0, long) ])
           = eb [ Integer ]);
        check "union {long double; double}"
          (classes (strukt ~size:16 ~align:16 [ (0, real Long_double); (0, double) ])
           = Memory);
        check "{long double} alone keeps X87, X87UP"
          (classes (strukt ~size:16 ~align:16 [ (0, real Long_double) ])
           = eb [ X87; X87_up ]);
        check "{long double complex} member is MEMORY"
          (classes (strukt ~size:32 ~align:16 [ (0, Complex Long_double) ])
           = Memory));

    pin "SV-07" "an SSEUP not preceded by SSE becomes SSE" (fun () ->
        check "union {__m128; long}"
          (classes (strukt ~size:16 ~align:16 [ (0, sc M128); (0, long) ])
           = eb [ Integer; Sse ]));

    pin "SV-08" "an empty aggregate has no eightbytes and a non-trivial one is by reference"
      (fun () ->
        check "empty" (classes (strukt ~size:0 ~align:1 []) = eb []);
        check "non-trivial"
          (classes (strukt ~trivial:false ~size:8 ~align:8 [ (0, long) ])
           = Invisible_reference);
        check "non-trivial and large"
          (classes (strukt ~trivial:false ~size:128 ~align:8 [])
           = Invisible_reference));

    pin "SV-09"
      "the specification's example (Figures 3.5 and 3.6) is allocated as printed"
      (fun () ->
        let structparm =
          strukt ~size:16 ~align:8 [ (0, int_); (4, int_); (8, double) ] in
        let call =
          place_call ~return:None
            [ int_; int_; structparm; int_; int_; real Long_double; double;
              sc M256; sc M512; double; int_; int_; int_ ] in
        let ints i = { location = Registers [ Integer_register i ]; indirect = false }
        and vector index eightbytes =
          { location = Registers [ Vector_register { index; eightbytes } ];
            indirect = false }
        and stack offset size =
          { location = Stack { offset; size }; indirect = false } in
        let expected =
          [ ints 0;  (* e   -> %rdi *)
            ints 1;  (* f   -> %rsi *)
            { location =  (* s.a, s.b -> %rdx; s.d -> %xmm0 *)
                Registers [ Integer_register 2;
                            Vector_register { index = 0; eightbytes = 1 } ];
              indirect = false };
            ints 3;  (* g   -> %rcx *)
            ints 4;  (* h   -> %r8 *)
            stack 0 16;  (* ld  -> stack 0 *)
            vector 1 1;  (* m   -> %xmm1 *)
            vector 2 4;  (* y   -> %ymm2 *)
            vector 3 8;  (* z   -> %zmm3 *)
            vector 4 1;  (* n   -> %xmm4 *)
            ints 5;  (* i   -> %r9 *)
            stack 16 8;  (* j   -> stack 16 *)
            stack 24 8 ]  (* k   -> stack 24 *) in
        check "arguments" (call.arguments = expected);
        check "five vector registers are used" (call.vector_registers_used = 5);
        check "the stack holds ld, j and k" (call.stack_size = 32));

    pin "SV-10"
      "an argument with too few registers for any eightbyte goes whole to the stack and its registers are not consumed"
      (fun () ->
        let pair = strukt ~size:16 ~align:8 [ (0, long); (8, long) ] in
        let call =
          place_call ~return:None
            [ long; long; long; long; long; pair; long ] in
        check "the pair goes to the stack, the next integer takes %r9"
          ((List.nth call.arguments 5).location = Stack { offset = 0; size = 16 }
           && (List.nth call.arguments 6).location
              = Registers [ Integer_register 5 ]);
        let vectors = place_call ~return:None
            (List.init 7 (fun _ -> double)
             @ [ strukt ~size:16 ~align:8 [ (0, double); (8, double) ]; double ]) in
        check "the SSE pair goes to the stack, the next double takes %xmm7"
          ((List.nth vectors.arguments 7).location = Stack { offset = 0; size = 16 }
           && (List.nth vectors.arguments 8).location
              = Registers [ Vector_register { index = 7; eightbytes = 1 } ]));

    pin "SV-11" "X87 and MEMORY arguments go on the stack at their alignment"
      (fun () ->
        let call =
          place_call ~return:None
            (List.init 6 (fun _ -> long)
             @ [ int_; real Long_double; int_; Complex Long_double; long ]) in
        let at i = (List.nth call.arguments i).location in
        check "the seventh integer is the first stack word"
          (at 6 = Stack { offset = 0; size = 8 });
        check "long double aligns to 16"
          (at 7 = Stack { offset = 16; size = 16 });
        check "the next integer follows it"
          (at 8 = Stack { offset = 32; size = 8 });
        check "long double complex is MEMORY, 16-aligned, 32 bytes"
          (at 9 = Stack { offset = 48; size = 32 });
        check "the stack ends after the last word" (call.stack_size = 88));

    pin "SV-12" "a non-trivial object is passed as a pointer" (fun () ->
        let obj = strukt ~trivial:false ~size:24 ~align:8 [] in
        let call = place_call ~return:None [ obj ] in
        check "pointer in %rdi"
          (call.arguments
           = [ { location = Registers [ Integer_register 0 ]; indirect = true } ]));

    pin "SV-13" "an empty aggregate consumes nothing" (fun () ->
        let call =
          place_call ~return:None [ strukt ~size:0 ~align:1 []; long ] in
        check "no location, and the next integer takes %rdi"
          ((List.nth call.arguments 0).location = Nowhere
           && (List.nth call.arguments 1).location
              = Registers [ Integer_register 0 ]));

    pin "SV-14" "a MEMORY return is a hidden first argument" (fun () ->
        let big = array long ~count:3 in
        let call = place_call ~return:(Some big) [ long; double ] in
        check "returned in memory" (call.return = Returned_in_memory);
        check "the first integer argument takes %rsi"
          ((List.nth call.arguments 0).location
           = Registers [ Integer_register 1 ]);
        check "vector arguments are unaffected"
          ((List.nth call.arguments 1).location
           = Registers [ Vector_register { index = 0; eightbytes = 1 } ]));

    pin "SV-15" "a value is returned in the next register of its class" (fun () ->
        let ret ty = place_return (Some ty) in
        check "void" (place_return None = Void);
        check "int" (ret int_ = Returned_in [ Integer_return 0 ]);
        check "pointer" (ret ptr = Returned_in [ Integer_return 0 ]);
        check "__int128 in %rax:%rdx"
          (ret (sc Int128) = Returned_in [ Integer_return 0; Integer_return 1 ]);
        check "double" (ret double = Returned_in [ Vector_return { index = 0; eightbytes = 1 } ]);
        check "{double, double} in %xmm0:%xmm1"
          (ret (strukt ~size:16 ~align:8 [ (0, double); (8, double) ])
           = Returned_in [ Vector_return { index = 0; eightbytes = 1 };
                           Vector_return { index = 1; eightbytes = 1 } ]);
        check "{long, double} in %rax and %xmm0"
          (ret (strukt ~size:16 ~align:8 [ (0, long); (8, double) ])
           = Returned_in [ Integer_return 0;
                           Vector_return { index = 0; eightbytes = 1 } ]);
        check "{double, long} in %xmm0 and %rax"
          (ret (strukt ~size:16 ~align:8 [ (0, double); (8, long) ])
           = Returned_in [ Vector_return { index = 0; eightbytes = 1 };
                           Integer_return 0 ]);
        check "__m256 in %ymm0"
          (ret (sc M256) = Returned_in [ Vector_return { index = 0; eightbytes = 4 } ]);
        check "__m128 in %xmm0"
          (ret (sc M128) = Returned_in [ Vector_return { index = 0; eightbytes = 2 } ]);
        check "long double in %st0" (ret (real Long_double) = Returned_in [ X87_return ]);
        check "long double complex in %st0, %st1"
          (ret (Complex Long_double) = Returned_in [ X87_complex_return ]);
        check "double complex in %xmm0:%xmm1"
          (ret (Complex Double)
           = Returned_in [ Vector_return { index = 0; eightbytes = 1 };
                           Vector_return { index = 1; eightbytes = 1 } ]);
        check "three longs in memory" (ret (array long ~count:3) = Returned_in_memory);
        check "a non-trivial object in memory"
          (ret (strukt ~trivial:false ~size:8 ~align:8 [ (0, long) ])
           = Returned_in_memory);
        check "an empty aggregate returns nothing"
          (ret (strukt ~size:0 ~align:1 []) = Void));

    pin "SV-16" "a variadic call's %al bounds the vector registers used" (fun () ->
        check "none" ((place_call ~return:None [ long; ptr ]).vector_registers_used = 0);
        check "three doubles"
          ((place_call ~return:None [ ptr; double; double; double ])
             .vector_registers_used = 3);
        check "a vector register shared by SSE and SSEUP counts once"
          ((place_call ~return:None [ sc M256 ]).vector_registers_used = 1);
        check "never more than eight"
          ((place_call ~return:None (List.init 12 (fun _ -> double)))
             .vector_registers_used = 8));

    pin "SV-17" "types are written as S-expressions" (fun () ->
        let parse text = ctype_of_sexp (Sexplib.Sexp.of_string text) in
        check "scalars" (parse "Pointer" = ptr && parse "Double" = double);
        check "complex" (parse "(Complex Long_double)" = Complex Long_double);
        let text =
          "(Aggregate ((size 16) (align 8) \
           (fields (((offset 0) (ty Int)) ((offset 4) (ty Int)) \
           ((offset 8) (ty Double))))))" in
        check "aggregate with the default trivial"
          (parse text
           = strukt ~size:16 ~align:8 [ (0, int_); (4, int_); (8, double) ]);
        check "non-trivial"
          (parse "(Aggregate ((size 8) (align 8) (fields ()) (trivial false)))"
           = strukt ~trivial:false ~size:8 ~align:8 []);
        check "round trip"
          (ctype_of_sexp (sexp_of_ctype (parse text)) = parse text);
        List.iter (fun bad ->
            check ("rejects " ^ bad)
              (match parse bad with exception _ -> true | _ -> false))
          [ "Quad"; "(Complex Int)"; "(Aggregate ((size 8)))";
            "(Aggregate ((size 8) (align 8) (fields (((offset 0))))))" ]);

    pin "SV-18" "a nested aggregate is classified before it merges into its parent"
      (fun () ->
        (* union { long double; long long; long; __int128 }: the X87 eightbytes
           meet INTEGER inside, and INTEGER wins (rule d). *)
        let inner =
          strukt ~size:16 ~align:16
            [ (0, real Long_double); (0, sc Long_long); (0, long);
              (0, array (sc Int128) ~count:1) ] in
        check "inner" (classes inner = eb [ Integer; Integer ]);
        (* The parent adds a double and an __m128 (SSE) to the same
           eightbytes; with the inner already INTEGER the result is INTEGER.
           Merging the inner's leaves one by one would meet X87 with SSE
           first, which is MEMORY (rule e). *)
        let outer =
          strukt ~size:16 ~align:16 [ (0, double); (0, sc M128); (0, inner) ] in
        check "outer" (classes outer = eb [ Integer; Integer ]);
        check "returned in %rax:%rdx"
          (place_return (Some outer)
           = Returned_in [ Integer_return 0; Integer_return 1 ]));
  ]

let () = run "sysv" tests
