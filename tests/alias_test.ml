(** Test for register alias resolution *)

open Format
open Base
open Bap.Std
open Bap_core_theory
open Theory.Alias
open Convlir

(* Helper functions to define register variables of various sizes *)
let bitv n = Theory.Bitv.define n
let r64 = bitv 64
let r32 = bitv 32
let r16 = bitv 16
let r8 = bitv 8
let r128 = bitv 128
let r256 = bitv 256
let var64 name = Theory.Var.define r64 name
let var32 name = Theory.Var.define r32 name
let var16 name = Theory.Var.define r16 name
let var8 name = Theory.Var.define r8 name
let var128 name = Theory.Var.define r128 name
let var256 name = Theory.Var.define r256 name

(* Define the 5 general-purpose 64-bit registers and their subregisters *)
let rax64 = var64 "RAX"
let eax32 = var32 "EAX"
let ax16 = var16 "AX"
let al8 = var8 "AL"
let ah8 = var8 "AH"
let rbx64 = var64 "RBX"
let ebx32 = var32 "EBX"
let bx16 = var16 "BX"
let bl8 = var8 "BL"
let bh8 = var8 "BH"
let rcx64 = var64 "RCX"
let ecx32 = var32 "ECX"
let cx16 = var16 "CX"
let cl8 = var8 "CL"
let ch8 = var8 "CH"
let rdx64 = var64 "RDX"
let edx32 = var32 "EDX"
let dx16 = var16 "DX"
let dl8 = var8 "DL"
let dh8 = var8 "DH"
let rsp64 = var64 "RSP"
let esp32 = var32 "ESP"
let sp16 = var16 "SP"
let spl8 = var8 "SPL"
(* note: no high byte for SP *)

(* XMM and YMM registers *)
let xmm0 = var128 "XMM0"
let ymm0 = var256 "YMM0"

(* Collect all variables for the target *)
let vars =
  [
    rax64;
    eax32;
    ax16;
    al8;
    ah8;
    rbx64;
    ebx32;
    bx16;
    bl8;
    bh8;
    rcx64;
    ecx32;
    cx16;
    cl8;
    ch8;
    rdx64;
    edx32;
    dx16;
    dl8;
    dh8;
    rsp64;
    esp32;
    sp16;
    spl8;
    xmm0;
    ymm0;
  ]

(* Define aliasing rules *)
let aliasing =
  [
    (* RAX *)
    def rax64 [ unk; reg eax32 ];
    def eax32 [ unk; reg ax16 ];
    def ax16 [ reg ah8; reg al8 ];
    (* RBX *)
    def rbx64 [ unk; reg ebx32 ];
    def ebx32 [ unk; reg bx16 ];
    def bx16 [ reg bh8; reg bl8 ];
    (* RCX *)
    def rcx64 [ unk; reg ecx32 ];
    def ecx32 [ unk; reg cx16 ];
    def cx16 [ reg ch8; reg cl8 ];
    (* RDX *)
    def rdx64 [ unk; reg edx32 ];
    def edx32 [ unk; reg dx16 ];
    def dx16 [ reg dh8; reg dl8 ];
    (* RSP *)
    def rsp64 [ unk; reg esp32 ];
    def esp32 [ unk; reg sp16 ];
    def sp16 [ unk; reg spl8 ];
    (* YMM0 contains XMM0 as low 128 bits *)
    def ymm0 [ unk; reg xmm0 ];
  ]

(* untype helper *)
let untyped = List.map ~f:Theory.Var.forget
let ( @< ) xs ys = untyped xs @ untyped ys

(* Register roles: mark which registers are aliases *)
let regs =
  Theory.Role.Register.
    [
      ( [ general; integer ],
        [ rax64 ] @< [ rbx64 ] @< [ rcx64 ] @< [ rdx64 ] @< [ rsp64 ] );
      ([ stack_pointer ], untyped [ rsp64 ]);
      ([ general; floating ], untyped [ ymm0 ]);
      ( [ alias ],
        untyped
          [
            eax32;
            ax16;
            al8;
            ah8;
            ebx32;
            bx16;
            bl8;
            bh8;
            ecx32;
            cx16;
            cl8;
            ch8;
            edx32;
            dx16;
            dl8;
            dh8;
            esp32;
            sp16;
            spl8;
            xmm0;
          ] );
    ]

(* Memory variable *)
let mem = Theory.Mem.define r64 r8
let data = Theory.Var.define mem "mem"

let target =
  Theory.Target.declare ~package:"sim" "x86_64_test" ~bits:64 ~byte:8 ~data
    ~code:data ~vars:(untyped vars) ~regs ~aliasing
    ~endianness:Theory.Endianness.le

let test_unaliased_reg_exp () =
  let size_of_name name =
    match name with
    | "RAX" | "RBX" | "RCX" | "RDX" | "RSP" -> 64
    | "EAX" | "EBX" | "ECX" | "EDX" | "ESP" -> 32
    | "AX" | "BX" | "CX" | "DX" | "SP" -> 16
    | "AL" | "BL" | "CL" | "DL" | "SPL" | "AH" | "BH" | "CH" | "DH" -> 8
    | "XMM0" -> 128
    | "YMM0" -> 256
    | _ -> 64 (* fallback *)
  in
  let test_reg name expected_exp =
    let size = size_of_name name in
    let reg = Var.create name (Imm size) in
    let result = Ppllvm.unaliased_reg_exp reg in
    let result_str =
      match result with
      | Bil.Var v -> Var.name v
      | Bil.Extract (hi, lo, Bil.Var v) ->
          Printf.sprintf "Extract(%d, %d, %s)" hi lo (Var.name v)
      | _ -> "other"
    in
    if String.equal result_str expected_exp then
      printf "PASS: %s -> %s\n" name result_str
    else printf "FAIL: %s -> %s, expected %s\n" name result_str expected_exp
  in

  printf "Testing unaliased_reg_exp...\n";
  test_reg "RAX" "RAX";
  test_reg "EAX" "Extract(31, 0, RAX)";
  test_reg "AX" "Extract(15, 0, RAX)";
  test_reg "AL" "Extract(7, 0, RAX)";
  test_reg "AH" "Extract(15, 8, RAX)";
  test_reg "RBX" "RBX";
  test_reg "EBX" "Extract(31, 0, RBX)";
  test_reg "BX" "Extract(15, 0, RBX)";
  test_reg "BL" "Extract(7, 0, RBX)";
  test_reg "BH" "Extract(15, 8, RBX)";
  test_reg "RCX" "RCX";
  test_reg "ECX" "Extract(31, 0, RCX)";
  test_reg "CX" "Extract(15, 0, RCX)";
  test_reg "CL" "Extract(7, 0, RCX)";
  test_reg "CH" "Extract(15, 8, RCX)";
  test_reg "RDX" "RDX";
  test_reg "EDX" "Extract(31, 0, RDX)";
  test_reg "DX" "Extract(15, 0, RDX)";
  test_reg "DL" "Extract(7, 0, RDX)";
  test_reg "DH" "Extract(15, 8, RDX)";
  test_reg "RSP" "RSP";
  test_reg "ESP" "Extract(31, 0, RSP)";
  test_reg "SP" "Extract(15, 0, RSP)";
  test_reg "SPL" "Extract(7, 0, RSP)";
  test_reg "XMM0" "Extract(127, 0, YMM0)";
  test_reg "YMM0" "YMM0"

let () =
  Ppllvm.test_setup target;
  printf "Running alias resolution tests...\n";
  test_unaliased_reg_exp ();
  printf "\nDone.\n"
