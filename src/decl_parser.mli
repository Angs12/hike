type functype =
  | Void
  | Pointer
  | Int of int
  | Half
  | Bfloat
  | Float
  | Double
  | FP128
  | X86fp80
  | PPCfp128
  | X86amx
  | Struct of functype list

type funcdef = { return : functype; args : functype list }
type libcmap = funcdef Map.Make(String).t

val parse_header_file : string -> libcmap
val functype_to_lltype : Llvm.llcontext -> functype -> Llvm.lltype
