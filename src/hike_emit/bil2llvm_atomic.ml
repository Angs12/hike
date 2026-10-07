(* Constructors missing from LLVM's OCaml bindings, using the same C API. *)
external fence : Llvm.AtomicOrdering.t -> Llvm.llbuilder -> unit
  = "hike_build_fence"

external cmpxchg :
  Llvm.llvalue -> Llvm.llvalue -> Llvm.llvalue -> Llvm.llbuilder -> Llvm.llvalue
  = "hike_build_cmpxchg"
