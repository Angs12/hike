#include <caml/mlvalues.h>
#include <caml/custom.h>
#include <llvm-c/Core.h>

/* LLVM 19's OCaml pointer conversion and builder representation. */
extern value to_val(void *ptr);
extern void *from_val(value v);
#define Hike_builder(v) (*(LLVMBuilderRef *)Data_custom_val(v))

CAMLprim value hike_build_fence(value ordering, value builder) {
  LLVMBuildFence(Hike_builder(builder), Int_val(ordering), 0, "");
  return Val_unit;
}

CAMLprim value hike_build_cmpxchg(value ptr, value expected, value desired,
                                value builder) {
  LLVMValueRef result = LLVMBuildAtomicCmpXchg(
      Hike_builder(builder), from_val(ptr), from_val(expected), from_val(desired),
      LLVMAtomicOrderingSequentiallyConsistent,
      LLVMAtomicOrderingSequentiallyConsistent, 0);
  return to_val(result);
}

CAMLprim value hike_atomic_load_seq_cst(value instruction) {
  LLVMSetOrdering(from_val(instruction), LLVMAtomicOrderingSequentiallyConsistent);
  return Val_unit;
}
