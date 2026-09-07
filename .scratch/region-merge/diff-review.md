# Diff review — control (c46454a) vs region-merge, all 35 gate binaries

Method: per-binary `diff` of `out_*.ll`; every hunk classified by
`stack_r[0-9]+`-renaming residue (alloca decls, `getelementptr` refs, region
operands). Residue = any changed line NOT matching the renaming shapes.

| binary | verdict | diff lines | non-renaming residue |
|---|---|---|---|
| alloca_vla | IDENTICAL | 0 | 0 |
| array_local | IDENTICAL | 0 | 0 |
| bitfield_struct | IDENTICAL | 0 | 0 |
| byte_copy | IDENTICAL | 0 | 0 |
| deep_chain | IDENTICAL | 0 | 0 |
| deep_recursion | IDENTICAL | 0 | 0 |
| factorial | renumbering only | 22 | 0 |
| fizzbuzz | renumbering only | 24 | 0 |
| fizzbuzz_safe | renumbering only | 54 | 0 |
| fptr_table | IDENTICAL | 0 | 0 |
| landmark_loop_1000 | renumbering only | 20 | 0 |
| list | IDENTICAL | 0 | 0 |
| many_args | IDENTICAL | 0 | 0 |
| mixed_fp_int | IDENTICAL | 0 | 0 |
| nested_calls | renumbering only | 20 | 0 |
| nested_struct | IDENTICAL | 0 | 0 |
| printf | IDENTICAL | 0 | 0 |
| ptr_chain | IDENTICAL | 0 | 0 |
| rec_struct | IDENTICAL | 0 | 0 |
| rmw_oob | IDENTICAL | 0 | 0 |
| setjmp_longjmp | renumbering only | 30 | 0 |
| setjmp_loop | IDENTICAL | 0 | 0 |
| sort | renumbering only | 68 | 0 |
| spill_many | IDENTICAL | 0 | 0 |
| sret_big | IDENTICAL | 0 | 0 |
| struct_arr_dynidx | IDENTICAL | 0 | 0 |
| struct_by_value | IDENTICAL | 0 | 0 |
| struct | IDENTICAL | 0 | 0 |
| tail_callish | IDENTICAL | 0 | 0 |
| union_overlap | IDENTICAL | 0 | 0 |
| va_arg_mixed | IDENTICAL | 0 | 0 |
| va_arg_vacopy | IDENTICAL | 0 | 0 |
| variadic | IDENTICAL | 0 | 0 |
| grep | renumbering only | 24 | 0 |
| gcc-12 | renumbering only | (31 allocas + GEPs) | 0 |

Summary: 25/35 byte-identical; 10/35 differ in `stack_rN` renumbering only;
zero non-renaming residue anywhere. The renumbering direction is ids now
ascending in lo (tie-broken lo/hi/tid).
