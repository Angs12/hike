# 02: Fix bitfield sign-extension for negative sub-word fields (bitfield_struct)

**What to build:** When BAP lifts a C bitfield struct like

```c
struct BitFields { int a : 3; int b : 5; int c : 24; };
bf.a = -1;  bf.b = -8;
printf("a=%d b=%d\n", bf.a, bf.b);
```

the lifted bitfield read of `bf.b` (5-bit signed field = -8) returns `-7`
instead of `-8`. The store path packs the 5-bit field into the byte with
a mask that leaves the sign bit of `b` at the wrong position; the read
path then `ashr`s by 3 against an `i8` that contains extra junk bits,
producing `-7` instead of `-8`.

**Blocked by:** None (can start immediately; independent of issue 01).

**Status:** ready-for-agent

## Symptom fingerprint

`/tmp/corpus/bitfield_struct` (native) prints:
```
a=3 b=-15 c=12345
a=-1 b=-8
```

The lifted binary (`/tmp/heritage_p5/out_bitfield_struct.ll`) prints:
```
a=3 b=-15 c=12345
a=-1 b=-7      <-- b=-8 mis-read as -7
```

The first line matches (positive `b=-15` happens to extract correctly
because the sign bit doesn't interact with the 3-bit `a` field above it).
The second line fails only when both `a` and `b` are negative: the
3-bit `a` field at bits 0-2 is `0b111`, the 5-bit `b` at bits 3-7 is
`0b11000`, packed byte = `0b111_11000 = 0xF8`. The expected
extraction `(byte >> 3) sign-extended` should give `-1`; the lifted code
emits a slightly different sequence (OR-merge + trunc + ashr 3) that
yields `0b11111001 = 0xF9` in the storage, then ashr 3 = `0b11111 = -1`
printed? — actually emits `-7` (`0b11111001` = 0xF9, ashr 3 = 0xFF = -1
in arithmetic; the printed -7 is the i32 sign-extension of an i8 result
that has bit 0 set somewhere). The precise mechanism is in
`/tmp/sem_diag/out_bitfield_struct_lifted.ll` lines 100-110:

```
%81 = or i32 %78, %80     ; OR the 5-bit b value into the low byte
%82 = trunc i32 %81 to i8 ; packed byte
%83 = zext i8 %82 to i64
%86 = trunc i64 %83 to i8
%87 = ashr i8 %86, 3       ; 3-bit arith shift — but b is 5 bits at offset 3
```

The `ashr i8 by 3` is the bug: it shifts the WHOLE 8-bit byte (including
the `a` field at bits 0-2) instead of the 5-bit `b` field, then sign-
extends. The fix is a `(byte >> 3) & 0x1F` mask followed by a 5-bit
arithmetic shift.

## Acceptance criteria

- [ ] `bash scripts/semantic/run_semantic.sh /tmp/corpus /tmp/heritage_p5 /tmp/sem_diag`
      reports `bitfield_struct` as PASS (currently FAIL)
- [ ] `/tmp/heritage_p5/out_bitfield_struct.ll` correctly extracts the
      5-bit signed field `b` for any value in `-16..15`, with correct
      sign extension
- [ ] The 3-bit signed field `a` continues to extract correctly (the first
      `a=3 b=-15 c=12345` line must remain byte-identical to native)
- [ ] `dune runtest` remains all-PASS
- [ ] `bash scripts/run_corpus.sh` remains 31/31 rc=0
- [ ] No regression on the other 10/11 semantic-gate failures (these
      should be fixed by issue 01, not this one)
- [ ] AGENTS.md "CURRENT VALIDATION STATE" updated with the new numbers
      and timestamp

## Out of scope

- The 10 sub-signature failures (issue 01)
- Changes to the bitfield syntax model (BAP-side)
- The 3 unit-test FAILs and the 3 surviving `hike: guarded:` warnings

## Diagnostic

- `bash /tmp/opencode/check_sem_failures.sh` — runs the binary through
  the harness and reports `bitfield_struct: OUT_DIFF(28b_vs_28b)` with
  the diff `b=-8 → b=-7` on line 4
- Native vs lifted stdout diff is at `/tmp/sem_diag/out_bitfield_struct_native.out`
  vs `/tmp/sem_diag/out_bitfield_struct_lifted.out`
