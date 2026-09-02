# 01 — Diagnose and fix the 100%-Tagging-Invariant gaps (restore the hard check)

**Status:** needs-triage
**Depends on:** none
**Blocks:** none

**What to build:** the 100% VSA Tagging Invariant (every `stack_access`-tagged
def carries a `vsa_info` tag) currently holds on the 32-binary corpus but is
VIOLATED on real big binaries: full conversions warn-enumerate the gaps
(/usr/bin/ls: 3 — sub_18270/sub_18440/sub_6a60; /usr/bin/sort: 13;
/usr/bin/df: 1). Diagnose the class (which sub shape produces a tagged def
the offsets walk never tags), fix the walk, and RESTORE the hard
`failwith`-grade check (the current state: warning-neutralized at
hike_vsa.ml's invariant check, per the user's 2026-09-01 "later fix" ruling).

Note: the restriction-removal spec (.scratch/restriction-removal/spec.md)
DELETES the `stack_access` tag entirely and makes the invariant structural
(an access is a stack access iff it carries vsa_info) — if that spec lands
first, this ticket reduces to verifying no gap warnings remain and deleting
the check outright.

Acceptance:
- [ ] The gap class diagnosed with a minimal reproducer (fixture or sub).
- [ ] Fixed; the big-binary conversions (ls/sort/df) emit ZERO gap warnings.
- [ ] The hard invariant restored (or deleted per the restriction-removal
      structural form, whichever lands).
- [ ] Full gate battery green (runtest / corpus 32/32 / allocas 128/0 /
      semantics 29/3+8/8) + big-binary conversions still complete rc=0.
