# 06: Add landmark types to cbat_ai_representation + cbat_refinement

**What to build:** The abstract-domain representation and refinement carry a landmark environment so the CLP widening join can read/write it. This is the type-level foundation that lets T07 consume landmarks without a separate side channel.

**Blocked by:** T01 (Recover cbat_landmarks.ml (compiling API surface)).

**Status:** ready-for-agent

- [ ] `cbat_ai_representation` and `cbat_refinement` compile with a landmark-env field/parameter
- [ ] Existing representations unchanged in behavior
