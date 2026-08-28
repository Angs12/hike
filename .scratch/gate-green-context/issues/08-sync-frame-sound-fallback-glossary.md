# 08: Sync Frame + Sound Fallback glossary

**What to build:** The Frame and Sound Fallback entries describe the partitioned/degraded geometry actually emitted, so the fallback doctrine is checkable against `check_allocas.sh` (d).

**Blocked by:** 07: Sync Stack Access + VSA Tag glossary

**Status:** ready-for-agent

- [ ] `Frame` defined as `sub_frame{frame,stack,regions,is_precise}` with B1 partitioned (escape slots in frame + split regions) and S2 one-big `stack_rN` via `degraded_dims` with `64MiB` cap, `frame=None` when precise
- [ ] `Sound Fallback` defined as `degraded = has_indirect_jump ∨ Fixpoint_not_converged`, falling back to S2 GEP `stack_rN` except cap-fail `inttoptr`; dead-path untagged stays warned `poison`
- [ ] `Avoid` lists no longer ban `span`/`stack` when referring to `region.span` or `hike_stack`
