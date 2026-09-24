# test_wto pins

Source: `test_cbat/test_wto.ml`. Target: `test/unit/test_wto.ml`.
31 pins. Every surviving assertion migrated; none retired.

The red-evidence cells below state the expected failure mode; the recipes
are textual, so no measured red is claimed here.

| id | mechanism | disable recipe | red evidence |
|----|-----------|----------------|--------------|
| WTO-01 | `Cbat_wto.flatten_comps` emits all blocks with each head before its members | in `src/cbat_vsa/cbat_wto.ml` `flatten_comps`, emit `inner` before `h` in the `SCC` arm | to be recorded |
| WTO-02 | `Cbat_wto.heads_of_comps` reaches innermost nested SCCs; vertices contribute no heads | in `heads_of_comps`, drop the `inner` recursion so only the outermost head is collected | to be recorded |
| WTO-03 | An acyclic graph yields no SCC heads | in `Cbat_wto.wto`, wrap every multi-successor vertex in `SCC` regardless of back-reachability | to be recorded |
| WTO-04 | An acyclic graph's components are all `Vertex` | in `Cbat_wto.wto`, wrap a diamond join in `SCC` (false head) | to be recorded |
| WTO-05 | A self-loop vertex is its own head with no inner members | in `Cbat_wto.wto`, skip the self-edge when computing heads | to be recorded |
| WTO-06 | A two-node cycle is one `SCC` headed by the cycle entry | in `Cbat_wto.wto`, pick the last vertex of the SCC as head instead of the entry | to be recorded |
| WTO-07 | `flatten_comps` puts the cycle head first | in `flatten_comps`, reorder the `SCC` arm to emit members before the head | to be recorded |
| WTO-08 | Battery: every vertex appears exactly once in the flattened order | in `flatten_comps`, duplicate the head into the flattened list | to be recorded |
| WTO-09 | Battery: every head lies on a cycle (no spurious widening points) | in `Cbat_wto.wto`, add a non-cyclic join block to `heads` | to be recorded |
| WTO-10 | Battery: every nontrivial graph SCC is exactly one WTO component's member set | in `Cbat_wto.wto`, split a loop's SCC into two components | to be recorded |
| WTO-11 | Battery: every nontrivial graph SCC contains one of the heads | in `Cbat_wto.wto`, omit the head from an emitted loop `SCC` | to be recorded |
| WTO-12 | Battery: `heads_of_comps` equals the forest's head set | in `heads_of_comps`, also return `Vertex` tids | to be recorded |
| WTO-13 | Integrated graph: heads are exactly the three loop heads | in `Cbat_wto.wto`, treat the `x` exit block as a head | to be recorded |
| WTO-14 | The inner loop's `SCC` is nested inside the outer loop's `SCC` | in `Cbat_wto.wto`, hoist the inner SCC to a sibling of the outer SCC | to be recorded |
| WTO-15 | Flatten order: heads first, inner body, outer tail, next loop | in `flatten_comps`, emit the outer tail before the inner body | to be recorded |
| WTO-16 | The inner loop's members stabilize before the outer tail | in `Cbat_wto.wto`, order the outer tail before the inner SCC | to be recorded |
| WTO-17 | Sequential loops are sibling components in traversal order | in `Cbat_wto.wto`, nest `l2`'s SCC inside `h1`'s SCC | to be recorded |
| WTO-18 | Reversed-accessor battery: every vertex appears exactly once | in `flatten_comps`, duplicate a head on the reversed ordering | to be recorded |
| WTO-19 | Reversed-accessor battery: every head lies on a cycle | in `Cbat_wto.wto`, let the reversed pred accessor mark a non-cycle vertex | to be recorded |
| WTO-20 | Reversed-accessor battery: each nontrivial SCC is one component's members | in `Cbat_wto.wto`, split an SCC under the reversed ordering | to be recorded |
| WTO-21 | Reversed-accessor battery: each nontrivial SCC contains a head | in `Cbat_wto.wto`, drop the head from a reversed loop SCC | to be recorded |
| WTO-22 | Reversed-accessor battery: `heads_of_comps` equals the head set | in `heads_of_comps`, include `Vertex` tids under the reversed ordering | to be recorded |
| WTO-23 | `Cbat_wto.Scc.partition` isolates a 2-cycle and a singleton | in `src/cbat_vsa/cbat_wto.ml` `Scc.partition`, skip the transpose pass so components merge | to be recorded |
| WTO-24 | `Scc.partition` keeps two cycles joined by a bridge as two disjoint components | in `Scc.partition`, union bridge-reachable components | to be recorded |
| DG-01 | `Cbat_dispatch_graph.make` adds resolved in-sub targets to the dispatch block's successors, filtered and deduplicated | in `src/cbat_vsa/cbat_dispatch_graph.ml` `make`, skip the `blocks` filter or drop the dedup | to be recorded |
| DG-02 | `make` mirrors each extra edge into the fresh target's predecessor list | in `make`, omit the predecessor mirror | to be recorded |
| DG-03 | `make` keeps no duplicate mirror when the target is already a base successor | in `make`, add an unguarded mirror for base successors | to be recorded |
| DG-04 | An empty resolved map yields the plain CFG | in `make`, add a synthetic extra edge even with an empty resolved map | to be recorded |
| DG-05 | The extra resolved edge alone closes the loop's WTO component | in `make`, drop the extra edge so the loop stays acyclic | to be recorded |
| DG-06 | A completed dispatch's case edges are term edges, one per target | in `make`, filter the rewrite's term edges out of the successor list | to be recorded |
| DG-07 | The completed dispatch's case target mirrors into preds | in `make`, omit the predecessor mirror for term edges | to be recorded |
