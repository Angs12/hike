# Ticket 05 — ref → fold conversions (+ the never-convert keep-list)

Deps: lands with/after its natural merge tickets (the Kosaraju refs ride
ticket 04's functorization; the frame-geometry refs ride ticket 06's
geometry merge). One battery-verified commit for the standalone items.

Convert (each verified a plain accumulator this session):
- The KB map-join's base/conflict ref pair → one fold that keeps the FIRST
  conflict (the pair exists only to early-exit semantics; the fold preserves
  them: first conflict wins, base extends).
- The VSA pass's per-sub tag map ref → the per-sub computation is pure:
  fold the subs into the map BEFORE the single KB write (deletes the
  monad-iter-plus-ref shape; the write stays one call).
- The DCE load-mem collector's accumulator ref → the pure
  visitor-accumulator pattern the stack model already uses (the function
  is called once per def in the census — the fold shape is identical).
- The frame-geometry triple max refs → one fold returning the triple
  (rides the geometry merge; listed here so the conversion is deliberate).
- The two byte-assembly for-loops (the .text constant loader, the section
  initializer) → fold over the index range. These are hot emission paths:
  verify neutrality by byte-identity, and if a fold costs readability,
  keep the for-loop — the win is deleting the `ref`, not the loop.
- The Kosaraju block's six refs → die inside the generic-SCC merge.
- The KB read's single ref → KEEP (it is the monad-escape idiom: the
  library callback cannot return a value; document it as such in a
  one-line comment so the next census doesn't flag it).

NEVER-CONVERT keep-list (recorded so no future pass lands these; each is
load-bearing mutable state or a sanctioned closure idiom):
- The shared per-SCC walk-budget cell (a ref field SHARES the cell across
  context copies — the binding-regime seam; converting it to a fold breaks
  the sharing by construction).
- The worklist fixpoint driver's state (pending set, counters, the
  solution cell) — the fixpoint is a mutable worklist by design (the C8
  lane's whole point); `pop_min`'s scan is ticket 07's measurement item,
  not a ref removal.
- The memo/stages debug counters (the sanctioned debug regime; production
  arms are compiled out).
- The flag/latch/widening-head globals in the landmark module (paper-
  faithful acquisition windows; the API is global by design).
- The emitter context's ref fields (the KB-threaded maps — the seam's
  contract).
- The undef-warned per-sub cell in the emitter (a memo inserted into the
  context map; a fold can't replace a per-key memo).
- The growth-closure `derived` set in the escape analysis (a fixpoint
  growth loop, not a fold).

Acceptance: full battery; corpus IR byte-identity 32/32; for the hot-path
byte-assembly conversions, byte-identity is the neutrality proof. The
mutate-census grep after this ticket should return exactly the keep-list
plus the debug counters.
