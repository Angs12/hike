# Pins — test_dce

Module: `test/unit/test_dce.ml` (group `dce`, ids `DCE-01`…`DCE-02`).
Production mechanism: `Hike.Dce.dce_sub`, the narrow dead-code rule: only
target flags and virtual temporaries are candidates; named non-flag values
and memory accesses stay.

| id | mechanism | disable recipe | red evidence |
|----|-----------|----------------|--------------|
| DCE-01 | Unread target flags and virtual temporaries are removed; named non-flag defs and memory stores stay. | Drop the flag/virtual liveness check so every unread def is kept. | DCE-01 removed FAILs: the unread virtual or flag survives. |
| DCE-02 | A flag read by a jump condition stays. | Treat jump conditions as non-reads when computing liveness. | DCE-02 FAILs: the flag is removed. |
