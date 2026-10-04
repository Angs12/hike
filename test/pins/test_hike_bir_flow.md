# BIR flow pins

| Pin | Behavior | Mutator | Expected failure |
|---|---|---|---|
| FLOW-01 | `Hike_bir_flow.run` propagates through CFG loops in both directions, dispatches def/phi/jmp transfers, and reverses block term order with `rev` | Ignore `rev` for CFG or term traversal, or skip one term callback | Forward and reverse block states lose the expected construct facts |
