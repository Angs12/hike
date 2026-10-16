# BIR flow pins

| Pin | Behavior | Mutator | Expected failure |
|---|---|---|---|
| FLOW-01 | `Hike_bir_flow.run` propagates through CFG loops in both directions, dispatches def/phi/jmp transfers, and reverses block term order with `rev` | Ignore `rev` for CFG or term traversal, or skip one term callback | Forward and reverse block states lose the expected construct facts |
| FLOW-02 | `Hike_bir_flow.liveness` (per-block gen/kill compiled once) equals the closure-driven reverse `run` over a loop with in-block kills and a phi that kills nothing | Let the phi kill its writes, drop a def's kill from the gen/kill composition, or compose kills in the wrong order | The compiled `before`/`after` states differ from the reference states |
