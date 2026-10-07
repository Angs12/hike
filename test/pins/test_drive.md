# Program discovery pins

| Pin | Invariant |
|---|---|
| DRIVE-01 | `Hike.Drive.run` returns decoded raw BIR, leaves final analysis facts alone, and keeps discovery's origin stamps internal. |
| DRIVE-02 | Conditional successors and raw flag expressions survive discovery for the registered jump compiler. |
| DRIVE-03 | A resolved indirect jump target is decoded as a block of its owner, without becoming a function root through the code-value scan. |
| DRIVE-04 | BAP discovers a separate function from a resolved indirect call destination supplied through instruction semantics. |

All use minimal x86-64 ELF fixtures through the production program seam,
with a `.text` section and the LLVM loader pinned. No compiler or external corpus is required.
