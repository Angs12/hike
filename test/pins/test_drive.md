# Program discovery pins

| Pin | Invariant |
|---|---|
| DRIVE-01 | `Hike.Drive.run` returns decoded raw BIR, leaves final analysis facts alone, and keeps discovery's origin stamps internal. |
| DRIVE-02 | Conditional successors and raw flag expressions survive discovery for the registered jump compiler. |

Both use minimal x86-64 ELF fixtures through the production program seam,
with the LLVM loader pinned. No compiler or external corpus is required.
