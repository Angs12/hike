# Extract-of-concat pins (`test_concat.ml`)

One row per pin. The normalization looks through a same-block concat
temporary so a field inside one operand never meets the domain's concat
hull (x86 `div`: `t := rem.quot; RAX := 63:0[t]`).

| id | mechanism | disable recipe | red evidence |
|----|-----------|----------------|--------------|
| CC-01 | A field covering a whole operand of a concat temporary reads that operand. | Drop the `reduce` branch for `hi < wb` / `lo >= wb`. | CC-01 red: the extracts keep `Var t`. |
| CC-02 | A field inside one operand extracts from that operand alone. | Return the whole operand regardless of the field. | CC-02 red: the field bits are lost. |
| CC-03 | A field spanning both operands keeps the concat. | Reduce when the field straddles the boundary. | CC-03 red: the rhs changes. |
| CC-04 | A redefined operand ends the look-through. | Skip the kill step in `normalize_block`. | CC-04 red: the extract reads the stale operand. |
| CC-05 | An operand that reads memory is not duplicated. | Drop the `stable` guard. | CC-05 red: the load is copied into the extract. |
| CC-06 | A literal concat under an extract reduces in place. | Look only through temporaries. | CC-06 red: the concat survives. |
| CC-07 | Through the solve, the extracted quotient of a `div`-shaped concat is not TOP. | Skip `Hike_concat.normalize`. | CC-07 red: the extract is TOP before and after. |
