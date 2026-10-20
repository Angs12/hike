# Pins — test_drive

Module: `test/unit/test_drive.ml` (group `drive`, ids `DRIVE-01`…`DRIVE-03`).
Production mechanism: `Hike.Drive` / `Hike.Decode`, discovery over the
decoder's own scan (ADR 0032). Fixtures are hand-assembled binaries with
code at `0x400078`.

| id | mechanism | disable recipe | red evidence |
|----|-----------|----------------|--------------|
| DRIVE-01 | A project loaded without BAP's disassembly still discovers its program, facts, and symbol table. | Require `Project.program` to be non-empty before running discovery. | DRIVE-01.program/facts/symtab FAIL: the empty project discovers nothing. |
| DRIVE-02 | Discovery gives the same program and symbol table with and without BAP's disassembly. | Seed discovery from the existing `Project.program`. | DRIVE-02.program or DRIVE-02.symtab FAIL: the two loads disagree. |
| DRIVE-03 | A fresh scan's symbol table matches the one BAP's disassembly builds. | Skip the scan's root symbolization. | DRIVE-03 FAILs: the symbol tables differ. |
