# Pins: Hike_image

Module `src/hike_image.ml` (interface `src/hike_image.mli`).
One row per pin in `test/unit/test_image.ml` (ids `IMG-02`..`IMG-08`; `IMG-01` is retired).

The module reads the ELF image the solve consumes.  A section whose words
the loader's relocation facts name is not its static image, so the pinned
mechanism substitutes each RELATIVE word with its runtime value (the RELA
addend plus the load bias) and drops each externally-relocated word — the
abstract read is the sound identity there.  A section is emitted as the
maximal fragments no dropped word interrupts, so a load spanning a dropped
word finds no image.

`rela_rows` and `substitute_relocated_words` are pure over bytes, so the
pins build their own RELA and section images.

Red evidence is by review: each disable recipe is the textual inversion of
the pinned branch, and the pin's exact assertion fails under it.

| id | mechanism | disable recipe | red evidence |
|----|-----------|----------------|--------------|
| IMG-02 | a RELATIVE word takes its runtime value, an externally-relocated word is dropped, the rest keep the file bytes; the section splits into the runs no dropped word interrupts. | leave the external word in place (drop the `dropped.(off+k) <- true` marking). | IMG-02 red: one fragment covers the whole section, so the fragment count and the word asserts fail. |
| IMG-03 | a section whose every word is externally relocated yields no image; a relocation-free section is its own bytes. | as IMG-02 (never mark a dropped byte). | IMG-03 red: the all-external section yields a fragment instead of `[]`. |

| IMG-04 | PT_TLS type, extent, first-byte alignment and file bytes come from Ogre, with no section table. | Ignore the type/alignment facts or round without the prefix. | The sectionless initialized layout assertions fail. |
| IMG-05 | A file-empty PT_TLS has a zero-only extent; filesz greater than memsz refuses. | Accept the invalid header. | The malformed-header refusal assertion fails. |
| IMG-06 | The protections are the PT_LOAD segments without PF_W (`Read_only`) plus each PT_GNU_RELRO range (`Relro`) with its end rounded down to the page (the loader's mprotect), from the `llvm:elf-program-header*` facts. A writable segment contributes nothing. | Drop the PF_W test, or keep the RELRO end unrounded. | IMG-06.ranges FAILs: the RW segment appears, or the RELRO range ends at 0x4020ff. |
| IMG-07 | `clip_image` keeps exactly the bytes of an image inside the ranges, one fragment per overlapping range. | Return the image unclipped. | IMG-07.fragments FAILs. |
| IMG-08 | `access` gives a range the protection that covers it wholly, `Read_only` before `Relro`; a range no protection covers, or one straddling a protection's end, is `Writable`. The emitter's section constness follows it; the analysis images clip to the same protections. | Answer `Read_only` for any overlap. | IMG-08.straddle FAILs. |
