# Pins: Hike_image

Module `src/hike_image.ml` (interface `src/hike_image.mli`).
One row per pin in `test/unit/test_image.ml` (ids `IMG-01`..`IMG-03`).

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
| IMG-01 | `rela_rows` reads `(site, type, addend)` from the RELA bytes: the addend is the `r_addend` field at offset 16, the type the low 32 bits of `r_info`, and a trailing partial entry is ignored. | read the addend from the `r_info` field (`rela_addend_off = 8`). | IMG-01 red: the row's addend is the type, not `0x11d0`. |
| IMG-02 | a RELATIVE word takes its runtime value, an externally-relocated word is dropped, the rest keep the file bytes; the section splits into the runs no dropped word interrupts. | leave the external word in place (drop the `dropped.(off+k) <- true` marking). | IMG-02 red: one fragment covers the whole section, so the fragment count and the word asserts fail. |
| IMG-03 | a section whose every word is externally relocated yields no image; a relocation-free section is its own bytes. | as IMG-02 (never mark a dropped byte). | IMG-03 red: the all-external section yields a fragment instead of `[]`. |
