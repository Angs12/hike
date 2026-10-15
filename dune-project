(lang dune 3.23)

(using dune_site 0.1)

(name hike)

(generate_opam_files true)

(source
 (github Angs12/hike))

(authors "Angs12")

(maintainers "Angs12")

(package
 (name hike)
 (synopsis "Lifts x86-64 ELF binaries to LLVM IR through a value-set analysis")
 (description
  "A BAP plugin that lifts x86-64 ELF binaries to LLVM IR.  A vendored \
   value-set analysis attributes every memory access to a section; the \
   stack splits into real LLVM allocas (regions, VLA allocas, the \
   residue fallback), and the emitter renders the program through one \
   seam (bil2llvm) with the semantic harness as the acceptance oracle.")
 (depends
  ocaml
  dune
  bap
  llvm
  bap-core-theory
  bap-future
  bap-knowledge
  bap-main
  bitvec
  bin_prot
  core
  findlib
  graphlib
  monads
  ogre
  zarith
  unix
  (ppx_bap :build)
  (alcotest :with-test)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
